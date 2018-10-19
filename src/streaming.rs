use std::cmp::Ordering;
use std::collections::BinaryHeap;
use std::collections::VecDeque;
use std::fs;
use std::fs::File;
use std::fs::OpenOptions;
use std::io::prelude::*;
use std::io::{BufReader, BufWriter, SeekFrom};
use std::mem;

use normalize::merge_terms;
use number::Number;
use structure::{
    Element, ElementPrinter, GlobalVarInfo, PrintMode, PrintObject, Statement, VarInfo, VarName,
};

pub const MAXTERMMEM: usize = 10_000_000; // maximum number of terms allowed in memory
pub const SMALL_BUFFER: u64 = 100_000; // number of terms before sorting

#[derive(Clone)]
struct ElementStreamTuple<'a>(Element, &'a GlobalVarInfo, usize);

impl<'a> Ord for ElementStreamTuple<'a> {
    fn cmp(&self, other: &ElementStreamTuple) -> Ordering {
        // min order
        other.0.partial_cmp(&self.0, self.1, true).unwrap()
    }
}

// `PartialOrd` needs to be implemented as well.
impl<'a> PartialOrd for ElementStreamTuple<'a> {
    fn partial_cmp(&self, other: &ElementStreamTuple) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

// `PartialOrd` needs to be implemented as well.
impl<'a> PartialEq for ElementStreamTuple<'a> {
    fn eq(&self, other: &ElementStreamTuple) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl<'a> Eq for ElementStreamTuple<'a> {}

#[derive(Debug, Clone)]
pub struct InputExpression {
    pub name: VarName,
    mem_buffer: VecDeque<Element>,
    file_name: Option<String>, // name of the file, if it has any
    num_terms: usize,
}

impl InputExpression {
    pub fn new(name: VarName) -> InputExpression {
        InputExpression {
            name,
            mem_buffer: VecDeque::with_capacity(MAXTERMMEM),
            file_name: None,
            num_terms: 0,
        }
    }

    pub fn into_iter<'a>(&'a self) -> InputExpressionIterator<'a> {
        InputExpressionIterator {
            it: &self,
            file: self
                .file_name
                .as_ref()
                .map(|x| BufReader::new(File::open(x).unwrap())),
            count: 0,
            buffer: Element::default(),
        }
    }

    pub fn term_count(&self) -> usize {
        self.num_terms
    }
}

#[derive(Debug)]
pub struct InputExpressionIterator<'a> {
    it: &'a InputExpression,
    buffer: Element, // buffer for element read from file
    file: Option<BufReader<File>>,
    count: usize,
}

impl<'a> InputExpressionIterator<'a> {
    pub fn new(input: &InputExpression) -> InputExpressionIterator {
        InputExpressionIterator {
            it: input,
            file: input
                .file_name
                .as_ref()
                .map(|x| BufReader::new(File::open(x).unwrap())),
            count: 0,
            buffer: Element::default(),
        }
    }

    pub fn next(&mut self) -> Option<&Element> {
        if self.count < self.it.mem_buffer.len() {
            self.count += 1;
            return Some(&self.it.mem_buffer[self.count - 1]);
        } else {
            // read from file
            if let Some(ref mut x) = self.file {
                if let Ok(e) = Element::deserialize(x) {
                    self.buffer = e;
                    return Some(&self.buffer);
                } else {
                    // reset file buffer position
                    // TODO: not needed, we have our own bufreader and file
                    x.seek(SeekFrom::Start(0)).unwrap();
                    mem::replace(&mut self.buffer, Element::default());
                    None
                }
            } else {
                None
            }
        }
    }
}

#[derive(Debug)]
pub struct InputExpressionWriter<'a> {
    input: &'a mut InputExpression,
    file: Option<BufWriter<File>>,
}

impl<'a> InputExpressionWriter<'a> {
    pub fn new(source: &'a mut InputExpression) -> InputExpressionWriter {
        InputExpressionWriter {
            input: source,
            file: None,
        }
    }

    pub fn get_mem_buffer(&mut self) -> &mut VecDeque<Element> {
        &mut self.input.mem_buffer
    }

    pub fn add_term_input(&mut self, element: Element) {
        // TODO: write to file when the buffer is too big
        self.input.mem_buffer.push_back(element);
        self.input.num_terms += 1;
    }

    pub fn termcount(&mut self) -> usize {
        if self.input.num_terms < self.input.mem_buffer.len() {
            self.input.num_terms = self.input.mem_buffer.len();
        }
        self.input.num_terms
    }

    pub fn reset(&mut self) {}
}

// stream from file or from memory
#[derive(Debug)]
pub struct OutputTermStreamer {
    sortfiles: Vec<File>,     // the sort files, a buffer for each file
    mem_buffer: Vec<Element>, // the memory buffer, storing unserialized terms
    termcounter: u64,         // current term count
}

impl OutputTermStreamer {
    pub fn new() -> OutputTermStreamer {
        OutputTermStreamer {
            sortfiles: vec![],
            mem_buffer: vec![], // TODO: prevent internal allocation to go beyond MAXTERMMEM
            termcounter: 0,
        }
    }

    fn new_file(&mut self) {
        let file = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(true)
            .open(format!("{}.srt", self.sortfiles.len()))
            .unwrap();
        self.sortfiles.push(file); // FIXME: do here?
    }

    pub fn termcount(&self) -> u64 {
        self.termcounter
    }

    // add a term. First try to add it to the
    // in-memory buffer. If that one is full
    // write it to file
    pub fn add_term(&mut self, element: Element, var_info: &GlobalVarInfo) {
        // print intermediate statistics
        if self.termcounter >= SMALL_BUFFER && self.termcounter % SMALL_BUFFER == 0 {
            println!("    -- generated: {}", self.termcounter);

            // sort to potentially reduce the memory footprint
            let mut tmp = vec![];
            mem::swap(&mut self.mem_buffer, &mut tmp);
            let mut a = Element::SubExpr(true, tmp);
            a.normalize_inplace(var_info);

            match a {
                Element::SubExpr(_, ref mut x) => mem::swap(&mut self.mem_buffer, x),
                x => self.mem_buffer = vec![x],
            }
        }

        if self.mem_buffer.len() < MAXTERMMEM {
            self.mem_buffer.push(element);
        } else {
            // write the buffer to a new file
            if self.termcounter % MAXTERMMEM as u64 == 0 || self.sortfiles.is_empty() {
                println!("Creating new file {}", self.sortfiles.len());
                self.new_file();
            }

            let mut b = BufWriter::new(self.sortfiles.last().unwrap());

            for x in &self.mem_buffer {
                x.serialize(&mut b);
            }

            self.mem_buffer.clear();
            self.mem_buffer.push(element);
        }
        self.termcounter += 1;
    }

    /*
    pub fn print_info(&self, element: &Element, write_log: bool) {
        if write_log {
			// FIXME: filename
			let mut f = File::create("test.log").expect(&format!("Unable to create file {:?}", "test.log"));
        	writeln!(f, "{} -- \t terms in: {}\tgenerated: {}\tterms out: {}", module.name,
            	inpcount, genterms, outterms).unwrap();
        	writeln!(f, "{}", program.input).unwrap();
		}
    }*/

    /*
    Sort the output stream and create a new input stream.
    */
    pub fn sort(
        &mut self,
        exprname: &str,
        mut input_streamer: InputExpressionWriter,
        module_name: &str,
        var_info: &mut VarInfo,
        sort_statements: &mut Vec<Statement>,
        mut print_output: bool,
        _write_log: bool,
    ) {
        let inpterm = input_streamer.termcount();
        let genterm = self.termcounter;

        self.termcounter = 0; // reset the output term counter

        let mut print_mode = PrintMode::Form;

        // can the sort be done completely in memory?
        if self.sortfiles.is_empty() {
            debug!("In-memory sorting {} terms", self.mem_buffer.len());

            let mut tmp = vec![];
            mem::swap(&mut self.mem_buffer, &mut tmp);
            let mut a = Element::SubExpr(true, tmp);
            a.normalize_inplace(&var_info.global_info);

            // execute the global statements
            for s in sort_statements.drain(..) {
                match s {
                    Statement::Collect(ref v) => {
                        a = Element::Fn(false, v.clone(), vec![a]);
                    }
                    Statement::Print(mode, ref es) => {
                        if es.len() == 0 || es.iter().any(|e| {
                            if let PrintObject::Special(name) = e {
                                exprname == var_info.global_info.get_name(*name)
                            } else {
                                false
                            }
                        }) {
                            print_output = true;
                        }
                        print_mode = mode;
                    }
                    x => unreachable!("Unhandled sort statement: {}", x),
                }
            }

            // move to input buffer
            match a {
                Element::SubExpr(_, x) => *input_streamer.get_mem_buffer() = VecDeque::from(x),
                Element::Num(_, Number::SmallInt(0)) => {
                    *input_streamer.get_mem_buffer() = VecDeque::new();
                }
                x => {
                    *input_streamer.get_mem_buffer() = {
                        let mut v = VecDeque::new();
                        v.push_back(x);
                        v
                    }
                }
            }

            if print_output {
                println!("{} =", exprname);
                for x in input_streamer.get_mem_buffer() {
                    println!(
                        "\t+{}",
                        ElementPrinter {
                            element: x,
                            var_info: &var_info.global_info,
                            print_mode: print_mode
                        }
                    );
                }
            }

            println!(
                "{} --\tterms in: {}\t\tgenerated: {}\t\tterms out: {}",
                module_name,
                inpterm,
                genterm,
                input_streamer.termcount()
            );

            return;
        }

        // sort every sort file
        let mut x = self.sortfiles.len();
        loop {
            // the first buffer is in memory and doesn't have a file yet
            if x == self.sortfiles.len() {
                self.new_file();
            } else {
                let mut reader = BufReader::new(&self.sortfiles[x]);
                reader.seek(SeekFrom::Start(0)).unwrap();
                while let Ok(e) = Element::deserialize(&mut reader) {
                    self.mem_buffer.push(e);
                }
            }

            self.mem_buffer
                .sort_unstable_by(|l, r| l.partial_cmp(r, &var_info.global_info, true).unwrap());

            // write back
            self.sortfiles[x].set_len(0).unwrap(); // delete the contents
            self.sortfiles[x].seek(SeekFrom::Start(0)).unwrap();
            {
                let mut bw = BufWriter::new(&self.sortfiles[x]);
                for v in &self.mem_buffer {
                    v.serialize(&mut bw);
                }
            }
            self.mem_buffer.clear();

            self.sortfiles[x].seek(SeekFrom::Start(0)).unwrap(); // go back to start
            if x == 0 {
                break;
            }
            x -= 1;
        }

        self.mem_buffer = vec![]; // replace by empty vector, so memory is freed
        let maxsortmem = MAXTERMMEM / self.sortfiles.len() + 1;

        if maxsortmem < 2 {
            panic!("NOT ENOUGH MEM");
        }

        {
            // FIXME: a buffered reader may read too much, so there is less ram
            // the bufreader should read at most maxsortmem
            let mut streamer = self
                .sortfiles
                .iter()
                .map(BufReader::new)
                .collect::<Vec<_>>();

            // create the output file, which will be the new input
            let of = OpenOptions::new()
                .read(true)
                .write(true)
                .create(true)
                .truncate(true)
                .open("input.srt")
                .unwrap();

            let mut ofb = BufWriter::new(of);

            self.mem_buffer.clear();

            let mut heap = BinaryHeap::new();

            // populate the heap with an element from each bucket
            for (i, mut s) in streamer.iter_mut().enumerate() {
                if let Ok(e) = Element::deserialize(&mut s) {
                    heap.push(ElementStreamTuple(e, &var_info.global_info, i));
                }
            }

            while let Some(ElementStreamTuple(mut mv, vi, i)) = heap.pop() {
                // add or merge the new term into the buffer
                if self.mem_buffer.is_empty() {
                    self.mem_buffer.push(mv);
                } else {
                    let mut tmp = Element::default();
                    mem::swap(self.mem_buffer.last_mut().unwrap(), &mut tmp);
                    match tmp.partial_cmp(&mv, &vi, true) {
                        Some(Ordering::Equal) => {
                            if merge_terms(&mut tmp, &mut mv, &vi) {
                                self.mem_buffer.pop();
                            } else {
                                mem::swap(self.mem_buffer.last_mut().unwrap(), &mut tmp);
                            }
                        }
                        _ => {
                            mem::swap(self.mem_buffer.last_mut().unwrap(), &mut tmp);
                            self.mem_buffer.push(mv);
                        }
                    }
                }

                if self.mem_buffer.len() == maxsortmem {
                    for x in &self.mem_buffer[..maxsortmem - 1] {
                        println!(
                            "\t+{}",
                            ElementPrinter {
                                element: x,
                                var_info: &vi,
                                print_mode: print_mode
                            }
                        );
                        x.serialize(&mut ofb);
                    }

                    let last = self.mem_buffer.pop().unwrap();

                    for x in self.mem_buffer.drain(..) {
                        input_streamer.add_term_input(x);
                    }

                    // make sure one element is left
                    self.mem_buffer.push(last);
                }

                // push new objects to the queue
                if let Ok(e) = Element::deserialize(&mut streamer[i]) {
                    heap.push(ElementStreamTuple(e, vi, i))
                }
            }

            // execute the global statements
            for s in sort_statements.drain(..) {
                match s {
                    Statement::Collect(ref v) => {
                        // does the output fit in memory?
                        if input_streamer.termcount() > MAXTERMMEM {
                            self.mem_buffer = vec![Element::Fn(
                                false,
                                v.clone(),
                                mem::replace(&mut self.mem_buffer, vec![]),
                            )];
                        } else {
                            panic!("Cannot collect, since output does not fit in memory.");
                        }
                    }
                    Statement::Print(mode, ref es) => {
                        if es.len() == 0 || es.iter().any(|e| {
                            if let PrintObject::Special(name) = e {
                                exprname == var_info.global_info.get_name(*name)
                            } else {
                                false
                            }
                        }) {
                            print_output = true;
                        }
                        print_mode = mode;
                    }
                    x => unreachable!("Unhandled sort statement: {}", x),
                }
            }

            if print_output {
                println!("{} =", exprname);
                for x in &self.mem_buffer {
                    println!(
                        "\t+{}",
                        ElementPrinter {
                            element: x,
                            var_info: &var_info.global_info,
                            print_mode: print_mode
                        }
                    );
                }
            }

            // move the mem_buffer to the input buffer
            for x in self.mem_buffer.drain(..) {
                input_streamer.add_term_input(x);
            }

            println!(
                "{} --\tterms in: {}\t\t\tgenerated: {}\t\t\tterms out: {}",
                module_name,
                inpterm,
                genterm,
                input_streamer.termcount()
            );
        }

        let sortc = self.sortfiles.len();
        self.sortfiles.clear();

        // clean up all the sortfiles
        for x in 0..sortc {
            fs::remove_file(format!("{}.srt", x)).unwrap();
        }
    }
}
