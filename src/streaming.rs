use std::cmp::Ordering;
use std::collections::BinaryHeap;
use std::collections::VecDeque;
use std::fs;
use std::fs::File;
use std::fs::OpenOptions;
use std::io::prelude::*;
use std::io::{BufReader, BufWriter, Cursor, SeekFrom};
use std::mem;

use normalize::merge_terms;
use number::Number;
use serialize::SerializedTerm;
use sort::split_merge;
use structure::{Element, ElementPrinter, GlobalVarInfo, PrintMode, Statement, VarInfo};

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

#[derive(Debug)]
pub struct InputTermStreamer {
    input: Option<BufReader<File>>,      // the input file
    mem_buffer_input: VecDeque<Element>, // the memory buffer, storing unserialized terms
    termcounter_input: u64,              // input term count
}

impl InputTermStreamer {
    pub fn new(source: Option<BufReader<File>>) -> InputTermStreamer {
        InputTermStreamer {
            input: source,
            mem_buffer_input: VecDeque::with_capacity(SMALL_BUFFER as usize),
            termcounter_input: 0,
        }
    }

    // get the next term from the input
    pub fn read_term(&mut self) -> Option<Element> {
        if !self.mem_buffer_input.is_empty() {
            self.termcounter_input -= 1;
            return self.mem_buffer_input.pop_front();
        } else {
            // read the next terms from the input file,
            // so that the membuffer is filled
            if let Some(ref mut x) = self.input {
                for _ in 0..MAXTERMMEM {
                    if let Ok(e) = Element::deserialize(x) {
                        self.mem_buffer_input.push_front(e);
                    } else {
                        break;
                    }
                }

                if !self.mem_buffer_input.is_empty() {
                    self.termcounter_input -= 1;
                    return self.mem_buffer_input.pop_front();
                }
            }
        }
        None
    }

    pub fn add_term_input(&mut self, element: Element) {
        self.mem_buffer_input.push_back(element);
        self.termcounter_input += 1;
    }

    pub fn termcount(&self) -> u64 {
        self.termcounter_input
    }
}

// stream from file or from memory
#[derive(Debug)]
pub struct OutputTermStreamer {
    sortfiles: Vec<File>,            // the sort files, a buffer for each file
    mem_buffer: Vec<SerializedTerm>, // the memory buffer, storing unserialized terms
    termcounter: u64,                // current term count
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
            let map = split_merge(
                &mut self.mem_buffer,
                &|x1, x2| {
                    Element::compare_term_serialized(&mut Cursor::new(x1), &mut Cursor::new(x2))
                },
                &|x1: &mut SerializedTerm, x2: &mut SerializedTerm| {
                    Element::serialized_terms_add(&mut Cursor::new(x1), &mut Cursor::new(x2))
                },
            );

            let mut tmp = vec![SerializedTerm::default(); map.len()];
            for i in 0..map.len() {
                tmp[i] = mem::replace(&mut self.mem_buffer[map[i]], SerializedTerm::default());
            }
            self.mem_buffer = tmp;
        }

        if self.mem_buffer.len() < MAXTERMMEM {
            let mut buf = Cursor::new(vec![]);
            element.serialize_term(&mut buf);
            self.mem_buffer.push(SerializedTerm(buf.into_inner()));
        } else {
            unimplemented!();
            /*
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
            self.mem_buffer.push(element);*/
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
        input_streamer: &mut InputTermStreamer,
        module_name: &str,
        var_info: &mut VarInfo,
        sort_statements: &mut Vec<Statement>,
        mut print_output: bool,
        _write_log: bool,
    ) {
        let inpterm = input_streamer.termcount();
        let genterm = self.termcounter;

        self.termcounter = 0; // reset the output term counter
        input_streamer.termcounter_input = 0;

        assert!(input_streamer.mem_buffer_input.is_empty());

        let mut print_mode = PrintMode::Form;

        // can the sort be done completely in memory?
        if self.sortfiles.is_empty() {
            debug!("In-memory sorting {} terms", self.mem_buffer.len());

            //println!("pre-sort {:#?}", self.mem_buffer);

            let map = split_merge(
                &mut self.mem_buffer,
                &|x1, x2| {
                    Element::compare_term_serialized(&mut Cursor::new(x1), &mut Cursor::new(x2))
                },
                &|x1: &mut SerializedTerm, x2: &mut SerializedTerm| {
                    Element::serialized_terms_add(&mut Cursor::new(x1), &mut Cursor::new(x2))
                },
            );

            //println!("post-sort {:#?}", self.mem_buffer);

            let mut tmp = vec![SerializedTerm::default(); map.len()];
            for i in 0..map.len() {
                tmp[i] = mem::replace(&mut self.mem_buffer[map[i]], SerializedTerm::default());
            }
            self.mem_buffer.clear();

            input_streamer.input = None;

            // execute the global statements
            for s in sort_statements.drain(..) {
                match s {
                    /*Statement::Collect(ref v) => {
                        a = Element::Fn(false, v.clone(), vec![a]);
                    }*/
                    Statement::Print(mode, ref es) => {
                        if es.len() == 0 || es
                            .iter()
                            .any(|e| exprname == var_info.global_info.get_name(*e))
                        {
                            print_output = true;
                        }
                        print_mode = mode;
                    }
                    x => unreachable!("Unhandled sort statement: {}", x),
                }
            }

            // move to input buffer
            // TODO: keep the input buffer serialized too!
            input_streamer.mem_buffer_input = VecDeque::new();

            //println!("{:#?}", tmp);

            for x in mem::replace(&mut tmp, vec![]) {
                input_streamer
                    .mem_buffer_input
                    .push_back(x.deserialize().unwrap());
            }

            /*match a {
                Element::SubExpr(_, x) => input_streamer.mem_buffer_input = VecDeque::from(x),
                Element::Num(_, Number::SmallInt(0)) => {
                    input_streamer.mem_buffer_input = VecDeque::new();
                }
                x => {
                    input_streamer.mem_buffer_input = {
                        let mut v = VecDeque::new();
                        v.push_back(x);
                        v
                    }
                }
            }*/

            if print_output {
                println!("{} =", exprname);
                for x in &input_streamer.mem_buffer_input {
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

            input_streamer.termcounter_input = input_streamer.mem_buffer_input.len() as u64;

            println!(
                "{} --\tterms in: {}\t\tgenerated: {}\t\tterms out: {}",
                module_name, inpterm, genterm, input_streamer.termcounter_input
            );

            return;
        }

        unimplemented!()

        /*

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
                    input_streamer.termcounter_input += maxsortmem as u64 - 1;
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

                    self.mem_buffer[0] = self.mem_buffer.pop().unwrap();
                    self.mem_buffer.truncate(1);
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
                        if input_streamer.termcounter_input == 0 {
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
                        if es.len() == 0 || es
                            .iter()
                            .any(|e| exprname == var_info.global_info.get_name(*e))
                        {
                            print_output = true;
                        }
                        print_mode = mode;
                    }
                    x => unreachable!("Unhandled sort statement: {}", x),
                }
            }

            input_streamer.termcounter_input += self.mem_buffer.len() as u64;

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
            //mem::swap(&mut self.mem_buffer, &mut input_streamer.mem_buffer_input);
            input_streamer.mem_buffer_input =
                VecDeque::from(mem::replace(&mut self.mem_buffer, vec![]));

            let mut of = ofb.into_inner().unwrap();
            of.seek(SeekFrom::Start(0)).unwrap();
            input_streamer.input = Some(BufReader::new(of)); // set it as the new input

            println!(
                "{} --\tterms in: {}\t\t\tgenerated: {}\t\t\tterms out: {}",
                module_name, inpterm, genterm, input_streamer.termcounter_input
            );
        }

        let sortc = self.sortfiles.len();
        self.sortfiles.clear();

        // clean up all the sortfiles
        for x in 0..sortc {
            fs::remove_file(format!("{}.srt", x)).unwrap();
        }
        */
    }
}
