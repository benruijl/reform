use std::io::prelude::*;
use std::fs;
use std::fs::File;
use std::fs::OpenOptions;
use std::io::{BufReader, BufWriter, SeekFrom};
use std::collections::BinaryHeap;
use std::cmp::Ordering;
use std::mem;

use structure::{Element, VarInfo, ElementPrinter, Func, Statement};
use normalize::merge_terms;

pub const MAXTERMMEM: usize = 10000000; // maximum number of terms allowed in memory

#[derive(Clone, Eq, PartialEq)]
struct ElementStreamTuple(Element, usize);

impl Ord for ElementStreamTuple {
    fn cmp(&self, other: &ElementStreamTuple) -> Ordering {
        // min order
        other.0.cmp(&self.0)
    }
}

// `PartialOrd` needs to be implemented as well.
impl PartialOrd for ElementStreamTuple {
    fn partial_cmp(&self, other: &ElementStreamTuple) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

// stream from file or from memory
#[derive(Debug)]
pub struct TermStreamer {
    input: Option<BufReader<File>>,        // the input file
    mem_buffer_input: Vec<Element>,        // the memory buffer, storing unserialized terms
    sortfiles: Vec<File>,                  // the sort files, a buffer for each file
    mem_buffer: Vec<Element>,              // the memory buffer, storing unserialized terms
    termcounter_input: u64,                // input term count
    termcounter: u64,                      // current term count
}

impl TermStreamer {
    pub fn new() -> TermStreamer {
        TermStreamer {
            input: None,
            sortfiles: vec![],
            mem_buffer: vec![], // TODO: prevent internal allocation to go beyond MAXTERMMEM
            mem_buffer_input: vec![],
            termcounter_input: 0,
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

    pub fn input_termcount(&self) -> u64 {
        self.termcounter_input
    }

    pub fn termcount(&self) -> u64 {
        self.termcounter
    }

    // add a term. First try to add it to the
    // in-memory buffer. If that one is full
    // write it to file
    pub fn add_term(&mut self, element: Element) {
        // print intermediate statistics
        if self.termcounter >= 100000 && self.termcounter % 100000 == 0 {
            println!("    -- generated: {}", self.termcounter);
        }

        if self.mem_buffer.len() < MAXTERMMEM {
            self.mem_buffer.push(element);
        } else {
            // write the buffer to a new file
            if self.termcounter % MAXTERMMEM as u64 == 0 {
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

    // add input term. TODO: support input file for very large input
    pub fn add_term_input(&mut self, element: Element) {
        self.mem_buffer_input.push(element);
        self.termcounter_input += 1;
    }

    // get the next term from the input
    pub fn read_term(&mut self) -> Option<Element> {
        if self.mem_buffer_input.len() > 0 {
            return self.mem_buffer_input.pop();
        } else {
            // read the next terms from the input file,
            // so that the membuffer is filled
            if let Some(ref mut x) = self.input {
                for _ in 0..MAXTERMMEM {
                    if let Ok(e) = Element::deserialize(x) {
                        self.mem_buffer_input.push(e);
                    } else {
                        break;
                    }
                }

                self.mem_buffer_input.reverse(); // FIXME: wasteful...
                if self.mem_buffer_input.len() > 0 {
                    return self.mem_buffer_input.pop();
                }
            }
        }
        None
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

    pub fn sort(&mut self, var_info: &mut VarInfo, global_statements: &[Statement], write_log: bool) {
        let inpterm = self.termcounter_input;
        let genterm = self.termcounter;

        self.termcounter = 0; // reset the output term counter
        self.termcounter_input = 0;

        assert!(self.mem_buffer_input.len() == 0);

        // can the sort be done completely in memory?
        if self.sortfiles.len() == 0 {
            debug!("In-memory sorting {} terms", self.mem_buffer.len());

            let mut tmp = vec![];
            mem::swap(&mut self.mem_buffer, &mut tmp);
            let mut a = Element::SubExpr(true, tmp);
            a.normalize_inplace();
            self.input = None;

            // execute the global statements
            for s in global_statements {
                match s {
                    &Statement::Collect(ref v) => {
                        a = Element::Fn(false, Func { name: v.clone(), args: vec![a] } );
                    },
                    &Statement::Maximum(ref d) => {
                        /*match var_info.variables.get_mut(d) {
                            Some(ref mut x) => if 
                            None => {}
                        }*/
                    }
                    _ => unreachable!()
                }
            }

            // for now, print the dollar variables
            for (k,v) in &var_info.variables {
                println!("{} = {}", k, v);
            }

            // move to input buffer
            match a {
                Element::SubExpr(_, x) => self.mem_buffer_input = x,
                x => self.mem_buffer_input = vec![x],
            }

            for x in self.mem_buffer_input.iter() {
                println!("\t+{}", ElementPrinter { element: x, var_info });
            }

            self.termcounter_input = self.mem_buffer_input.len() as u64;

            println!(
                "sort -- \t terms in: {}\tgenerated: {}\tterms out: {}",
                inpterm,
                genterm,
                self.termcounter_input
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

            self.mem_buffer.sort_unstable();

            // write back
            self.sortfiles[x].set_len(0).unwrap(); // delete the contents
            self.sortfiles[x].seek(SeekFrom::Start(0)).unwrap();
            {
                let mut bw = BufWriter::new(&self.sortfiles[x]);
                for v in self.mem_buffer.iter() {
                    v.serialize(&mut bw);
                }
            }
            self.mem_buffer.clear();

            self.sortfiles[x].seek(SeekFrom::Start(0)).unwrap(); // go back to start
            if x == 0 { break; }
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
            let mut streamer = self.sortfiles
                .iter()
                .map(|x| BufReader::new(x))
                .collect::<Vec<_>>();

            // create the output file, which will be the new input
            let of = OpenOptions::new()
                .read(true)
                .write(true)
                .create(true)
                .truncate(true)
                .open(format!("input.srt"))
                .unwrap();

            let mut ofb = BufWriter::new(of);

            self.mem_buffer.clear();

            let mut heap = BinaryHeap::new();

            // populate the heap with an element from each bucket
            for (i, mut s) in streamer.iter_mut().enumerate() {
                if let Ok(e) = Element::deserialize(&mut s) {
                    heap.push(ElementStreamTuple(
                        e,
                        i,
                    ));
                }
            }

            while let Some(ElementStreamTuple(mv, i)) = heap.pop() {
                // add or merge
                let shouldadd = match self.mem_buffer.last_mut() {
                    Some(ref mut x) => !merge_terms(x, &mv),
                    _ => true,
                };
                if shouldadd {
                    self.mem_buffer.push(mv);
                }

                if self.mem_buffer.len() == maxsortmem {
                    self.termcounter_input += maxsortmem as u64 - 1;
                    for x in &self.mem_buffer[..maxsortmem - 1] {
                        println!("\t+{}", ElementPrinter { element: x, var_info });
                        x.serialize(&mut ofb);
                    }

                    self.mem_buffer[0] = self.mem_buffer.pop().unwrap();
                    self.mem_buffer.truncate(1);
                }

                // push new objects to the queue
                if let Ok(e) = Element::deserialize(&mut streamer[i]) {
                    heap.push(ElementStreamTuple(
                        e,
                        i,
                    ))
                }
            }

            self.termcounter_input += self.mem_buffer.len() as u64;

            for x in &self.mem_buffer {
                println!("\t+{}", ElementPrinter { element: x, var_info });
            }

            // move the mem_buffer to the input buffer
            mem::swap(&mut self.mem_buffer, &mut self.mem_buffer_input);

            let mut of = ofb.into_inner().unwrap();
            of.seek(SeekFrom::Start(0)).unwrap();
            self.input = Some(BufReader::new(of)); // set it as the new input

            println!(
                "sort -- \t terms in: {}\tgenerated: {}\tterms out: {}",
                inpterm,
                genterm,
                self.termcounter_input
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
