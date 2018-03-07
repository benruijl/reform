#[macro_use]
extern crate combine;
extern crate itertools; // command line argument options
                        //extern crate rand;
extern crate byteorder; // for serialization
extern crate crossbeam;

#[macro_use]
extern crate log;

#[macro_use]
pub mod structure;
pub mod parser;
pub mod id;
pub mod normalize;
pub mod streaming;
pub mod tools;
pub mod module;
pub mod serialize;

#[cfg(test)]
mod tests;
