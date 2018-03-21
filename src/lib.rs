#[macro_use]
extern crate combine;
extern crate itertools; // command line argument options
                        //extern crate rand;
extern crate byteorder; // for serialization
extern crate crossbeam;
extern crate num_traits;
extern crate rug; // for gmp and bigint support
extern crate rand;

#[macro_use]
extern crate log;

#[macro_use]
pub mod number;

#[macro_use]
pub mod structure;
pub mod id;
pub mod module;
pub mod normalize;
pub mod parser;
pub mod serialize;
pub mod streaming;
pub mod tools;
pub mod poly;

#[cfg(test)]
mod tests;
