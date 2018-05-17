#[macro_use]
extern crate combine;
extern crate itertools; // command line argument options
                        //extern crate rand;
extern crate byteorder; // for serialization
extern crate crossbeam;
extern crate fastdivide;
extern crate gmp_mpfr_sys;
extern crate ndarray;
extern crate num_integer;
extern crate num_traits;
extern crate rand;
extern crate rug; // for gmp and bigint support
extern crate fnv;

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
pub mod poly;
pub mod serialize;
pub mod sort;
pub mod streaming;
pub mod tools;

#[cfg(test)]
mod tests;
