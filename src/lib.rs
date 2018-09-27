extern crate pest;
#[macro_use]
extern crate pest_derive;
extern crate byteorder; // for serialization
extern crate chrono;
extern crate crossbeam;
extern crate fastdivide;
extern crate fnv;
extern crate gmp_mpfr_sys;
extern crate itertools; // command line argument options
extern crate ndarray;
extern crate num_integer;
extern crate num_traits;
extern crate rand;
extern crate rug; // for gmp and bigint support

#[macro_use]
extern crate bitflags;

#[cfg(feature = "python_api")]
#[macro_use]
extern crate cpython;

#[cfg(feature = "c_api")]
extern crate libc;

#[macro_use]
extern crate log;

#[macro_use]
pub mod number;

#[macro_use]
pub mod structure;
pub mod expand;
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
