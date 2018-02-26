// "cargo bench" is still unstable (rust-lang/rfcs#2287).
#![cfg_attr(all(test, feature = "nightly"), feature(test))]
#[cfg(all(test, feature = "nightly"))]
extern crate test;

extern crate clap;
#[macro_use]
extern crate combine;
extern crate itertools; // command line argument options
                        //extern crate rand;
extern crate byteorder; // for serialization
extern crate crossbeam;

extern crate env_logger;
#[macro_use]
extern crate log;

#[cfg(feature = "profile")]
extern crate cpuprofiler;

#[macro_use]
mod structure;
mod parser;
mod id;
mod normalize;
mod streaming;
mod tools;
mod module;
mod serialize;

#[cfg(test)]
mod tests;

#[cfg(all(test, feature = "nightly"))]
mod benches;

use clap::{App, Arg};

#[cfg(feature = "profile")]
use cpuprofiler::PROFILER;

fn main() {
    env_logger::init().unwrap();

    #[cfg(feature = "profile")]
    let do_profile = match std::env::var("CPUPROFILE") {
        Ok(val) => {
            info!("Using profiler: saving in {}", val);
            PROFILER.lock().unwrap().start(val).unwrap();
            true
        }
        _ => {
            info!("Not using profiler");
            false
        }
    };

    let matches = App::new("reFORM")
        .version("0.1.0")
        .author("Ben Ruijl <benruyl@gmail.com>")
        .about("A symbolic manipulation toolkit")
        .arg(
            Arg::with_name("config")
                .short("c")
                .long("config")
                .value_name("FILE")
                .help("Sets a custom config file")
                .takes_value(true),
        )
        .arg(
            Arg::with_name("log")
                .short("l")
                .long("log")
                .help("Create a log file with the output"),
        )
        .arg(
            Arg::with_name("workers")
                .short("w")
                .long("workers")
                .help("Number of workers (threads)")
                .default_value("1")
                .takes_value(true),
        )
        .arg(
            Arg::with_name("INPUT")
                .help("Sets the input file to use")
                .required(true)
                .default_value("test.frm")
                .index(1),
        )
        .arg(
            Arg::with_name("v")
                .short("v")
                .multiple(true)
                .help("Sets the level of verbosity"),
        )
        .get_matches();

    let mut program = parser::parse_file(matches.value_of("INPUT").unwrap());
    module::do_program(
        &mut program,
        matches.is_present("log"),
        matches.value_of("workers").unwrap().parse().unwrap(),
    );

    #[cfg(feature = "profile")]
    {
        if do_profile {
            PROFILER.lock().unwrap().stop().unwrap();
        }
    }
}
