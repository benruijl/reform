#[macro_use]
extern crate combine;
extern crate itertools;
extern crate clap; // command line argument options
//extern crate rand;
extern crate byteorder; // for serialization

#[macro_use]
extern crate log;
extern crate env_logger;

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
mod tests;
mod serialize;

use clap::{Arg, App};

#[cfg(feature = "profile")]
use cpuprofiler::PROFILER;

fn main() {
  env_logger::init().unwrap();

  #[cfg(feature = "profile")]
  let do_profile = match std::env::var("CPUPROFILE") {
    Ok(val) => {
      info!("Using profiler");
      PROFILER.lock().unwrap().start(val).unwrap();
      true
    },
    _ => {
      info!("Not using profiler");
      false
    },
  };

  let matches = App::new("reFORM")
                          .version("0.1.0")
                          .author("Ben Ruijl <benruyl@gmail.com>")
                          .about("A symbolic manipulation toolkit")
                          .arg(Arg::with_name("config")
                               .short("c")
                               .long("config")
                               .value_name("FILE")
                               .help("Sets a custom config file")
                               .takes_value(true))                          
                          .arg(Arg::with_name("log")
                               .short("l")
                               .long("log")
                               .help("Create a log file with the output"))
                          .arg(Arg::with_name("INPUT")
                               .help("Sets the input file to use")
                               .required(true)
                               .default_value("test.frm")
                               .index(1))
                          .arg(Arg::with_name("v")
                               .short("v")
                               .multiple(true)
                               .help("Sets the level of verbosity"))
                          .get_matches();

  let mut program = parser::parse_file(matches.value_of("INPUT").unwrap());
  module::do_program(&mut program, matches.is_present("log"));

  #[cfg(feature = "profile")]
  {
    if do_profile {
      PROFILER.lock().unwrap().stop().unwrap();
    }
  }
}
