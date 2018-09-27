extern crate clap;
extern crate env_logger;
extern crate reform;

#[cfg(feature = "profile")]
extern crate cpuprofiler;

use clap::{App, Arg};
use std::str::FromStr;

#[cfg(feature = "profile")]
use cpuprofiler::PROFILER;

use reform::structure::Element;

fn main() -> Result<(), Box<std::error::Error>> {
    env_logger::init();
    #[cfg(feature = "profile")]
    PROFILER.lock().unwrap().state(); // Ensure linking to gperftools

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
        ).arg(
            Arg::with_name("log")
                .short("l")
                .long("log")
                .help("Create a log file with the output"),
        ).arg(
            Arg::with_name("workers")
                .short("w")
                .long("workers")
                .help("Number of workers (threads)")
                .default_value("1")
                .takes_value(true),
        ).arg(
            Arg::with_name("dollars")
                .short("d")
                .long("dollars")
                .help("Define dollar variables in a list as $a=x,b=\"1 + x\"")
                .takes_value(true),
        ).arg(
            Arg::with_name("INPUT")
                .help("Sets the input file to use")
                .required(true)
                .default_value("test.frm")
                .index(1),
        ).arg(
            Arg::with_name("v")
                .short("v")
                .multiple(true)
                .help("Sets the level of verbosity"),
        ).get_matches();

    // parse the program
    let mut program = reform::parser::parse_file(matches.value_of("INPUT").unwrap());

    // read in dollar variables from the command line
    if let Some(ds) = matches.value_of("dollars") {
        for s in ds.split(',') {
            let r: Vec<_> = s.split('=').collect();
            if r.len() != 2 {
                panic!("Expected key-value pair for dollar variable: $a=5 or a=5");
            }

            if r[0].is_empty() {
                panic!("Expected key-value pair for dollar variable: $a=5 or a=5");
            }

            let lhs_str = if r[0].starts_with('$') {
                r[0].to_owned()
            } else {
                "$".to_owned() + r[0]
            };

            let mut lhs = Element::from_str(&lhs_str)?.to_element(&mut program.var_info);
            lhs.normalize_inplace(&program.var_info.global_info);

            let mut rhs = Element::from_str(r[1])?.to_element(&mut program.var_info);
            rhs.normalize_inplace(&program.var_info.global_info);

            program.var_info.local_info.add_dollar(lhs, rhs);
        }
    }

    program.do_program(
        matches.is_present("log"),
        matches.occurrences_of("v"),
        matches.value_of("workers").unwrap().parse().unwrap(),
    );
    Ok(())
}
