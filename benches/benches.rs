#![feature(test)]

extern crate test;

use std::env;
use std::path::PathBuf;
use std::process::{Command, ExitStatus, Stdio};
use test::Bencher;

/// Runs reFORM with the given input filename in this directory.
fn run_reform(input: &str) -> ExitStatus {
    let mut bin_path = env::current_dir().unwrap();
    bin_path.push("target");
    bin_path.push("release");
    bin_path.push("reform");
    let bin_path = bin_path.as_os_str();
    let mut input_path = PathBuf::from(file!());
    input_path.pop();
    input_path.push(input);
    let input_path = input_path.as_os_str();
    Command::new(bin_path)
        .arg(input_path)
        .stdout(Stdio::null())
        .status()
        .expect("failed to run reFORM")
}

#[bench]
fn fibonacci(b: &mut Bencher) {
    b.iter(|| run_reform("fibonacci.reform"))
}

#[bench]
fn tracen(b: &mut Bencher) {
    b.iter(|| run_reform("tracen.reform"))
}
