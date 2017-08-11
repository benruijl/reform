#[macro_use]
extern crate nom;
extern crate itertools;

mod structure;
mod parser;
mod id;
mod normalize;
mod tools;
mod module;

fn main() {
  let mut program = parser::parse_file("test.frm");
  module::do_program(&mut program);
}
