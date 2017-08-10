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
  let mut module = parser::parse_file("test.frm");
  module.input = module.input.normalize();
  module::do_module(&mut module);
}
