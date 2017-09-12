use structure::{Module,Statement,Element,Func,StatementResult,IdentityStatement,Program,VarName,VarInfo,Procedure};
use id::{MatchIterator,MatchKind};
use std::mem;
use streaming::TermStreamer;
use std::collections::HashMap;

impl Element {
	fn expand(&self) -> Element {
		match self {
			&Element::Fn(_, Func{ref name, ref args}) => Element::Fn(true, Func{ name: name.clone(),
				args: args.iter().map(|x| x.expand()).collect()}), // TODO: only flag when changed
			&Element::Term(_, ref fs) => {
				let mut r : Vec<Vec<Element>> = vec![vec![]];

				for f in fs {
					match f {
						&Element::SubExpr(_, ref s) => {
							// use cartesian product function?
							r = r.iter().flat_map(|x| s.iter().map(|y| { 
								let mut k = x.clone(); k.push(y.expand()); k } ).collect::<Vec<_>>() ).collect();
						},
						_ => {
							for rr in r.iter_mut() {
								rr.push(f.expand());
							}
						}
					}
				}

				// FIXME: this should not happen for the ground level
				Element::SubExpr(true, r.iter().map(|x| Element::Term(true, x.clone())).collect()).normalize()
			},
			&Element::SubExpr(_, ref f) => Element::SubExpr(true, f.iter().map(|x| x.expand()).collect()).normalize(),
			&Element::Pow(_, ref b, ref p) => {
				if let Element::Num(_, true, n, 1) = **p {
					if let Element::SubExpr(_, ref t) = **b {
						warn!("Expand not implemented yet for pow");
					}

					// TODO: simplify (x*y)^z to z^z*y^z?
				}

				self.clone()
			},
			_ => self.clone()
		}
	}
}

#[derive(Debug)]
enum StatementIter<'a> {
	IdentityStatement(MatchIterator<'a>),
	Multiple(Vec<Element>, bool),
	Simple(Element, bool), // yield a term once
	None
}

impl<'a> StatementIter<'a> {
	fn next(&mut self) -> StatementResult<Element> {
		match *self {
			StatementIter::IdentityStatement(ref mut id) => id.next(),
			StatementIter::Multiple(ref mut f, m) => {
				if f.len() == 0 { return StatementResult::Done; }
				if m {
					StatementResult::Executed(f.pop().unwrap()) // FIXME: pops the last term
				} else {
					StatementResult::NotExecuted(f.pop().unwrap())
				}
            },
			StatementIter::Simple(..) => {
				let mut to_swap = StatementIter::None;
                mem::swap(self, &mut to_swap); //f switch self to none
                match to_swap {
                    StatementIter::Simple(f, true)  => StatementResult::Executed(f), // set the default to not executed!
                    StatementIter::Simple(f, false)  => StatementResult::NotExecuted(f), // set the default to not executed!
                    _   => panic!(), // never reached
                }
            },
			StatementIter::None => StatementResult::Done
		}
	}
}

impl Statement {
	fn to_iter<'a>(&'a self, input: &'a Element) -> StatementIter<'a> {
		match *self {
	      Statement::IdentityStatement (ref id) => {
	        StatementIter::IdentityStatement(id.to_iter(input))
	      },
	      Statement::SplitArg(ref name) => {
	        // split function arguments at the ground level
	        let subs = | n : &VarName , a: &Vec<Element> |  Element::Fn(false, Func {name: n.clone(), args: 
	              a.iter().flat_map( |x| match x { &Element::SubExpr(_, ref y) => y.clone(), _ => vec![x.clone()] } ).collect()});

	        match *input {
	          // FIXME: check if the splitarg actually executed!
	          Element::Fn(_, Func{name: ref n, args: ref a}) if *n == *name => StatementIter::Simple(subs(n, a), false),
	          Element::Term(_, ref fs) => {
	            StatementIter::Simple(Element::Term(false, fs.iter().map(|f| match f {
	              &Element::Fn(_, Func{name: ref n, args: ref a}) if *n == *name => subs(n, a),
	              _ => f.clone()
	            } ).collect()), false)
	          }
	          _ => StatementIter::Simple(input.clone(), false)
	        }
	      },
	      Statement::Expand => {
	      	// FIXME: treat ground level differently in the expand routine
			// don't generate all terms in one go
			match input.expand() {
				Element::SubExpr(_, f) => {
					if f.len() == 1 {
						 StatementIter::Simple(f[0].clone(), false)
					} else {
						 StatementIter::Multiple(f, true)
					}
				}
				a => StatementIter::Simple(a, false)
			}

	      },
	      Statement::Print => {
	      	println!("\t+{}", input);
	      	StatementIter::Simple(input.clone(), false)
	      },
	      Statement::Multiply(ref x) => {
	      	let res = match (input, x) {
	      		(&Element::Term(_,ref xx), &Element::Term(_,ref yy)) => { let mut r = xx.clone(); r.extend(yy.clone()); Element::Term(true, r) },
				(&Element::Term(_,ref xx), _) => { let mut r = xx.clone(); r.push(x.clone()); Element::Term(true, r) },
				(_, &Element::Term(_,ref xx)) => { let mut r = xx.clone(); r.push(input.clone()); Element::Term(true, r) },
	      		_ => Element::Term(true, vec![input.clone(), x.clone()])
	      	}.normalize();
	      	StatementIter::Simple(res, true)
	      },
		  // TODO: use visitor pattern? this is almost a copy of splitarg
	      Statement::Symmetrize(ref name) => {
	        // sort function arguments at the ground level
	        let subs = | n : &VarName , a: &Vec<Element> |  Element::Fn(false, Func {name: n.clone(), args: 
	              { let mut b = a.clone(); b.sort(); b } });

	        match *input {
	          // FIXME: check if the symmetrize actually executed!
	          Element::Fn(_, Func{name: ref n, args: ref a}) if *n == *name => StatementIter::Simple(subs(n, a), false),
	          Element::Term(_, ref fs) => {
	            StatementIter::Simple(Element::Term(false, fs.iter().map(|f| match f {
	              &Element::Fn(_, Func{name: ref n, args: ref a}) if *n == *name => subs(n, a),
	              _ => f.clone()
	            } ).collect()), false)
	          }
	          _ => StatementIter::Simple(input.clone(), false)
	        }
	      },
	      _ => unreachable!()
	    }
	}
}

fn do_module_rec(input: &Element, statements: &[Statement], current_index: usize, term_affected: &mut Vec<bool>,
	output: &mut TermStreamer) {
	if current_index == statements.len() {
		output.add_term(input);
		return;
	}

	// handle control flow instructions
	match statements[current_index] {
		Statement::PushChange => {
			term_affected.push(false);
			return do_module_rec(input, statements, current_index + 1, term_affected, output)
		},
		Statement::JumpIfChanged(i) => { // the i should be one after the PushChange
			let l = term_affected.len();
			let repeat = term_affected[l - 1];

			if repeat {
				term_affected[l - 2] = true;
				term_affected[l - 1] = false;
				return do_module_rec(input, statements, i, term_affected, output);
			} else {
				term_affected.pop();
				return do_module_rec(input, statements, current_index + 1, term_affected, output);
			}
		},
		Statement::Eval(ref cond, i) => { // if statement`
			// do the match
			let mut m = MatchKind::from_element(cond, input);
			if let Some(_) = m.next() {
				return do_module_rec(input, statements, current_index + 1, term_affected, output);
			} else {
				return do_module_rec(input, statements, i, term_affected, output);
			}
		},
		Statement::Jump(i) => {
			return do_module_rec(input, statements, i, term_affected, output);
		},
		_ => {}
	}
	
	let mut it = statements[current_index].to_iter(&input);
	loop {
		match it.next() { // for every term
			StatementResult::Executed(ref f) => { 
				// make a copy that will be modified further in the recursion. FIXME: is this the only way?
				let mut newtermaff = term_affected.clone();
				*newtermaff.last_mut().unwrap() = true; 
				do_module_rec(f, statements, current_index + 1, &mut newtermaff, output);
			},
			StatementResult::NotExecuted(ref f) => do_module_rec(f, statements, current_index + 1, term_affected, output),
			StatementResult::Done => { return; }
		};
	}
}

impl Module {
	// flatten the statement structure and use conditional jumps
	// also inline the procedures
	fn to_control_flow_stat(statements: &[Statement], var_info: &mut VarInfo, procedures: &[Procedure], output: &mut Vec<Statement>) {
		for x in statements.iter() {
			match x {
				&Statement::Repeat(ref ss) => {
					output.push(Statement::PushChange);
					let pos = output.len();
					Module::to_control_flow_stat(ss, var_info, procedures, output);
					output.push(Statement::JumpIfChanged(pos));
				},
				&Statement::IfElse(ref prod, ref m, ref nm) => {
					let pos = output.len();
					output.push(Statement::Jump(0)); // note: placeholder 0
					Module::to_control_flow_stat(m, var_info, procedures, output);
					
					if nm.len() > 0 { // is there an else block?
						let pos2 = output.len(); // pos after case
						output.push(Statement::Jump(0)); // placeholder
						output[pos] = Statement::Eval(prod.clone(), output.len());
						Module::to_control_flow_stat(nm, var_info, procedures, output);
						output[pos2] = Statement::Jump(output.len());
					} else {
						output[pos] = Statement::Eval(prod.clone(), output.len());
					}		
				},
				&Statement::Call(ref name, ref args) => {
					// copy the procedure and rename local variables
					var_info.clear_local(); // remove all previous maps
					for p in procedures {
						if p.name == *name {
							if p.args.len() != args.len() {
								panic!("Procedure {} takes {} arguments instead of {}", p.name, p.args.len(), args.len());
							}
							// add the local variables to the list of variables
							for lv in &p.local_args {
								match lv {
									&Element::Var(VarName::Name(ref x)) => var_info.add_local(&x),
									&Element::Var(_) => panic!("Subsituted name for local var"),
									_ => panic!("Only variables are allowed as local variables")
								}
							}

							// now map all the procedure arguments
							let mut map = HashMap::new();
							for (k, v) in p.args.iter().zip(args.iter()) {
								if let &Element::Var(ref x) = k {
									let mut y = x.clone();
									var_info.replace_name(&mut y); // FIXME: make the replacement earlier?
									map.insert(y, v.clone());
								} else {
									panic!("Argument in procedure header should be a variable");
								}
							}

							let newmod = p.statements.iter().cloned().map(|mut x| { x.var_to_id(var_info); x}).
								map(|mut x| {x.replace_var(&map); x}).collect::<Vec<_>>();
							
							Module::to_control_flow_stat(&newmod, var_info, procedures, output);
						}
					}
				},
				a => output.push(a.clone())
			}
		}
	}

	// normalize all expressions in statements
	fn normalize_module(&mut self, var_info: &mut VarInfo, procedures: &[Procedure]) {
		let oldstat = self.statements.clone();
		self.statements.clear();
		Module::to_control_flow_stat(&oldstat, var_info, procedures, &mut self.statements);

		for x in self.statements.iter_mut() {
			match *x {
				Statement::IdentityStatement(IdentityStatement{ref mut lhs, ref mut rhs, ..}) => {
					lhs.normalize_inplace();
					rhs.normalize_inplace();
				},
				_ => {}
			}
		}
	}
}

// execute the module
pub fn do_program(program : &mut Program, write_log: bool) {
	for module in program.modules.iter_mut() {
		module.normalize_module(&mut program.var_info, &mut program.procedures);
		debug!("{}", module); // print module code

		let mut executed = vec![false];

		let mut inpcount = 0u64;
		while let Some(x) = program.input.read_term() {
			do_module_rec(&x, &module.statements, 0, &mut executed, &mut program.input);

			if program.input.termcount() > 100000 && program.input.termcount() % 100000 == 0 {
				println!("{} -- generated: {}\tterms left: {}", module.name,
					program.input.termcount(), program.input.input_termcount() - inpcount);
			}

			inpcount += 1;
		}

	  	program.input.sort(&program.var_info, write_log);
	}
}