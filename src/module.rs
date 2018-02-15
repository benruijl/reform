use std::mem;
use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::sync::{Arc, Mutex};
use std::thread;
use std::time;

use crossbeam;
use crossbeam::sync::MsQueue;

use structure::*;
use id::{MatchIterator, MatchKind};
use streaming::MAXTERMMEM;
use streaming::TermStreamer;
use tools::exponentiate;

impl Element {
	fn expand(&self) -> Element {
		match self {
			&Element::Fn(_, Func { ref name, ref args }) => Element::Fn(
				true,
				Func {
					name: name.clone(),
					args: args.iter().map(|x| x.expand()).collect(),
				},
			), // TODO: only flag when changed
			&Element::Term(_, ref fs) => {
				let mut r: Vec<Vec<Element>> = vec![vec![]];

				for f in fs {
					match f {
						&Element::SubExpr(_, ref s) => {
							// use cartesian product function?
							r = r.iter()
								.flat_map(|x| {
									s.iter()
										.map(|y| {
											let mut k = x.clone();
											k.push(y.expand());
											k
										})
										.collect::<Vec<_>>()
								})
								.collect();
						}
						_ => for rr in r.iter_mut() {
							rr.push(f.expand());
						},
					}
				}

				// FIXME: this should not happen for the ground level
				Element::SubExpr(
					true,
					r.into_iter().map(|x| Element::Term(true, x)).collect(),
				).normalize()
			}
			&Element::SubExpr(_, ref f) => {
				Element::SubExpr(true, f.iter().map(|x| x.expand()).collect()).normalize()
			}
			&Element::Pow(_, ref b, ref p) => {
				if let Element::Num(_, true, n, 1) = **p {
					if let Element::SubExpr(_, ref t) = **b {
						let mut e = exponentiate(t, n);
						e.normalize_inplace();
						return e;
					}

					// TODO: simplify (x*y)^z to z^z*y^z?
				}

				self.clone()
			}
			_ => self.clone(),
		}
	}
}

#[derive(Debug)]
enum StatementIter<'a> {
	IdentityStatement(MatchIterator<'a>),
	Multiple(Vec<Element>, bool),
	Simple(Element, bool), // yield a term once
	None,
}

impl<'a> StatementIter<'a> {
	fn next(&mut self) -> StatementResult<Element> {
		match *self {
			StatementIter::IdentityStatement(ref mut id) => id.next(),
			StatementIter::Multiple(ref mut f, m) => {
				if f.len() == 0 {
					return StatementResult::Done;
				}
				if m {
					StatementResult::Executed(f.pop().unwrap()) // FIXME: pops the last term
				} else {
					StatementResult::NotExecuted(f.pop().unwrap())
				}
			}
			StatementIter::Simple(..) => {
				let mut to_swap = StatementIter::None;
				mem::swap(self, &mut to_swap); //f switch self to none
				match to_swap {
					StatementIter::Simple(f, true) => StatementResult::Executed(f), // set the default to not executed!
					StatementIter::Simple(f, false) => StatementResult::NotExecuted(f), // set the default to not executed!
					_ => panic!(),                                                      // never reached
				}
			}
			StatementIter::None => StatementResult::Done,
		}
	}
}

impl Statement {
	fn to_iter<'a>(
		&'a self,
		input: &'a mut Element,
		var_info: &'a HashMap<VarName, Element>,
	) -> StatementIter<'a> {
		match *self {
			Statement::IdentityStatement(ref id) => {
				StatementIter::IdentityStatement(id.to_iter(input, &var_info))
			}
			Statement::SplitArg(ref name) => {
				// TODO: use mutability to prevent unnecessary copy
				// split function arguments at the ground level
				let subs = |n: &VarName, a: &Vec<Element>| {
					Element::Fn(
						false,
						Func {
							name: n.clone(),
							args: a.iter()
								.flat_map(|x| match x {
									&Element::SubExpr(_, ref y) => y.clone(),
									_ => vec![x.clone()],
								})
								.collect(),
						},
					)
				};

				match *input {
					// FIXME: check if the splitarg actually executed!
					Element::Fn(
						_,
						Func {
							name: ref mut n,
							args: ref mut a,
						},
					) if *n == *name =>
					{
						StatementIter::Simple(subs(n, a), false)
					}
					Element::Term(_, ref fs) => StatementIter::Simple(
						Element::Term(
							false,
							fs.iter()
								.map(|f| match f {
									&Element::Fn(
										_,
										Func {
											name: ref n,
											args: ref a,
										},
									) if *n == *name =>
									{
										subs(n, a)
									}
									_ => f.clone(),
								})
								.collect(),
						),
						false,
					),
					_ => StatementIter::Simple(mem::replace(input, Element::default()), false),
				}
			}
			Statement::Expand => {
				// FIXME: treat ground level differently in the expand routine
				// don't generate all terms in one go
				match input.expand() {
					Element::SubExpr(_, mut f) => {
						if f.len() == 1 {
							StatementIter::Simple(f.swap_remove(0), false)
						} else {
							StatementIter::Multiple(f, true)
						}
					}
					a => StatementIter::Simple(a, false),
				}
			}
			Statement::Print => {
				println!("\t+{}", input);
				StatementIter::Simple(mem::replace(input, Element::default()), false)
			}
			Statement::Multiply(ref x) => {
				let mut res = match (input, x) {
					(&mut Element::Term(_, ref mut xx), &Element::Term(_, ref yy)) => {
						xx.extend(yy.iter().map(|x| x.clone()));
						Element::Term(true, mem::replace(xx, vec![]))
					}
					(&mut Element::Term(_, ref mut xx), _) => {
						xx.push(x.clone());
						Element::Term(true, mem::replace(xx, vec![]))
					}
					(ref mut a, &Element::Term(_, ref xx)) => {
						let mut r = xx.clone();
						r.push(mem::replace(a, DUMMY_ELEM!()));
						Element::Term(true, r)
					}
					(ref mut a, aa) => {
						Element::Term(true, vec![mem::replace(a, DUMMY_ELEM!()), aa.clone()])
					}
				};

				res.replace_vars(var_info, true); // apply the dollar variables
				res.normalize_inplace();
				StatementIter::Simple(res, true)
			}
			// TODO: use visitor pattern? this is almost a copy of splitarg
			Statement::Symmetrize(ref name) => {
				// sort function arguments at the ground level
				let subs = |n: &VarName, a: &Vec<Element>| {
					Element::Fn(
						false,
						Func {
							name: n.clone(),
							args: {
								let mut b = a.clone();
								b.sort();
								b
							},
						},
					)
				};

				match *input {
					// FIXME: check if the symmetrize actually executed!
					Element::Fn(
						_,
						Func {
							name: ref n,
							args: ref a,
						},
					) if *n == *name =>
					{
						StatementIter::Simple(subs(n, a), false)
					}
					Element::Term(_, ref fs) => StatementIter::Simple(
						Element::Term(
							false,
							fs.iter()
								.map(|f| match f {
									&Element::Fn(
										_,
										Func {
											name: ref n,
											args: ref a,
										},
									) if *n == *name =>
									{
										subs(n, a)
									}
									_ => f.clone(),
								})
								.collect(),
						),
						false,
					),
					_ => StatementIter::Simple(mem::replace(input, Element::default()), false),
				}
			}
			_ => unreachable!(),
		}
	}
}

fn do_module_rec(
	mut input: Element,
	statements: &[Statement],
	var_info: &mut VarInfo,
	current_index: usize,
	term_affected: &mut Vec<bool>,
	output: &mut Arc<&mut Mutex<TermStreamer>>,
) {
	if let Element::Num(_, true, 0, 1) = input {
		return; // drop 0
	}
	if current_index == statements.len() {
		output.lock().unwrap().add_term(input);
		return;
	}

	// handle control flow instructions
	match statements[current_index] {
		Statement::PushChange => {
			term_affected.push(false);
			return do_module_rec(
				input,
				statements,
				var_info,
				current_index + 1,
				term_affected,
				output,
			);
		}
		Statement::JumpIfChanged(i) => {
			if Some(&true) == term_affected.last() {
				return do_module_rec(input, statements, var_info, i, term_affected, output);
			} else {
				term_affected.pop(); // it should be as if the repeated wasn't there
				return do_module_rec(
					input,
					statements,
					var_info,
					current_index + 1,
					term_affected,
					output,
				);
			}
		}
		Statement::Eval(ref cond, i) => {
			// if statement
			// do the match
			if let Some(_) = MatchKind::from_element(cond, &input, &var_info.variables).next() {
				return do_module_rec(
					input,
					statements,
					var_info,
					current_index + 1,
					term_affected,
					output,
				);
			} else {
				return do_module_rec(input, statements, var_info, i, term_affected, output);
			}
		}
		Statement::Jump(i) => {
			return do_module_rec(input, statements, var_info, i, term_affected, output);
		}
		// TODO: not a control flow instruction
		// move to iter if we decide how to propagate the var_info
		Statement::Assign(ref dollar, ref e) => {
			let mut ee = e.clone();
			ee.replace_vars(&var_info.variables, true);
			if let &Element::Dollar(ref d, ..) = dollar {
				var_info.add_dollar(d.clone(), ee);
			}
			return do_module_rec(
				input,
				statements,
				var_info,
				current_index + 1,
				term_affected,
				output,
			);
		}
		Statement::Maximum(ref dollar) => {
			if let &Element::Dollar(ref d, ..) = dollar {
				match var_info.variables.get_mut(d) {
					Some(x) => {
						match var_info.global_variables.entry(d.clone()) {
							Entry::Occupied(mut y) => {
								if *y.get() < *x {
									mem::swap(x, y.get_mut());
								}
							}
							Entry::Vacant(y) => {
								y.insert(mem::replace(x, DUMMY_ELEM!()));
							}
						};
					}
					None => {}
				}
			}
			return do_module_rec(
				input,
				statements,
				var_info,
				current_index + 1,
				term_affected,
				output,
			);
		}
		_ => {}
	}

	{
		let oldvarinfo = var_info.variables.clone(); // TODO: prevent clone somehow?
		let mut it = statements[current_index].to_iter(&mut input, &oldvarinfo);
		loop {
			match it.next() {
				// for every term
				StatementResult::Executed(f) => {
					*term_affected.last_mut().unwrap() = true;
					let d = term_affected.len(); // store the depth of the stack
					do_module_rec(
						f,
						statements,
						var_info,
						current_index + 1,
						term_affected,
						output,
					);
					term_affected.truncate(d);
				}
				StatementResult::NotExecuted(f) => do_module_rec(
					f,
					statements,
					var_info,
					current_index + 1,
					term_affected,
					output,
				),
				StatementResult::NoChange => {
					break;
				}
				StatementResult::Done => {
					return;
				}
			};
		}
	}

	// only reached when the input was not changed
	do_module_rec(
		input,
		statements,
		var_info,
		current_index + 1,
		term_affected,
		output,
	);
}

impl Module {
	// flatten the statement structure and use conditional jumps
	// also inline the procedures
	fn to_control_flow_stat(
		statements: &[Statement],
		var_info: &mut VarInfo,
		procedures: &[Procedure],
		output: &mut Vec<Statement>,
	) {
		for x in statements.iter() {
			match x {
				&Statement::Repeat(ref ss) => {
					output.push(Statement::PushChange);
					let pos = output.len();
					Module::to_control_flow_stat(ss, var_info, procedures, output);
					output.push(Statement::JumpIfChanged(pos - 1));
				}
				&Statement::IfElse(ref prod, ref m, ref nm) => {
					let pos = output.len();
					output.push(Statement::Jump(0)); // note: placeholder 0
					Module::to_control_flow_stat(m, var_info, procedures, output);

					if nm.len() > 0 {
						// is there an else block?
						let pos2 = output.len(); // pos after case
						output.push(Statement::Jump(0)); // placeholder
						output[pos] = Statement::Eval(prod.clone(), output.len());
						Module::to_control_flow_stat(nm, var_info, procedures, output);
						output[pos2] = Statement::Jump(output.len());
					} else {
						output[pos] = Statement::Eval(prod.clone(), output.len());
					}
				}
				&Statement::Call(ref name, ref args) => {
					// copy the procedure and rename local variables
					var_info.clear_local(); // remove all previous maps
					for p in procedures {
						if p.name == *name {
							if p.args.len() != args.len() {
								panic!(
									"Procedure {} takes {} arguments instead of {}",
									p.name,
									p.args.len(),
									args.len()
								);
							}
							// add the local variables to the list of variables
							for lv in &p.local_args {
								match lv {
									&Element::Var(VarName::Name(ref x)) => var_info.add_local(&x),
									&Element::Var(_) => panic!("Subsituted name for local var"),
									_ => panic!("Only variables are allowed as local variables"),
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

							let newmod = p.statements
								.iter()
								.cloned()
								.map(|mut x| {
									x.var_to_id(var_info);
									x
								})
								.map(|mut x| {
									x.replace_vars(&map, false);
									x
								})
								.collect::<Vec<_>>();

							Module::to_control_flow_stat(&newmod, var_info, procedures, output);
						}
					}
				}
				a => output.push(a.clone()),
			}
		}
	}

	// normalize all expressions in statements
	fn normalize_module(&mut self, var_info: &mut VarInfo, procedures: &[Procedure]) {
		let oldstat = mem::replace(&mut self.statements, vec![]);
		let mut newstat = vec![];

		// split off global statements
		for x in oldstat {
			match x {
				Statement::Collect(_) => self.global_statements.push(x),
				_ => newstat.push(x),
			}
		}

		Module::to_control_flow_stat(&newstat, var_info, procedures, &mut self.statements);

		for x in self.statements.iter_mut() {
			match *x {
				Statement::IdentityStatement(IdentityStatement {
					ref mut lhs,
					ref mut rhs,
					..
				}) => {
					lhs.normalize_inplace();
					rhs.normalize_inplace();
				}
				Statement::Multiply(ref mut e) => {
					e.normalize_inplace();
				}
				Statement::Eval(ref mut e, _) => {
					e.normalize_inplace();
				}
				Statement::Assign(_, ref mut e) => {
					e.normalize_inplace();
				}
				_ => {}
			}
		}
	}
}

// execute the module
pub fn do_program(program: &mut Program, write_log: bool, num_threads: usize) {
	for module in program.modules.iter_mut() {
		// move global statements from the previous module into the new one
		// TODO: do swap instead of clone?
		program.var_info.variables = program.var_info.global_variables.clone();

		module.normalize_module(&mut program.var_info, &mut program.procedures);
		debug!("{}", module); // print module code

		let mut inpcount = 0u64;

		if num_threads > 1 {
			let queue: Arc<MsQueue<Option<Element>>> = Arc::new(MsQueue::new());
			let mut output = Arc::new(&mut program.input); // TODO: split in input and output stream

			let thread_varinfo = program.var_info.clone();

			// create threads that process terms
			crossbeam::scope(|scope| {
				for _ in 0..num_threads {
					let queue = queue.clone();
					let m = module.statements.clone(); // TODO: why do we need to do this?
					let mut thread_varinfo = thread_varinfo.clone();
					let mut executed = vec![false];
					let mut output = output.clone();
					scope.spawn(move || {
						while let Some(x) = queue.pop() {
							do_module_rec(
								x,
								&m,
								&mut thread_varinfo,
								0,
								&mut executed,
								&mut output,
							);
						}
					});
				}

				// TODO: use semaphore or condvar for refills
				let mut done = false;
				while !done {
					if queue.is_empty() {
						debug!("Loading new batch");
						for _ in 0..MAXTERMMEM {
							// FIXME: this lock now interferes with the output lock
							if let Some(x) = output.lock().unwrap().read_term() {
								queue.push(Some(x));
							} else {
								// post exist signal to all threads
								for _ in 0..num_threads {
									queue.push(None); // post exit signal
								}

								done = true;
								break;
							}
						}
					}
					thread::sleep(time::Duration::from_millis(10));
				}
			});
		} else {
			let mut executed = vec![false];

			loop {
				// note: while let Some(x) = program.input.lock().unwrap().read_term() keeps the lock
				let r = program.input.lock().unwrap().read_term();
				match r {
					Some(x) => {
						let mut output = Arc::new(&mut program.input);
						do_module_rec(
							x,
							&module.statements,
							&mut program.var_info,
							0,
							&mut executed,
							&mut output.clone(),
						);
						let output = output.lock().unwrap();
						if output.termcount() > 100_000 && output.termcount() % 100_000 == 0 {
							println!(
								"{} -- generated: {}\tterms left: {}",
								module.name,
								output.termcount(),
								output.input_termcount() - inpcount
							);
						}

						inpcount += 1;
					}
					None => break,
				}
			}
		}

		program.input.lock().unwrap().sort(
			&mut program.var_info,
			&module.global_statements,
			write_log,
		);
	}
}
