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
use streaming::{InputTermStreamer, OutputTermStreamer};
use tools::exponentiate;

/*
Abstract away the difference between a threaded term streamer
and a single-core streamer.
*/
enum TermStreamWrapper {
    Threaded(Arc<Mutex<OutputTermStreamer>>),
    Single(OutputTermStreamer),
}

impl TermStreamWrapper {
    fn extract(self) -> OutputTermStreamer {
        match self {
            TermStreamWrapper::Threaded(x) => Arc::try_unwrap(x).unwrap().into_inner().unwrap(),
            TermStreamWrapper::Single(x) => x,
        }
    }

    fn add_term(&mut self, e: Element) {
        match *self {
            TermStreamWrapper::Threaded(ref mut x) => x.lock().unwrap().add_term(e),
            TermStreamWrapper::Single(ref mut x) => x.add_term(e),
        }
    }
}

impl Element {
    // TODO: mutate self to prevent unnecessary cloning
    fn expand(&self) -> Element {
        match *self {
            Element::Fn(_, ref name, ref args) => {
                let mut f = Element::Fn(
                    true,
                    name.clone(),
                    args.iter().map(|x| x.expand()).collect(),
                );
                f.normalize_inplace();
                f
            } // TODO: only flag when changed
            Element::Term(_, ref fs) => {
                let mut r: Vec<Vec<Element>> = vec![vec![]];

                for f in fs {
                    let fe = f.expand();
                    match fe {
                        Element::SubExpr(_, ref s) => {
                            // use cartesian product function?
                            r = r.iter()
                                .flat_map(|x| {
                                    s.iter()
                                        .map(|y| {
                                            let mut k = x.clone();
                                            k.push(y.clone());
                                            k
                                        })
                                        .collect::<Vec<_>>()
                                })
                                .collect();
                        }
                        _ => for rr in &mut r {
                            rr.push(fe.clone());
                        },
                    }
                }

                // FIXME: this should not happen for the ground level
                let mut e = Element::SubExpr(
                    true,
                    r.into_iter().map(|x| Element::Term(true, x)).collect(),
                );

                e.normalize_inplace();
                e
            }
            Element::SubExpr(_, ref f) => {
                let mut e = Element::SubExpr(true, f.iter().map(|x| x.expand()).collect());
                e.normalize_inplace();
                e
            }
            Element::Pow(_, ref be) => {
                let (ref b, ref e) = **be;

                let (eb, ee) = (b.expand(), e.expand());

                if let Element::Num(_, true, n, 1) = ee {
                    if let Element::SubExpr(_, ref t) = eb {
                        let mut e = exponentiate(t, n);
                        e.normalize_inplace();
                        return e.expand();
                    }

                    //  (x*y)^z -> x^z*y^z
                    if let Element::Term(_, t) = eb {
                        let mut e = Element::Term(
                            true,
                            t.iter()
                                .map(|x| {
                                    Element::Pow(
                                        true,
                                        Box::new((x.clone(), Element::Num(false, true, n, 1))),
                                    )
                                })
                                .collect(),
                        );
                        e.normalize_inplace();
                        return e.expand();
                    }
                }

                let mut e = Element::Pow(true, Box::new((eb, ee)));
                e.normalize_inplace();
                e
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
                if f.is_empty() {
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
                    _ => panic!(), // never reached
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
        local_var_info: &'a mut LocalVarInfo,
        global_var_info: &GlobalVarInfo,
    ) -> StatementIter<'a> {
        match *self {
            Statement::IdentityStatement(ref id) => {
                StatementIter::IdentityStatement(id.to_iter(input, &local_var_info.variables))
            }
            Statement::SplitArg(ref name) => {
                // TODO: use mutability to prevent unnecessary copy
                // split function arguments at the ground level
                let subs = |n: &VarName, a: &Vec<Element>| {
                    Element::Fn(
                        false,
                        n.clone(),
                        a.iter()
                            .flat_map(|x| match *x {
                                Element::SubExpr(_, ref y) => y.clone(),
                                _ => vec![x.clone()],
                            })
                            .collect(),
                    )
                };

                match *input {
                    // FIXME: check if the splitarg actually executed!
                    Element::Fn(_, ref mut n, ref mut a) if *n == *name => {
                        StatementIter::Simple(subs(n, a), false)
                    }
                    Element::Term(_, ref fs) => StatementIter::Simple(
                        Element::Term(
                            false,
                            fs.iter()
                                .map(|f| match *f {
                                    Element::Fn(_, ref n, ref a) if *n == *name => subs(n, a),
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
            Statement::Multiply(ref x) => {
                let mut res = match (input, x) {
                    (&mut Element::Term(_, ref mut xx), &Element::Term(_, ref yy)) => {
                        xx.extend(yy.iter().cloned());
                        Element::Term(true, mem::replace(xx, vec![]))
                    }
                    (&mut Element::Term(_, ref mut xx), _) => {
                        xx.push(x.clone());
                        Element::Term(true, mem::replace(xx, vec![]))
                    }
                    (ref mut a, &Element::Term(_, ref xx)) => {
                        let mut r = xx.clone();
                        r.reverse(); // FIXME: for testing
                        r.push(mem::replace(a, DUMMY_ELEM!()));
                        r.reverse(); // FIXME: for testing
                        Element::Term(false, r)
                    }
                    (ref mut a, aa) => {
                        Element::Term(true, vec![mem::replace(a, DUMMY_ELEM!()), aa.clone()])
                    }
                };

                res.replace_vars(&local_var_info.variables, true); // apply the dollar variables
                res.normalize_inplace();
                StatementIter::Simple(res, true)
            }
            // TODO: use visitor pattern? this is almost a copy of splitarg
            Statement::Symmetrize(ref name) => {
                // sort function arguments at the ground level
                let subs = |n: &VarName, a: &Vec<Element>| {
                    Element::Fn(false, n.clone(), {
                        let mut b = a.clone();
                        b.sort();
                        b
                    })
                };

                match *input {
                    // FIXME: check if the symmetrize actually executed!
                    Element::Fn(_, ref n, ref a) if *n == *name => {
                        StatementIter::Simple(subs(n, a), false)
                    }
                    Element::Term(_, ref fs) => StatementIter::Simple(
                        Element::Term(
                            false,
                            fs.iter()
                                .map(|f| match *f {
                                    Element::Fn(_, ref n, ref a) if *n == *name => subs(n, a),
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
    local_var_info: &mut LocalVarInfo,
    global_var_info: &GlobalVarInfo,
    current_index: usize,
    term_affected: &mut Vec<bool>,
    output: &mut TermStreamWrapper,
) {
    if let Element::Num(_, true, 0, 1) = input {
        return; // drop 0
    }
    if current_index == statements.len() {
        output.add_term(input);
        return;
    }

    // handle control flow instructions
    match statements[current_index] {
        Statement::PushChange => {
            term_affected.push(false);
            return do_module_rec(
                input,
                statements,
                local_var_info,
                global_var_info,
                current_index + 1,
                term_affected,
                output,
            );
        }
        Statement::JumpIfChanged(i) => {
            if Some(&true) == term_affected.last() {
                return do_module_rec(
                    input,
                    statements,
                    local_var_info,
                    global_var_info,
                    i,
                    term_affected,
                    output,
                );
            } else {
                term_affected.pop(); // it should be as if the repeated wasn't there
                return do_module_rec(
                    input,
                    statements,
                    local_var_info,
                    global_var_info,
                    current_index + 1,
                    term_affected,
                    output,
                );
            }
        }
        Statement::Eval(ref cond, i) => {
            // if statement
            // do the match
            if MatchKind::from_element(cond, &input, &local_var_info.variables)
                .next()
                .is_some()
            {
                return do_module_rec(
                    input,
                    statements,
                    local_var_info,
                    global_var_info,
                    current_index + 1,
                    term_affected,
                    output,
                );
            } else {
                return do_module_rec(
                    input,
                    statements,
                    local_var_info,
                    global_var_info,
                    i,
                    term_affected,
                    output,
                );
            }
        }
        Statement::Jump(i) => {
            return do_module_rec(
                input,
                statements,
                local_var_info,
                global_var_info,
                i,
                term_affected,
                output,
            );
        }
        // TODO: not a control flow instruction
        // move to iter if we decide how to propagate the var_info
        Statement::Assign(ref dollar, ref e) => {
            let mut ee = e.clone();
            if ee.replace_vars(&local_var_info.variables, true) {
                ee.normalize_inplace();
            }
            if let Element::Dollar(ref d, ..) = *dollar {
                local_var_info.add_dollar(d.clone(), ee);
            }
            return do_module_rec(
                input,
                statements,
                local_var_info,
                global_var_info,
                current_index + 1,
                term_affected,
                output,
            );
        }
        Statement::Maximum(ref dollar) => {
            if let Element::Dollar(ref d, ..) = *dollar {
                if let Some(x) = local_var_info.variables.get(d) {
                    match local_var_info.global_variables.entry(d.clone()) {
                        Entry::Occupied(mut y) => {
                            if *y.get() < *x {
                                *y.get_mut() = x.clone();
                            }
                        }
                        Entry::Vacant(y) => {
                            y.insert(x.clone());
                        }
                    };
                }
            }
            return do_module_rec(
                input,
                statements,
                local_var_info,
                global_var_info,
                current_index + 1,
                term_affected,
                output,
            );
        }
        Statement::Print => {
            println!(
                "\t+{}",
                ElementPrinter {
                    element: &input,
                    var_info: &global_var_info,
                }
            );
            return do_module_rec(
                input,
                statements,
                local_var_info,
                global_var_info,
                current_index + 1,
                term_affected,
                output,
            );
        }
        _ => {}
    }

    // TODO: generate first two elements? performance doesnt seem too much affected though
    {
        let mut oldvarinfo = local_var_info.clone(); // TODO: prevent clone somehow? if one term is in the output, the clone is unnecessary
        let mut it =
            statements[current_index].to_iter(&mut input, &mut oldvarinfo, global_var_info);
        loop {
            match it.next() {
                // for every term
                StatementResult::Executed(f) => {
                    *term_affected.last_mut().unwrap() = true;
                    let d = term_affected.len(); // store the depth of the stack
                    do_module_rec(
                        f,
                        statements,
                        local_var_info,
                        global_var_info,
                        current_index + 1,
                        term_affected,
                        output,
                    );
                    term_affected.truncate(d);
                }
                StatementResult::NotExecuted(f) => do_module_rec(
                    f,
                    statements,
                    local_var_info,
                    global_var_info,
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
        local_var_info,
        global_var_info,
        current_index + 1,
        term_affected,
        output,
    );
}

impl Module {
    // flatten the statement structure and use conditional jumps
    // also inline the procedures
    fn statements_to_control_flow_stat(
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
                    Module::statements_to_control_flow_stat(ss, var_info, procedures, output);
                    output.push(Statement::JumpIfChanged(pos - 1));
                }
                &Statement::IfElse(ref prod, ref m, ref nm) => {
                    let pos = output.len();
                    output.push(Statement::Jump(0)); // note: placeholder 0
                    Module::statements_to_control_flow_stat(m, var_info, procedures, output);

                    if !nm.is_empty() {
                        // is there an else block?
                        let pos2 = output.len(); // pos after case
                        output.push(Statement::Jump(0)); // placeholder
                        output[pos] = Statement::Eval(prod.clone(), output.len());
                        Module::statements_to_control_flow_stat(nm, var_info, procedures, output);
                        output[pos2] = Statement::Jump(output.len());
                    } else {
                        output[pos] = Statement::Eval(prod.clone(), output.len());
                    }
                }
                &Statement::Call(ref name, ref args) => {
                    // copy the procedure and rename local variables
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

                            // add the map for the procedure arguments
                            let mut map = HashMap::new();
                            for (k, v) in p.args.iter().zip(args.iter()) {
                                if let Element::Var(map_source) = *k {
                                    map.insert(map_source.clone(), v.clone());
                                } else {
                                    panic!("Argument in procedure header should be a variable");
                                }
                            }

                            for lv in &p.local_args {
                                // create unique variable
                                if let Element::Var(name) = *lv {
                                    map.insert(
                                        name.clone(),
                                        Element::Var(var_info.add_local(&name)),
                                    );
                                }
                            }

                            let newmod = p.statements
                                .iter()
                                .cloned()
                                .map(|mut x| {
                                    x.replace_vars(&map, false);
                                    x
                                })
                                .collect::<Vec<_>>();

                            Module::statements_to_control_flow_stat(
                                &newmod,
                                var_info,
                                procedures,
                                output,
                            );
                        }
                    }
                }
                a => output.push(a.clone()),
            }
        }
    }

    // normalize all expressions in statements and execute global
    // operations
    fn normalize_module(&mut self, var_info: &mut VarInfo, procedures: &[Procedure]) {
        for x in &self.global_statements {
            match *x {
                Statement::Assign(ref dollar, ref e) => {
                    let mut ee = e.clone();
                    ee.replace_vars(&var_info.local_info.variables, true);
                    ee.normalize_inplace();
                    if let Element::Dollar(ref d, ..) = *dollar {
                        var_info.local_info.add_dollar(d.clone(), ee);
                    }
                }
                Statement::Attrib(ref f, ref attribs) => match *f {
                    Element::Var(ref name) => {
                        var_info
                            .global_info
                            .func_attribs
                            .insert(name.clone(), attribs.clone());
                    }
                    _ => {
                        panic!("Can only assign attributes to functions");
                    }
                },
                _ => unimplemented!(),
            }
        }

        let old_statements = mem::replace(&mut self.statements, vec![]);
        Module::statements_to_control_flow_stat(
            &old_statements,
            var_info,
            procedures,
            &mut self.statements,
        );

        for x in &mut self.statements {
            match *x {
                Statement::IdentityStatement(IdentityStatement {
                    ref mut lhs,
                    ref mut rhs,
                    ..
                }) => {
                    lhs.normalize_inplace();
                    rhs.normalize_inplace();
                }
                Statement::Multiply(ref mut e)
                | Statement::Eval(ref mut e, _)
                | Statement::Assign(_, ref mut e) => {
                    e.normalize_inplace();
                }
                _ => {}
            }
        }
    }
}

// execute the module
pub fn do_program(program: &mut Program, write_log: bool, num_threads: usize) {
    // extract the initial input stream from the program
    let mut input_stream = mem::replace(&mut program.input, InputTermStreamer::new(None));

    for module in &mut program.modules {
        // move global statements from the previous module into the new one
        // TODO: do swap instead of clone?
        program.var_info.local_info.variables =
            program.var_info.local_info.global_variables.clone();

        module.normalize_module(&mut program.var_info, &program.procedures);
        debug!("{}", module); // print module code

        let global_info = program.var_info.global_info.clone();

        let mut output = OutputTermStreamer::new();

        output = if num_threads > 1 {
            let mut output_mutarc = Arc::new(Mutex::new(output));

            let queue: MsQueue<Option<Element>> = MsQueue::new();
            let thread_local_varinfo = program.var_info.local_info.clone();

            // create threads that process terms
            crossbeam::scope(|scope| {
                for _ in 0..num_threads {
                    scope.spawn(|| {
                        let mut thread_varinfo = thread_local_varinfo.clone();
                        let mut executed = vec![false];
                        let mut output = TermStreamWrapper::Threaded(output_mutarc.clone());
                        while let Some(x) = queue.pop() {
                            do_module_rec(
                                x,
                                &module.statements,
                                &mut thread_varinfo,
                                &global_info,
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
                            if let Some(x) = input_stream.read_term() {
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
                    thread::sleep(time::Duration::from_millis(50));
                }
            });

            Arc::try_unwrap(output_mutarc)
                .unwrap()
                .into_inner()
                .unwrap()
        } else {
            let mut executed = vec![false];
            let mut output_wrapped = TermStreamWrapper::Single(output);

            while let Some(x) = input_stream.read_term() {
                do_module_rec(
                    x,
                    &module.statements,
                    &mut program.var_info.local_info,
                    &program.var_info.global_info,
                    0,
                    &mut executed,
                    &mut output_wrapped,
                );

                if let TermStreamWrapper::Single(ref output) = output_wrapped {
                    if output.termcount() > 100_000 && output.termcount() % 100_000 == 0 {
                        println!(
                            "{} -- generated: {}\tterms left: {}",
                            module.name,
                            output.termcount(),
                            input_stream.termcount()
                        );
                    }
                }
            }

            output_wrapped.extract()
        };

        output.sort(
            &mut input_stream,
            &mut program.var_info, // TODO: this is not correct in the parallel case
            &module.global_statements,
            write_log,
        );
    }
}
