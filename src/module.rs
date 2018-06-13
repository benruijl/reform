use num_traits::{One, Zero};
use number::Number;
use std::borrow::Cow;
use std::cmp::Ordering;
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::collections::VecDeque;
use std::mem;
use std::sync::{Arc, Mutex};
use std::thread;
use std::time;

use crossbeam;
use crossbeam::sync::MsQueue;

use id::{MatchIterator, MatchKind};
use streaming::MAXTERMMEM;
use streaming::{InputTermStreamer, OutputTermStreamer};
use structure::*;
use tools;

/*
Abstract away the difference between a threaded term streamer
and a single-core streamer.
*/
enum TermStreamWrapper {
    Threaded(Arc<Mutex<OutputTermStreamer>>),
    Single(OutputTermStreamer),
    Owned(Vec<Element>), // used for arguments
}

impl TermStreamWrapper {
    fn extract(self) -> OutputTermStreamer {
        match self {
            TermStreamWrapper::Threaded(x) => Arc::try_unwrap(x).unwrap().into_inner().unwrap(),
            TermStreamWrapper::Single(x) => x,
            TermStreamWrapper::Owned(_) => unreachable!(),
        }
    }

    fn add_term(&mut self, e: Element, var_info: &GlobalVarInfo) {
        match *self {
            TermStreamWrapper::Threaded(ref mut x) => x.lock().unwrap().add_term(e, var_info),
            TermStreamWrapper::Single(ref mut x) => x.add_term(e, var_info),
            TermStreamWrapper::Owned(ref mut x) => x.push(e),
        }
    }
}

impl Element {
    pub fn append_factors(self, other: Element) -> Element {
        match (self, other) {
            (Element::Term(_, mut t1), Element::Term(_, t2)) => {
                t1.extend(t2);
                Element::Term(true, t1)
            }
            (Element::Term(_, mut t1), x) => {
                t1.push(x);
                Element::Term(true, t1)
            }
            (x, Element::Term(_, mut t2)) => {
                t2.push(x);
                Element::Term(true, t2)
            }
            (x1, x2) => Element::Term(true, vec![x1, x2]),
        }
    }

    /// Expands products and positive powers in the element.
    pub fn expand(self, var_info: &GlobalVarInfo) -> Element {
        match self {
            Element::Fn(_, name, args) => {
                let mut f = Element::Fn(
                    true,
                    name,
                    args.into_iter().map(|x| x.expand(var_info)).collect(),
                );
                f.normalize_inplace(var_info);
                f
            }
            Element::Term(_, fs) => {
                let mut r: Vec<Element> = vec![Element::Term(false, vec![])];

                for f in fs {
                    let fe = f.expand(var_info);
                    match fe {
                        Element::SubExpr(_, s) => {
                            r = r
                                .into_iter()
                                .flat_map(|x| {
                                    s.iter()
                                        .map(|y| x.clone().append_factors(y.clone()))
                                        .collect::<Vec<_>>()
                                })
                                .collect();
                        }
                        _ => for rr in &mut r {
                            *rr = mem::replace(rr, DUMMY_ELEM!()).append_factors(fe.clone());
                        },
                    }
                }

                let mut e = Element::SubExpr(true, r);
                e.normalize_inplace(var_info);
                e
            }
            Element::SubExpr(_, f) => {
                let mut e =
                    Element::SubExpr(true, f.into_iter().map(|x| x.expand(var_info)).collect());
                e.normalize_inplace(var_info);
                e
            }
            Element::Pow(_, be) => {
                let (b, e) = { *be };

                let (eb, ee) = (b.expand(var_info), e.expand(var_info));

                if let Element::Num(_, Number::SmallInt(n)) = ee {
                    if n > 0 {
                        if let Element::SubExpr(_, ref t) = eb {
                            // compute the exponent of a list, without generating double entries
                            let it = tools::CombinationsWithReplacement::new(t, n as usize);

                            let mut terms_out = Vec::with_capacity(tools::ncr(
                                t.len() as u64 + n as u64 - 1,
                                t.len() as u64 - 1,
                            )
                                as usize);

                            for (c, mut newt) in it {
                                newt.push(Element::Num(false, c));
                                let mut nt = Element::Term(true, newt);
                                nt.normalize_inplace(var_info);
                                terms_out.push(nt);
                            }

                            let mut e = Element::SubExpr(true, terms_out);
                            e.normalize_inplace(var_info);
                            return e.expand(var_info);
                        }

                        //  (x*y)^z -> x^z*y^z
                        if let Element::Term(_, t) = eb {
                            let mut e = Element::Term(
                                true,
                                t.iter()
                                    .map(|x| {
                                        Element::Pow(
                                            true,
                                            Box::new((
                                                x.clone(),
                                                Element::Num(false, Number::SmallInt(n)),
                                            )),
                                        )
                                    })
                                    .collect(),
                            );
                            e.normalize_inplace(var_info);
                            return e.expand(var_info);
                        }
                    }
                }

                let mut e = Element::Pow(true, Box::new((eb, ee)));
                e.normalize_inplace(var_info);
                e
            }
            _ => self,
        }
    }

    fn extract(mut self, names: &[VarName], var_info: &GlobalVarInfo) -> Element {
        if names.len() == 0 {
            return self;
        }

        if let Element::SubExpr(_, ref mut ts) = self {
            let mut powmap: HashMap<isize, Vec<Element>> = HashMap::new();
            for t in ts.drain(..) {
                let mut pow = 0;
                let mut newterm = vec![];
                match t {
                    Element::Term(_, fs) => {
                        let mut newfacs = vec![];
                        for f in fs {
                            match &f {
                                Element::Pow(_, be) => {
                                    if let Element::Var(n, Number::SmallInt(e)) = be.0 {
                                        if n == names[0] {
                                            if let Element::Num(_, Number::SmallInt(en)) = be.1 {
                                                pow = en * e;
                                                continue;
                                            }
                                        }
                                    }
                                }
                                Element::Var(n, Number::SmallInt(e)) if n == &names[0] => {
                                    pow = *e;
                                    continue;
                                }
                                _ => {}
                            }
                            newfacs.push(f);
                        }
                        newterm.push(Element::Term(true, newfacs));
                    }
                    Element::Var(n, Number::SmallInt(e)) if n == names[0] => {
                        pow = e;
                        newterm.push(Element::Num(false, Number::one()));
                    }
                    Element::Pow(_, ref be) => {
                        if let Element::Var(n, Number::SmallInt(e)) = be.0 {
                            if n == names[0] {
                                if let Element::Num(_, Number::SmallInt(en)) = be.1 {
                                    pow = en * e;
                                    newterm.push(Element::Num(false, Number::one()));
                                }
                            }
                        }
                        if pow == 0 {
                            newterm.push(t.clone());
                        }
                    }
                    _ => newterm.push(t),
                }

                powmap.entry(pow).or_insert(vec![]).extend(newterm);
            }

            for (k, v) in powmap {
                let mut newv = Element::SubExpr(true, v);
                newv.normalize_inplace(var_info);
                newv = newv.extract(&names[1..], var_info);

                ts.push(Element::Term(
                    true,
                    vec![Element::Var(names[0].clone(), Number::SmallInt(k)), newv],
                ));
                ts.last_mut().unwrap().normalize_inplace(var_info);
            }
        }
        self
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
                // FIXME: this pops the last term instead of the first
                match f.pop() {
                    Some(x) => {
                        if m {
                            StatementResult::Executed(x)
                        } else {
                            StatementResult::NotExecuted(x)
                        }
                    }
                    None => StatementResult::Done,
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
        var_info: &'a BorrowedVarInfo<'a>,
    ) -> StatementIter<'a> {
        match *self {
            Statement::IdentityStatement(ref id) => {
                StatementIter::IdentityStatement(id.to_iter(input, var_info))
            }
            Statement::Collect(ref name) => StatementIter::Simple(
                Element::Fn(
                    false,
                    name.clone(),
                    vec![mem::replace(input, DUMMY_ELEM!())],
                ),
                true,
            ),
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
                let mut i = mem::replace(input, DUMMY_ELEM!());
                match i.expand(var_info.global_info) {
                    Element::SubExpr(_, mut f) => {
                        if f.len() == 1 {
                            StatementIter::Simple(f.swap_remove(0), false)
                        } else {
                            f.reverse(); // the multiple iterator pops from the back, so reverse the array
                            StatementIter::Multiple(f, true)
                        }
                    }
                    a => StatementIter::Simple(a, false),
                }
            }
            Statement::Multiply(ref x) => {
                // multiply to the right
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
                        let mut r = Vec::with_capacity(xx.len() + 1);
                        r.push(mem::replace(*a, DUMMY_ELEM!()));
                        for x in xx {
                            r.push(x.clone());
                        }
                        Element::Term(true, r)
                    }
                    (ref mut a, aa) => {
                        Element::Term(true, vec![mem::replace(a, DUMMY_ELEM!()), aa.clone()])
                    }
                };

                res.replace_vars(&var_info.local_info.variables, true); // apply the dollar variables
                res.normalize_inplace(&var_info.global_info);
                StatementIter::Simple(res, true)
            }
            // TODO: use visitor pattern? this is almost a copy of splitarg
            Statement::Symmetrize(ref name) => {
                // sort function arguments at the ground level
                let subs = |n: &VarName, a: &Vec<Element>| {
                    Element::Fn(false, n.clone(), {
                        let mut b = a.clone();
                        b.sort_by(|a, b| a.partial_cmp(b, &var_info.global_info, false).unwrap());
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
            _ => panic!("Unexpected statement '{}' at this stage", self),
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
    if let Element::Num(_, ref n) = input {
        if n.is_zero() {
            return; // drop 0
        }
    }
    if current_index == statements.len() {
        output.add_term(input, global_var_info);
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
            if MatchKind::from_element(
                cond,
                &input,
                &BorrowedVarInfo {
                    global_info: global_var_info,
                    local_info: local_var_info,
                },
            ).next()
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
                ee.normalize_inplace(&global_var_info);
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
        Statement::Extract(ref d, ref xs) => {
            if let Element::Dollar(name, _) = *d {
                let mut dollar = DUMMY_ELEM!();
                let mut dp = local_var_info
                    .variables
                    .get_mut(&name)
                    .expect("Dollar variable is uninitialized");

                mem::swap(&mut dollar, dp);
                *dp = dollar.extract(xs, &global_var_info);
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
        // for every function, execute the statements
        // this will create a subrecursion
        Statement::Argument(ref func, ref sts) => {
            if let Element::Var(name, _) = *func {
                match input {
                    Element::Fn(_, name1, ref mut args) => {
                        if name == name1 {
                            // execute the statements
                            let mut newfuncarg = Vec::with_capacity(args.len());
                            let old_args = mem::replace(args, vec![]);

                            for x in old_args {
                                let mut tsr = TermStreamWrapper::Owned(vec![]);
                                do_module_rec(
                                    x,
                                    sts,
                                    local_var_info,
                                    global_var_info,
                                    0,
                                    term_affected, // TODO: what to do here?
                                    &mut tsr,
                                );

                                if let TermStreamWrapper::Owned(mut nfa) = tsr {
                                    match nfa.len() {
                                        0 => newfuncarg.push(Element::Num(false, Number::zero())),
                                        1 => newfuncarg.push(nfa.swap_remove(0)),
                                        _ => {
                                            let mut sub = Element::SubExpr(true, nfa);
                                            sub.normalize_inplace(global_var_info);
                                            newfuncarg.push(sub)
                                        }
                                    }
                                } else {
                                    unreachable!()
                                }
                            }

                            let mut newfunc = Element::Fn(true, name1.clone(), newfuncarg);
                            newfunc.normalize_inplace(global_var_info);

                            return do_module_rec(
                                newfunc,
                                statements,
                                local_var_info,
                                global_var_info,
                                current_index + 1,
                                term_affected,
                                output,
                            );
                        }
                    }
                    Element::Term(_, factors) => {
                        let mut newfactors = vec![];
                        for f in factors {
                            if let Element::Fn(d, name1, args) = f {
                                if name == name1 {
                                    // execute the statements
                                    let mut newfuncarg = Vec::with_capacity(args.len());

                                    for x in args {
                                        let mut tsr = TermStreamWrapper::Owned(vec![]);
                                        do_module_rec(
                                            x,
                                            sts,
                                            local_var_info,
                                            global_var_info,
                                            0,
                                            term_affected, // TODO: what to do here?
                                            &mut tsr,
                                        );

                                        if let TermStreamWrapper::Owned(mut nfa) = tsr {
                                            match nfa.len() {
                                                0 => newfuncarg
                                                    .push(Element::Num(false, Number::zero())),
                                                1 => newfuncarg.push(nfa.swap_remove(0)),
                                                _ => {
                                                    let mut sub = Element::SubExpr(true, nfa);
                                                    sub.normalize_inplace(global_var_info);
                                                    newfuncarg.push(sub)
                                                }
                                            }
                                        } else {
                                            unreachable!()
                                        }
                                    }

                                    let mut newfunc = Element::Fn(true, name1.clone(), newfuncarg);
                                    newfunc.normalize_inplace(global_var_info);
                                    newfactors.push(newfunc);
                                } else {
                                    newfactors.push(Element::Fn(d, name1, args));
                                }
                            } else {
                                newfactors.push(f);
                            }
                        }

                        let mut newterm = Element::Term(true, newfactors);
                        newterm.normalize_inplace(global_var_info);

                        return do_module_rec(
                            newterm,
                            statements,
                            local_var_info,
                            global_var_info,
                            current_index + 1,
                            term_affected,
                            output,
                        );
                    }
                    _ => {
                        // TODO: add case for term
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
            } else {
                panic!("Specify the function name as argument to argument.")
            }
        }
        // this will create a subrecursion
        Statement::Inside(ref ds, ref sts) => {
            for d in ds {
                if let Element::Dollar(name, _) = *d {
                    let mut dollar = mem::replace(
                        local_var_info
                            .variables
                            .get_mut(&name)
                            .expect("Dollar variable is uninitialized"),
                        DUMMY_ELEM!(),
                    );

                    let mut tsr = TermStreamWrapper::Owned(vec![]);
                    match dollar {
                        Element::SubExpr(_, se) => {
                            for x in se {
                                do_module_rec(
                                    x,
                                    sts,
                                    local_var_info,
                                    global_var_info,
                                    0,
                                    &mut vec![false],
                                    &mut tsr,
                                );
                            }
                        }
                        _ => do_module_rec(
                            dollar,
                            sts,
                            local_var_info,
                            global_var_info,
                            0,
                            &mut vec![false],
                            &mut tsr,
                        ),
                    }

                    if let TermStreamWrapper::Owned(mut nfa) = tsr {
                        local_var_info.variables.insert(
                            name,
                            match nfa.len() {
                                0 => Element::Num(false, Number::zero()),
                                1 => nfa.swap_remove(0),
                                _ => {
                                    let mut sub = Element::SubExpr(true, nfa);
                                    sub.normalize_inplace(global_var_info);
                                    sub
                                }
                            },
                        );
                    }
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
        Statement::Maximum(ref dollar) => {
            if let Element::Dollar(ref d, ..) = *dollar {
                if let Some(x) = local_var_info.variables.get(d) {
                    match local_var_info.global_variables.entry(d.clone()) {
                        Entry::Occupied(mut y) => {
                            if let Some(Ordering::Less) =
                                y.get().partial_cmp(x, global_var_info, false)
                            {
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
        Statement::Print(ref mode, ref vars) => {
            if vars.len() == 0 {
                println!(
                    "\t+{}",
                    ElementPrinter {
                        element: &input,
                        var_info: &global_var_info,
                        print_mode: *mode
                    }
                );
            } else {
                for d in vars {
                    if let Some(x) = local_var_info.variables.get(d) {
                        println!(
                            "{}",
                            ElementPrinter {
                                element: x,
                                var_info: &global_var_info,
                                print_mode: *mode
                            }
                        );
                    }
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
        _ => {}
    }

    {
        // replace all dollar variables in current statement
        // this prevents copying of dollar variables
        // consider this as a workaround for excessive copying of (large) dollar variables
        let mut ns = Cow::Borrowed(&statements[current_index]);
        if ns.contains_dollar() {
            if ns.to_mut().replace_vars(&local_var_info.variables, true) {
                ns.to_mut().normalize(global_var_info);
            }
        }

        // now we can pass an empty list of variables, since they are all replaced
        let oldvarinfo = LocalVarInfo {
            variables: HashMap::new(),
            global_variables: HashMap::new(),
        };
        let var_info = BorrowedVarInfo {
            global_info: global_var_info,
            local_info: &oldvarinfo,
        };

        let mut it = ns.to_iter(&mut input, &var_info);
        loop {
            match it.next() {
                StatementResult::Executed(f) => {
                    // make sure every new term has its own local variables
                    /*for (var, e) in &oldvarinfo.variables {
                        if let Some(attribs) = global_var_info.func_attribs.get(var) {
                            if attribs.contains(&FunctionAttributes::NonLocal) {
                                continue;
                            }
                        }

                        // if the value of a local dollar is different, we change it back
                        if let Some(v) = local_var_info.variables.get_mut(var) {
                            if v != e {
                                *v = e.clone();
                            }
                        } else {
                            unreachable!("Dollar variable disappeared");
                        }
                    }*/

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
        statements: &mut [Statement],
        var_info: &mut VarInfo,
        procedures: &[Procedure],
        output: &mut Vec<Statement>,
    ) {
        for x in statements.iter_mut() {
            match *x {
                Statement::Repeat(ref mut ss) => {
                    output.push(Statement::PushChange);
                    let pos = output.len();
                    Module::statements_to_control_flow_stat(ss, var_info, procedures, output);
                    output.push(Statement::JumpIfChanged(pos - 1));
                }
                Statement::Argument(ref f, ref mut ss) => {
                    // keep the substructure
                    let mut linarg = vec![];
                    Module::statements_to_control_flow_stat(ss, var_info, procedures, &mut linarg);
                    output.push(Statement::Argument(f.clone(), linarg));
                }
                Statement::Inside(ref f, ref mut ss) => {
                    // keep the substructure
                    let mut linarg = vec![];
                    Module::statements_to_control_flow_stat(ss, var_info, procedures, &mut linarg);
                    output.push(Statement::Inside(f.clone(), linarg));
                }
                Statement::IfElse(ref prod, ref mut m, ref mut nm) => {
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
                Statement::ForInRange(ref d, ref mut l, ref mut u, ref mut s) => {
                    if let Element::Dollar(dd, _) = *d {
                        // TODO: note that dollar variables in the range parameters are evaluted at
                        // module compile time instead of runtime!
                        l.normalize_inplace(&var_info.global_info);
                        u.normalize_inplace(&var_info.global_info);

                        let mut replace_map = HashMap::new();
                        if let Element::Num(_, Number::SmallInt(li)) = *l {
                            if let Element::Num(_, Number::SmallInt(ui)) = *u {
                                // unroll the loop
                                for ll in li..ui {
                                    let lle = Element::Num(false, Number::SmallInt(ll));
                                    replace_map.insert(dd, lle);
                                    for ss in s.iter() {
                                        let mut news = ss.clone();
                                        if news.replace_vars(&replace_map, true) {
                                            news.normalize(&var_info.global_info);
                                        }
                                        output.push(news);
                                    }
                                }
                            } else {
                                panic!("Upper range index is not an integer");
                            }
                        } else {
                            panic!("Lower range index is not an integer");
                        }
                    } else {
                        panic!("Loop counter should be a dollar variable");
                    }
                }
                Statement::ForIn(ref d, ref mut l, ref mut s) => {
                    if let Element::Dollar(dd, _) = *d {
                        let mut replace_map = HashMap::new();

                        // unroll the loop
                        for ll in l {
                            replace_map.insert(dd, ll.clone());
                            for ss in s.iter() {
                                let mut news = ss.clone();
                                if news.replace_vars(&replace_map, true) {
                                    news.normalize(&var_info.global_info);
                                }
                                output.push(news);
                            }
                        }
                    } else {
                        panic!("Loop counter should be a dollar variable");
                    }
                }
                Statement::Call(ref name, ref mut args) => {
                    for a in args.iter_mut() {
                        a.normalize_inplace(&var_info.global_info);
                    }

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
                                if let Element::Var(map_source, _) = *k {
                                    map.insert(map_source.clone(), v.clone());
                                } else {
                                    panic!("Argument in procedure header should be a variable");
                                }
                            }

                            for lv in &p.local_args {
                                // create unique variable
                                if let Element::Var(name, _) = *lv {
                                    map.insert(
                                        name.clone(),
                                        Element::Var(var_info.add_local(&name), Number::one()),
                                    );
                                }
                            }

                            let mut newmod = p
                                .statements
                                .iter()
                                .cloned()
                                .map(|mut x| {
                                    x.normalize(&var_info.global_info);
                                    if x.replace_vars(&map, false) {
                                        x.normalize(&var_info.global_info);
                                    }
                                    x
                                })
                                .collect::<Vec<_>>();

                            Module::statements_to_control_flow_stat(
                                &mut newmod,
                                var_info,
                                procedures,
                                output,
                            );
                        }
                    }
                }
                Statement::Module(_) => panic!("Nesting of modules is not allowed"),
                ref a => output.push(a.clone()),
            }
        }
    }

    fn execute_module(
        &mut self,
        expressions: &mut Vec<Expression>,
        var_info: &mut VarInfo,
        procedures: &[Procedure],
        sort_statements: &mut Vec<Statement>,
        write_log: bool,
        verbosity: u64,
        num_threads: usize,
    ) {
        // normalize the module
        let mut old_statements = mem::replace(&mut self.statements, vec![]);
        Module::statements_to_control_flow_stat(
            &mut old_statements,
            var_info,
            &procedures,
            &mut self.statements,
        );

        for x in &mut self.statements {
            x.normalize(&var_info.global_info);
        }

        debug!("{}", self); // print module code

        // execute the module for every expression
        for &mut (ref name, ref mut input_stream) in expressions {
            // only process active expressions
            if (!self.active_exprs.is_empty() && !self.active_exprs.contains(name))
                || self.exclude_exprs.contains(name)
            {
                continue;
            }

            let global_info = var_info.global_info.clone();

            let mut output = OutputTermStreamer::new();

            output = if num_threads > 1 {
                let mut output_mutarc = Arc::new(Mutex::new(output));

                let queue: MsQueue<Option<Element>> = MsQueue::new();
                let thread_local_varinfo = var_info.local_info.clone();

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
                                    &self.statements,
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
                        &self.statements,
                        &mut var_info.local_info,
                        &var_info.global_info,
                        0,
                        &mut executed,
                        &mut output_wrapped,
                    );

                    if let TermStreamWrapper::Single(ref output) = output_wrapped {
                        if output.termcount() > 100_000 && output.termcount() % 100_000 == 0 {
                            println!(
                                "{} -- generated: {}\tterms left: {}",
                                self.name,
                                output.termcount(),
                                input_stream.termcount()
                            );
                        }
                    }
                }

                output_wrapped.extract()
            };

            let exprname = var_info.get_str_name(name);
            output.sort(
                &exprname,
                input_stream,
                &self.name,
                var_info, // TODO: this is not correct in the parallel case
                sort_statements,
                verbosity > 0,
                write_log,
            );
        }

        // update the variables by their global values
        for (d, v) in var_info.local_info.global_variables.drain() {
            var_info.local_info.variables.insert(d, v);
        }
    }
}

impl Program {
    pub fn do_program(&mut self, write_log: bool, verbosity: u64, num_threads: usize) {
        // set the log level
        self.var_info.global_info.log_level = verbosity as usize;

        // statements that should be executed during sorting
        let mut sort_statements = vec![];

        let mut statements: VecDeque<Statement> = self.statements.iter().cloned().collect();

        while let Some(mut x) = statements.pop_front() {
            match &mut x {
                Statement::Module(ref mut m) => m.execute_module(
                    &mut self.expressions,
                    &mut self.var_info,
                    &self.procedures,
                    &mut sort_statements,
                    write_log,
                    verbosity,
                    num_threads,
                ),
                Statement::NewExpression(ref name, ref mut e) => {
                    let mut expr = InputTermStreamer::new(None);
                    let mut ee = mem::replace(e, DUMMY_ELEM!());
                    ee.normalize_inplace(&self.var_info.global_info);

                    match ee {
                        Element::SubExpr(_, t) => for x in t {
                            expr.add_term_input(x);
                        },
                        x => {
                            expr.add_term_input(x);
                        }
                    }
                    self.expressions.push((name.clone(), expr));
                }
                Statement::Assign(ref dollar, ref e) => {
                    let mut ee = e.clone();
                    ee.replace_vars(&self.var_info.local_info.variables, true);
                    ee.normalize_inplace(&self.var_info.global_info);
                    if let Element::Dollar(ref d, ..) = *dollar {
                        self.var_info.local_info.add_dollar(d.clone(), ee);
                    }
                }
                Statement::Extract(ref d, ref xs) => {
                    if let Element::Dollar(name, _) = *d {
                        let mut dollar = DUMMY_ELEM!();
                        let mut dp = self
                            .var_info
                            .local_info
                            .variables
                            .get_mut(&name)
                            .expect("Dollar variable is uninitialized");

                        mem::swap(&mut dollar, dp);
                        *dp = dollar.extract(xs, &self.var_info.global_info);
                    }
                }
                // this will create a subrecursion
                Statement::Inside(ref ds, ref mut sts) => {
                    // normalize the statements
                    let mut old_statements = mem::replace(sts, vec![]);
                    Module::statements_to_control_flow_stat(
                        &mut old_statements,
                        &mut self.var_info,
                        &self.procedures,
                        sts,
                    );

                    for x in sts.iter_mut() {
                        x.normalize(&self.var_info.global_info);
                    }

                    for d in ds {
                        if let Element::Dollar(name, _) = *d {
                            let mut dollar = mem::replace(
                                self.var_info
                                    .local_info
                                    .variables
                                    .get_mut(&name)
                                    .expect("Dollar variable is uninitialized"),
                                DUMMY_ELEM!(),
                            );

                            let mut tsr = TermStreamWrapper::Owned(vec![]);

                            match dollar {
                                Element::SubExpr(_, se) => {
                                    for x in se {
                                        do_module_rec(
                                            x,
                                            sts,
                                            &mut self.var_info.local_info,
                                            &self.var_info.global_info,
                                            0,
                                            &mut vec![false],
                                            &mut tsr,
                                        );
                                    }
                                }
                                _ => do_module_rec(
                                    dollar,
                                    sts,
                                    &mut self.var_info.local_info,
                                    &self.var_info.global_info,
                                    0,
                                    &mut vec![false],
                                    &mut tsr,
                                ),
                            }

                            if let TermStreamWrapper::Owned(mut nfa) = tsr {
                                self.var_info.local_info.variables.insert(
                                    name,
                                    match nfa.len() {
                                        0 => Element::Num(false, Number::zero()),
                                        1 => nfa.swap_remove(0),
                                        _ => {
                                            let mut sub = Element::SubExpr(true, nfa);
                                            sub.normalize_inplace(&self.var_info.global_info);
                                            sub
                                        }
                                    },
                                );
                            }
                        }
                    }
                }
                Statement::Attrib(ref f, ref attribs) => match *f {
                    Element::Var(ref name, _) | Element::Dollar(ref name, _) => {
                        self.var_info
                            .global_info
                            .func_attribs
                            .insert(name.clone(), attribs.clone());
                    }
                    _ => {
                        panic!("Can only assign attributes to functions or dollar variables");
                    }
                },
                Statement::ForInRange(ref d, ref mut l, ref mut u, ref mut s) => {
                    if let Element::Dollar(dd, _) = *d {
                        l.normalize_inplace(&self.var_info.global_info);
                        u.normalize_inplace(&self.var_info.global_info);

                        let mut replace_map = HashMap::new();
                        if let Element::Num(_, Number::SmallInt(li)) = *l {
                            if let Element::Num(_, Number::SmallInt(ui)) = *u {
                                // unroll the loop
                                for ll in (li..ui).rev() {
                                    let lle = Element::Num(false, Number::SmallInt(ll));
                                    replace_map.insert(dd, lle);
                                    for ss in s.iter().rev() {
                                        let mut news = ss.clone();
                                        if news.replace_vars(&replace_map, true) {
                                            news.normalize(&self.var_info.global_info);
                                        }
                                        statements.push_front(news);
                                    }
                                }
                            } else {
                                panic!("Upper range index is not an integer");
                            }
                        } else {
                            panic!("Lower range index is not an integer");
                        }
                    } else {
                        panic!("Loop counter should be a dollar variable");
                    }
                }
                Statement::ForIn(ref d, ref l, ref s) => {
                    if let Element::Dollar(dd, _) = *d {
                        let mut replace_map = HashMap::new();

                        // unroll the loop
                        for ll in l.iter().rev() {
                            replace_map.insert(dd, ll.clone());
                            for ss in s.iter().rev() {
                                let mut news = ss.clone();
                                if news.replace_vars(&replace_map, true) {
                                    news.normalize(&self.var_info.global_info);
                                }
                                statements.push_front(news);
                            }
                        }
                    } else {
                        panic!("Loop counter should be a dollar variable");
                    }
                }
                Statement::Print(ref mode, ref vars) => {
                    // only print dollar variables at this stage
                    for d in vars {
                        if let Some(x) = self.var_info.local_info.variables.get(d) {
                            println!(
                                "{}",
                                ElementPrinter {
                                    element: x,
                                    var_info: &self.var_info.global_info,
                                    print_mode: *mode
                                }
                            );
                        }
                    }

                    if vars.len() == 0 {
                        sort_statements.push(Statement::Print(mode.clone(), vec![]));
                    }
                }
                Statement::Collect(ref id) => sort_statements.push(Statement::Collect(id.clone())),
                _ => unimplemented!(),
            }
        }
    }
}
