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
use std::time::{Duration, Instant};

use crossbeam;
use crossbeam::queue::MsQueue;

use expand::ExpandIterator;
use id::{MatchIterator, MatchKind, MatchObject, MatchOpt};
use streaming::MAXTERMMEM;
use streaming::{
    InputExpression, InputExpressionIterator, InputExpressionWriter, OutputTermStreamer,
};
use structure::*;

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
    pub fn append_factors(self, other: &Element) -> Element {
        match (self, other) {
            (Element::Term(_, ref mut t1), Element::Term(_, t2)) => {
                t1.extend(t2.iter().cloned());
                Element::Term(true, mem::replace(t1, vec![]))
            }
            (x1, Element::Num(false, Number::SmallInt(1))) => x1,
            (Element::Term(_, mut t1), x) => {
                t1.push(x.clone());
                Element::Term(true, t1)
            }
            (Element::Num(false, Number::SmallInt(1)), x2) => x2.clone(),
            (ref x, Element::Term(_, t2)) => {
                let mut k = t2.clone();
                k.push(x.clone());
                Element::Term(true, k)
            }
            (x1, x2) => Element::Term(true, vec![x1, x2.clone()]),
        }
    }

    pub fn append_factors_mut(&mut self, other: &Element) {
        *self = match (&mut *self, other) {
            (Element::Term(ref mut dirty, ref mut t1), Element::Term(_, t2)) => {
                t1.extend(t2.iter().cloned());
                *dirty = true;
                return;
            }
            (Element::Num(false, Number::SmallInt(1)), x2) => x2.clone(),
            (_, Element::Num(false, Number::SmallInt(1))) => {
                return;
            }
            (Element::Term(ref mut dirty, ref mut t1), x) => {
                t1.push(x.clone());
                *dirty = true;
                return;
            }

            (ref mut x1, Element::Term(_, t2)) => {
                let mut k = t2.clone();
                k.push(mem::replace(x1, Element::default()));
                Element::Term(true, k)
            }
            (x1, x2) => Element::Term(true, vec![mem::replace(x1, Element::default()), x2.clone()]),
        }
    }

    pub fn append_factors_mut_move(&mut self, other: Element) {
        *self = match (&mut *self, other) {
            (Element::Term(ref mut dirty, ref mut t1), Element::Term(_, ref mut t2)) => {
                t1.extend(mem::replace(t2, vec![]));
                *dirty = true;
                return;
            }
            (Element::Num(false, Number::SmallInt(1)), ref mut x2) => {
                mem::replace(x2, Element::default())
            }
            (_, Element::Num(false, Number::SmallInt(1))) => {
                return;
            }
            (Element::Term(ref mut dirty, ref mut t1), ref mut x) => {
                t1.push(mem::replace(x, Element::default()));
                *dirty = true;
                return;
            }
            (ref mut x1, Element::Term(_, ref mut t2)) => {
                t2.push(mem::replace(x1, Element::default()));
                Element::Term(true, mem::replace(t2, vec![]))
            }
            (ref mut x1, ref mut x2) => Element::Term(
                true,
                vec![
                    mem::replace(*x1, Element::default()),
                    mem::replace(x2, Element::default()),
                ],
            ),
        }
    }

    pub fn pow(self, num: Element) -> Element {
        if let Element::Num(dirty, n) = num {
            if let Element::Var(x1, n1) = self {
                return Element::Var(x1, n1 * n);
            } else {
                Element::Pow(true, Box::new((self, Element::Num(dirty, n))))
            }
        } else {
            Element::Pow(true, Box::new((self, num)))
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
    ExpandIterator(ExpandIterator<'a>),
    Multiple(Vec<Element>, bool),
    Simple(Element, bool), // yield a term once
    None,
}

impl<'a> StatementIter<'a> {
    fn next(&mut self, var_info: &GlobalVarInfo) -> StatementResult<Element> {
        match *self {
            StatementIter::IdentityStatement(ref mut id) => id.next(),
            StatementIter::ExpandIterator(ref mut it) => {
                match it.next(var_info) {
                    Some(x) => match x {
                        MatchOpt::Single(x) => StatementResult::Executed({ x.clone() }), // FIXME: it is not always executed!
                        MatchOpt::SingleOwned(x) => StatementResult::Executed({ x }),
                        MatchOpt::Multiple(x) => {
                            StatementResult::Executed(Element::Term(false, x.to_vec()))
                        }
                    },
                    None => StatementResult::Done,
                }
            }
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
                    vec![mem::replace(input, Element::default())],
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
                // use the iterator by default
                if true {
                    StatementIter::ExpandIterator(ExpandIterator::new(
                        input,
                        &var_info.global_info,
                        true,
                    ))
                } else {
                    let mut i = mem::replace(input, Element::default());
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
                        r.push(mem::replace(*a, Element::default()));
                        for x in xx {
                            r.push(x.clone());
                        }
                        Element::Term(true, r)
                    }
                    (ref mut a, aa) => {
                        Element::Term(true, vec![mem::replace(a, Element::default()), aa.clone()])
                    }
                };

                res.replace_dollar(&var_info.local_info.variables); // apply the dollar variables
                res.normalize_inplace(&var_info.global_info);
                StatementIter::Simple(res, true)
            }
            Statement::ReplaceBy(ref x) => {
                let mut res = x.clone();
                res.replace_dollar(&var_info.local_info.variables);
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
        Statement::Discard => {
            // discard the term
            return;
        }
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
            match cond {
                IfCondition::Match(e) => {
                    let true_block = {
                        let bi = BorrowedVarInfo {
                            global_info: global_var_info,
                            local_info: local_var_info,
                        };
                        let mut m = MatchObject::new();
                        let mut remaining = vec![];
                        MatchKind::from_element(e, &input, &bi).next(&mut m, &mut remaining)
                    };
                    if true_block {
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
                IfCondition::Defined(e) => {
                    if local_var_info.get_dollar(e).is_some() {
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
                IfCondition::Comparison(e1, e2, c) => {
                    let istrue = if e1.contains_dollar() || e2.contains_dollar() {
                        let mut ee1 = e1.clone();

                        if e1.contains_dollar() {
                            if ee1
                                .replace_dollar(&local_var_info.variables)
                                .contains(ReplaceResult::Replaced)
                            {
                                ee1.normalize_inplace(&global_var_info);
                            } else {
                                panic!("Unsubstituted dollar variable in comparison");
                            }
                        }

                        let mut ee2 = e2.clone();
                        if e2.contains_dollar() {
                            if ee2
                                .replace_dollar(&local_var_info.variables)
                                .contains(ReplaceResult::Replaced)
                            {
                                ee2.normalize_inplace(&global_var_info);
                            } else {
                                panic!("Unsubstituted dollar variable in comparison");
                            }
                        }

                        c.cmp_rel(ee1.partial_cmp(&ee2, global_var_info, false).unwrap())
                    } else {
                        c.cmp_rel(e1.partial_cmp(e2, global_var_info, false).unwrap())
                    };

                    if istrue {
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
            ee.normalize_inplace(&global_var_info);
            if ee
                .replace_dollar(&local_var_info.variables)
                .contains(ReplaceResult::Replaced)
            {
                ee.normalize_inplace(&global_var_info);
            }
            local_var_info.add_dollar(dollar.clone(), ee);
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
        Statement::MatchAssign(ref pat, ref ss) => {
            let mut newss = vec![];
            {
                let bi = BorrowedVarInfo {
                    global_info: global_var_info,
                    local_info: local_var_info,
                };
                let mut m = MatchObject::new();
                let mut remaining = vec![];
                if MatchKind::from_element(pat, &input, &bi).next(&mut m, &mut remaining) {
                    for s in ss {
                        if let Statement::Assign(ref dollar, ref e) = s {
                            newss.push(Statement::Assign(
                                dollar.clone(),
                                e.apply_map(&mut m).into_single().0,
                            ));
                        }
                    }
                }
            }

            for s in newss {
                if let Statement::Assign(ref dollar, ref e) = s {
                    let mut ee = e.clone();
                    if ee
                        .replace_dollar(&local_var_info.variables)
                        .contains(ReplaceResult::Replaced)
                    {
                        ee.normalize_inplace(&global_var_info);
                    }
                    local_var_info.add_dollar(dollar.clone(), ee);
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
        Statement::Extract(ref d, ref xs) => {
            if let Element::Dollar(..) = *d {
                let mut dp = local_var_info
                    .get_dollar_mut(d)
                    .expect("Dollar variable is uninitialized");
                *dp = mem::replace(dp, Element::default()).extract(xs, &global_var_info);
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
        Statement::Argument(ref funcs, ref sts) => {
            // TODO: apply to functions at all levels instead of just the ground level
            match input {
                Element::Fn(_, name1, args) => {
                    // the dollar variable should be substituted
                    if funcs.contains(&Element::Var(name1, Number::one())) {
                        // execute the statements
                        let mut newfuncarg = Vec::with_capacity(args.len());

                        for x in args {
                            let mut tsr = TermStreamWrapper::Owned(vec![]);
                            match x {
                                Element::SubExpr(_, terms) => {
                                    for t in terms {
                                        do_module_rec(
                                            t,
                                            sts,
                                            local_var_info,
                                            global_var_info,
                                            0,
                                            term_affected, // TODO: what to do here?
                                            &mut tsr,
                                        );
                                    }
                                }
                                _ => {
                                    do_module_rec(
                                        x,
                                        sts,
                                        local_var_info,
                                        global_var_info,
                                        0,
                                        term_affected, // TODO: what to do here?
                                        &mut tsr,
                                    );
                                }
                            }

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
                    } else {
                        return do_module_rec(
                            Element::Fn(false, name1, args),
                            statements,
                            local_var_info,
                            global_var_info,
                            current_index + 1,
                            term_affected,
                            output,
                        );
                    }
                }
                Element::Term(_, mut factors) => {
                    for f in &mut factors {
                        let mut changed = false;
                        if let Element::Fn(dirty, name1, args) = f {
                            if funcs.contains(&Element::Var(*name1, Number::one())) {
                                // execute the statements
                                let mut newfuncarg = Vec::with_capacity(args.len());
                                changed = true;
                                *dirty = true;

                                for x in mem::replace(args, vec![]) {
                                    let mut tsr = TermStreamWrapper::Owned(vec![]);

                                    match x {
                                        Element::SubExpr(_, terms) => {
                                            for t in terms {
                                                do_module_rec(
                                                    t,
                                                    sts,
                                                    local_var_info,
                                                    global_var_info,
                                                    0,
                                                    term_affected, // TODO: what to do here?
                                                    &mut tsr,
                                                );
                                            }
                                        }
                                        _ => {
                                            do_module_rec(
                                                x,
                                                sts,
                                                local_var_info,
                                                global_var_info,
                                                0,
                                                term_affected, // TODO: what to do here?
                                                &mut tsr,
                                            );
                                        }
                                    }

                                    if let TermStreamWrapper::Owned(mut nfa) = tsr {
                                        match nfa.len() {
                                            0 => {
                                                newfuncarg.push(Element::Num(false, Number::zero()))
                                            }
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

                                *args = newfuncarg;
                            }
                        }
                        if changed {
                            f.normalize_inplace(global_var_info);
                        }
                    }

                    let mut newterm = Element::Term(true, factors);
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
        }
        // this will create a subrecursion
        Statement::Inside(ref ds, ref sts) => {
            for d in ds {
                if let Element::Dollar(..) = *d {
                    let mut dollar = mem::replace(
                        local_var_info
                            .get_dollar_mut(d)
                            .expect("Dollar variable is uninitialized"),
                        Element::default(),
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
                        local_var_info.add_dollar(
                            d.clone(),
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
            if let Element::Dollar(ref name, ..) = *dollar {
                if let Some(x) = local_var_info.get_dollar(dollar).cloned() {
                    match local_var_info.global_variables.entry(name.clone()) {
                        Entry::Occupied(mut y) => {
                            if let Some(Ordering::Less) =
                                y.get().partial_cmp(&x, global_var_info, false)
                            {
                                *y.get_mut() = x;
                            }
                        }
                        Entry::Vacant(y) => {
                            y.insert(x);
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
            let mut out = String::new();

            let add_newline = vars.iter().all(|e| {
                if let PrintObject::Literal(..) = e {
                    false
                } else {
                    true
                }
            });
            for v in vars {
                v.print(&mut out, &input, local_var_info, global_var_info, mode);
                if add_newline {
                    out.push('\n');
                }
            }
            if add_newline {
                print!("{}", out);
            } else {
                println!("{}", out);
            }

            if vars.len() == 0 {
                println!(
                    "{}",
                    ElementPrinter {
                        element: &input,
                        var_info: global_var_info,
                        print_mode: *mode
                    }
                );
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
            if ns
                .to_mut()
                .replace_dollar(&local_var_info.variables)
                .contains(ReplaceResult::Replaced)
            {
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
            match it.next(global_var_info) {
                StatementResult::Executed(mut f) => {
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

                    // It could be that the result contains a dollar variable
                    // that became substitutable after an index change
                    if f.replace_dollar(&local_var_info.variables)
                        .contains(ReplaceResult::Replaced)
                    {
                        f.normalize_inplace(global_var_info);
                    }

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
                Statement::IdentityStatement(..) => {
                    if x.contains_dollar() {
                        // For the moment this command will set a flag if the statement
                        // contains no dollar variables. We cannot replace all dollar variables
                        // at compile time, since they may change at runtime.
                        // TODO: track if dollar variables change
                        x.replace_dollar(&HashMap::new());
                    }
                    output.push(x.clone())
                }
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
                    if let Element::Dollar(dd, ref inds) = *d {
                        // TODO: note that dollar variables in the range parameters are evaluted at
                        // module compile time instead of runtime!
                        l.normalize_inplace(&var_info.global_info);
                        u.normalize_inplace(&var_info.global_info);

                        let mut replace_map = HashMap::new();
                        if let Element::Num(_, Number::SmallInt(li)) = *l {
                            if let Element::Num(_, Number::SmallInt(ui)) = *u {
                                // unroll the loop
                                let mut newout = vec![];
                                for ll in li..ui {
                                    let lle = Element::Num(false, Number::SmallInt(ll));
                                    let mut mm = HashMap::new();
                                    mm.insert(inds.clone(), lle);
                                    replace_map.insert(dd, mm);
                                    for ss in s.iter() {
                                        let mut news = ss.clone();
                                        if news
                                            .replace_dollar(&replace_map)
                                            .contains(ReplaceResult::Replaced)
                                        {
                                            news.normalize(&var_info.global_info);
                                        }
                                        newout.push(news);
                                    }
                                }

                                Module::statements_to_control_flow_stat(
                                    &mut newout,
                                    var_info,
                                    procedures,
                                    output,
                                );
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
                    if let Element::Dollar(dd, ref inds) = *d {
                        let mut replace_map = HashMap::new();

                        // unroll the loop
                        let mut newout = vec![];
                        for ll in l {
                            let mut mm = HashMap::new();
                            mm.insert(inds.clone(), ll.clone());
                            replace_map.insert(dd, mm);
                            for ss in s.iter() {
                                let mut news = ss.clone();
                                if news
                                    .replace_dollar(&replace_map)
                                    .contains(ReplaceResult::Replaced)
                                {
                                    news.normalize(&var_info.global_info);
                                }
                                newout.push(news);
                            }
                        }

                        Module::statements_to_control_flow_stat(
                            &mut newout,
                            var_info,
                            procedures,
                            output,
                        );
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
                                    if x.replace_elements(&map) {
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
        let expression_names: Vec<_> = var_info
            .global_info
            .expressions
            .values()
            .map(|x| x.name)
            .collect();

        for expression_name in expression_names {
            let mut input_stream = var_info
                .global_info
                .expressions
                .remove(&expression_name)
                .unwrap();

            // only process active expressions
            if (!self.active_exprs.is_empty() && !self.active_exprs.contains(&input_stream.name))
                || self.exclude_exprs.contains(&input_stream.name)
            {
                continue;
            }

            let module_start_time = Instant::now();

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
                    let mut input_iter = input_stream.into_iter();
                    while !done {
                        if queue.is_empty() {
                            debug!("Loading new batch");
                            for _ in 0..MAXTERMMEM {
                                if let Some(x) = input_iter.next() {
                                    queue.push(Some(x.to_element()));
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
                        thread::sleep(Duration::from_millis(50));
                    }
                });

                Arc::try_unwrap(output_mutarc)
                    .unwrap()
                    .into_inner()
                    .unwrap()
            } else {
                let mut executed = vec![false];
                let mut output_wrapped = TermStreamWrapper::Single(output);
                let mut input_iter = input_stream.into_iter();

                while let Some(x) = input_iter.next() {
                    do_module_rec(
                        x.to_element(),
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
                                input_stream.term_count()
                            );
                        }
                    }
                }

                output_wrapped.extract()
            };

            let exprname = var_info.get_str_name(&input_stream.name);
            let pre_sort_time = Instant::now();
            output.sort(
                &exprname,
                InputExpressionWriter::new(&mut input_stream),
                &self.name,
                var_info, // TODO: this is not correct in the parallel case
                sort_statements,
                verbosity > 0,
                write_log,
            );

            var_info
                .global_info
                .expressions
                .insert(expression_name, input_stream);

            let post_sort_time = Instant::now();

            println!(
                "{} --\ttime: {:#?}\tsort time: {:#?}",
                self.name,
                post_sort_time.duration_since(module_start_time),
                post_sort_time.duration_since(pre_sort_time)
            );
        }

        // update the variables by their global values
        // TODO: global variables can also have indices?
        let gi = mem::replace(&mut var_info.local_info.global_variables, HashMap::new());
        for (d, v) in gi {
            var_info
                .local_info
                .add_dollar(Element::Dollar(d.clone(), vec![]), v);
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
            x.normalize(&self.var_info.global_info);

            match x {
                Statement::Module(mut m) => m.execute_module(
                    &mut self.var_info,
                    &self.procedures,
                    &mut sort_statements,
                    write_log,
                    verbosity,
                    num_threads,
                ),
                Statement::NewExpression(name, mut e) => {
                    let mut expr = InputExpression::new(name);
                    {
                        let mut writer = InputExpressionWriter::new(&mut expr);
                        if e.replace_dollar(&self.var_info.local_info.variables)
                            .contains(ReplaceResult::Replaced)
                        {
                            e.normalize_inplace(&self.var_info.global_info);
                        }

                        match e {
                            Element::SubExpr(_, t) => {
                                for x in t {
                                    writer.add_term_input(x);
                                }
                            }
                            x => {
                                writer.add_term_input(x);
                            }
                        }

                        if self
                            .var_info
                            .global_info
                            .expressions
                            .keys()
                            .any(|x| *x == name)
                        {
                            panic!("Cannot define the same expression multiple times");
                        }
                    }

                    self.var_info
                        .global_info
                        .expressions
                        .insert(name, expr.clone());
                }
                Statement::NewFunction(name, args, mut e) => {
                    self.var_info
                        .global_info
                        .user_functions
                        .insert(name, (args, e));
                }
                Statement::Assign(dollar, mut e) => {
                    if e.replace_dollar(&self.var_info.local_info.variables)
                        .contains(ReplaceResult::Replaced)
                    {
                        e.normalize_inplace(&self.var_info.global_info);
                    }
                    self.var_info.local_info.add_dollar(dollar, e);
                }
                Statement::Extract(d, xs) => {
                    if let Element::Dollar(..) = d {
                        let mut dp = self
                            .var_info
                            .local_info
                            .get_dollar_mut(&d)
                            .expect("Dollar variable is uninitialized");
                        *dp = mem::replace(dp, Element::default())
                            .extract(&xs, &self.var_info.global_info);
                    }
                }
                // this will create a subrecursion
                Statement::Inside(ds, mut old_statements) => {
                    // normalize the statements
                    let mut sts = Vec::with_capacity(old_statements.len());
                    Module::statements_to_control_flow_stat(
                        &mut old_statements,
                        &mut self.var_info,
                        &self.procedures,
                        &mut sts,
                    );

                    for x in sts.iter_mut() {
                        x.normalize(&self.var_info.global_info);
                    }

                    for d in ds {
                        if let Element::Dollar(..) = d {
                            let mut dollar = mem::replace(
                                self.var_info
                                    .local_info
                                    .get_dollar_mut(&d)
                                    .expect("Dollar variable is uninitialized"),
                                Element::default(),
                            );

                            let mut tsr = TermStreamWrapper::Owned(vec![]);

                            match dollar {
                                Element::SubExpr(_, se) => {
                                    for x in se {
                                        do_module_rec(
                                            x,
                                            &sts,
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
                                    &sts,
                                    &mut self.var_info.local_info,
                                    &self.var_info.global_info,
                                    0,
                                    &mut vec![false],
                                    &mut tsr,
                                ),
                            }

                            if let TermStreamWrapper::Owned(mut nfa) = tsr {
                                self.var_info.local_info.add_dollar(
                                    d.clone(),
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
                Statement::Attrib(f, attribs) => match f {
                    Element::Var(name, _) | Element::Dollar(name, _) => {
                        self.var_info.global_info.func_attribs.insert(name, attribs);
                    }
                    _ => {
                        panic!("Can only assign attributes to functions or dollar variables");
                    }
                },
                Statement::ForInRange(ref d, ref mut l, ref mut u, ref mut s) => {
                    if let Element::Dollar(dd, ref inds) = *d {
                        l.normalize_inplace(&self.var_info.global_info);
                        u.normalize_inplace(&self.var_info.global_info);

                        // TODO: make sure that the loop counter dollar variable can be printed
                        // this is tricky, since we cannot simply add it to the local variable list,
                        // since the loops are unrolled
                        let mut replace_map = HashMap::new();
                        if let Element::Num(_, Number::SmallInt(li)) = *l {
                            if let Element::Num(_, Number::SmallInt(ui)) = *u {
                                // unroll the loop
                                for ll in (li..ui).rev() {
                                    let lle = Element::Num(false, Number::SmallInt(ll));
                                    let mut mm = HashMap::new();
                                    mm.insert(inds.clone(), lle);
                                    replace_map.insert(dd, mm);
                                    for ss in s.iter().rev() {
                                        let mut news = ss.clone();
                                        if news
                                            .replace_dollar(&replace_map)
                                            .contains(ReplaceResult::Replaced)
                                        {
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
                    if let Element::Dollar(dd, ref inds) = *d {
                        let mut replace_map = HashMap::new();

                        // unroll the loop
                        for ll in l.iter().rev() {
                            let mut mm = HashMap::new();
                            mm.insert(inds.clone(), ll.clone());
                            replace_map.insert(dd, mm);
                            for ss in s.iter().rev() {
                                let mut news = ss.clone();
                                if news
                                    .replace_dollar(&replace_map)
                                    .contains(ReplaceResult::Replaced)
                                {
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
                    let mut out = String::new();

                    let add_newline = vars.iter().all(|e| {
                        if let PrintObject::Literal(..) = e {
                            false
                        } else {
                            true
                        }
                    });
                    for v in vars {
                        if let PrintObject::Special(id) = v {
                            if let Some(mut i) = self.var_info.global_info.expressions.remove(id) {
                                println!("{} =", self.var_info.global_info.get_name(*id));
                                {
                                    let mut it = InputExpressionIterator::new(&mut i);

                                    while let Some(t) = it.next() {
                                        println!(
                                            "\t+{}",
                                            ElementPrinter {
                                                element: t.as_ref(),
                                                var_info: &self.var_info.global_info,
                                                print_mode: *mode
                                            }
                                        );
                                    }
                                }

                                self.var_info.global_info.expressions.insert(*id, i);
                                continue;
                            }
                        }

                        v.print(
                            &mut out,
                            &Element::default(),
                            &mut self.var_info.local_info,
                            &self.var_info.global_info,
                            mode,
                        );
                        if add_newline {
                            out.push('\n');
                        }
                    }
                    if add_newline {
                        print!("{}", out);
                    } else {
                        println!("{}", out);
                    }

                    if vars.len() == 0 {
                        // print all active expressions
                        for x in &mut self.var_info.global_info.expressions.values() {
                            println!("{} =", self.var_info.global_info.get_name(x.name));
                            let mut it = InputExpressionIterator::new(x);

                            while let Some(t) = it.next() {
                                println!(
                                    "\t+{}",
                                    ElementPrinter {
                                        element: t.as_ref(),
                                        var_info: &self.var_info.global_info,
                                        print_mode: *mode
                                    }
                                );
                            }
                        }
                    }
                }
                Statement::IfElse(ref mut cond, ref trueblock, ref falseblock) => {
                    cond.replace_dollar(&self.var_info.local_info.variables); // apply the dollar variables
                    cond.normalize_inplace(&self.var_info.global_info);

                    match cond {
                        IfCondition::Match(_) => {
                            panic!("Matching in if statement is not supported in the global scope")
                        }
                        IfCondition::Defined(e) => {
                            if self.var_info.local_info.get_dollar(e).is_some() {
                                for ss in trueblock.iter().rev() {
                                    statements.push_front(ss.clone());
                                }
                            } else {
                                for ss in falseblock.iter().rev() {
                                    statements.push_front(ss.clone());
                                }
                            }
                        }
                        IfCondition::Comparison(e1, e2, c) => {
                            if c.cmp_rel(
                                e1.partial_cmp(e2, &self.var_info.global_info, false)
                                    .unwrap(),
                            ) {
                                for ss in trueblock.iter().rev() {
                                    statements.push_front(ss.clone());
                                }
                            } else {
                                for ss in falseblock.iter().rev() {
                                    statements.push_front(ss.clone());
                                }
                            }
                        }
                    }
                }
                Statement::Collect(ref id) => sort_statements.push(Statement::Collect(id.clone())),
                Statement::MatchAssign(..) => {
                    panic!("Match assignment cannot be performed in the global scope.")
                }
                Statement::Multiply(..) => {
                    panic!("Multiply statement cannot be performed in the global scope.")
                }
                Statement::ReplaceBy(..) => {
                    panic!("ReplaceBy statement cannot be performed in the global scope.")
                }
                Statement::SplitArg(..) => {
                    panic!("Splitarg statement cannot be performed in the global scope.")
                }
                Statement::Symmetrize(..) => {
                    panic!("Symmetrize statement cannot be performed in the global scope.")
                }
                Statement::IdentityStatement(..) => {
                    panic!("Identity statement cannot be performed in the global scope.")
                }
                Statement::Discard => {
                    panic!("Discard statement cannot be performed in the global scope.")
                }
                Statement::Expand => {
                    panic!("Expand statement cannot be performed in the global scope.")
                }
                Statement::Argument(..) => {
                    panic!("Argument statement cannot be performed in the global scope.")
                }
                _ => unimplemented!(),
            }
        }
    }
}
