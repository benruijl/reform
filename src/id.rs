use structure::{Element, Func, IdentityStatement, IdentityStatementMode, StatementResult, VarName};
use std;
use std::fmt;
use std::mem;
use itertools;
use itertools::Itertools;
use tools::{add_terms, is_number_in_range, Heap, SliceRef};
use std::collections::HashMap;

pub const MAXMATCH: usize = 1_000_000; // maximum number of matches

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum MatchOpt<'a> {
    Single(&'a Element),
    Multiple(&'a [Element]),
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum MatchOptOwned {
    Single(Element, bool), // bool is the changed flag
    Multiple(Vec<Element>),
}

impl<'a> MatchOpt<'a> {
    fn to_owned(&self) -> MatchOptOwned {
        match *self {
            MatchOpt::Single(x) => MatchOptOwned::Single(x.clone(), true),
            MatchOpt::Multiple(x) => {
                MatchOptOwned::Multiple(x.iter().map(|y| (*y).clone()).collect())
            }
        }
    }
}

impl MatchOptOwned {
    fn into_single(self) -> (Element, bool) {
        match self {
            MatchOptOwned::Single(x, c) => (x, c),
            _ => panic!("Trying to get single element from a multiple"),
        }
    }
}

impl<'a> fmt::Display for MatchOpt<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            MatchOpt::Single(x) => write!(f, "{}", x),
            MatchOpt::Multiple(x) => {
                if let Some(u) = x.first() {
                    write!(f, "{}", u)?
                }
                for u in x.iter().skip(1) {
                    write!(f, ",{}", u)?;
                }
                write!(f, "")
            }
        }
    }
}

// map of variables names to a function argument slice
pub type MatchObject<'a> = Vec<(&'a VarName, MatchOpt<'a>)>;

// push something to the match object, keeping track of the old length
fn push_match<'a>(m: &mut MatchObject<'a>, k: &'a VarName, v: &'a Element) -> Option<usize> {
    for &(rk, ref rv) in m.iter() {
        if *rk == *k {
            match *rv {
                MatchOpt::Single(ref vv) if *v == **vv => return Some(m.len()),
                _ => return None,
            }
        }
    }

    m.push((k, MatchOpt::Single(v)));
    Some(m.len() - 1)
}

// push something to the match object, keeping track of the old length
fn push_match_slice<'a>(
    m: &mut MatchObject<'a>,
    k: &'a VarName,
    v: &'a [Element],
) -> Option<usize> {
    for &(rk, ref rv) in m.iter() {
        if *rk == *k {
            match *rv {
                MatchOpt::Multiple(vv) if *v == *vv => return Some(m.len()),
                _ => return None,
            }
        }
    }

    m.push((k, MatchOpt::Multiple(v)));
    Some(m.len() - 1)
}

fn find_match<'a>(m: &'a MatchObject<'a>, k: &'a VarName) -> Option<&'a MatchOpt<'a>> {
    for &(ref rk, ref rv) in m {
        if **rk == *k {
            return Some(rv);
        }
    }
    None
}

// apply a mapping of wildcards to a function argument
impl Element {
    fn apply_map<'a>(&self, m: &MatchObject<'a>) -> MatchOptOwned {
        match *self {
            Element::VariableArgument(ref name) | Element::Wildcard(ref name, ..) => {
                find_match(m, name).unwrap().to_owned()
            }
            Element::Pow(_, ref be) => {
                let (ref b, ref e) = **be;
                let mut changed = false;
                let (bb, c) = b.apply_map(m).into_single();
                changed |= c;
                let (pp, c) = e.apply_map(m).into_single();
                changed |= c;
                MatchOptOwned::Single(Element::Pow(changed, Box::new((bb, pp))), changed)
            }
            Element::Fn(_, ref f) => {
                let (ff, c) = f.apply_map(m);
                MatchOptOwned::Single(Element::Fn(c, ff), c)
            }
            Element::Term(_, ref f) => {
                let mut changed = false;
                let mut args = vec![];
                for x in f.iter() {
                    let (xx, c) = x.apply_map(m).into_single();
                    changed |= c;
                    args.push(xx);
                }
                MatchOptOwned::Single(Element::Term(changed, args), changed)
            }
            Element::SubExpr(_, ref f) => {
                let mut changed = false;
                let mut args = vec![];
                for x in f.iter() {
                    let (xx, c) = x.apply_map(m).into_single();
                    changed |= c;
                    args.push(xx);
                }
                MatchOptOwned::Single(Element::SubExpr(changed, args), changed)
            }
            _ => MatchOptOwned::Single(self.clone(), false), // no match, so no change
        }
    }
}

impl Func {
    fn apply_map<'a>(&self, m: &MatchObject<'a>) -> (Func, bool) {
        let mut changed = false;
        let mut args = vec![];
        for a in &self.args {
            match a.apply_map(m) {
                MatchOptOwned::Single(x, c) => {
                    changed |= c;
                    args.push(x)
                }
                MatchOptOwned::Multiple(x) => {
                    changed = true;
                    args.extend(x)
                }
            }
        }

        (
            Func {
                name: self.name.clone(),
                args: args,
            },
            changed,
        )
    }
}

#[derive(Debug)]
pub enum ElementIterSingle<'a> {
    FnIter(FuncIterator<'a>),            // match function
    Once,                                // matching without wildcard, ie number vs number
    OnceMatch(&'a VarName, &'a Element), // simple match of variable
    PermIter(
        &'a [Element],
        Heap<&'a Element>,
        SequenceIter<'a>,
        &'a HashMap<VarName, Element>,
    ), // term and arg combinations,
    SeqIt(Vec<&'a Element>, SequenceIter<'a>), // target and iterator
    None,
}

#[derive(Debug)]
pub enum ElementIter<'a> {
    SliceIter(&'a VarName, usize, &'a [Element]), // slice from 0 to Element end
    SingleArg(&'a [Element], ElementIterSingle<'a>), // iters consuming a single argument
    None,                                         // no match
}

impl<'a> ElementIterSingle<'a> {
    fn next(&mut self, m: &mut MatchObject<'a>) -> Option<usize> {
        match *self {
            ElementIterSingle::None => None,
            ElementIterSingle::Once => {
                let mut to_swap = ElementIterSingle::None;
                mem::swap(self, &mut to_swap); //f switch self to none
                match to_swap {
                    ElementIterSingle::Once => Some(m.len()),
                    _ => panic!(), // never reached
                }
            }
            ElementIterSingle::OnceMatch(_, _) => {
                let mut to_swap = ElementIterSingle::None;
                mem::swap(self, &mut to_swap);
                match to_swap {
                    ElementIterSingle::OnceMatch(name, target) => push_match(m, name, target),
                    _ => panic!(), // never reached
                }
            }
            ElementIterSingle::FnIter(ref mut f) => f.next(m),
            ElementIterSingle::PermIter(pat, ref mut heap, ref mut termit, var_info) => {
                if pat.len() != heap.data.len() {
                    return None;
                }

                loop {
                    if let Some(x) = termit.next(&heap.data, m) {
                        return Some(x);
                    }
                    if let Some(x) = heap.next_permutation() {
                        *termit = SequenceIter::new(&SliceRef::BorrowedSlice(pat), x[0], var_info);
                    } else {
                        break;
                    }
                }

                None
            }
            ElementIterSingle::SeqIt(ref target, ref mut seqit) => seqit.next(target, m),
        }
    }
}

impl<'a> ElementIter<'a> {
    fn next(&mut self, m: &mut MatchObject<'a>) -> Option<(&'a [Element], usize)> {
        match *self {
            ElementIter::None => None,
            ElementIter::SliceIter(name, ref mut index, target) => {
                // if the slice is already found, we can immediately compare
                if *index > target.len() {
                    return None;
                }

                if let Some(&MatchOpt::Multiple(v)) = find_match(m, name) {
                    *index = target.len() + 1; // make sure next call gives None
                    if v.len() > target.len() {
                        return None;
                    }
                    //let rr = target[..v.len()].iter().map(|x| x).collect::<Vec<_>>(); // FIXME: is this wrong?
                    if *v == target[..v.len()] {
                        return Some((&target[v.len()..], m.len()));
                    } else {
                        return None;
                    }
                }

                'findcandidate: while *index <= target.len() {
                    let (f, l) = target.split_at(*index);
                    *index += 1;

                    //let rr = f.iter().map(|x| x).collect();
                    match push_match_slice(m, name, f) {
                        Some(x) => return Some((l, x)),
                        _ => continue 'findcandidate,
                    }
                }
                None
            }
            ElementIter::SingleArg(rest, ref mut f) => f.next(m).map(move |x| (rest, x)),
        }
    }
}

impl Element {
    // create an iterator over a pattern
    fn to_iter<'a>(
        &'a self,
        target: &'a [Element],
        var_info: &'a HashMap<VarName, Element>,
    ) -> ElementIter<'a> {
        // go through all possible options (slice sizes) for the variable argument
        if let Element::VariableArgument(ref name) = *self {
            return ElementIter::SliceIter(name, 0, target);
        }

        // is the slice non-zero length?
        match target.first() {
            Some(x) => ElementIter::SingleArg(&target[1..], self.to_iter_single(x, var_info)),
            None => ElementIter::None,
        }
    }

    // create an iterator over a pattern
    fn to_iter_single<'a>(
        &'a self,
        target: &'a Element,
        var_info: &'a HashMap<VarName, Element>,
    ) -> ElementIterSingle<'a> {
        match (target, self) {
            (&Element::Pow(_, ref be1), &Element::Pow(_, ref be2)) => {
                let (ref b1, ref e1) = **be1;
                let (ref b2, ref e2) = **be2;
                ElementIterSingle::SeqIt(
                    vec![b1, e1],
                    SequenceIter::new(&SliceRef::OwnedSlice(vec![b2, e2]), b1, var_info),
                )
            }
            (i1, &Element::Dollar(ref i2, _)) => {
                if var_info.get(i2) == Some(i1) {
                    ElementIterSingle::Once
                } else {
                    ElementIterSingle::None
                }
            }
            (&Element::Var(ref i1), &Element::Var(ref i2)) if i1 == i2 => ElementIterSingle::Once,
            (
                &Element::Num(_, ref pos1, ref num1, ref den1),
                &Element::Num(_, ref pos2, ref num2, ref den2),
            ) if pos1 == pos2 && num1 == num2 && den1 == den2 =>
            {
                ElementIterSingle::Once
            }
            (&Element::Num(_, ref pos, ref num, ref den), &Element::Wildcard(ref i2, ref rest)) => {
                if rest.is_empty() {
                    return ElementIterSingle::OnceMatch(i2, target);
                }

                for restriction in rest {
                    match restriction {
                        &Element::NumberRange(ref pos1, ref num1, ref den1, ref rel) => {
                            // see if the number is in the range
                            if is_number_in_range(*pos, *num, *den, *pos1, *num1, *den1, rel) {
                                return ElementIterSingle::OnceMatch(i2, target);
                            }
                        }
                        _ if restriction == target => {
                            return ElementIterSingle::OnceMatch(i2, target)
                        }
                        _ => {}
                    }
                }

                ElementIterSingle::None
            }
            (_, &Element::Wildcard(ref i2, ref rest)) => {
                if rest.is_empty() || rest.contains(target) {
                    ElementIterSingle::OnceMatch(i2, target)
                } else {
                    ElementIterSingle::None
                }
            }
            (&Element::Fn(_, ref f1), &Element::Fn(_, ref f2)) => {
                ElementIterSingle::FnIter(f2.to_iter(f1, var_info))
            }
            (&Element::Term(_, ref f1), &Element::Term(_, ref f2))
            | (&Element::SubExpr(_, ref f1), &Element::SubExpr(_, ref f2)) => {
                ElementIterSingle::PermIter(
                    f2,
                    Heap::new(f1.iter().map(|x| x).collect::<Vec<_>>()),
                    SequenceIter::dummy(f2, var_info),
                    var_info,
                )
            }
            _ => ElementIterSingle::None,
        }
    }
}

impl Func {
    fn to_iter<'a>(
        &'a self,
        target: &'a Func,
        var_info: &'a HashMap<VarName, Element>,
    ) -> FuncIterator<'a> {
        if self.name != target.name {
            return FuncIterator {
                pattern: self,
                iterators: vec![],
                matches: vec![],
                var_info: var_info,
            };
        }

        // shortcut if the number of arguments is wrong
        let varargcount = self.args
            .iter()
            .filter(|x| match **x {
                Element::VariableArgument { .. } => true,
                _ => false,
            })
            .count();
        if self.args.len() - varargcount > target.args.len() {
            return FuncIterator {
                pattern: self,
                iterators: vec![],
                matches: vec![],
                var_info: var_info,
            };
        };
        if varargcount == 0 && self.args.len() != target.args.len() {
            return FuncIterator {
                pattern: self,
                iterators: vec![],
                matches: vec![],
                var_info: var_info,
            };
        };

        let mut iterator = (0..self.args.len())
            .map(|_| ElementIter::None)
            .collect::<Vec<_>>(); // create placeholder iterators
        iterator[0] = self.args[0].to_iter(&target.args, var_info); // initialize the first iterator

        let matches = vec![(&target.args[..], MAXMATCH); self.args.len()]; // placeholder matches

        FuncIterator {
            pattern: self,
            iterators: iterator,
            matches: matches,
            var_info: var_info,
        }
    }
}

// iterator over a pattern of a function
#[derive(Debug)]
pub struct FuncIterator<'a> {
    pattern: &'a Func,
    iterators: Vec<ElementIter<'a>>,
    matches: Vec<(&'a [Element], usize)>, // keep track of stack depth
    var_info: &'a HashMap<VarName, Element>,
}

impl<'a> FuncIterator<'a> {
    fn next(&mut self, m: &mut MatchObject<'a>) -> Option<usize> {
        if self.iterators.len() == 0 {
            return None;
        }

        // find the first iterator from the back that is not None
        let mut i = self.iterators.len() - 1;
        'next: loop {
            //println!("matching {:?} {:?}", self.pattern, m);
            // FIXME: not correct. the iters should pop the stack on a next match
            m.truncate(self.matches[i].1); // pop the matches from the stack

            if let Some(x) = self.iterators[i].next(m) {
                self.matches[i] = x;

                // now update all elements after
                let mut j = i + 1;
                while j < self.iterators.len() {
                    // create a new iterator at j based on the previous match dictionary and slice
                    self.iterators[j] =
                        self.pattern.args[j].to_iter(self.matches[j - 1].0, self.var_info);

                    match self.iterators[j].next(m) {
                        Some(y) => {
                            self.matches[j] = y;
                        }
                        None => {
                            i = j - 1;
                            continue 'next;
                        } // try the next match at j-1
                    }

                    j += 1;
                }

                let leftover = self.matches.last().unwrap().0;
                // FIXME: we dont // we need the index from the first: before the iterator started
                let index = self.matches.last().unwrap().1;
                if leftover.len() == 0 {
                    //println!("yielding new match {:?} {}", m, index);
                    return Some(index); // should be the same as the length of m
                } else {
                    // not all arguments consumed, try the next one at the back
                    i = self.iterators.len() - 1;
                    continue 'next;
                }
            }

            //println!("truncating {:?} to {} {} {:?}", m, self.matches[i].1, i, self.matches.iter().map(|x| x.1).collect::<Vec<_>>());

            if i == 0 {
                m.truncate(self.matches[0].1); // delete the first match
                break; // we are done
            }
            i -= 1;
        }

        None
    }
}

// iterator over a pattern that could occur in any order
#[derive(Debug)]
pub struct SequenceIter<'a> {
    pattern: SliceRef<'a, Element>, // input term
    iterators: Vec<ElementIterSingle<'a>>,
    matches: Vec<usize>, // keep track of stack depth
    var_info: &'a HashMap<VarName, Element>,
}

impl<'a> SequenceIter<'a> {
    fn dummy(pattern: &'a [Element], var_info: &'a HashMap<VarName, Element>) -> SequenceIter<'a> {
        SequenceIter {
            pattern: SliceRef::BorrowedSlice(pattern),
            iterators: vec![],
            matches: vec![],
            var_info,
        }
    }

    fn new(
        pattern: &SliceRef<'a, Element>,
        first: &'a Element,
        var_info: &'a HashMap<VarName, Element>,
    ) -> SequenceIter<'a> {
        let mut its = (0..pattern.len())
            .map(|_| ElementIterSingle::None)
            .collect::<Vec<_>>();
        its[0] = pattern.index(0).to_iter_single(first, var_info);
        SequenceIter {
            pattern: pattern.clone(),
            iterators: its,
            matches: vec![MAXMATCH; pattern.len()],
            var_info,
        }
    }

    fn next(&mut self, target: &[&'a Element], m: &mut MatchObject<'a>) -> Option<usize> {
        if self.iterators.is_empty() {
            return None;
        }

        // find the first iterator from the back that is not None
        let mut i = self.iterators.len() - 1;
        'next: loop {
            m.truncate(self.matches[i]); // pop the matches from the stack

            if let Some(x) = self.iterators[i].next(m) {
                self.matches[i] = x;

                // now update all elements after
                let mut j = i + 1;
                while j < self.iterators.len() {
                    // create a new iterator at j based on the previous match dictionary and slice
                    self.iterators[j] = self.pattern
                        .index(j)
                        .to_iter_single(target[j], self.var_info);

                    match self.iterators[j].next(m) {
                        Some(y) => {
                            self.matches[j] = y;
                        }
                        None => {
                            i = j - 1;
                            continue 'next;
                        } // try the next match at j-1
                    }

                    j += 1;
                }
                return Some(*self.matches.last().unwrap());
            }

            if i == 0 {
                m.truncate(self.matches[0]); // delete the first match
                break; // we are done
            }
            i -= 1;
        }

        None
    }
}

// match a pattern to a subset of the terms
// FIXME: nasty structure
#[derive(Debug)]
pub struct MatchTermIterator<'a> {
    pattern: &'a [Element],
    target: &'a [Element],
    subtarget: Option<Vec<&'a Element>>,
    remaining: Option<Vec<&'a Element>>,
    m: MatchObject<'a>,
    combinator: itertools::Combinations<std::slice::Iter<'a, Element>>,
    permutator: ElementIterSingle<'a>,
    var_info: &'a HashMap<VarName, Element>,
}

impl<'a> MatchTermIterator<'a> {
    fn new(
        pattern: &'a [Element],
        target: &'a [Element],
        var_info: &'a HashMap<VarName, Element>,
    ) -> MatchTermIterator<'a> {
        let combinator = target.iter().combinations(pattern.len());

        MatchTermIterator {
            pattern: pattern,
            target: target,
            subtarget: None,
            remaining: None,
            m: vec![],
            combinator: combinator,
            permutator: ElementIterSingle::None,
            var_info,
        }
    }

    fn next(&mut self) -> Option<(Vec<&'a Element>, MatchObject<'a>)> {
        if self.pattern.len() > self.target.len() {
            return None;
        }

        loop {
            if self.subtarget.is_some() {
                if self.permutator.next(&mut self.m).is_some() {
                    if let Some(ref x) = self.remaining {
                        return Some((x.clone(), self.m.clone()));
                    }
                }
            }

            if let Some(x) = self.combinator.next() {
                self.permutator = ElementIterSingle::PermIter(
                    self.pattern,
                    Heap::new(x.iter().map(|x| *x).collect::<Vec<_>>()),
                    SequenceIter::dummy(self.pattern, self.var_info),
                    self.var_info,
                );

                SequenceIter::new(&SliceRef::BorrowedSlice(self.pattern), x[0], self.var_info);

                // construct the factors that are not affected
                let mut rem = vec![];
                for y in self.target.iter() {
                    if !x.contains(&y) {
                        rem.push(y); // FIXME: does this work? we need to check pointers!
                    }
                }
                self.remaining = Some(rem);
                self.subtarget = Some(x);
            } else {
                return None;
            }
        }
    }
}

#[derive(Debug)]
pub enum MatchKind<'a> {
    Single(MatchObject<'a>, ElementIterSingle<'a>),
    SinglePat(
        &'a Element,
        MatchObject<'a>,
        ElementIterSingle<'a>,
        &'a [Element],
        usize,
        &'a HashMap<VarName, Element>,
    ),
    Many(MatchTermIterator<'a>),
    None,
}

impl<'a> MatchKind<'a> {
    pub fn from_element(
        pattern: &'a Element,
        target: &'a Element,
        var_info: &'a HashMap<VarName, Element>,
    ) -> MatchKind<'a> {
        match (pattern, target) {
            (&Element::Term(_, ref x), &Element::Term(_, ref y)) => {
                MatchKind::Many(MatchTermIterator::new(x, y, var_info))
            }
            (a, &Element::Term(_, ref y)) => {
                MatchKind::SinglePat(a, vec![], ElementIterSingle::None, y, 0, var_info)
            }
            (a, b) => MatchKind::Single(vec![], a.to_iter_single(b, var_info)),
        }
    }

    pub fn next(&mut self) -> Option<(Vec<&'a Element>, MatchObject<'a>)> {
        match *self {
            MatchKind::Single(ref mut m, ref mut x) => x.next(m).map(|_| (vec![], m.clone())),
            MatchKind::Many(ref mut x) => x.next(),
            MatchKind::SinglePat(pat, ref mut m, ref mut it, target, ref mut index, var_info) => {
                loop {
                    if it.next(m).is_some() {
                        let rem = target
                            .iter()
                            .enumerate()
                            .filter_map(|(i, x)| if i + 1 == *index { None } else { Some(x) })
                            .collect();
                        return Some((rem, m.clone()));
                    }

                    if *index == target.len() {
                        return None;
                    }
                    *it = pat.to_iter_single(&target[*index], var_info);
                    *index += 1;
                }
            }
            MatchKind::None => None,
        }
    }
}

#[derive(Debug)]
pub struct MatchIterator<'a> {
    mode: IdentityStatementMode,
    rhs: &'a Element,
    m: MatchObject<'a>,
    remaining: Vec<Element>,
    it: MatchKind<'a>,
    rhsp: usize, // current rhs index,
    hasmatch: bool,
    input: &'a Element,
    var_info: &'a HashMap<VarName, Element>,
}

// iterate over the output terms of a match
impl<'a> MatchIterator<'a> {
    pub fn next(&mut self) -> StatementResult<Element> {
        if self.rhsp == 0 {
            match self.it.next() {
                Some((rem, m)) => {
                    if let IdentityStatementMode::Once = self.mode {
                        self.it = MatchKind::None;
                    }

                    self.m = m;
                    self.remaining = rem.iter().map(|&x| x.clone()).collect();
                    printmatch(&self.m);
                }
                None => {
                    if self.hasmatch {
                        return StatementResult::Done;
                    } else {
                        return StatementResult::NoChange;
                    }
                }
            }
        }

        self.hasmatch = true;

        StatementResult::Executed(match self.rhs {
            &Element::SubExpr(_, ref x) => {
                let r = x[self.rhsp].apply_map(&self.m);
                self.rhsp += 1;
                if self.rhsp == x.len() {
                    self.rhsp = 0;
                }

                let (mut res, _changed) = r.into_single();
                if !self.remaining.is_empty() {
                    add_terms(&mut res, &self.remaining);
                }
                res.replace_vars(self.var_info, true); // subsitute dollars in rhs
                res.normalize_inplace();
                res
            }
            x => {
                let r = x.apply_map(&self.m);
                let (mut res, _changed) = r.into_single();
                if !self.remaining.is_empty() {
                    add_terms(&mut res, &self.remaining);
                }
                res.replace_vars(self.var_info, true); // subsitute dollars in rhs
                res.normalize_inplace();
                res
            }
        })
    }
}

impl IdentityStatement {
    pub fn to_iter<'a>(
        &'a self,
        input: &'a Element,
        var_info: &'a HashMap<VarName, Element>,
    ) -> MatchIterator<'a> {
        MatchIterator {
            input: input,
            hasmatch: false,
            m: vec![],
            remaining: vec![],
            mode: self.mode.clone(),
            rhs: &self.rhs,
            rhsp: 0,
            it: MatchKind::from_element(&self.lhs, input, var_info),
            var_info,
        }
    }
}

fn printmatch<'a>(m: &MatchObject<'a>) {
    debug!("MATCH: [ ");

    for &(k, ref v) in m.iter() {
        debug!("{}={};", k, v);
    }
    debug!("]");
}
