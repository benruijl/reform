use structure::{Element,Func,IdentityStatementMode,IdentityStatement,StatementResult};
use std;
use std::fmt;
use std::mem;
use itertools;
use itertools::Itertools;
use tools::{Heap,add_terms,is_number_in_range};

pub const MAXMATCH: usize = 1000000; // maximum number of matches

#[derive(Debug,Clone,Eq,PartialEq)]
enum MatchOpt<'a> {
    Single(&'a Element),
    Multiple(&'a [Element])
}

impl<'a> MatchOpt<'a> {
    fn to_vec(&self) -> Vec<Element> {
        match *self {
            MatchOpt::Single(ref x) => vec![(*x).clone()],
            MatchOpt::Multiple(ref x) => x.iter().map(|y| (*y).clone()).collect()
        }
    }
}

impl<'a> fmt::Display for MatchOpt<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            MatchOpt::Single(x) => write!(f, "{}", x),
            MatchOpt::Multiple(ref x) => {
                match x.first() {
                    Some(u) => write!(f,"{}", u)?,
                    None => {}
                }
                for u in x.iter().skip(1) {
                    write!(f,",{}", u)?;
                }
                write!(f,"")
            }
        }
    }
}

// map of variables names to a function argument slice
pub type MatchObject<'a> = Vec<(&'a String, MatchOpt<'a>)>;

// push something to the match object, keeping track of the old length
fn push_match<'a>(m : &mut MatchObject<'a>, k: &'a String, v: &'a Element) -> Option<usize> {
    for &(ref rk, ref rv) in m.iter() {
        if **rk == *k {
            match *rv {
                MatchOpt::Single(ref vv) if *v == **vv => return Some(m.len()),
                _ => return None 
            }
        }
    }

    m.push((k, MatchOpt::Single(v)));
    Some(m.len() - 1)
}

// push something to the match object, keeping track of the old length
fn push_match_slice<'a>(m : &mut MatchObject<'a>, k: &'a String, v: &'a [Element]) -> Option<usize> {
    for &(ref rk, ref rv) in m.iter() {
        if **rk == *k {
            match *rv {
                MatchOpt::Multiple(ref vv) if *v == **vv => return Some(m.len()),
                _ => return None 
            }
        }
    }

    m.push((k, MatchOpt::Multiple(v)));
    Some(m.len() - 1)
}


fn find_match<'a,>(m : &'a MatchObject<'a>, k: &'a String) -> Option<&'a MatchOpt<'a>> {
    for &(ref rk, ref rv) in m.iter() {
        if **rk == *k {
            return Some(rv);
        }
    }
    None
}

// apply a mapping of wildcards to a function argument
impl Element {
    fn apply_map<'a>(&self, m: &MatchObject<'a>) -> Vec<Element> {
        match *self {
            Element::VariableArgument(ref name) => find_match(m, name).unwrap().to_vec(),
            Element::Wildcard(ref name, ..) => find_match(m, name).unwrap().to_vec(),
            Element::Fn(ref f) => vec![Element::Fn(f.apply_map(m)).normalize()],
            Element::Term(ref f) => vec![ Element::Term(f.iter().flat_map(|x| x.apply_map(m)).collect()).normalize()],
            Element::SubExpr(ref f) => vec![Element::SubExpr(f.iter().flat_map(|x| x.apply_map(m)).collect()).normalize()],
            _ => vec![self.clone()]
        }
    }
}

impl Func {
    fn apply_map<'a>(&self, m: &MatchObject<'a>) -> Func {
        let r = self.args.iter().flat_map(|x| x.apply_map(m)).collect();
        Func { name: self.name.clone(), args : r }.normalize()
    }
}

#[derive(Debug)]
enum ElementIterSingle<'a> {
    FnIter(FuncIterator<'a>), // match function
    Once, // matching without wildcard, ie number vs number
    OnceMatch(&'a String, &'a Element), // simple match of variable
    PermIter(&'a [Element], Heap<&'a Element>, SequenceIter<'a>), // term and arg combinations
    None
}


#[derive(Debug)]
enum ElementIter<'a> {
    SliceIter(&'a String, usize, &'a [Element]), // slice from 0 to Element end
    SingleArg(&'a [Element], ElementIterSingle<'a>), // iters consuming a single argument
    None, // no match
}

impl<'a>  ElementIterSingle<'a> {
    fn next(& mut self, m: &mut MatchObject<'a>) -> Option<usize> {
        match *self {
            ElementIterSingle::None => None,
            ElementIterSingle::Once => {
                let mut to_swap = ElementIterSingle::None;
                mem::swap(self, &mut to_swap); //f switch self to none
                match to_swap {
                    ElementIterSingle::Once  => Some(m.len()),
                    _   => panic!(), // never reached
                }
            },
            ElementIterSingle::OnceMatch(_,_) => {
                let mut to_swap = ElementIterSingle::None;
                mem::swap(self, &mut to_swap);
                match to_swap {
                    ElementIterSingle::OnceMatch(name, target)  => {
                        push_match(m, name, &target)
                    },
                    _ => panic!(), // never reached
                }
            },
            ElementIterSingle::FnIter(ref mut f) => f.next(m),
            ElementIterSingle::PermIter(ref pat, ref mut heap, ref mut termit) => {
                loop {
                    if let Some(x) = termit.next(&heap.data, m) {
                        return Some(x);
                    }
                    if let Some(x) = heap.next_permutation() {
                        *termit = SequenceIter::new(pat, x[0]);
                    } else {
                        break;
                    }
                }

                None
            }
        }
    }
}


impl<'a>  ElementIter<'a> {
    fn next(& mut self, m: &mut MatchObject<'a>) -> Option<(&'a [Element], usize)> {
        match *self {
            ElementIter::None => None,
            ElementIter::SliceIter(name, ref mut index, target) => {
                // if the slice is already found, we can immediately compare
                if *index > target.len() {
                    return None;
                }

                if let Some(&MatchOpt::Multiple(ref v)) = find_match(m, name) {
                    *index = target.len() + 1; // make sure next call gives None
                    if v.len() > target.len() {
                        return None;
                    }
                    //let rr = target[..v.len()].iter().map(|x| x).collect::<Vec<_>>(); // FIXME: is this wrong?
                    match **v == target[..v.len()] {
                        true => return Some((&target[v.len()..], m.len())),
                        false => return None,
                    }
                }

                'findcandidate: while *index <= target.len() {
                    let (f,l) = target.split_at(*index);
                    *index += 1;

                    //let rr = f.iter().map(|x| x).collect();
                    match push_match_slice(m, name, f) {
                        Some(x) => return Some((&l, x)),
                        _ => continue 'findcandidate
                    }

                }
                None
            }
            ElementIter::SingleArg(rest, ref mut f) => f.next(m).map(move |x| { (rest, x) })
        }
    }
}


impl Element {
    // create an iterator over a pattern
    fn to_iter<'a>(&'a self, target: &'a [Element]) -> ElementIter<'a> {

        // go through all possible options (slice sizes) for the variable argument
        if let &Element::VariableArgument(ref name) = self {
            return ElementIter::SliceIter(name,0,target);
        }

        // is the slice non-zero length?
        match target.first() {
            Some(x) => ElementIter::SingleArg(&target[1..], self.to_iter_single(x)),
            None => ElementIter::None
        }
    }

    // create an iterator over a pattern
    fn to_iter_single<'a>(&'a self, target: &'a Element) -> ElementIterSingle<'a> {
        match (target, self) {
                (&Element::Var(ref i1), &Element::Var(ref i2)) if i1 == i2 =>
                             ElementIterSingle::Once,
                (&Element::Num(ref pos1, ref num1, ref den1), &Element::Num(ref pos2, ref num2, ref den2)) 
                    if pos1 == pos2 && num1 == num2 && den1 == den2 =>
                            ElementIterSingle::Once,
                (&Element::Num(ref pos, ref num, ref den), &Element::Wildcard(ref i2, ref rest)) => {
                    if rest.len() == 0 {
                        return ElementIterSingle::OnceMatch(i2, &target)
                    }

                    for restriction in rest {
                        match restriction {
                            &Element::NumberRange(ref pos1, ref num1, ref den1, ref rel) => {
                                // see if the number is in the range
                                if is_number_in_range(*pos,*num,*den,*pos1,*num1,*den1,rel) {
                                    return ElementIterSingle::OnceMatch(i2, &target);
                                }
                            }
                            _ if restriction == target => return ElementIterSingle::OnceMatch(i2, &target),
                            _ => {}
                        }
                    }

                    ElementIterSingle::None
                    
                },
                (_, &Element::Wildcard(ref i2, ref rest)) => {
                    if rest.len() == 0 || rest.contains(target) {
                        ElementIterSingle::OnceMatch(i2, &target)
                    } else {
                        ElementIterSingle::None
                    }
                },
                (&Element::Fn(ref f1), &Element::Fn(ref f2)) =>
                            ElementIterSingle::FnIter(f2.to_iter(&f1)),
                (&Element::Term(ref f1), &Element::Term(ref f2)) |
                (&Element::SubExpr(ref f1), &Element::SubExpr(ref f2)) => {
                    ElementIterSingle::PermIter(f2, Heap::new(f1.iter().map(|x| x).collect::<Vec<_>>()),
                        SequenceIter::dummy(f2))
                },
                _ =>  ElementIterSingle::None
        }
    }
}

impl Func {

  fn to_iter<'a>(&'a self, target: &'a Func) -> FuncIterator<'a> {
    if self.name != target.name { return FuncIterator { pattern: self, iterators: vec![], matches : vec![] }; }

    // shortcut if the number of arguments is wrong
    let varargcount = self.args.iter().filter(|x| match *x { &Element::VariableArgument {..} => true, _ => false } ).count();
    if self.args.len() - varargcount > target.args.len() { 
        return FuncIterator { pattern: self, iterators: vec![], matches : vec![] }; 
    };
    if varargcount == 0 && self.args.len() != target.args.len() {
        return FuncIterator { pattern: self, iterators: vec![], matches : vec![] }; 
    };

    let mut iterator = (0..self.args.len()).map(|_| { ElementIter::None }).collect::<Vec<_>>(); // create placeholder iterators
    iterator[0] = self.args[0].to_iter(&target.args); // initialize the first iterator

    let matches = vec![(&target.args[..], MAXMATCH); self.args.len()]; // placeholder matches

    FuncIterator { pattern: self, iterators: iterator, matches : matches }
  }
}

// iterator over a pattern of a function
#[derive(Debug)]
struct FuncIterator<'a> {
    pattern: &'a Func,
    iterators: Vec<ElementIter<'a>>,
    matches: Vec<(&'a [Element], usize)>, // keep track of stack depth
}

impl<'a>FuncIterator<'a> {

    fn next(& mut self,  m: &mut MatchObject<'a>) -> Option<usize> {
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
                    self.iterators[j] = self.pattern.args[j].to_iter(self.matches[j-1].0);

                    match self.iterators[j].next(m) {
                        Some(y) => { self.matches[j] = y; },
                        None => { i = j - 1; continue 'next; } // try the next match at j-1
                    }

                    j += 1;
                }

                let leftover = self.matches.last().unwrap().0;
                let index = self.matches.last().unwrap().1; // FIXME: we dont // we need the index from the first: before the iterator started
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
struct SequenceIter<'a> {
    pattern: &'a [Element], // input term
    iterators: Vec<ElementIterSingle<'a>>,
    matches: Vec<usize>, // keep track of stack depth
}

impl<'a> SequenceIter<'a> {
    fn dummy(pattern: &'a [Element]) -> SequenceIter<'a> {
        SequenceIter { pattern: pattern, iterators: vec![], matches: vec![] }
    }

    fn new(pattern: &'a [Element], first: &'a Element) -> SequenceIter<'a> {
        let mut its =  (0..pattern.len()).map(|_| { ElementIterSingle::None }).collect::<Vec<_>>();
        its[0] = pattern[0].to_iter_single(first);
        SequenceIter { pattern: pattern, iterators: its, matches: vec![MAXMATCH; pattern.len()] }
    }

    fn next(&mut self, target: &[&'a Element], m: &mut MatchObject<'a>) -> Option<usize> {
        if self.iterators.len() == 0 {
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
                    self.iterators[j] = self.pattern[j].to_iter_single(target[j]);

                    match self.iterators[j].next(m) {
                        Some(y) => { self.matches[j] = y; },
                        None => { i = j - 1; continue 'next; } // try the next match at j-1
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
struct MatchTermIterator<'a> {
    pattern: &'a [Element],
    target: &'a [Element],
    subtarget: Option<Vec<&'a Element>>,
    remaining: Option<Vec<&'a Element>>,
    m : MatchObject<'a>,
    combinator: itertools::Combinations<std::slice::Iter<'a, Element>>,
    permutator: ElementIterSingle<'a>
}

impl<'a> MatchTermIterator<'a> {
    fn new(pattern: &'a [Element], target: &'a [Element]) -> MatchTermIterator<'a> {
        let combinator = target.iter().combinations(pattern.len());

        MatchTermIterator { pattern: pattern, target: target, subtarget: None, remaining: None, m: vec![],
        combinator: combinator, permutator: ElementIterSingle::None  }

    }

    fn next(&mut self) -> Option<(Vec<&'a Element>, MatchObject<'a>)> {
        if self.pattern.len() > self.target.len() {
            return None;
        }

        loop {
            if let Some(_) = self.subtarget {
                if let Some(_) = self.permutator.next(&mut self.m) {
                    if let Some(ref x) = self.remaining {
                        return Some((x.clone(), self.m.clone()));
                    }
                }
            }
            
            if let Some(x) = self.combinator.next() {
                self.permutator = ElementIterSingle::PermIter(self.pattern, Heap::new(x.iter().map(|x| *x).collect::<Vec<_>>()),
                        SequenceIter::dummy(self.pattern));

                SequenceIter::new(self.pattern, x[0]);

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
    SinglePat(&'a Element, MatchObject<'a>, ElementIterSingle<'a>, &'a [Element], usize),
    Many(MatchTermIterator<'a>),
    None
}

impl<'a> MatchKind<'a> {
    pub fn from_element(pattern: &'a Element, target: &'a Element) -> MatchKind<'a> {
        match (pattern, target) {
            (&Element::Term(ref x), &Element::Term(ref y)) => MatchKind::Many(MatchTermIterator::new(x, y)),
            (ref a, &Element::Term(ref y)) => MatchKind::SinglePat(a, vec![], ElementIterSingle::None, y, 0),
            (a,b) => MatchKind::Single(vec![], a.to_iter_single(b)) 
        }
    }

    pub fn next(&mut self) -> Option<(Vec<&'a Element>, MatchObject<'a>)> {
        match *self {
            MatchKind::Single(ref mut m, ref mut x) => x.next(m).map(|_| { (vec![], m.clone()) }),
            MatchKind::Many(ref mut x) => x.next(),
            MatchKind::SinglePat(ref pat, ref mut m, ref mut it, ref target, ref mut index) => {
                loop {
                    if let Some(_) = it.next(m) {
                        let rem = target.iter().enumerate().filter_map(|(i,x)| 
                                if i + 1 == *index { None } else { Some(x) } ).collect();
                        return Some((rem, m.clone()));
                    }

                    if *index == target.len() { return None; }
                    *it = pat.to_iter_single(&target[*index]);
                    *index += 1;
                }                
            },
            MatchKind::None => None,
        }
    }
}

#[derive(Debug)]
pub struct MatchIterator<'a> {
    mode: IdentityStatementMode,
    rhs: &'a Element,
    m: MatchObject<'a>,
    remaining: Vec<&'a Element>,
    it: MatchKind<'a>,
    rhsp: usize, // current rhs index,
    hasmatch: bool,
    input: &'a Element
}

// iterate over the output terms of a match
impl<'a> MatchIterator<'a> {
    pub fn next(&mut self) -> StatementResult<Element> {
        if self.rhsp == 0 {
            match self.it.next() {
                Some((ref rem, ref m)) => {
                    if let IdentityStatementMode::Once = self.mode {
                        self.it = MatchKind::None;
                    }

                    self.m = m.clone(); //  TODO: prevent clone
                    self.remaining = rem.clone();
                    printmatch(&m);
                },
                None => { if self.hasmatch { return StatementResult::Done; } else { 
                    self.hasmatch = true;
                    return StatementResult::NotExecuted(self.input.clone()); } }
            }
        }

        self.hasmatch = true;

        StatementResult::Executed(
            match self.rhs {
                &Element::SubExpr(ref x) => {
                    let r = x[self.rhsp].apply_map(&self.m);
                    self.rhsp += 1;
                    if self.rhsp == x.len() {
                        self.rhsp = 0;
                    }
                    assert!(r.len() == 1); // result is a subexpr
                    let mut res = r[0].clone();
                    if self.remaining.len() > 0 {
                        add_terms(&mut res, &self.remaining);
                        res = res.normalize();
                    }
                    res
                },
                x => {
                    let r = x.apply_map(&self.m);
                    assert!(r.len() == 1);
                    let mut res = r[0].clone();
                    if self.remaining.len() > 0 {
                        add_terms(&mut res, &self.remaining);
                        res = res.normalize();
                    }
                    res
                }
            }
        )
    }
}

impl IdentityStatement {
    pub fn to_iter<'a>(&'a self, input: &'a Element) -> MatchIterator<'a> {
        MatchIterator { input: input, hasmatch: false, m: vec![], remaining: vec![], mode: self.mode.clone(), rhs: &self.rhs, rhsp: 0, it:
            MatchKind::from_element(&self.lhs, input) }
        
    }
}

fn printmatch<'a>(m: &MatchObject<'a>) {
    debug!("MATCH: [ ");

    for &(ref k, ref v) in m.iter() {
        debug!("{}={};", k,v);
    }
    debug!("]");
}
