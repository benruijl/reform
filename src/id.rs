use structure::{FuncArg,Func,IdentityStatementMode,IdentityStatement,StatementResult};
use std;
use std::fmt;
use std::mem;
use itertools;
use itertools::Itertools;
use std::env;
use parser;
use tools::{Heap,add_terms,is_number_in_range};

pub const MAXMATCH: usize = 1000000; // maximum number of matches

#[derive(Debug,Clone,Eq,PartialEq)]
enum MatchOpt<'a> {
    Single(&'a FuncArg),
    Multiple(&'a [FuncArg])
}

impl<'a> MatchOpt<'a> {
    fn to_vec(&self) -> Vec<FuncArg> {
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
type MatchObject<'a> = Vec<(&'a String, MatchOpt<'a>)>;

// push something to the match object, keeping track of the old length
fn push_match<'a>(m : &mut MatchObject<'a>, k: &'a String, v: &'a FuncArg) -> Option<usize> {
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
fn push_match_slice<'a>(m : &mut MatchObject<'a>, k: &'a String, v: &'a [FuncArg]) -> Option<usize> {
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
impl FuncArg {
    fn apply_map<'a>(&self, m: &MatchObject<'a>) -> Vec<FuncArg> {
        match *self {
            FuncArg::VariableArgument(ref name) => find_match(m, name).unwrap().to_vec(),
            FuncArg::Wildcard(ref name, ..) => find_match(m, name).unwrap().to_vec(),
            FuncArg::Fn(ref f) => vec![FuncArg::Fn(f.apply_map(m)).normalize()],
            FuncArg::Term(ref f) => vec![ FuncArg::Term(f.iter().flat_map(|x| x.apply_map(m)).collect()).normalize()],
            FuncArg::SubExpr(ref f) => vec![FuncArg::SubExpr(f.iter().flat_map(|x| x.apply_map(m)).collect()).normalize()],
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
enum FuncArgIterSingle<'a> {
    FnIter(FuncIterator<'a>), // match function
    Once, // matching without wildcard, ie number vs number
    OnceMatch(&'a String, &'a FuncArg), // simple match of variable
    PermIter(&'a [FuncArg], Heap<&'a FuncArg>, SequenceIter<'a>), // term and arg combinations
    None
}


#[derive(Debug)]
enum FuncArgIter<'a> {
    SliceIter(&'a String, usize, &'a [FuncArg]), // slice from 0 to funcarg end
    SingleArg(&'a [FuncArg], FuncArgIterSingle<'a>), // iters consuming a single argument
    None, // no match
}

impl<'a>  FuncArgIterSingle<'a> {
    fn next(& mut self, m: &mut MatchObject<'a>) -> Option<usize> {
        match *self {
            FuncArgIterSingle::None => None,
            FuncArgIterSingle::Once => {
                let mut to_swap = FuncArgIterSingle::None;
                mem::swap(self, &mut to_swap); //f switch self to none
                match to_swap {
                    FuncArgIterSingle::Once  => Some(m.len()),
                    _   => panic!(), // never reached
                }
            },
            FuncArgIterSingle::OnceMatch(_,_) => {
                let mut to_swap = FuncArgIterSingle::None;
                mem::swap(self, &mut to_swap);
                match to_swap {
                    FuncArgIterSingle::OnceMatch(name, target)  => {
                        push_match(m, name, &target)
                    },
                    _ => panic!(), // never reached
                }
            },
            FuncArgIterSingle::FnIter(ref mut f) => f.next(m),
            FuncArgIterSingle::PermIter(ref pat, ref mut heap, ref mut termit) => {
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


impl<'a>  FuncArgIter<'a> {
    fn next(& mut self, m: &mut MatchObject<'a>) -> Option<(&'a [FuncArg], usize)> {
        match *self {
            FuncArgIter::None => None,
            FuncArgIter::SliceIter(name, ref mut index, target) => {
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
            FuncArgIter::SingleArg(rest, ref mut f) => f.next(m).map(move |x| { (rest, x) })
        }
    }
}


impl FuncArg {
    // create an iterator over a pattern
    fn to_iter<'a>(&'a self, target: &'a [FuncArg]) -> FuncArgIter<'a> {

        // go through all possible options (slice sizes) for the variable argument
        if let &FuncArg::VariableArgument(ref name) = self {
            return FuncArgIter::SliceIter(name,0,target);
        }

        // is the slice non-zero length?
        match target.first() {
            Some(x) => FuncArgIter::SingleArg(&target[1..], self.to_iter_single(x)),
            None => FuncArgIter::None
        }
    }

    // create an iterator over a pattern
    fn to_iter_single<'a>(&'a self, target: &'a FuncArg) -> FuncArgIterSingle<'a> {
        match (target, self) {
                (&FuncArg::Var(ref i1), &FuncArg::Var(ref i2)) if i1 == i2 =>
                             FuncArgIterSingle::Once,
                (&FuncArg::Num(ref pos1, ref num1, ref den1), &FuncArg::Num(ref pos2, ref num2, ref den2)) 
                    if pos1 == pos2 && num1 == num2 && den1 == den2 =>
                            FuncArgIterSingle::Once,
                (&FuncArg::Num(ref pos, ref num, ref den), &FuncArg::Wildcard(ref i2, ref rest)) => {
                    if rest.len() == 0 {
                        return FuncArgIterSingle::OnceMatch(i2, &target)
                    }

                    for restriction in rest {
                        match restriction {
                            &FuncArg::NumberRange(ref pos1, ref num1, ref den1, ref rel) => {
                                // see if the number is in the range
                                if is_number_in_range(*pos,*num,*den,*pos1,*num1,*den1,rel) {
                                    return FuncArgIterSingle::OnceMatch(i2, &target);
                                }
                            }
                            _ if restriction == target => return FuncArgIterSingle::OnceMatch(i2, &target),
                            _ => {}
                        }
                    }

                    FuncArgIterSingle::None
                    
                },
                (_, &FuncArg::Wildcard(ref i2, ref rest)) => {
                    if rest.len() == 0 || rest.contains(target) {
                        FuncArgIterSingle::OnceMatch(i2, &target)
                    } else {
                        FuncArgIterSingle::None
                    }
                },
                (&FuncArg::Fn(ref f1), &FuncArg::Fn(ref f2)) =>
                            FuncArgIterSingle::FnIter(f2.to_iter(&f1)),
                (&FuncArg::Term(ref f1), &FuncArg::Term(ref f2)) |
                (&FuncArg::SubExpr(ref f1), &FuncArg::SubExpr(ref f2)) => {
                    FuncArgIterSingle::PermIter(f2, Heap::new(f1.iter().map(|x| x).collect::<Vec<_>>()),
                        SequenceIter::dummy(f2))
                },
                _ =>  FuncArgIterSingle::None
        }
    }
}

impl Func {

  fn to_iter<'a>(&'a self, target: &'a Func) -> FuncIterator<'a> {
    if self.name != target.name { return FuncIterator { pattern: self, iterators: vec![], matches : vec![] }; }

    // shortcut if the number of arguments is wrong
    let varargcount = self.args.iter().filter(|x| match *x { &FuncArg::VariableArgument {..} => true, _ => false } ).count();
    if self.args.len() - varargcount > target.args.len() { 
        return FuncIterator { pattern: self, iterators: vec![], matches : vec![] }; 
    };
    if varargcount == 0 && self.args.len() != target.args.len() {
        return FuncIterator { pattern: self, iterators: vec![], matches : vec![] }; 
    };

    let mut iterator = (0..self.args.len()).map(|_| { FuncArgIter::None }).collect::<Vec<_>>(); // create placeholder iterators
    iterator[0] = self.args[0].to_iter(&target.args); // initialize the first iterator

    let matches = vec![(&target.args[..], MAXMATCH); self.args.len()]; // placeholder matches

    FuncIterator { pattern: self, iterators: iterator, matches : matches }
  }
}

// iterator over a pattern of a function
#[derive(Debug)]
struct FuncIterator<'a> {
    pattern: &'a Func,
    iterators: Vec<FuncArgIter<'a>>,
    matches: Vec<(&'a [FuncArg], usize)>, // keep track of stack depth
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
    pattern: &'a [FuncArg], // input term
    iterators: Vec<FuncArgIterSingle<'a>>,
    matches: Vec<usize>, // keep track of stack depth
}

impl<'a> SequenceIter<'a> {
    fn dummy(pattern: &'a [FuncArg]) -> SequenceIter<'a> {
        SequenceIter { pattern: pattern, iterators: vec![], matches: vec![] }
    }

    fn new(pattern: &'a [FuncArg], first: &'a FuncArg) -> SequenceIter<'a> {
        let mut its =  (0..pattern.len()).map(|_| { FuncArgIterSingle::None }).collect::<Vec<_>>();
        its[0] = pattern[0].to_iter_single(first);
        SequenceIter { pattern: pattern, iterators: its, matches: vec![MAXMATCH; pattern.len()] }
    }

    fn next(&mut self, target: &[&'a FuncArg], m: &mut MatchObject<'a>) -> Option<usize> {
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
    pattern: &'a [FuncArg],
    target: &'a [FuncArg],
    subtarget: Option<Vec<&'a FuncArg>>,
    remaining: Option<Vec<&'a FuncArg>>,
    m : MatchObject<'a>,
    combinator: itertools::Combinations<std::slice::Iter<'a, FuncArg>>,
    permutator: FuncArgIterSingle<'a>
}

impl<'a> MatchTermIterator<'a> {
    fn new(pattern: &'a [FuncArg], target: &'a [FuncArg]) -> MatchTermIterator<'a> {
        let combinator = target.iter().combinations(pattern.len());

        MatchTermIterator { pattern: pattern, target: target, subtarget: None, remaining: None, m: vec![],
        combinator: combinator, permutator: FuncArgIterSingle::None  }

    }

    fn next(&mut self) -> Option<(Vec<&'a FuncArg>, MatchObject<'a>)> {
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
                self.permutator = FuncArgIterSingle::PermIter(self.pattern, Heap::new(x.iter().map(|x| *x).collect::<Vec<_>>()),
                        SequenceIter::dummy(self.pattern));

                SequenceIter::new(self.pattern, x[0]);

                // construct the factors that are not affected
                let mut rem = vec![];
                for y in self.target.iter() {
                    if !x.contains(&y) {
                        rem.push(y); // FIXME: does this work? we need to check pointers!
                    }
                }
                println!("rem {:?}", rem);
                self.remaining = Some(rem);
                self.subtarget = Some(x);

            } else {
                return None;
            }
        }
    }
}

#[derive(Debug)]
enum MatchKind<'a> {
    Single(MatchObject<'a>, FuncArgIterSingle<'a>),
    SinglePat(&'a FuncArg, MatchObject<'a>, FuncArgIterSingle<'a>, &'a [FuncArg], usize),
    Many(MatchTermIterator<'a>),
    None
}

impl<'a> MatchKind<'a> {
    fn from_funcarg(pattern: &'a FuncArg, target: &'a FuncArg) -> MatchKind<'a> {
        match (pattern, target) {
            (&FuncArg::Term(ref x), &FuncArg::Term(ref y)) => MatchKind::Many(MatchTermIterator::new(x, y)),
            (ref a, &FuncArg::Term(ref y)) => MatchKind::SinglePat(a, vec![], FuncArgIterSingle::None, y, 0),
            (a,b) => MatchKind::Single(vec![], a.to_iter_single(b)) 
        }
    }

    fn next(&mut self) -> Option<(Vec<&'a FuncArg>, MatchObject<'a>)> {
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
    rhs: &'a FuncArg,
    m: MatchObject<'a>,
    remaining: Vec<&'a FuncArg>,
    it: MatchKind<'a>,
    rhsp: usize, // current rhs index,
    hasmatch: bool,
    input: &'a FuncArg
}

// iterate over the output terms of a match
impl<'a> MatchIterator<'a> {
    pub fn next(&mut self) -> StatementResult<FuncArg> {
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
                &FuncArg::SubExpr(ref x) => {
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
    pub fn to_iter<'a>(&'a self, input: &'a FuncArg) -> MatchIterator<'a> {
        MatchIterator { input: input, hasmatch: false, m: vec![], remaining: vec![], mode: self.mode.clone(), rhs: &self.rhs, rhsp: 0, it:
            MatchKind::from_funcarg(&self.lhs, input) }
        
    }
}

fn printmatch<'a>(m: &MatchObject<'a>) {
    print!("MATCH: [ ");

    for &(ref k, ref v) in m.iter() {
        print!("{}={};", k,v);
    }
    println!("]");
}
