use num_traits::One;
use num_traits::Zero;
use number::Number;
use std::fmt;
use std::mem;
use structure::{
    BorrowedVarInfo, Element, FunctionAttributes, IdentityStatement, IdentityStatementMode,
    ReplaceResult, StatementResult, VarName,
};
use tools::{is_number_in_range, SliceRef};

pub const MAXMATCH: usize = 1_000_000; // maximum number of matches

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum MatchOpt<'a> {
    Single(&'a Element),
    SingleOwned(Element),
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
            MatchOpt::SingleOwned(ref x) => MatchOptOwned::Single(x.clone(), true),
            MatchOpt::Multiple(x) => {
                MatchOptOwned::Multiple(x.iter().map(|y| (*y).clone()).collect())
            }
        }
    }
}

impl MatchOptOwned {
    pub fn into_single(self) -> (Element, bool) {
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
            MatchOpt::SingleOwned(ref x) => write!(f, "{}", x),
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
                MatchOpt::SingleOwned(ref vv) if v == vv => return Some(m.len()),
                _ => return None,
            }
        }
    }

    m.push((k, MatchOpt::Single(v)));
    Some(m.len() - 1)
}

// push something to the match object, keeping track of the old length
fn push_match_owned<'a>(m: &mut MatchObject<'a>, k: &'a VarName, v: Element) -> Option<usize> {
    for &(rk, ref rv) in m.iter() {
        if *rk == *k {
            match *rv {
                MatchOpt::Single(ref vv) if v == **vv => return Some(m.len()),
                MatchOpt::SingleOwned(ref vv) if v == *vv => return Some(m.len()),
                _ => return None,
            }
        }
    }

    m.push((k, MatchOpt::SingleOwned(v)));
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
    pub fn apply_map<'a>(&self, m: &MatchObject<'a>) -> MatchOptOwned {
        match *self {
            Element::VariableArgument(ref name) | Element::Wildcard(ref name, ..) => {
                find_match(m, name)
                    .expect("Unknown wildcard in rhs")
                    .to_owned()
            }
            Element::FnWildcard(ref name, ref b) => {
                let (ref restrictions, ref old_args) = **b;

                if restrictions.len() > 0 {
                    panic!("No restrictions allowed in the rhs");
                }

                let newname = match find_match(m, name)
                    .expect("Unknown wildcard function in rhs")
                    .to_owned()
                    .into_single()
                    .0
                {
                    Element::Var(n, _) => n,
                    _ => unreachable!(),
                };

                let mut changed = false;
                let mut args = Vec::with_capacity(old_args.len());
                for a in old_args {
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

                MatchOptOwned::Single(Element::Fn(changed, newname, args), changed)
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
            Element::Comparison(_, ref be, ref cond) => {
                let (ref b, ref e) = **be;
                let mut changed = false;
                let (bb, c) = b.apply_map(m).into_single();
                changed |= c;
                let (pp, c) = e.apply_map(m).into_single();
                changed |= c;
                MatchOptOwned::Single(
                    Element::Comparison(changed, Box::new((bb, pp)), cond.clone()),
                    changed,
                )
            }
            Element::Fn(_, name, ref old_args) => {
                let mut changed = false;
                let mut args = Vec::with_capacity(old_args.len());
                for a in old_args {
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

                MatchOptOwned::Single(Element::Fn(changed, name, args), changed)
            }
            Element::Term(_, ref f) => {
                let mut changed = false;
                let mut args = Vec::with_capacity(f.len());
                for x in f.iter() {
                    let (xx, c) = x.apply_map(m).into_single();
                    changed |= c;
                    args.push(xx);
                }
                MatchOptOwned::Single(Element::Term(changed, args), changed)
            }
            Element::SubExpr(_, ref f) => {
                let mut changed = false;
                let mut args = Vec::with_capacity(f.len());
                for x in f.iter() {
                    let (xx, c) = x.apply_map(m).into_single();
                    changed |= c;
                    args.push(xx);
                }
                MatchOptOwned::Single(Element::SubExpr(changed, args), changed)
            }
            Element::Dollar(ref name, ref inds) => {
                let mut changed = false;
                let mut newinds = Vec::with_capacity(inds.len());
                for a in inds.iter() {
                    match a.apply_map(m) {
                        MatchOptOwned::Single(x, c) => {
                            changed |= c;
                            newinds.push(x)
                        }
                        MatchOptOwned::Multiple(x) => {
                            changed = true;
                            newinds.extend(x)
                        }
                    }
                }

                MatchOptOwned::Single(Element::Dollar(name.clone(), newinds), changed)
            }
            _ => MatchOptOwned::Single(self.clone(), false), // no match, so no change
        }
    }
}

#[derive(Debug)]
pub enum ElementIterSingle<'a> {
    FnIter(FuncIterator<'a>), // match function
    FnWildcardIter(&'a VarName, Element, usize, FuncIterator<'a>),
    SymFnWildcardIter(&'a VarName, Element, usize, SubSequenceIter<'a>),
    PermIter(SubSequenceIter<'a>), // go through all permutations to find a match
    Once,                          // matching without wildcard, ie number vs number
    OnceMatch(&'a VarName, &'a Element), // simple match of variable
    VarPowerMatch(
        VarName,
        &'a Number,
        &'a Element,
        &'a Element,
        &'a BorrowedVarInfo<'a>,
    ), // match a variable x^n to x?^y?
    SeqIt(Vec<&'a Element>, SequenceIter<'a>), // target and iterator
    None(bool),                    // should we pop?
}

#[derive(Debug)]
pub enum ElementIter<'a> {
    SliceIter(&'a VarName, usize, usize, &'a [Element]), // slice
    SingleArg(&'a [Element], ElementIterSingle<'a>),     // iters consuming a single argument
    Once,                                                // match without any changes
    None,                                                // no match
}

impl<'a> ElementIterSingle<'a> {
    fn next(&mut self, m: &mut MatchObject<'a>) -> Option<usize> {
        match *self {
            ElementIterSingle::None(should_pop) => {
                if should_pop {
                    m.pop();
                }
                None
            }
            ElementIterSingle::Once => match mem::replace(self, ElementIterSingle::None(false)) {
                ElementIterSingle::Once => Some(m.len()),
                _ => unreachable!(),
            },
            ElementIterSingle::OnceMatch(_, _) => {
                match mem::replace(self, ElementIterSingle::None(false)) {
                    ElementIterSingle::OnceMatch(name, target) => {
                        mem::replace(self, ElementIterSingle::None(true));
                        push_match(m, name, target)
                    }
                    _ => unreachable!(),
                }
            }
            ElementIterSingle::VarPowerMatch(..) => {
                match mem::replace(self, ElementIterSingle::None(false)) {
                    ElementIterSingle::VarPowerMatch(b1, p1, b2, p2, var_info) => {
                        let oldlen = m.len();
                        let mut newlen = oldlen;

                        // match the base
                        let r = Element::Var(b1, Number::one());

                        match b2 {
                            Element::Wildcard(vn, rest) => {
                                let mut found = false;
                                for restriction in rest {
                                    match restriction {
                                        _ if restriction == &r => {
                                            match push_match_owned(m, vn, r.clone()) {
                                                Some(x) => {
                                                    found = true;
                                                    newlen = x;
                                                    break;
                                                }
                                                None => return None,
                                            }
                                        }
                                        _ => {}
                                    }
                                }

                                if rest.len() == 0 {
                                    match push_match_owned(m, vn, r.clone()) {
                                        Some(x) => {
                                            newlen = x;
                                        }
                                        None => return None,
                                    }
                                } else {
                                    if !found {
                                        return None;
                                    }
                                }
                            }
                            Element::Var(i, v) => {
                                if *i != b1 || !v.is_one() {
                                    return None;
                                }
                            }
                            Element::Dollar(..) => {
                                if var_info.local_info.get_dollar(b2) != Some(&r) {
                                    return None;
                                }
                            }
                            _ => return None,
                        }

                        let r1 = Element::Num(false, p1.clone());
                        // match the power
                        match p2 {
                            Element::Wildcard(vn, rest) => {
                                for restriction in rest {
                                    match restriction {
                                        &Element::NumberRange(ref num1, ref rel) => {
                                            // see if the number is in the range
                                            if is_number_in_range(p1, num1, rel) {
                                                match push_match_owned(m, vn, r1) {
                                                    Some(x) => {
                                                        return Some(x);
                                                    }
                                                    None => {
                                                        m.truncate(oldlen);
                                                        return None;
                                                    }
                                                }
                                            }
                                        }
                                        _ if restriction == &r1 => {
                                            match push_match_owned(m, vn, r1) {
                                                Some(x) => {
                                                    return Some(x);
                                                }
                                                None => {
                                                    m.truncate(oldlen);
                                                    return None;
                                                }
                                            }
                                        }
                                        _ => {}
                                    }
                                }

                                if rest.len() == 0 {
                                    match push_match_owned(m, vn, r1) {
                                        Some(y) => Some(y),
                                        None => {
                                            m.truncate(oldlen);
                                            None
                                        }
                                    }
                                } else {
                                    None
                                }
                            }
                            Element::Dollar(..) => {
                                if var_info.local_info.get_dollar(p2) != Some(&r1) {
                                    return None;
                                }
                                Some(newlen)
                            }
                            Element::Num(_, i) => {
                                if i != p1 {
                                    m.truncate(oldlen);
                                    None
                                } else {
                                    Some(newlen)
                                }
                            }
                            _ => {
                                m.truncate(oldlen);
                                None
                            }
                        }
                    }
                    _ => unreachable!(),
                }
            }
            ElementIterSingle::FnIter(ref mut f) => f.next(m),
            ElementIterSingle::FnWildcardIter(ref name, ref target, ref mut old_len, ref mut f) => {
                if *old_len == MAXMATCH {
                    match push_match_owned(m, name, target.clone()) {
                        Some(x) => {
                            *old_len = x;
                        }
                        None => {
                            return None;
                        }
                    }
                }

                match f.next(m) {
                    None => {
                        // pop the function name match
                        m.truncate(*old_len);
                        None
                    }
                    x => x,
                }
            }
            ElementIterSingle::SymFnWildcardIter(
                ref name,
                ref target,
                ref mut old_len,
                ref mut f,
            ) => {
                if *old_len == MAXMATCH {
                    match push_match_owned(m, name, target.clone()) {
                        Some(x) => {
                            *old_len = x;
                        }
                        None => {
                            return None;
                        }
                    }
                }

                match f.next(m).map(|(_, s)| s) {
                    None => {
                        // pop the function name match
                        m.truncate(*old_len);
                        None
                    }
                    x => x,
                }
            }
            ElementIterSingle::PermIter(ref mut f) => f.next(m).map(|(_, s)| s),
            ElementIterSingle::SeqIt(ref target, ref mut seqit) => seqit.next(target, m),
        }
    }
}

impl<'a> ElementIter<'a> {
    fn next(&mut self, m: &mut MatchObject<'a>) -> Option<(&'a [Element], usize)> {
        match *self {
            ElementIter::None => None,
            ElementIter::Once => {
                let mut to_swap = ElementIter::None;
                mem::swap(self, &mut to_swap); //f switch self to none
                match to_swap {
                    ElementIter::Once => Some((&[], 0)), // return empty slice
                    _ => panic!(),                       // never reached
                }
            }
            ElementIter::SliceIter(name, ref mut curlength, upper_bound, target) => {
                // if the slice is already found, we can immediately compare
                if *curlength > upper_bound {
                    return None;
                }

                if let Some(&MatchOpt::Multiple(v)) = find_match(m, name) {
                    *curlength = upper_bound + 1; // make sure next call gives None
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

                'findcandidate: while *curlength <= target.len() {
                    let (f, l) = target.split_at(*curlength);
                    *curlength += 1;

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
        slice_min_bound: usize,
        slice_max_bound: usize,
        var_info: &'a BorrowedVarInfo<'a>,
        level: usize,
    ) -> ElementIter<'a> {
        // go through all possible options (slice sizes) for the variable argument
        if let Element::VariableArgument(ref name) = *self {
            return ElementIter::SliceIter(name, slice_min_bound, slice_max_bound, target);
        }

        // is the slice non-zero length?
        match target.first() {
            Some(x) => {
                ElementIter::SingleArg(&target[1..], self.to_iter_single(x, var_info, level))
            }
            None => ElementIter::None,
        }
    }

    // create an iterator over a pattern
    fn to_iter_single<'a>(
        &'a self,
        target: &'a Element,
        var_info: &'a BorrowedVarInfo<'a>,
        level: usize,
    ) -> ElementIterSingle<'a> {
        match (target, self) {
            (&Element::Var(ref i1, ref e1), &Element::Pow(_, ref be2)) => {
                // match x^x1? to x^expr
                let (ref b2, ref e2) = **be2;

                ElementIterSingle::VarPowerMatch(*i1, e1, b2, e2, var_info)
            }
            (&Element::Pow(_, ref be1), &Element::Pow(_, ref be2)) => {
                let (ref b1, ref e1) = **be1;
                let (ref b2, ref e2) = **be2;

                // match an expression to its multiple on the ground level
                if level == 0 {
                    if let Element::Num(false, Number::SmallInt(n1)) = e1 {
                        if let Element::Num(false, Number::SmallInt(n2)) = e2 {
                            if n2 < n1 {
                                return b1.to_iter_single(b2, var_info, level + 1);
                            }
                        }
                    }
                }

                ElementIterSingle::SeqIt(
                    vec![b1, e1],
                    SequenceIter::new(&SliceRef::OwnedSlice(vec![b2, e2]), b1, var_info, level + 1),
                )
            }
            (&Element::Dollar(ref name, ref inds), &Element::Dollar(ref name1, ref inds1)) => {
                // match $a[x?] to $a[1]
                ElementIterSingle::FnIter(FuncIterator::from_element(
                    name1,
                    inds1,
                    name,
                    inds,
                    var_info,
                    level + 1,
                ))
            }
            (i1, d @ &Element::Dollar(..)) => {
                if var_info.local_info.get_dollar(d) == Some(i1) {
                    ElementIterSingle::Once
                } else {
                    ElementIterSingle::None(false)
                }
            }
            (Element::Pow(_, ref be1), x) => {
                // match x to x^num on the ground level
                let (ref b2, ref e2) = **be1;

                if level == 0 && x == b2 {
                    if let Element::Num(_, Number::SmallInt(n)) = e2 {
                        if *n > 0 {
                            return ElementIterSingle::Once;
                        }
                    }
                }

                ElementIterSingle::None(false)
            }
            (&Element::Var(ref i1, ref e1), &Element::Var(ref i2, ref e2))
                if i1 == i2 && (e1 == e2 || (level == 0 && e1 >= e2 && e2 > &Number::zero())) =>
            {
                ElementIterSingle::Once
            }
            (&Element::Num(_, ref n1), &Element::Num(_, ref n2)) if n1 == n2 => {
                ElementIterSingle::Once
            }
            (&Element::Num(_, ref n), &Element::Wildcard(ref i2, ref rest)) => {
                if rest.is_empty() {
                    return ElementIterSingle::OnceMatch(i2, target);
                }

                for restriction in rest {
                    match restriction {
                        &Element::NumberRange(ref num1, ref rel) => {
                            // see if the number is in the range
                            if is_number_in_range(n, num1, rel) {
                                return ElementIterSingle::OnceMatch(i2, target);
                            }
                        }
                        _ if restriction == target => {
                            return ElementIterSingle::OnceMatch(i2, target)
                        }
                        _ => {}
                    }
                }

                ElementIterSingle::None(false)
            }
            (_, &Element::Wildcard(ref i2, ref rest)) => {
                if rest.is_empty() || rest.contains(target) {
                    ElementIterSingle::OnceMatch(i2, target)
                } else {
                    ElementIterSingle::None(false)
                }
            }
            (&Element::Fn(_, ref name1, ref args1), &Element::Fn(_, ref name2, ref args2)) => {
                // check if we have a symmetric function
                if name1 == name2 && args1.len() == args2.len() {
                    if let Some(attribs) = var_info.global_info.func_attribs.get(name1) {
                        // check if the pattern contains no wildcard
                        if attribs.contains(&FunctionAttributes::Symmetric) {
                            if !args2.iter().any(|x| {
                                if let Element::VariableArgument(_) = *x {
                                    true
                                } else {
                                    false
                                }
                            }) {
                                return ElementIterSingle::PermIter(SubSequenceIter::new(
                                    args2,
                                    args1,
                                    var_info,
                                    level + 1,
                                ));
                            } else {
                                println!("Warning: used ?a in symmetric function pattern match. Ignoring symmetric property.");
                            }
                        }
                    }
                }

                ElementIterSingle::FnIter(FuncIterator::from_element(
                    name2, args2, name1, args1, var_info, level,
                ))
            }
            (&Element::Fn(_, ref name1, ref args1), &Element::FnWildcard(ref name2, ref b)) => {
                let (restrictions, args2) = &**b;

                if restrictions.len() > 0
                    && !restrictions.contains(&Element::Var(*name1, Number::one()))
                {
                    ElementIterSingle::None(false)
                } else {
                    if args1.len() == args2.len() {
                        if let Some(attribs) = var_info.global_info.func_attribs.get(name1) {
                            // check if the pattern contains no wildcard
                            if attribs.contains(&FunctionAttributes::Symmetric) {
                                if !args2.iter().any(|x| {
                                    if let Element::VariableArgument(_) = *x {
                                        true
                                    } else {
                                        false
                                    }
                                }) {
                                    return ElementIterSingle::SymFnWildcardIter(
                                        name2,
                                        Element::Var(*name1, Number::one()),
                                        MAXMATCH,
                                        SubSequenceIter::new(args2, args1, var_info, level + 1),
                                    );
                                } else {
                                    println!("Warning: used ?a in symmetric function pattern match. Ignoring symmetric property.");
                                }
                            }
                        }
                    }

                    ElementIterSingle::FnWildcardIter(
                        name2,
                        Element::Var(*name1, Number::one()),
                        MAXMATCH,
                        FuncIterator::from_element(name1, args2, name1, args1, var_info, level),
                    )
                }
            }
            (&Element::Term(_, ref f1), &Element::Term(_, ref f2))
            | (&Element::SubExpr(_, ref f1), &Element::SubExpr(_, ref f2)) => {
                if f1.len() == f2.len() {
                    // TODO: increase the level by 1 in case of a subexpr?
                    ElementIterSingle::PermIter(SubSequenceIter::new(f2, f1, var_info, level))
                } else {
                    ElementIterSingle::None(false)
                }
            }
            _ => ElementIterSingle::None(false),
        }
    }
}

// iterator over a pattern of a function
#[derive(Debug)]
pub struct FuncIterator<'a> {
    args: &'a Vec<Element>,
    iterators: Vec<ElementIter<'a>>,
    matches: Vec<(&'a [Element], usize)>, // keep track of stack depth
    var_info: &'a BorrowedVarInfo<'a>,
    level: usize,
}

impl<'a> FuncIterator<'a> {
    fn from_element(
        name: &'a VarName,
        args: &'a Vec<Element>,
        target_name: &'a VarName,
        target_args: &'a Vec<Element>,
        var_info: &'a BorrowedVarInfo<'a>,
        level: usize,
    ) -> FuncIterator<'a> {
        if name != target_name {
            return FuncIterator {
                args: args,
                iterators: vec![],
                matches: vec![],
                var_info,
                level,
            };
        }

        // shortcut if the number of arguments is wrong
        let varargcount = args
            .iter()
            .filter(|x| match **x {
                Element::VariableArgument { .. } => true,
                _ => false,
            }).count();
        if args.len() - varargcount > target_args.len() {
            return FuncIterator {
                args: args,
                iterators: vec![],
                matches: vec![],
                var_info,
                level,
            };
        };
        if varargcount == 0 && args.len() != target_args.len() {
            return FuncIterator {
                args: args,
                iterators: vec![],
                matches: vec![],
                var_info,
                level,
            };
        };

        if varargcount == 0 && target_args.len() == 0 {
            // we match two functions without arguments
            // return an iterator that yields a success once
            return FuncIterator {
                args: args,
                iterators: vec![ElementIter::Once],
                matches: vec![(&[], MAXMATCH)],
                var_info,
                level,
            };
        }

        let mut iterator = (0..args.len())
            .map(|_| ElementIter::None)
            .collect::<Vec<_>>(); // create placeholder iterators
                                  // compute limits for wildcards
        if let Element::VariableArgument(_) = args[0] {
            let mut minbound = target_args.len();
            let mut maxbound = target_args.len();

            for a in &args[1..] {
                if let Element::VariableArgument(_) = *a {
                    minbound = 0;
                } else {
                    if minbound > 0 {
                        minbound -= 1;
                    }
                    maxbound -= 1;
                }
            }

            iterator[0] = args[0].to_iter(&target_args, minbound, maxbound, var_info, level + 1); // initialize the first iterator
        } else {
            iterator[0] = args[0].to_iter(&target_args, 0, 0, var_info, level + 1); // initialize the first iterator
        }

        let matches = vec![(&target_args[..], MAXMATCH); args.len()]; // placeholder matches

        FuncIterator {
            args: args,
            iterators: iterator,
            matches: matches,
            var_info,
            level,
        }
    }

    fn next(&mut self, m: &mut MatchObject<'a>) -> Option<usize> {
        if self.iterators.len() == 0 {
            return None;
        }

        // find the first iterator from the back that is not None
        let mut i = self.iterators.len() - 1;
        'next: loop {
            //println!("matching {:?} {:?}", self.args, m);
            // FIXME: not correct. the iters should pop the stack on a next match
            m.truncate(self.matches[i].1); // pop the matches from the stack

            if let Some(x) = self.iterators[i].next(m) {
                self.matches[i] = x;

                // now update all elements after
                let mut j = i + 1;
                while j < self.iterators.len() {
                    // create a new iterator at j based on the previous match dictionary and slice
                    let slicem = self.matches[j - 1].0;
                    if let Element::VariableArgument(_) = self.args[j] {
                        let mut minbound = slicem.len();
                        let mut maxbound = slicem.len();

                        for a in &self.args[j + 1..] {
                            if let Element::VariableArgument(_) = *a {
                                minbound = 0;
                            } else {
                                if minbound > 0 {
                                    minbound -= 1;
                                }
                                maxbound -= 1;
                            }
                        }

                        self.iterators[j] = self.args[j].to_iter(
                            slicem,
                            minbound,
                            maxbound,
                            self.var_info,
                            self.level + 1,
                        );
                    } else {
                        self.iterators[j] = self.args[j].to_iter(
                            self.matches[j - 1].0,
                            0,
                            0,
                            self.var_info,
                            self.level + 1,
                        );
                    }

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

/// Iterator over a sequence of pattern matches.
#[derive(Debug)]
pub struct SequenceIter<'a> {
    pattern: SliceRef<'a, Element>, // input term
    iterators: Vec<ElementIterSingle<'a>>,
    matches: Vec<usize>, // keep track of stack depth
    var_info: &'a BorrowedVarInfo<'a>,
    level: usize,
}

impl<'a> SequenceIter<'a> {
    fn new(
        pattern: &SliceRef<'a, Element>,
        first: &'a Element,
        var_info: &'a BorrowedVarInfo<'a>,
        level: usize,
    ) -> SequenceIter<'a> {
        let mut its = (0..pattern.len())
            .map(|_| ElementIterSingle::None(false))
            .collect::<Vec<_>>();
        its[0] = pattern.index(0).to_iter_single(first, var_info, level);
        SequenceIter {
            pattern: pattern.clone(),
            iterators: its,
            matches: vec![MAXMATCH; pattern.len()],
            var_info,
            level,
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
                    self.iterators[j] =
                        self.pattern
                            .index(j)
                            .to_iter_single(target[j], self.var_info, self.level);

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

/// An iterator that matches a pattern of multiple factors to
/// a subset of a term.
/// For example:
/// `IN = f(1,2,3)*g(1,2,3)*g(4,5,6);
/// {
///     id all f(?a,n?,?b)*g(?c,n?,?d) = f(n?)*g(n?);
/// }
///`
/// uses this iterator to match the `g` to one of the `g`s in the input.
#[derive(Debug)]
pub struct SubSequenceIter<'a> {
    pattern: &'a [Element], // input term
    target: &'a [Element],
    iterators: Vec<ElementIterSingle<'a>>,
    indices: Vec<usize>,
    initialized: bool,
    matches: Vec<usize>, // keep track of stack depth
    var_info: &'a BorrowedVarInfo<'a>,
    level: usize,
}

impl<'a> SubSequenceIter<'a> {
    fn new(
        pattern: &'a [Element],
        target: &'a [Element],
        var_info: &'a BorrowedVarInfo<'a>,
        level: usize,
    ) -> SubSequenceIter<'a> {
        SubSequenceIter {
            pattern: pattern,
            iterators: (0..pattern.len())
                .map(|_| ElementIterSingle::None(false))
                .collect(),
            matches: vec![MAXMATCH; pattern.len()],
            indices: vec![0; pattern.len()],
            target,
            var_info,
            level,
            initialized: false,
        }
    }

    fn next(&mut self, m: &mut MatchObject<'a>) -> Option<(&Vec<usize>, usize)> {
        if self.pattern.len() > self.target.len() {
            return None;
        }

        let mut i = if self.initialized {
            // find the first iterator from the back that is not None
            self.iterators.len() - 1
        } else {
            // build the first iterator from the start
            self.indices = (0..self.pattern.len())
                .map(|_| self.target.len() + 1)
                .collect(); // start with unique indices
            0
        };
        self.initialized = true;

        loop {
            m.truncate(self.matches[i]); // pop the matches from the stack

            if let Some(x) = self.iterators[i].next(m) {
                self.matches[i] = x;

                // we have found a match!
                if i + 1 == self.pattern.len() {
                    return Some((&self.indices, self.matches[i]));
                }
                i += 1;
            } else {
                // find a new empty position
                if self.indices[i] == self.target.len() + 1 {
                    self.indices[i] = 0; // initialize

                    // for non-commutative functions, we make sure the index in the
                    // target is higher than that of its left neighbour
                    if i > 0 {
                        if let Element::Fn(_, ref name, _) = self.pattern[i] {
                            if let Element::Fn(_, ref name1, _) = self.pattern[i - 1] {
                                if name == name1 {
                                    if let Some(attribs) =
                                        self.var_info.global_info.func_attribs.get(name)
                                    {
                                        if attribs.contains(&FunctionAttributes::NonCommutative) {
                                            self.indices[i] = self.indices[i - 1] + 1;
                                        }
                                    }
                                }
                            }
                        }
                    }
                } else {
                    self.indices[i] += 1;
                }
                while self.indices[..i].iter().any(|x| self.indices[i] == *x)
                    && self.indices[i] < self.target.len()
                {
                    self.indices[i] += 1;
                }

                if self.indices[i] == self.target.len() {
                    // out of tries, fall back one level
                    if i == 0 {
                        // we are out of matches
                        return None;
                    }

                    self.indices[i] = self.target.len() + 1; // reset the index
                    i -= 1;
                } else {
                    self.iterators[i] = self.pattern[i].to_iter_single(
                        &self.target[self.indices[i]],
                        self.var_info,
                        self.level,
                    );
                }
            }
        }
    }
}

#[derive(Debug)]
pub enum MatchKind<'a> {
    Single(ElementIterSingle<'a>),
    SinglePat(
        &'a Element,
        ElementIterSingle<'a>,
        &'a [Element],
        usize,
        &'a BorrowedVarInfo<'a>,
    ),
    Many(SubSequenceIter<'a>),
    None,
}

impl<'a> MatchKind<'a> {
    pub fn from_element(
        pattern: &'a Element,
        target: &'a Element,
        var_info: &'a BorrowedVarInfo<'a>,
    ) -> MatchKind<'a> {
        match (pattern, target) {
            (&Element::Term(_, ref x), &Element::Term(_, ref y)) => {
                MatchKind::Many(SubSequenceIter::new(x, y, var_info, 0))
            }
            (a, &Element::Term(_, ref y)) => {
                MatchKind::SinglePat(a, ElementIterSingle::None(false), y, 0, var_info)
            }
            (a, b) => MatchKind::Single(a.to_iter_single(b, var_info, 0)),
        }
    }

    pub fn next(&mut self, m: &mut MatchObject<'a>, indices: &mut Vec<usize>) -> bool {
        match *self {
            MatchKind::Single(ref mut x) => {
                indices.clear();
                x.next(m).is_some()
            }
            MatchKind::Many(ref mut x) => match x.next(m) {
                Some((ind, _)) => {
                    indices.clone_from(ind);
                    true
                }
                None => false,
            },
            MatchKind::SinglePat(pat, ref mut it, target, ref mut index, var_info) => loop {
                if it.next(m).is_some() {
                    indices.clear();
                    indices.push(*index - 1);
                    return true;
                }

                if *index == target.len() {
                    return false;
                }
                *it = pat.to_iter_single(&target[*index], var_info, 0);
                *index += 1;
            },
            MatchKind::None => false,
        }
    }
}

#[derive(Debug)]
pub struct MatchIterator<'a> {
    mode: IdentityStatementMode,
    lhs: &'a Element,
    rhs: &'a Element,
    target: &'a Element,
    m: MatchObject<'a>,
    used_indices: Vec<usize>,
    result: Element,
    it: MatchKind<'a>,
    rhsp: usize, // current rhs index,
    hasmatch: bool,
    var_info: &'a BorrowedVarInfo<'a>,
}

// iterate over the output terms of a match
impl<'a> MatchIterator<'a> {
    /// Find out how often the pattern fits in the
    /// target term.
    fn find_multiplicity(&self, lhs: &Element, rhs: &Element) -> usize {
        match (lhs, rhs) {
            (Element::Term(_, ref pts), Element::Term(_, ref tts)) => {
                let mut max_mul = 0;
                for (i, k) in pts.iter().enumerate() {
                    let mul = self.find_multiplicity(k, &tts[self.used_indices[i]]);
                    if mul < max_mul || max_mul == 0 {
                        max_mul = mul;

                        if mul == 1 {
                            return 1;
                        }
                    }
                }
                max_mul
            }
            (_, Element::Term(_, ref tts)) => {
                self.find_multiplicity(lhs, &tts[self.used_indices[0]])
            }
            (Element::Pow(_, be), Element::Pow(_, be1)) => {
                if let Element::Num(_, Number::SmallInt(p)) = be.1 {
                    if let Element::Num(_, Number::SmallInt(p1)) = be1.1 {
                        if p > 0 && p1 > 0 {
                            return (p1 / p) as usize;
                        }
                    }
                }
                1
            }
            (_, Element::Pow(_, be)) => {
                if let Element::Num(_, Number::SmallInt(p)) = be.1 {
                    if p > 0 {
                        return p as usize;
                    }
                }
                1
            }
            (Element::Var(_, pow), Element::Var(_, pow1)) => {
                if let Number::SmallInt(p) = pow {
                    if let Number::SmallInt(p1) = pow1 {
                        if *p > 0 && *p1 > 0 {
                            return (p1 / p) as usize;
                        }
                    }
                }
                1
            }
            (Element::Wildcard(_, _), Element::Var(_, pow)) => {
                if let Number::SmallInt(p) = pow {
                    if *p > 0 {
                        return *p as usize;
                    }
                }
                1
            }
            _ => 1,
        }
    }

    fn construct_rest_term(
        &self,
        lhs: &Element,
        rhs: &Element,
        accum: &mut Vec<Element>,
        multiplicity: usize,
    ) {
        match (lhs, rhs) {
            (Element::Term(_, ref pts), Element::Term(_, ref tts)) => {
                for (i, k) in tts.iter().enumerate() {
                    // add factors that were not matched or whatever remains of a match
                    if self.used_indices.len() < tts.len() && !self.used_indices.contains(&i) {
                        accum.push(k.clone())
                    } else {
                        self.construct_rest_term(
                            &pts[self.used_indices.iter().position(|x| *x == i).unwrap()],
                            k,
                            accum,
                            multiplicity,
                        )
                    }
                }
            }
            (_, Element::Term(_, ref tts)) => {
                for (i, k) in tts.iter().enumerate() {
                    if i == self.used_indices[0] {
                        self.construct_rest_term(lhs, k, accum, multiplicity);
                    } else {
                        accum.push(k.clone());
                    }
                }
            }
            (Element::Pow(_, be), Element::Pow(dirty, be1)) => {
                if let Element::Num(_, ref p) = be.1 {
                    if let Element::Num(_, ref p1) = be1.1 {
                        let newpow =
                            p1.clone() - Number::SmallInt(multiplicity as isize) * p.clone();
                        if !newpow.is_zero() {
                            accum.push(Element::Pow(
                                *dirty,
                                Box::new((be1.0.clone(), Element::Num(false, newpow))),
                            ));
                        }
                    } else {
                        unreachable!()
                    }
                } else {
                    unreachable!()
                }
            }
            (_, Element::Pow(dirty, be)) => {
                if let Element::Num(_, ref p) = be.1 {
                    let newpow = p.clone() - Number::SmallInt(multiplicity as isize);
                    if !newpow.is_zero() {
                        accum.push(Element::Pow(
                            *dirty,
                            Box::new((be.0.clone(), Element::Num(false, newpow))),
                        ));
                    }
                } else {
                    unreachable!()
                }
            }
            (Element::Var(_, pow), Element::Var(x1, pow1)) => {
                let newpow = pow1.clone() - Number::SmallInt(multiplicity as isize) * pow.clone();
                if !newpow.is_zero() {
                    accum.push(Element::Var(*x1, newpow));
                }
            }
            (Element::Wildcard(_, _), Element::Var(x1, pow1)) => {
                let newpow = pow1.clone() - Number::SmallInt(multiplicity as isize);
                if !newpow.is_zero() {
                    accum.push(Element::Var(*x1, newpow));
                }
            }
            _ => {} // factor needs to be removed completely
        }
    }

    /// Construct the part of the input that remains in the output.
    /// This takes multiplicity of the pattern into account.
    fn construct_remaining(&self, target: &Element) -> (usize, Element) {
        // determine the maximimum multiplicity
        let multiplicity = if self.mode != IdentityStatementMode::Once {
            self.find_multiplicity(&self.lhs, target)
        } else {
            1
        };

        // construct the rest terms
        let mut e = vec![];
        self.construct_rest_term(&self.lhs, target, &mut e, multiplicity);

        if e.is_empty() {
            (multiplicity, Element::Num(false, Number::one()))
        } else {
            (multiplicity, Element::Term(true, e))
        }
    }

    pub fn next(&mut self) -> StatementResult<Element> {
        if self.rhsp == 0 {
            if self.it.next(&mut self.m, &mut self.used_indices) {
                if self.mode != IdentityStatementMode::All {
                    self.it = MatchKind::None;
                }

                let (mult, mut rem) = self.construct_remaining(self.target);

                self.result = if mult == 1 {
                    self.rhs.apply_map(&self.m).into_single().0
                } else {
                    self.rhs
                        .apply_map(&self.m)
                        .into_single()
                        .0
                        .pow(Element::Num(false, Number::SmallInt(mult as isize)))
                };

                // in many-mode we keep on matching on the terms that remain
                // TODO: support many-all mode
                if self.mode == IdentityStatementMode::Many {
                    self.used_indices.clear();

                    let mut r;
                    loop {
                        {
                            let mut m2 = vec![]; // needs to be local to prevent borrow issues
                            if !MatchKind::from_element(self.lhs, &rem, self.var_info)
                                .next(&mut m2, &mut self.used_indices)
                            {
                                break;
                            }

                            let (mult, rem1) = self.construct_remaining(&rem);

                            self.result.append_factors_mut_move(if mult == 1 {
                                self.rhs.apply_map(&m2).into_single().0
                            } else {
                                self.rhs
                                    .apply_map(&m2)
                                    .into_single()
                                    .0
                                    .pow(Element::Num(false, Number::SmallInt(mult as isize)))
                            });

                            r = rem1;
                        }
                        rem = r;
                    }
                }

                self.result.append_factors_mut_move(rem);
            } else {
                if self.hasmatch {
                    return StatementResult::Done;
                } else {
                    return StatementResult::NoChange;
                }
            }
        }

        self.hasmatch = true;

        let mut e = match &mut self.result {
            Element::SubExpr(_, ref mut x) => {
                if x.len() == 1 {
                    self.rhsp = 0;
                } else {
                    self.rhsp = x.len();
                }
                x.pop().unwrap()
            }
            x => mem::replace(x, Element::default()),
        };

        // FIXME: in the current setup, the dollar variable list
        // handed to the id routines are empty. We have to
        // replace dollar variables that are suddenly replacable
        // due to index changes elsewhere now
        if e.contains_dollar() {
            e.normalize_inplace(self.var_info.global_info);
            if e.replace_dollar(&self.var_info.local_info.variables)
                .contains(ReplaceResult::Replaced)
            {
                e.normalize_inplace(self.var_info.global_info);
            }
        } else {
            e.normalize_inplace(self.var_info.global_info);
        }

        StatementResult::Executed(e)
    }
}

impl IdentityStatement {
    pub fn to_iter<'a>(
        &'a self,
        input: &'a Element,
        var_info: &'a BorrowedVarInfo<'a>,
    ) -> MatchIterator<'a> {
        MatchIterator {
            hasmatch: false,
            target: input,
            m: vec![],
            used_indices: vec![],
            mode: self.mode,
            result: Element::default(),
            lhs: &self.lhs,
            rhs: &self.rhs,
            rhsp: 0,
            it: MatchKind::from_element(&self.lhs, input, &var_info),
            var_info,
        }
    }
}
