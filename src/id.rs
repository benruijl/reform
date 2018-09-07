use num_traits::One;
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

/// Stores which wildcards map to which element, and stores which parts
/// of the term have matched.
#[derive(Debug, Clone)]
pub struct MatchObject<'a> {
    wildcard_map: Vec<(VarName, MatchOpt<'a>)>,
    rhs_map: Vec<*const Element>, // store pointers to Elements that need to be removed
}

impl<'a> MatchObject<'a> {
    pub fn new() -> MatchObject<'a> {
        MatchObject {
            wildcard_map: vec![],
            rhs_map: vec![],
        }
    }

    // push something to the match object, keeping track of the old length
    // returns None when there is a conflict.
    fn push_match(&mut self, k: VarName, v: &'a Element) -> Option<usize> {
        for &(rk, ref rv) in self.wildcard_map.iter() {
            if rk == k {
                match *rv {
                    MatchOpt::Single(ref vv) if *v == **vv => return Some(self.wildcard_map.len()),
                    MatchOpt::SingleOwned(ref vv) if v == vv => {
                        return Some(self.wildcard_map.len())
                    }
                    _ => return None,
                }
            }
        }

        self.wildcard_map.push((k, MatchOpt::Single(v)));
        Some(self.wildcard_map.len() - 1)
    }

    // push something to the match object, keeping track of the old length
    fn push_match_owned(&mut self, k: VarName, v: Element) -> Option<usize> {
        for &(rk, ref rv) in self.wildcard_map.iter() {
            if rk == k {
                match *rv {
                    MatchOpt::Single(ref vv) if v == **vv => return Some(self.wildcard_map.len()),
                    MatchOpt::SingleOwned(ref vv) if v == *vv => {
                        return Some(self.wildcard_map.len())
                    }
                    _ => return None,
                }
            }
        }

        self.wildcard_map.push((k, MatchOpt::SingleOwned(v)));
        Some(self.wildcard_map.len() - 1)
    }

    // push something to the match object, keeping track of the old length
    fn push_match_slice(&mut self, k: VarName, v: &'a [Element]) -> Option<usize> {
        for &(rk, ref rv) in self.wildcard_map.iter() {
            if rk == k {
                match *rv {
                    MatchOpt::Multiple(vv) if *v == *vv => return Some(self.wildcard_map.len()),
                    _ => return None,
                }
            }
        }

        self.wildcard_map.push((k, MatchOpt::Multiple(v)));
        Some(self.wildcard_map.len() - 1)
    }

    fn find_match<'b>(&'b self, k: VarName) -> Option<&'b MatchOpt<'a>> {
        for &(rk, ref rv) in &self.wildcard_map {
            if rk == k {
                return Some(rv);
            }
        }
        None
    }

    #[inline]
    fn truncate(&mut self, newlen: usize) {
        self.wildcard_map.truncate(newlen);
    }

    #[inline]
    fn len(&self) -> usize {
        self.wildcard_map.len()
    }

    /// Push a matched element if it is not already there
    #[inline]
    fn push_matched_element(&mut self, e: &'a Element) {
        // FIXME: check is a bit expensive
        if !self.rhs_map.contains(&(e as *const _)) {
            self.rhs_map.push(e);
        }
    }

    #[inline]
    fn pop_matched_element(&mut self) {
        self.rhs_map.pop();
    }
}

impl Element {
    pub fn strip_from<'a>(&self, m: &MatchObject<'a>) -> Option<Element> {
        // check if element should be removed
        if m.rhs_map.contains(&(self as *const _)) {
            match self {
                Element::Var(b, e) => {
                    return Some(Element::Var(*b, e.clone() - Number::one()));
                }
                _ => return None,
            }
        }

        match self {
            Element::Term(dirty, f) => Some(Element::Term(
                *dirty,
                f.iter().filter_map(|x| x.strip_from(m)).collect(),
            )),
            Element::SubExpr(dirty, f) => Some(Element::SubExpr(
                *dirty,
                f.iter().filter_map(|x| x.strip_from(m)).collect(),
            )),
            _ => Some(self.clone()),
        }
    }

    /// Apply a mapping of wildcards to a function argument.
    pub fn apply_map<'a>(&self, m: &MatchObject<'a>) -> MatchOptOwned {
        match *self {
            Element::VariableArgument(ref name) | Element::Wildcard(ref name, ..) => m
                .find_match(*name)
                .expect("Unknown wildcard in rhs")
                .to_owned(),
            Element::FnWildcard(ref name, ref b) => {
                let (ref restrictions, ref old_args) = **b;

                if restrictions.len() > 0 {
                    panic!("No restrictions allowed in the rhs");
                }

                let newname = match m
                    .find_match(*name)
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
    Once(&'a Element),             // matching without wildcard, ie number vs number
    OnceMatch(&'a VarName, &'a Element), // simple match of variable
    VarPowerMatch(
        VarName,
        &'a Number,
        &'a Element,
        &'a Element,
        &'a BorrowedVarInfo<'a>,
    ), // match a variable x^n to x?^y?
    SeqIt(Vec<&'a Element>, SequenceIter<'a>), // target and iterator
    None(bool, bool),              // pop flags
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
            ElementIterSingle::None(pop_wildcard_match, pop_match) => {
                if pop_wildcard_match {
                    m.wildcard_map.pop();
                }
                if pop_match {
                    m.pop_matched_element();
                }
                None
            }
            ElementIterSingle::Once(..) => {
                match mem::replace(self, ElementIterSingle::None(false, true)) {
                    ElementIterSingle::Once(elem) => {
                        m.push_matched_element(elem);
                        Some(m.len())
                    }
                    _ => unreachable!(),
                }
            }
            ElementIterSingle::OnceMatch(_, _) => {
                match mem::replace(self, ElementIterSingle::None(false, false)) {
                    ElementIterSingle::OnceMatch(name, target) => match m.push_match(*name, target)
                    {
                        Some(l1) => {
                            m.push_matched_element(target);
                            mem::replace(self, ElementIterSingle::None(true, true));
                            return Some(l1);
                        }
                        None => None,
                    },
                    _ => unreachable!(),
                }
            }
            ElementIterSingle::VarPowerMatch(..) => {
                match mem::replace(self, ElementIterSingle::None(false, false)) {
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
                                            match m.push_match_owned(*vn, r.clone()) {
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
                                    match m.push_match_owned(*vn, r.clone()) {
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
                                                match m.push_match_owned(*vn, r1) {
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
                                            match m.push_match_owned(*vn, r1) {
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
                                    match m.push_match_owned(*vn, r1) {
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
                    _ => panic!(), // never reached
                }
            }
            ElementIterSingle::FnIter(ref mut f) => f.next(m),
            ElementIterSingle::FnWildcardIter(name, ref target, ref mut old_len, ref mut f) => {
                if *old_len == MAXMATCH {
                    match m.push_match_owned(*name, target.clone()) {
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
            ElementIterSingle::SymFnWildcardIter(name, ref target, ref mut old_len, ref mut f) => {
                if *old_len == MAXMATCH {
                    // TOOD: m.push_matched_element(), needs original target
                    match m.push_match_owned(*name, target.clone()) {
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
                        // TODO: m.pop_matched_element();
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

                if let Some(&MatchOpt::Multiple(v)) = m.find_match(*name) {
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
                    match m.push_match_slice(*name, f) {
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
                // match x^x1? to x^2
                // on level 0, also match x to x^n
                let (ref b2, ref e2) = **be2;

                if level == 0 {
                    if let Element::Num(false, Number::SmallInt(1)) = e2 {
                        return ElementIterSingle::OnceMatch(i1, b2);
                    }
                }

                ElementIterSingle::VarPowerMatch(*i1, e1, b2, e2, var_info)
            }
            (&Element::Pow(_, ref be1), &Element::Pow(_, ref be2)) => {
                let (ref b1, ref e1) = **be1;
                let (ref b2, ref e2) = **be2;
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
                    target,
                    name,
                    inds,
                    var_info,
                    level + 1,
                ))
            }
            (i1, d @ &Element::Dollar(..)) => {
                if var_info.local_info.get_dollar(d) == Some(i1) {
                    ElementIterSingle::Once(d)
                } else {
                    ElementIterSingle::None(false, false)
                }
            }
            (&Element::Var(ref i1, ref e1), &Element::Var(ref i2, ref e2))
                if i1 == i2 && (level == 0 || e1 == e2) =>
            {
                ElementIterSingle::Once(target)
            }
            (&Element::Num(_, ref n1), &Element::Num(_, ref n2)) if n1 == n2 => {
                ElementIterSingle::Once(target)
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

                ElementIterSingle::None(false, false)
            }
            (_, &Element::Wildcard(ref i2, ref rest)) => {
                if rest.is_empty() || rest.contains(target) {
                    ElementIterSingle::OnceMatch(i2, target)
                } else {
                    ElementIterSingle::None(false, false)
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
                    name2, args2, target, name1, args1, var_info, level,
                ))
            }
            (&Element::Fn(_, ref name1, ref args1), &Element::FnWildcard(ref name2, ref b)) => {
                let (restrictions, args2) = &**b;

                if restrictions.len() > 0
                    && !restrictions.contains(&Element::Var(*name1, Number::one()))
                {
                    ElementIterSingle::None(false, false)
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
                        FuncIterator::from_element(
                            name1, args2, target, name1, args1, var_info, level,
                        ),
                    )
                }
            }
            (&Element::Term(_, ref f1), &Element::Term(_, ref f2))
            | (&Element::SubExpr(_, ref f1), &Element::SubExpr(_, ref f2)) => {
                if f1.len() == f2.len() {
                    // TODO: increase the level by 1 in case of a subexpr?
                    ElementIterSingle::PermIter(SubSequenceIter::new(f2, f1, var_info, level))
                } else {
                    ElementIterSingle::None(false, false)
                }
            }
            _ => ElementIterSingle::None(false, false),
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
    target: &'a Element,
    level: usize,
}

impl<'a> FuncIterator<'a> {
    fn from_element(
        name: &'a VarName,
        args: &'a Vec<Element>,
        target: &'a Element,
        target_name: &'a VarName,
        target_args: &'a Vec<Element>,
        var_info: &'a BorrowedVarInfo<'a>,
        level: usize,
    ) -> FuncIterator<'a> {
        if name != target_name {
            return FuncIterator {
                args: args,
                target,
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
                target,
                iterators: vec![],
                matches: vec![],
                var_info,
                level,
            };
        };
        if varargcount == 0 && args.len() != target_args.len() {
            return FuncIterator {
                args: args,
                target,
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
                target,
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
            target,
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

        // note: this will add only once
        m.push_matched_element(self.target);

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

        m.pop_matched_element();
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
            .map(|_| ElementIterSingle::None(false, false))
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
                .map(|_| ElementIterSingle::None(false, false))
                .collect(),
            matches: vec![MAXMATCH; pattern.len()],
            indices: vec![0; pattern.len()],
            target: target,
            var_info,
            initialized: false,
            level,
        }
    }

    fn next(&mut self, m: &mut MatchObject<'a>) -> Option<(Vec<usize>, usize)> {
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
                    return Some((self.indices.clone(), self.matches[i]));
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
        // TODO: remove the distinction and use level=0 to allow for subsequence matches
        match (pattern, target) {
            (&Element::Term(_, ref x), &Element::Term(_, ref y)) => {
                MatchKind::Many(SubSequenceIter::new(x, y, var_info, 0))
            }
            (a, &Element::Term(_, ref y)) => {
                MatchKind::SinglePat(a, ElementIterSingle::None(false, false), y, 0, var_info)
            }
            (a, b) => MatchKind::Single(a.to_iter_single(b, var_info, 0)),
        }
    }

    pub fn next(&mut self, m: &mut MatchObject<'a>) -> Option<(Vec<usize>)> {
        match *self {
            MatchKind::Single(ref mut x) => x.next(m).map(|_| vec![]),
            MatchKind::Many(ref mut x) => x.next(m).map(|(indices, _)| (indices)),
            MatchKind::SinglePat(pat, ref mut it, target, ref mut index, var_info) => loop {
                if it.next(m).is_some() {
                    return Some(vec![*index - 1]);
                }

                if *index == target.len() {
                    return None;
                }
                *it = pat.to_iter_single(&target[*index], var_info, 0);
                *index += 1;
            },
            MatchKind::None => None,
        }
    }
}

#[derive(Debug)]
pub struct MatchIterator<'a> {
    mode: IdentityStatementMode,
    rhs: &'a Element,
    target: &'a Element,
    m: MatchObject<'a>,
    remaining: Vec<usize>,
    it: MatchKind<'a>,
    rhsp: usize, // current rhs index,
    hasmatch: bool,
    var_info: &'a BorrowedVarInfo<'a>,
}

// iterate over the output terms of a match
impl<'a> MatchIterator<'a> {
    pub fn generate_rhs(&mut self, rhs: &Element) -> Element {
        let mut res = match self.target.strip_from(&self.m) {
            Some(mut x) => {
                if let Element::Term(ref mut dirty, ref mut fs) = x {
                    fs.push(rhs.apply_map(&self.m).into_single().0);
                    *dirty = true;
                }

                if let Element::Term(..) = x {
                    x
                } else {
                    Element::Term(true, vec![x, rhs.apply_map(&self.m).into_single().0])
                }
            }
            None => rhs.apply_map(&self.m).into_single().0,
        };

        // FIXME: in the current setup, the dollar variable list
        // handed to the id routines are empty. We have to
        // replace dollar varialbes that are suddenly replacable
        // due to index changes elsewhere now
        if res.contains_dollar() {
            res.normalize_inplace(self.var_info.global_info);
            if res
                .replace_dollar(&self.var_info.local_info.variables)
                .contains(ReplaceResult::Replaced)
            {
                res.normalize_inplace(self.var_info.global_info);
            }
        } else {
            res.normalize_inplace(self.var_info.global_info);
        }
        res
    }

    pub fn next(&mut self) -> StatementResult<Element> {
        if self.rhsp == 0 {
            match self.it.next(&mut self.m) {
                Some(rem) => {
                    if self.mode != IdentityStatementMode::All {
                        self.it = MatchKind::None;
                    }

                    self.remaining = rem;
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
                let i = self.rhsp;
                let res = self.generate_rhs(&x[i]);

                self.rhsp += 1;
                if self.rhsp == x.len() {
                    self.rhsp = 0;
                }
                res
            }
            x => self.generate_rhs(x),
        })
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
            m: MatchObject::new(),
            remaining: vec![],
            mode: self.mode.clone(),
            rhs: &self.rhs,
            rhsp: 0,
            it: MatchKind::from_element(&self.lhs, input, &var_info),
            var_info,
        }
    }
}

fn printmatch<'a>(m: &MatchObject<'a>) {
    debug!("MATCH: [ ");

    for &(k, ref v) in m.wildcard_map.iter() {
        debug!("{}={};", k, v);
    }
    debug!("]");
}
