use std::mem;
use structure::{Element, Func, VarName, FUNCTION_DELTA, FUNCTION_MUL, FUNCTION_NARGS, FUNCTION_SUM};
use tools::{add_fractions, add_one, exp_fraction, mul_fractions, normalize_fraction};
use std::cmp::Ordering;
use std::ptr;

impl Element {
    // TODO: return iterator over Elements for ground level?
    pub fn apply_builtin_functions(&mut self, ground_level: bool) -> bool {
        *self = match *self {
            Element::Fn(
                _,
                Func {
                    name: ref mut n,
                    args: ref mut a,
                },
            ) => {
                match *n {
                    VarName::ID(x) if x == FUNCTION_DELTA => {
                        if a.len() == 1 {
                            match a[0] {
                                Element::Num(_, _, 0, _) => Element::Num(false, true, 1, 1),
                                _ => Element::Num(false, true, 0, 1),
                            }
                        } else {
                            return false;
                        }
                    }
                    VarName::ID(x) if x == FUNCTION_NARGS => {
                        // get the number of arguments
                        Element::Num(false, true, a.len() as u64, 1)
                    }
                    VarName::ID(x) if x == FUNCTION_SUM || x == FUNCTION_MUL => {
                        if a.len() == 4 {
                            match (&a[1], &a[2]) {
                                (&Element::Num(_, true, n1, 1), &Element::Num(_, true, n2, 1)) => {
                                    let mut terms = vec![];
                                    for i in n1..n2 {
                                        let mut ne = a[3].clone();
                                        ne.replace(&a[0], &Element::Num(false, true, i, 1));
                                        terms.push(ne);
                                    }
                                    if x == FUNCTION_SUM {
                                        Element::SubExpr(true, terms)
                                    } else {
                                        Element::Term(true, terms)
                                    }
                                }
                                _ => return false,
                            }
                        } else {
                            return false;
                        }
                    }
                    _ => {
                        return false;
                    }
                }
            }
            _ => unreachable!(),
        };
        true
    }

    pub fn normalize_inplace<'a>(&mut self) -> bool {
        let mut changed = false;
        match *self {
            Element::Num(ref mut dirty, ref mut pos, ref mut num, ref mut den) => {
                if *dirty {
                    normalize_fraction(pos, num, den);
                    *dirty = false;
                    changed = true;
                }
            }
            Element::Wildcard(_, ref mut restriction) => for x in restriction {
                changed |= x.normalize_inplace();
            },
            Element::Pow(dirty, ..) => {
                if !dirty {
                    return false;
                }

                *self = if let Element::Pow(ref mut dirty, ref mut be) = *self {
                    let (ref mut b, ref mut e) = *&mut **be;
                    changed |= b.normalize_inplace();
                    changed |= e.normalize_inplace();
                    *dirty = false;

                    // TODO: Clippy doesn't like loops that never actually loop #[warn(never_loop)]
                    loop {
                        match *e {
                            Element::Num(_, _, 0, _) => {
                                // x^0 = 1
                                break Element::Num(false, true, 1, 1);
                            }
                            Element::Num(_, true, 1, 1) => {
                                // x^1 = x
                                break mem::replace(b, DUMMY_ELEM!());
                            }
                            Element::Num(_, true, n, 1) => {
                                // exponent is a positive integer
                                // check if some simplification can be made
                                if let Element::Num(_, mut pos, mut num, mut den) = *b {
                                    // base is a rational number: (p/q)^n = p^n/q^n
                                    exp_fraction(&mut pos, &mut num, &mut den, n);
                                    break Element::Num(false, pos, num, den);
                                }
                            }
                            Element::Num(_, false, n, 1) => {
                                // exponent is a negative integer
                                if let Element::Num(_, mut pos, mut num, mut den) = *b {
                                    // base is a rational number: (p/q)^(-n) = q^n/p^n
                                    exp_fraction(&mut pos, &mut num, &mut den, n);
                                    break Element::Num(false, pos, den, num);
                                }
                            }
                            _ => {}
                        };
                        // TODO: The old code contained reduction of (x^a)^b = x^(a*b).
                        // This may be mathematically wrong, e.g.,
                        //   for x = (-1+i), a = 2, b = 3/2,
                        //   (x^a)^b = - x^(a*b).
                        // We need more conditions.
                        return changed;
                    }
                } else {
                    unreachable!();
                };
                return changed;
                /*
                *self = if let Element::Pow(ref mut dirty, ref mut b, ref mut p) = *self {
                    changed |= b.normalize_inplace();
                    changed |= p.normalize_inplace();
                    *dirty = false;

                    // x^0 = 1
                    match **p {
                        Element::Num(_, _, 0, _) => Element::Num(false, true, 1, 1),
                        Element::Num(_, true, 1, 1) => mem::replace(&mut **b, DUMMY_ELEM!()),
                        _ => {
                            // simplify numbers if exponent is a positive integer
                            let rv = if let Element::Num(_, true, n, 1) = **p {
                                if let Element::Num(_, mut pos, mut num, mut den) = **b {
                                    exp_fraction(&mut pos, &mut num, &mut den, n);
                                    Some(Element::Num(false, pos, num, den))
                                } else {
                                    None
                                }
                            } else {
                                None
                            };

                            if let Some(x) = rv {
                                x
                            } else
                            // simplify x^a^b = x^(a*b)
                            // TODO: note the nasty syntax to avoid borrow checker bug
                            if let Element::Pow(_, ref mut c, ref mut d) = *&mut **b {
                                match (&mut **p, &mut **d) {
                                    (
                                        &mut Element::Term(ref mut dirty, ref mut f),
                                        &mut Element::Term(_, ref mut f1),
                                    ) => {
                                        *dirty = true;
                                        f.append(f1);
                                    }
                                    (&mut Element::Term(ref mut dirty, ref mut f), ref mut b) => {
                                        *dirty = true;
                                        f.push(mem::replace(b, DUMMY_ELEM!()))
                                    }
                                    (a, b) => {
                                        *a = Element::Term(
                                            true,
                                            vec![
                                                mem::replace(a, DUMMY_ELEM!()),
                                                mem::replace(b, DUMMY_ELEM!()),
                                            ],
                                        );
                                    }
                                }

                                // TODO: is this the best way? can the box be avoided?
                                // can we recycle the old box and move a new pointer in there?
                                let mut res = Element::Pow(
                                    true,
                                    mem::replace(c, Box::new(DUMMY_ELEM!())),
                                    mem::replace(p, Box::new(DUMMY_ELEM!())),
                                );
                                res.normalize_inplace();
                                res
                            } else {
                                return changed;
                            }
                        }
                    }
                } else {
                    unreachable!();
                };
                changed = true;
                */
            }
            Element::Fn(dirty, _) => {
                if dirty {
                    if let Element::Fn(ref mut dirty, ref mut f) = *self {
                        for x in f.args.iter_mut() {
                            changed |= x.normalize_inplace();
                        }
                        *dirty = false; // TODO: or should this be done by builtin_functions?

                        //f.args.shrink_to_fit(); // make sure we keep memory in check
                    }
                }
                changed |= self.apply_builtin_functions(false);
            }
            Element::Term(dirty, _) => {
                if !dirty {
                    return false;
                }

                *self = if let Element::Term(ref mut dirty, ref mut ts) = *self {
                    *dirty = false;

                    // normalize factors and flatten
                    // TODO: check for 0 here
                    let mut restructure = false;
                    for x in ts.iter_mut() {
                        changed |= x.normalize_inplace();
                        if let Element::Term(..) = *x {
                            restructure = true;
                            changed = true;
                        }
                    }

                    // flatten the term
                    if restructure {
                        let mut tmp = vec![];
                        for x in ts.iter_mut() {
                            match *x {
                                Element::Term(_, ref mut tss) => tmp.append(tss),
                                _ => tmp.push(mem::replace(x, DUMMY_ELEM!())),
                            }
                        }
                        *ts = tmp;
                    }

                    // sort and merge the terms at the same time
                    if cfg!(_NO_) {
                        expr_sort(ts, merge_factors);
                    } else {
                        // TODO: this is faster than expr_sort. presumable because there are fewer
                        // merge_factor calls
                        ts.sort_unstable();

                        // now merge pows: x^a*x^b = x^(a*b)
                        // x*x^a and x*x, all should be side by side now
                        let mut lastindex = 0;

                        for i in 1..ts.len() {
                            let (a, b) = ts.split_at_mut(i);
                            if !merge_factors(&mut a[lastindex], &mut b[0]) {
                                if lastindex + 1 < i {
                                    a[lastindex + 1] = mem::replace(&mut b[0], DUMMY_ELEM!());
                                }
                                lastindex += 1;
                            }
                        }
                        ts.truncate(lastindex + 1);

                        if let Some(&Element::Num(_, pos, num, den)) = ts.last() {
                            match (pos, num, den) {
                                (_, 0, _) => ts.clear(),
                                (true, 1, 1) if ts.len() > 1 => {
                                    ts.pop();
                                } // don't add a factor
                                _ => {}
                            }
                        }
                    }

                    //ts.shrink_to_fit(); // make sure we keep memory in check

                    match ts.len() {
                        0 => Element::Num(false, true, 0, 1),
                        1 => ts.swap_remove(0), // downgrade
                        _ => return true,       // TODO: only return true when actually changed
                    }
                } else {
                    unreachable!()
                }
            }
            Element::SubExpr(dirty, _) => {
                if !dirty {
                    return false;
                }
                *self = if let Element::SubExpr(ref mut dirty, ref mut ts) = *self {
                    *dirty = false;

                    // normalize factors and flatten
                    let mut restructure = false;
                    for x in ts.iter_mut() {
                        changed |= x.normalize_inplace();
                        if let Element::SubExpr(..) = *x {
                            restructure = true;
                            changed = true;
                        }
                    }

                    // flatten the expression
                    if restructure {
                        let mut tmp = vec![];
                        for x in ts.iter_mut() {
                            match *x {
                                Element::SubExpr(_, ref mut tss) => tmp.append(tss),
                                _ => tmp.push(mem::replace(x, DUMMY_ELEM!())),
                            }
                        }
                        *ts = tmp;
                    }

                    // sort and merge the terms at the same time
                    if cfg!(_YES_) {
                        expr_sort(ts, merge_terms);
                    } else {
                        ts.sort_unstable(); // TODO: slow!
                                            // merge coefficients of similar terms
                        let mut lastindex = 0;

                        for i in 1..ts.len() {
                            let (a, b) = ts.split_at_mut(i);
                            if !merge_terms(&mut a[lastindex], &mut b[0]) {
                                if lastindex + 1 < i {
                                    a[lastindex + 1] = mem::replace(&mut b[0], DUMMY_ELEM!());
                                }
                                lastindex += 1;
                            }
                        }
                        ts.truncate(lastindex + 1);
                    }

                    match ts.len() {
                        0 => Element::Num(false, true, 0, 1),
                        1 => ts.swap_remove(0),
                        _ => return true, // TODO: only return true when actually changed
                    }
                } else {
                    unreachable!();
                }
            }
            _ => {}
        };
        changed
    }

    // bring a term to canconical form
    pub fn normalize<'a>(&self) -> Element {
        match self {
            &Element::Num(dirty, mut pos, mut num, mut den) => {
                if dirty {
                    normalize_fraction(&mut pos, &mut num, &mut den);
                }
                Element::Num(false, pos, num, den)
            }
            &Element::Wildcard(ref name, ref restriction) => {
                let mut r = vec![];
                for x in restriction {
                    r.push(x.normalize());
                }
                Element::Wildcard(name.clone(), r)
            }
            &Element::Pow(dirty, _) => {
                if !dirty {
                    return self.clone();
                }

                // What is wrong with this??? The optimizer may eliminate temporary
                // redundant/objects.
                let mut x = self.clone();
                x.normalize_inplace();
                x
                /*
                let newb = b.normalize();
                let mut newp = p.normalize();

                // x^0 = 1
                if let Element::Num(_, _, 0, _) = newp {
                    return Element::Num(false, true, 1, 1);
                }
                // return x if x^1
                if let Element::Num(_, true, 1, 1) = newp {
                    return newb;
                }

                // simplify numbers if exponent is a positive integer
                if let Element::Num(_, true, n, 1) = newp {
                    if let Element::Num(_, mut pos, mut num, mut den) = newb {
                        exp_fraction(&mut pos, &mut num, &mut den, n);
                        return Element::Num(false, pos, num, den);
                    }
                }

                // simplify x^a^b = x^(a*b)
                if let Element::Pow(_, c, d) = newb {
                    match newp {
                        Element::Term(_, ref mut f) => f.push(*d),
                        _ => newp = Element::Term(true, vec![newp.clone(), *d]).normalize(),
                    }
                    Element::Pow(false, c, Box::new(newp))
                } else {
                    Element::Pow(false, Box::new(newb), Box::new(newp))
                }
                */
            }
            &Element::Fn(dirty, ref f) => {
                if dirty {
                    let mut new_fun = Element::Fn(
                        false,
                        Func {
                            name: f.name.clone(),
                            args: f.args.iter().map(|x| x.normalize()).collect(),
                        },
                    );
                    new_fun.apply_builtin_functions(false);
                    new_fun
                } else {
                    self.clone()
                }
            }
            &Element::Term(dirty, ref ts) => {
                if !dirty {
                    // TODO: this means we have to back propagate
                    // the dirty flag if one of its factors is dirty
                    // remove this flag and just check every factor?
                    return self.clone();
                }

                let mut factors = vec![];

                // normalize factors and flatten
                for x in ts {
                    match x.normalize() {
                        Element::Term(_, ref mut tt) => factors.append(tt),
                        t => factors.push(t),
                    }
                }

                factors.sort_unstable();

                let mut lastindex = 0;
                for i in 1..factors.len() {
                    let (a, b) = factors.split_at_mut(i);
                    if !merge_factors(&mut a[lastindex], &mut b[0]) {
                        if lastindex + 1 < i {
                            a[lastindex + 1] = mem::replace(&mut b[0], DUMMY_ELEM!());
                        }
                        lastindex += 1;
                    }
                }
                factors.truncate(lastindex + 1);

                // merge the coefficients
                let mut pos = true;
                let mut num = 1;
                let mut den = 1;

                while let Some(x) = factors.pop() {
                    match x {
                        Element::Num(_, pos1, num1, den1) => {
                            mul_fractions(&mut pos, &mut num, &mut den, pos1, num1, den1)
                        }
                        _ => {
                            factors.push(x);
                            break;
                        }
                    }
                }

                match (pos, num, den) {
                    (_, 0, _) => return Element::Num(false, true, 0, 1),
                    (true, 1, 1) if factors.len() > 0 => {} // don't add a factor
                    x => factors.push(Element::Num(false, x.0, x.1, x.2)),
                }

                match factors.len() {
                    0 => Element::Num(false, true, 0, 1),
                    1 => factors.swap_remove(0), // downgrade
                    _ => Element::Term(false, factors),
                }
            }
            // TODO: drop +0?
            &Element::SubExpr(dirty, ref ts) => {
                if !dirty {
                    return self.clone();
                }
                let mut terms = vec![];

                // normalize terms and flatten
                for x in ts {
                    match x.normalize() {
                        Element::SubExpr(_, ref mut tt) => terms.append(tt),
                        t => terms.push(t),
                    }
                }
                terms.sort_unstable();

                if terms.len() == 0 {
                    return Element::SubExpr(false, terms);
                }

                // merge coefficients of similar terms
                let mut lastindex = 0;

                for i in 1..terms.len() {
                    let (a, b) = terms.split_at_mut(i);
                    if !merge_terms(&mut a[lastindex], &mut b[0]) {
                        if lastindex + 1 < i {
                            a[lastindex + 1] = mem::replace(&mut b[0], DUMMY_ELEM!());
                        }
                        lastindex += 1;
                    }
                }
                terms.truncate(lastindex + 1);

                match terms.len() {
                    0 => Element::Num(false, true, 0, 1),
                    1 => terms.swap_remove(0),
                    _ => Element::SubExpr(false, terms),
                }
            }
            &ref o => o.clone(),
        }
    }
}

// returns true if merged
pub fn merge_factors(first: &mut Element, sec: &mut Element) -> bool {
    let mut changed = false;

    if let &mut Element::Num(_, ref mut pos, ref mut num, ref mut den) = first {
        if let &mut Element::Num(_, pos1, num1, den1) = sec {
            mul_fractions(pos, num, den, pos1, num1, den1);
            return true;
        }
        return false;
    }

    if let &mut Element::Num(..) = sec {
        return false;
    }

    // x*x => x^2
    if first == sec {
        *first = Element::Pow(
            true,
            Box::new((
                mem::replace(first, DUMMY_ELEM!()),
                Element::Num(false, true, 2, 1),
            )),
        );
        first.normalize_inplace();
        return true;
    }

    // x^a*x^b = x^(a+b)
    if let &mut Element::Pow(ref mut dirty, ref mut be2) = first {
        let (ref mut b2, ref mut e2) = *&mut **be2;
        if let &mut Element::Pow(_, ref mut be1) = sec {
            let (ref b1, ref mut e1) = *&mut **be1;
            if b1 == b2 {
                match (e1, e2) {
                    // TODO: can we remove many "&mut"?
                    (
                        &mut Element::SubExpr(_, ref mut a1),
                        &mut Element::SubExpr(ref mut d2, ref mut a2),
                    ) => {
                        *d2 = true;
                        a2.append(a1)
                    }
                    (ref mut a1, &mut Element::SubExpr(ref mut d2, ref mut a2)) => {
                        *d2 = true;
                        a2.push(mem::replace(a1, DUMMY_ELEM!()))
                    }
                    (a, b) => {
                        *b = Element::SubExpr(
                            true,
                            vec![
                                mem::replace(a, DUMMY_ELEM!()),
                                mem::replace(b, DUMMY_ELEM!()),
                            ],
                        )
                    }
                }
                *dirty = true;
                changed = true;
            }
        } else if sec == b2 {
            // e2 should become e2 + 1
            // avoid borrow checker error
            let mut addone = true;
            if let Element::Num(_, ref mut pos, ref mut num, ref mut den) = *e2 {
                add_one(pos, num, den);
                addone = false;
            }
            if addone {
                *e2 = Element::SubExpr(
                    true,
                    vec![
                        mem::replace(e2, DUMMY_ELEM!()),
                        Element::Num(false, true, 1, 1),
                    ],
                );
            }

            *dirty = true;
            changed = true;
        }
    };
    first.normalize_inplace();
    changed
}

// returns true if merged
pub fn merge_terms(first: &mut Element, sec: &mut Element) -> bool {
    // filter +0
    match sec {
        &mut Element::Num(_, _, 0, _) => {
            return true;
        }
        _ => {}
    }

    match (sec, first) {
        (&mut Element::Term(_, ref mut t1), &mut Element::Term(ref mut d2, ref mut t2)) => {
            // treat the case where the term doesn't have a coefficient
            assert!(t1.len() > 0 && t2.len() > 0);

            let mut pos1;
            let mut num1;
            let mut den1;
            {
                let (mut l1, l11) = t1.split_at(t1.len() - 1);
                match l11[0] {
                    Element::Num(_, pos, num, den) => {
                        pos1 = pos;
                        num1 = num;
                        den1 = den;
                    }
                    _ => {
                        l1 = t1;
                        pos1 = true;
                        num1 = 1;
                        den1 = 1;
                    }
                }

                {
                    let l2 = match t2.last() {
                        Some(&Element::Num(..)) => &t2[..t2.len() - 1],
                        _ => &t2[..],
                    };

                    if l1 != l2 {
                        return false;
                    }
                }
            }
            t1.clear(); // remove the old data
            *d2 = false;
            // should we add the terms?
            match t2.last_mut() {
                Some(&mut Element::Num(_, ref mut pos, ref mut num, ref mut den)) => {
                    add_fractions(pos, num, den, pos1, num1, den1);
                    return true;
                }
                _ => {}
            }

            // add 1
            add_one(&mut pos1, &mut num1, &mut den1);
            t2.push(Element::Num(false, pos1, num1, den1));
            if t2.capacity() - t2.len() > 10 {
                // FIXME: what value?
                // t2.shrink_to_fit(); // make sure the term doesn't grow too much
            }
        }
        // x + x/2
        // (1+x) + (1+x)/2
        (ref a, &mut Element::Term(_, ref mut t2)) => {
            assert!(t2.len() > 0);

            if **a == t2[0] && t2.len() == 2 {
                match t2[1] {
                    Element::Num(_, ref mut pos, ref mut num, ref mut den) => {
                        add_one(pos, num, den);
                    }
                    _ => {
                        return false;
                    }
                }
            } else {
                return false;
            }
        }
        (&mut Element::Term(_, ref t2), ref mut a) => {
            assert!(t2.len() > 0);

            if **a == t2[0] && t2.len() == 2 {
                match t2[1] {
                    Element::Num(_, mut pos, mut num, mut den) => {
                        add_one(&mut pos, &mut num, &mut den);
                        **a = Element::Term(
                            false,
                            vec![
                                mem::replace(a, DUMMY_ELEM!()),
                                Element::Num(false, pos, num, den),
                            ],
                        );
                    }
                    _ => {
                        return false;
                    }
                }
            } else {
                return false;
            }
        }
        (
            &mut Element::Num(_, pos1, num1, den1),
            &mut Element::Num(_, ref mut pos, ref mut num, ref mut den),
        ) => {
            add_fractions(pos, num, den, pos1, num1, den1);
        }
        (ref a1, ref mut a2) if a1 == a2 => {
            **a2 = Element::Term(
                false,
                vec![
                    mem::replace(a2, DUMMY_ELEM!()),
                    Element::Num(false, true, 2, 1),
                ],
            )
        }
        _ => return false,
    }

    true
}

// returns true if a and b should be swapped
pub fn expr_sort<'a, T: PartialOrd, F>(a: &mut Vec<T>, merger: F)
where
    F: Fn(&mut T, &mut T) -> bool,
{
    if a.len() == 0 {
        return;
    }

    // also count ascending runs and reverse them!
    let mut grouplen = vec![];
    let mut groupcount = 1;
    let mut writepos = 1;
    let mut ascenddescendmode = 0; // 0: no direction, 1: desc, 2: asc
    for x in 1..a.len() {
        {
            let (old, new) = a.split_at_mut(x);
            if merger(&mut old[writepos - 1], &mut new[0]) {
                continue;
            }
        }

        a.swap(writepos, x);
        writepos += 1;

        match a[writepos - 2].partial_cmp(&a[writepos - 1]) {
            Some(Ordering::Greater) => {
                if ascenddescendmode == 1 {
                    grouplen.push(groupcount);
                    ascenddescendmode = 0;
                    groupcount = 1;
                } else {
                    if ascenddescendmode == 0 {
                        ascenddescendmode = 2;
                    }
                    groupcount += 1;
                }
            }
            _ => {
                if ascenddescendmode == 2 {
                    // TODO: first check if the reversed array can join the last group?
                    grouplen.push(groupcount);
                    // change direction of last group, problem: writepos not included in this array
                    // yet..
                    a[writepos - groupcount - 1..writepos - 1].reverse();
                    ascenddescendmode = 0;
                    groupcount = 1;
                } else {
                    if ascenddescendmode == 0 {
                        ascenddescendmode = 1;
                    }
                    groupcount += 1;
                }
            }
        }
    }

    // reverse last group if ascending
    if ascenddescendmode == 2 {
        a[writepos - groupcount..writepos].reverse();
    }

    a.truncate(writepos);

    // allocate buffer, TODO: could be half the size
    let mut b: Vec<T> = Vec::with_capacity(a.len());
    grouplen.push(groupcount);

    //a.shrink_to_fit(); // slow!
    //b.shrink_to_fit();

    // Make successively longer sorted runs until whole array is sorted.
    while grouplen.len() > 1 {
        let mut groupcount = 0;
        let mut startpos = 0;
        let mut writepos = a.as_mut_ptr();
        while groupcount * 2 < grouplen.len() {
            let newsize;
            unsafe {
                if groupcount * 2 + 1 == grouplen.len() {
                    // odd number?
                    newsize = sub_merge_sort(
                        a,
                        startpos,
                        startpos + grouplen[groupcount * 2],
                        startpos + grouplen[groupcount * 2],
                        &mut b,
                        writepos,
                        &merger,
                    );
                } else {
                    newsize = sub_merge_sort(
                        a,
                        startpos,
                        startpos + grouplen[groupcount * 2],
                        startpos + grouplen[groupcount * 2] + grouplen[groupcount * 2 + 1],
                        &mut b,
                        writepos,
                        &merger,
                    );
                    startpos += grouplen[groupcount * 2] + grouplen[groupcount * 2 + 1];
                }

                writepos = writepos.offset(newsize as isize);
            }
            grouplen[groupcount] = newsize;
            groupcount += 1;
        }

        grouplen.truncate(groupcount);
        unsafe {
            a.set_len(*grouplen.last().unwrap());
        } // don't drop, but resize
    }
}

unsafe fn sub_merge_sort<T: PartialOrd, F>(
    a: &mut [T],
    left: usize,
    right: usize,
    end: usize,
    buf: &mut [T],
    mut writepos: *mut T,
    merger: &F,
) -> usize
where
    F: Fn(&mut T, &mut T) -> bool,
{
    let mut i = left;
    let mut j = right;
    let mut lastsource = 0; // 0: none, 1: left, 2: right
    let origwritepos = writepos;

    // copy left part to array
    let mut leftp = buf.as_mut_ptr();
    let mut rightp = a.get_unchecked_mut(right) as *mut T;

    ptr::copy_nonoverlapping(&a[left], buf.as_mut_ptr(), right - left);

    while i < right || j < end {
        if i < right && j < end {
            match (*leftp).partial_cmp(&*rightp) {
                Some(Ordering::Greater) => {
                    if lastsource != 1 || !merger(&mut *writepos.offset(-1), &mut *rightp) {
                        // FIXME: it should drop at writep! does this cause leaks?
                        assert!(writepos != rightp);
                        ptr::copy_nonoverlapping(rightp, writepos, 1);
                        writepos = writepos.offset(1);
                        lastsource = 2;
                    }
                    j += 1;
                    rightp = rightp.offset(1);
                }
                // TODO: special case if they are equal/mergeable
                _ => {
                    if lastsource != 2 || !merger(&mut *writepos.offset(-1), &mut *leftp) {
                        ptr::copy_nonoverlapping(leftp, writepos, 1);
                        writepos = writepos.offset(1);
                        lastsource = 1;
                    }
                    i += 1;
                    leftp = leftp.offset(1);
                }
            }
        } else {
            if i < right {
                if lastsource != 2 || !merger(&mut *writepos.offset(-1), &mut *leftp) {
                    ptr::copy_nonoverlapping(leftp, writepos, 1);
                    writepos = writepos.offset(1);
                    lastsource = 1;
                }
                i += 1;
                leftp = leftp.offset(1);
            } else {
                if lastsource != 1 || !merger(&mut *writepos.offset(-1), &mut *rightp) {
                    assert!(writepos != rightp);
                    ptr::copy_nonoverlapping(rightp, writepos, 1);
                    writepos = writepos.offset(1);
                    lastsource = 2;
                }
                j += 1;
                rightp = rightp.offset(1);
            }
        }
    }

    writepos as usize - origwritepos as usize
}
