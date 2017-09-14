use std::mem;
use structure::{Element,Func,VarName,FUNCTION_DELTA,FUNCTION_NARGS};
use tools::{mul_fractions,add_fractions,add_one,normalize_fraction,exp_fraction};

impl Element {
    // TODO: return iterator over Elements for ground level?
    pub fn apply_builtin_functions(&mut self, ground_level: bool) -> bool {
        *self = match *self {
            Element::Fn(_, Func { name: ref mut n, args: ref mut a } ) => {
                match *n {
                    VarName::ID(x) if x == FUNCTION_DELTA => {
                        if a.len() == 1 {
                            match a[0] {
                                Element::Num(_, _, 0, _) => Element::Num(false, true,1,1),
                                _ =>  Element::Num(false, true,0,1)
                            }
                        } else {
                            return false;
                        }
                    },
                    VarName::ID(x) if x == FUNCTION_NARGS => {
                        // get the number of arguments
                        Element::Num(false, true, a.len() as u64, 1)
                    }
                    _ => { return false; }
                }
            },
            _ => { unreachable!(); }
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
            },
            Element::Wildcard(_, ref mut restriction) => {
                for x in restriction {
                    changed |= x.normalize_inplace();
                }
            },
            Element::Pow(dirty, ..) => {
                if !dirty {
                    return false
                }

                *self = if let Element::Pow(ref mut dirty, ref mut b, ref mut p) = *self {
                    changed |= b.normalize_inplace();
                    changed |= p.normalize_inplace();
                    *dirty = false;

                    // x^0 = 1
                    match **p {
                        Element::Num(_,_, 0, _) => Element::Num(false, true, 1, 1),
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
                            }  else {
                                    None
                            };

                            if let Some(x) = rv {
                                x
                            } else {
                                // simplify x^a^b = x^(a*b)
                                // TODO: note the nasty syntax to avoid borrow checker bug
                                if let Element::Pow(_, ref mut c, ref mut d) = *&mut **b {
                                    match (&mut **p, &mut **d) {
                                        (&mut Element::Term(ref mut dirty, ref mut f), &mut Element::Term(_, ref mut f1)) => {*dirty = true; f.append(f1);},
                                        (&mut Element::Term(ref mut dirty, ref mut f), ref mut b) => {*dirty = true; f.push(mem::replace(b, DUMMY_ELEM!()))},
                                        (a,b) => { *a = 
                                            Element::Term(true, vec![mem::replace(a, DUMMY_ELEM!()), 
                                                mem::replace(b, DUMMY_ELEM!())]);
                                            }
                                    }

                                    // TODO: is this the best way? can the box be avoided?
                                    // can we recycle the old box and move a new pointer in there?
                                    let mut res = Element::Pow(true, mem::replace(c, Box::new(DUMMY_ELEM!())),
                                        mem::replace(p, Box::new(DUMMY_ELEM!())));
                                    res.normalize_inplace();
                                    res
                                } else {
                                    return changed;
                                }
                            }
                        }
                    }
                } else {
                    unreachable!();
                };
                changed = true;
            },
            Element::Fn(dirty, _) => {
                if dirty {
                    if let Element::Fn(ref mut dirty, ref mut f) = *self {
                        for x in f.args.iter_mut() {
                            changed |= x.normalize_inplace();   
                        }
                        *dirty = false; // TODO: or should this be done by builtin_functions?
                    }
                }
                changed |= self.apply_builtin_functions(false);  
            },
            Element::Term(dirty, _) => {
                if !dirty {
                    return false;
                }

                *self = if let Element::Term(ref mut dirty, ref mut ts) = *self {
                    *dirty = false;

                    // normalize factors and flatten
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
                                _ => tmp.push(mem::replace(x, DUMMY_ELEM!()))
                            }
                        }
                        *ts = tmp;
                    }

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

                    // merge the coefficients
                    let mut pos = true;
                    let mut num = 1;
                    let mut den = 1;

                    while let Some(x) = ts.pop() {
                        match x {
                            Element::Num(_,pos1,num1,den1) => mul_fractions(&mut pos, &mut num,&mut den,pos1,num1,den1),
                            _ => { ts.push(x); break; }
                        }
                    }

                    match (pos, num, den) {
                        (_, 0, _) => ts.clear(),
                        (true, 1, 1) if ts.len() > 0 => {}, // don't add a factor
                        x => ts.push(Element::Num(false, x.0, x.1, x.2))
                    }

                    match ts.len() {
                        0 => Element::Num(false, true, 0, 1),
                        1 => ts.swap_remove(0), // downgrade
                        _ => return false
                    }
                } else {
                    unreachable!()
                }
            },
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
                                _ => tmp.push(mem::replace(x, DUMMY_ELEM!()))
                            }
                        }
                        *ts = tmp;
                    }

                // normalize neighbouring terms on the first iteration
                // this may merge some terms
                // then sort, and do it again
                for _ in 0..1 {
                    ts.sort_unstable(); // TODO: slow!
                    // merge coefficients of similar terms
                    let mut lastindex = 0;

                    for i in 1..ts.len() {
                        let (a, b) = ts.split_at_mut(i);
                        if !merge_terms(&mut a[lastindex], &b[0]) {
                            if lastindex + 1 < i {
                                a[lastindex + 1] = mem::replace(&mut b[0], DUMMY_ELEM!());
                            }
                            lastindex += 1;
                        }
                    }
                    ts.truncate(lastindex + 1);

                    
                }

                match ts.len() {
                    0 => Element::Num(false, true,0,1),
                    1 => ts.swap_remove(0),
                    _ => return true
                }
                } else {
                    unreachable!();
                }

            },
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
            },
            &Element::Wildcard(ref name, ref restriction) => {
                let mut r = vec![];
                for x in restriction {
                    r.push(x.normalize());
                }
                Element::Wildcard(name.clone(), r)
            },
            &Element::Pow(dirty, ref b, ref p) => {
                if !dirty {
                    return self.clone();
                }

                let newb = b.normalize();
                let mut newp = p.normalize();

                // x^0 = 1
                if let Element::Num(_,_, 0, _) = newp {
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
                        _ => newp = Element::Term(true, vec![newp.clone(), *d]).normalize()
                    }
                    Element::Pow(false, c, Box::new(newp))
                } else {
                    Element::Pow(false, Box::new(newb), Box::new(newp))
                }
            },
            &Element::Fn(dirty, ref f) => {
                if dirty {
                    let mut new_fun = Element::Fn(false, 
                        Func { name: f.name.clone(), args: f.args.iter().map(|x| x.normalize()).collect() });
                    new_fun.apply_builtin_functions(false);
                    new_fun
                } else {
                    self.clone()
                }
            },
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
                        t => factors.push(t)
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
                        Element::Num(_,pos1,num1,den1) => mul_fractions(&mut pos, &mut num,&mut den,pos1,num1,den1),
                        _ => { factors.push(x); break; }
                    }
                }

                match (pos, num, den) {
                    (_, 0, _) => return Element::Num(false, true, 0, 1),
                    (true, 1, 1) if factors.len() > 0 => {}, // don't add a factor
                    x => factors.push(Element::Num(false, x.0, x.1, x.2))
                }

                match factors.len() {
                    0 => Element::Num(false, true, 0, 1),
                    1 => factors.swap_remove(0), // downgrade
                    _ => Element::Term(false, factors)
                }
            },
            // TODO: drop +0?
            &Element::SubExpr(dirty, ref ts) => {
                if !dirty {
                    return self.clone()
                }    
                let mut terms = vec![];

                // normalize terms and flatten
                for x in ts {
                    match x.normalize() {
                        Element::SubExpr(_, ref mut tt) => terms.append(tt),
                        t => terms.push(t)
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
                    if !merge_terms(&mut a[lastindex], &b[0]) {
                        if lastindex + 1 < i {
                            a[lastindex + 1] = mem::replace(&mut b[0], DUMMY_ELEM!());
                        }
                        lastindex += 1;
                    }
                }
                terms.truncate(lastindex + 1);

                match terms.len() {
                    0 => Element::Num(false, true,0,1),
                    1 => terms.swap_remove(0),
                    _ => Element::SubExpr(false, terms)
                }
            },
            &ref o => o.clone() 
        }
    }
}

// returns true if merged
pub fn merge_factors(first: &mut Element, sec: &mut Element) -> bool {
    let mut changed = false;

    // x*x => x^2
    if first == sec {
        *first = Element::Pow(true, Box::new(mem::replace(first, DUMMY_ELEM!())), 
            Box::new(Element::Num(false,true,2,1)));
        first.normalize_inplace();
        return true;
    }

    // x^a*x^b = x^(a+b)
    if let &mut Element::Pow(ref mut dirty, ref mut b2, ref mut e2) = first {
        if let &mut Element::Pow(_, ref b1, ref mut e1) = sec {
            if b1 == b2 {
                match (&mut **e1, &mut **e2) {
                    (&mut Element::SubExpr(_, ref mut a1), &mut Element::SubExpr(ref mut d2, ref mut a2)) => {*d2 = true; a2.append(a1)},
                    (ref mut a1, &mut Element::SubExpr(ref mut d2, ref mut a2)) => {*d2 = true; a2.push(mem::replace(*a1, DUMMY_ELEM!()))},
                    (ref mut a, ref mut b) => **b = Element::SubExpr(true, vec![mem::replace(a, DUMMY_ELEM!()), mem::replace(b, DUMMY_ELEM!())])
                }
                *dirty = true;
                changed = true;
            }
        } else {
            if *sec == **b2 {
                // e2 should become e2 + 1
                // avoid borrow checker error
                let mut addone = true;
                if let &mut Element::Num(_, ref mut pos, ref mut num, ref mut den) = &mut **e2 {
                    add_one(pos, num, den);
                    addone = false;
                }
                if addone {
                    **e2 = Element::SubExpr(true, vec![
                        mem::replace(e2, DUMMY_ELEM!()),
                        Element::Num(false,true,1,1)]);
                }
                
                *dirty = true;
                changed = true;
            }
        }
    };
    first.normalize_inplace();
    changed
}

// returns true if merged
pub fn merge_terms(first: &mut Element, sec: &Element) -> bool {
    // filter +0
    // TODO: also filter from unnormalized term
    match sec {
        &Element::Num(_, _, 0, _) => { return true; },
        _ => {}
    }

    match (sec, first) {
        (&Element::Term(_,ref t1), &mut Element::Term(ref mut d2, ref mut t2)) => {
            // treat the case where the term doesn't have a coefficient
            assert!(t1.len() > 0 && t2.len() > 0);

            let mut pos1;
            let mut num1;
            let mut den1;
            let (mut l1, l11) = t1.split_at(t1.len() - 1);
            match l11[0] {
                Element::Num(_, pos,num,den) => { pos1 = pos; num1 = num; den1 = den; },
                _ => { l1 = t1; pos1 = true; num1 = 1; den1 = 1; }
            }

            {
                let l2 = match t2.last() {
                    Some(&Element::Num(..)) => &t2[..t2.len() - 1],
                    _ => &t2[..]
                };

                if l1 != l2 { return false; }
            }

            *d2 = false;
            // should we add the terms?
            match t2.last_mut() {
                Some(&mut Element::Num(_,ref mut pos, ref mut num, ref mut den)) => 
                    {
                        add_fractions(pos, num, den, pos1, num1, den1);
                        return true
                    },
                _ => {}
            }

            // add 1
            add_one(&mut pos1, &mut num1, &mut den1);
            t2.push(Element::Num(false, pos1, num1 ,den1));
        },
        // x + x/2
        // (1+x) + (1+x)/2
        (ref a, &mut Element::Term(_, ref mut t2)) => {
            assert!(t2.len() > 0);

            if **a == t2[0] && t2.len() == 2 {
                match t2[1] {
                    Element::Num(_, ref mut pos, ref mut num, ref mut den) => { add_one(pos, num, den); },
                    _ => { return false; }
                }
            } else {
                return false;
            }
        },
        (&Element::Term(_, ref t2), ref mut a) => {          
            assert!(t2.len() > 0);

            if **a == t2[0] && t2.len() == 2 {
                match t2[1] {
                    Element::Num(_, mut pos, mut num, mut den) => {
                        add_one(&mut pos, &mut num, &mut den);
                        **a = Element::Term(false, vec![mem::replace(a, DUMMY_ELEM!()), Element::Num(false, pos, num, den)]);
                    },
                    _ => { return false; }
                }
            } else {
                return false;
            }
        },
        (&Element::Num(_, pos1, num1, den1), 
            &mut Element::Num(_, ref mut pos, ref mut num, ref mut den)) => {
            add_fractions(pos, num, den, pos1, num1, den1);
        },
        (ref a1, ref mut a2) if a1 == a2 => { 
                **a2 = Element::Term(false, vec![mem::replace(a2, DUMMY_ELEM!()), Element::Num(false, true, 2, 1)] ) 
            },
        _ => {return false}
    }

    true
}
