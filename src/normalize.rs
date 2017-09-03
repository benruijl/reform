use std::mem;
use structure::{Element,Func};
use tools::{mul_fractions,add_fractions,add_one,normalize_fraction,exp_fraction};

impl Element {
    // TODO: return iterator over Elements for ground level?
    // TODO: in-place?
    // FIXME: shouldn't the dirty flag be enabled in general?
    pub fn apply_builtin_functions(&self, ground_level: bool) -> Element {
        match self {
            &Element::Fn(_, Func { name: ref n, args: ref a } ) => {
                match n.as_str() {
                    "delta_" => {
                        if a.len() == 1 {
                            match a[0] {
                                Element::Num(_, _, 0, _) => Element::Num(false, true,1,1),
                                _ =>  Element::Num(false, true,0,1)
                            }
                        } else {
                            self.clone()
                        }
                    },
                    "nargs_" => {
                        // get the number of arguments
                        Element::Num(false, true, a.len() as u64, 1)
                    }
                    _ =>
                        Element::Fn(false, 
                        Func { name: n.clone(), args: a.iter().map(|x| x.apply_builtin_functions(false)).collect()})
                }
            },
            &Element::Term(_, ref fs) => Element::Term(false, fs.iter().map(|x| x.apply_builtin_functions(false)).collect()),
            &Element::SubExpr(_, ref ts) => Element::SubExpr(false, ts.iter().map(|x| x.apply_builtin_functions(false)).collect()),
            _ => self.clone()
         }
    }

    // bring a term to canconical form
    // TODO: in-place?
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
                    Element::Fn(false, f.normalize())
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
                flatten_and_normalize_term(ts, &mut factors);
                factors.sort();

                // create pows from terms that are the same
                // they may not be side to side...
                // first, find side-by-side factors
                let mut samecount = 1;
                let mut newfactors = vec![];

                for x in factors.windows(2) {
                    // do not treat numbers
                    //if let Element::Num(..) = x[0] {
                    //    newfactors.push(x[0].clone());
                    //    samecount = 1;
                    //}
                    if x[0] == x[1] {
                        samecount += 1;
                    } else {
                        if samecount > 1 {
                            newfactors.push(Element::Pow(true,
                                Box::new(x[0].clone()), 
                                Box::new(Element::Num(false, true, samecount, 1))).normalize());
                        } else {
                            newfactors.push(x[0].clone());
                        }
                        samecount = 1;
                    }
                }

                if let Some(x) = factors.last() {
                    if samecount > 1 {
                        newfactors.push(Element::Pow(true,
                            Box::new(x.clone()), 
                            Box::new(Element::Num(false, true, samecount, 1))).normalize());
                    } else {
                        newfactors.push(x.clone());
                    }
                }

                if newfactors.len() != factors.len() {
                    newfactors.sort(); // FIXME: costly
                }

                // FIXME: the case x*x^a is not supported yet
                factors = newfactors;

                // now merge pows: x^a*x^b = x^(a*b)
                // should be side by side
                let mut newfac2 = vec![];
                match factors.first() {
                    Some(x) => newfac2.push(x.clone()),
                    _ => {}
                }

                for x in factors.iter().skip(1) {
                    let mut add = true;
                    if let &Element::Pow(_, ref b1, ref e1) = x {
                        if let &mut Element::Pow(ref mut dirty, ref mut b2, ref mut e2) = newfac2.last_mut().unwrap() {
                            if b1 == b2 {
                                match (&**e1, &mut **e2) {
                                    (&Element::Term(_, ref a1), &mut Element::Term(ref mut d2, ref mut a2)) => {*d2 = true; a2.extend(a1.clone())},
                                    (ref a1, &mut Element::Term(ref mut d2, ref mut a2)) => {*d2 = true; a2.push((*a1).clone())},
                                    (_, ref mut b) => **b = Element::Term(true, vec![*e1.clone(), b.clone()])
                                }
                                *dirty = true;
                                add = false;
                            }
                        }
                        *newfac2.last_mut().unwrap() = newfac2.last().unwrap().normalize();
                    }
                    if add {
                        newfac2.push(x.clone());
                    }
                }

                factors = newfac2;

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
                    (true, 1, 1) => {}, // don't add a factor
                    x => factors.push(Element::Num(false, x.0, x.1, x.2))
                }

                match factors.len() {
                    0 => Element::Num(false, true, 0, 1),
                    1 => factors[0].clone(), // downgrade
                    _ => Element::Term(false, factors)
                }
            },
            // TODO: drop +0?
            &Element::SubExpr(dirty, ref ts) => {
                if !dirty {
                    return self.clone()
                }    
                let mut terms = vec![];
                flatten_and_normalize_expr(ts, &mut terms);
                terms.sort(); // TODO: merge during sort

                if terms.len() == 0 {
                    return Element::SubExpr(false, terms);
                }

                // merge coefficients of similar terms
                // FIXME: terms need not be next to eachother: f(0)+f(1)+f(0)*13
                //let mut newterms = vec![terms[0].clone()];
                let mut lastindex = 0;

                for i in 1..terms.len() {
                    let (a, b) = terms.split_at_mut(i);
                    if !merge_terms(&mut a[lastindex], &b[0]) {
                        if lastindex + 1 < i {
                            a[lastindex + 1] = b[0].clone();
                        }
                        lastindex += 1;
                    }
                }
                terms.truncate(lastindex + 1);

                match terms.len() {
                    0 => Element::Num(false, true,0,1),
                    1 => terms[0].clone(),
                    _ => Element::SubExpr(false, terms)
                }

                /*

                for x in terms.iter().skip(1) {
                    if !merge_terms(newterms.last_mut().unwrap(), x) {
                        newterms.push(x.clone());
                    }

                    // filter +0
                    // TODO: also filter from unnormalized term
                    match newterms.last() {
                        Some(&Element::Num(_, _, 0, _)) => { newterms.pop(); }
                        _ => {}
                    }
                }
                

                match newterms.len() {
                    0 => Element::Num(false, true,0,1),
                    1 => newterms[0].clone(),
                    _ => Element::SubExpr(false, newterms)
                }
                */
            },
            &ref o => o.clone() 
        }.apply_builtin_functions(false)

    }
}

impl Func {
    pub fn normalize(&self) -> Func {
        Func { name: self.name.clone(), args: self.args.iter().map(|x| x.normalize()).collect() }
    }
}

fn flatten_and_normalize_term(terms: &[Element], res: &mut Vec<Element>) {
    for x in terms {
        match x {
            &Element::Term(_, ref f) => flatten_and_normalize_term(f, res),
            _ => res.push(x.normalize())
        }
    }
}

fn flatten_and_normalize_expr(expr: &[Element], res: &mut Vec<Element>) {
    for x in expr {
        match x {
            &Element::SubExpr(_, ref f) => flatten_and_normalize_expr(f, res),
            _ => res.push(x.normalize())
        }
    }
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
                        **a = Element::Term(false, vec![a.clone(), Element::Num(false, pos, num, den)]);
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
                **a2 = Element::Term(false, vec![sec.clone(), Element::Num(false, true,2,1)] ) 
            },
        _ => {return false}
    }

    true
}