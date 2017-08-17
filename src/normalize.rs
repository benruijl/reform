use structure::{Element,Func};
use tools::{mul_fractions,add_fractions,add_one,normalize_fraction,exp_fraction};

impl Element {
    // TODO: return iterator over Elements for ground level?
    // TODO: in-place?
    pub fn apply_builtin_functions(&self, ground_level: bool) -> Element {
        match self {
            &Element::Fn(Func { name: ref n, args: ref a } ) => {
                match n.as_str() {
                    "delta_" => {
                        if a.len() == 1 {
                            match a[0] {
                                Element::Num(_, 0, _) => Element::Num(true,1,1),
                                _ =>  Element::Num(true,0,1)
                            }
                        } else {
                            self.clone()
                        }
                    },
                    "nargs_" => {
                        // get the number of arguments
                        Element::Num(true, a.len() as u64, 1)
                    }
                    _ =>
                        Element::Fn(
                        Func { name: n.clone(), args: a.iter().map(|x| x.apply_builtin_functions(false)).collect()})
                }
            },
            &Element::Term(ref fs) => Element::Term(fs.iter().map(|x| x.apply_builtin_functions(false)).collect()),
            &Element::SubExpr(ref ts) => Element::SubExpr(ts.iter().map(|x| x.apply_builtin_functions(false)).collect()),
            _ => self.clone()
         }
    }

    // bring a term to canconical form
    pub fn normalize<'a>(&self) -> Element {
        match self {
            &Element::Num(pos, mut num, mut den) => {
                normalize_fraction(&mut num, &mut den);
                Element::Num(pos, num, den)
            },
            &Element::Wildcard(ref name, ref restriction) => {
                let mut r = vec![];
                for x in restriction {
                    r.push(x.normalize());
                }
                Element::Wildcard(name.clone(), r)
            },
            &Element::Pow(ref b, ref p) => {
                let newb = b.normalize();
                let mut newp = p.normalize();

                // x^0 = 1
                if let Element::Num(_, 0, _) = newp {
                    return Element::Num(true, 1, 1);
                }
                // return x if x^1
                if let Element::Num(true, 1, 1) = newp {
                    return newb;
                }

                // simplify numbers if exponent is a positive integer
                if let Element::Num(true, n, 1) = newp {
                    if let Element::Num(mut pos, mut num, mut den) = newb {
                        exp_fraction(&mut pos, &mut num, &mut den, n);
                        return Element::Num(pos, num, den);
                    }
                }

                // simplify x^a^b = x^(a*b)
                if let Element::Pow(c, d) = newb {
                    match newp {
                        Element::Term(ref mut f) => f.push(*d),
                        _ => newp = Element::Term(vec![newp.clone(), *d])
                    }
                    Element::Pow(c, Box::new(newp))
                } else {
                    Element::Pow(Box::new(newb), Box::new(newp))
                }
            },
            &Element::Fn(ref f) => Element::Fn(f.normalize()),
            &Element::Term(ref ts) => {
                let mut factors = vec![];
                flatten_and_normalize_term(ts, &mut factors);
                factors.sort();
                println!("old factors {:?}", factors);

                // create pows from terms that are the same
                // they may not be side to side...
                // first, find side-by-side factors
                let mut samecount = 1;
                let mut newfactors = vec![];

                for x in factors.windows(2) {
                    if x[0] == x[1] {
                        samecount += 1;
                    } else {
                        if samecount > 1 {
                            newfactors.push(Element::Pow(
                                Box::new(x[0].clone()), 
                                Box::new(Element::Num(true, samecount, 1))));
                        } else {
                            newfactors.push(x[0].clone());
                        }
                        samecount = 1;
                    }
                }

                if let Some(x) = factors.last() {
                    if samecount > 1 {
                        newfactors.push(Element::Pow(
                            Box::new(x.clone()), 
                            Box::new(Element::Num(true, samecount, 1))));
                    } else {
                        newfactors.push(x.clone());
                    }
                }

                newfactors.sort(); // FIXME: costly
                println!("new fac {:?}", newfactors);

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
                    if let &Element::Pow(ref b1, ref e1) = x {
                        if let &mut Element::Pow(ref mut b2, ref mut e2) = newfac2.last_mut().unwrap() {
                            if b1 == b2 {
                                match (&**e1, &mut **e2) {
                                    (&Element::Term(ref a1), &mut Element::Term(ref mut a2)) => a2.extend(a1.clone()),
                                    (ref a1, &mut Element::Term(ref mut a2)) => a2.push((*a1).clone()),
                                    (_, ref mut b) => **b = Element::Term(vec![*e1.clone(), b.clone()])
                                }
                                add = false;
                            }
                        }
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
                        Element::Num(pos1,num1,den1) => mul_fractions(&mut pos, &mut num,&mut den,pos1,num1,den1),
                        _ => { factors.push(x); break; }
                    }
                }

                match (pos, num, den) {
                    (_, 0, _) => return Element::Num(true, 0, 1),
                    (true, 1, 1) => {}, // don't add a factor
                    x => factors.push(Element::Num(x.0, x.1, x.2))
                }

                match factors.len() {
                    0 => Element::Num(true, 0, 1),
                    1 => factors[0].clone(), // downgrade
                    _ => Element::Term(factors)
                }
            },
            // TODO: drop +0?
            &Element::SubExpr(ref ts) => {
                let mut terms = vec![];
                flatten_and_normalize_expr(ts, &mut terms);
                terms.sort(); // TODO: merge during sort

                if terms.len() == 0 {
                    return Element::SubExpr(terms);
                }

                // merge coefficients of similar terms
                let mut newterms = vec![terms[0].clone()];
                for x in terms.iter().skip(1) {
                    let mut newterm = false;
                    match (x, newterms.last_mut().unwrap()) {
                        (&Element::Term(ref t1), &mut Element::Term(ref mut t2)) => {
                            // treat the case where the term doesn't have a coefficient
                            assert!(t1.len() > 0 && t2.len() > 0);

                            let mut pos1;
                            let mut num1;
                            let mut den1;
                            let (mut l1, l11) = t1.split_at(t1.len() - 1);
                            match l11[0] {
                                Element::Num(pos,num,den) => { pos1 = pos; num1 = num; den1 = den; },
                                _ => { l1 = t1; pos1 = true; num1 = 1; den1 = 1; }
                            }

                            {
                                let l2 = match t2.last() {
                                    Some(&Element::Num(..)) => &t2[..t2.len() - 1],
                                    _ => &t2[..]
                                };

                                if l1 != l2 { newterm = true; }
                            }

                            if !newterm {
                                // should we add the terms?
                                match t2.last_mut() {
                                    Some(&mut Element::Num(ref mut pos, ref mut num, ref mut den)) => 
                                        add_fractions(pos, num, den, pos1, num1, den1),
                                    _ => newterm = true  
                                }
                                if newterm {
                                    // add 1
                                    add_one(&mut pos1, &mut num1, &mut den1);
                                    t2.push(Element::Num( pos1, num1 ,den1 ));
                                    newterm = false;
                                }
                            }
                        },
                        // x + x/2
                        // (1+x) + (1+x)/2
                        (ref a, &mut Element::Term(ref mut t2)) => {
                            assert!(t2.len() > 0);

                            if **a == t2[0] && t2.len() == 2 {
                                match t2[1] {
                                    Element::Num(ref mut pos, ref mut num, ref mut den) => { add_one(pos, num, den); },
                                    _ => { newterm = true; }
                                }
                            } else {
                                newterm = true;
                            }
                        },
                        (&Element::Term(ref t2), ref mut a) => {
                            assert!(t2.len() > 0);

                            if **a == t2[0] && t2.len() == 2 {
                                match t2[1] {
                                    Element::Num(mut pos, mut num, mut den) => {
                                        add_one(&mut pos, &mut num, &mut den);
                                        **a = Element::Term(vec![a.clone(), Element::Num(pos, num, den)]);
                                    },
                                    _ => { newterm = true; }
                                }
                            } else {
                                newterm = true;
                            }
                        },
                        (&Element::Num(pos1, num1, den1), 
                            &mut Element::Num(ref mut pos, ref mut num, ref mut den)) => {
                            add_fractions(pos, num, den, pos1, num1, den1);
                        },
                        (ref a1, ref mut a2) if a1 == a2 => { 
                                **a2 = Element::Term(vec![x.clone(), Element::Num(true,2,1)] ) 
                            },
                        _ => {newterm = true}
                    }

                    if newterm {
                        newterms.push(x.clone());
                    }

                    // filter +0
                    // TODO: also filter from unnormalized term
                    match newterms.last() {
                        Some(&Element::Num(_, 0, _)) => { newterms.pop(); }
                        _ => {}
                    }
                }

                match newterms.len() {
                    0 => Element::Num(true,0,1),
                    1 => newterms[0].clone(),
                    _ => Element::SubExpr(newterms)
                }
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
            &Element::Term(ref f) => flatten_and_normalize_term(f, res),
            _ => res.push(x.normalize())
        }
    }
}

fn flatten_and_normalize_expr(expr: &[Element], res: &mut Vec<Element>) {
    for x in expr {
        match x {
            &Element::SubExpr(ref f) => flatten_and_normalize_expr(f, res),
            _ => res.push(x.normalize())
        }
    }
}