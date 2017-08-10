use structure::{FuncArg,Func};
use tools::{mul_fractions,add_fractions,add_one,normalize_fraction};

impl FuncArg {
    // TODO: return iterator over funcargs for ground level?
    // TODO: in-place?
    pub fn apply_builtin_functions(&self, ground_level: bool) -> FuncArg {
        match self {
            &FuncArg::Fn(Func { name: ref n, args: ref a } ) => {
                match n.as_str() {
                    "delta_" => {

                    if a.len() == 1 {
                        match a[0] {
                            FuncArg::Num(_, 0, _) => FuncArg::Num(true,1,1),
                            _ =>  FuncArg::Num(true,0,1)
                        }
                    } else {
                        self.clone()
                    }
                },
                _ =>
                    FuncArg::Fn(
                        Func { name: n.clone(), args: a.iter().map(|x| x.apply_builtin_functions(false)).collect()})
                }
            },
            &FuncArg::Term(ref fs) => FuncArg::Term(fs.iter().map(|x| x.apply_builtin_functions(false)).collect()),
            &FuncArg::SubExpr(ref ts) => FuncArg::SubExpr(ts.iter().map(|x| x.apply_builtin_functions(false)).collect()),
            _ => self.clone()
         }
    }

    // bring a term to canconical form
    pub fn normalize<'a>(&self) -> FuncArg {
        match self {
            &FuncArg::Num(mut pos, mut num, mut den) => {
                normalize_fraction(&mut pos, &mut num, &mut den);
                FuncArg::Num(pos, num, den)
            }
            &FuncArg::Wildcard(ref name, ref restriction) => {
                let mut r = vec![];
                for x in restriction {
                    r.push(x.normalize());
                }
                FuncArg::Wildcard(name.clone(), r)
            }
            &FuncArg::Fn(ref f) => FuncArg::Fn(f.normalize()),
            &FuncArg::Term(ref ts) => {
                let mut factors = vec![];
                flatten_and_normalize_term(ts, &mut factors);
                factors.sort();

                // merge the coefficients
                let mut pos = true;
                let mut num = 1;
                let mut den = 1;

                while let Some(x) = factors.pop() {
                    match x {
                        FuncArg::Num(pos1,num1,den1) => mul_fractions(&mut pos, &mut num,&mut den,pos1,num1,den1),
                        _ => { factors.push(x); break; }
                    }
                }

                match (pos, num, den) {
                    (_, 0, _) => return FuncArg::Num(true, 0, 1),
                    (true, 1, 1) => {}, // don't add a factor
                    x => factors.push(FuncArg::Num(x.0, x.1, x.2))
                }

                match factors.len() {
                    0 => FuncArg::Num(true, 0, 1),
                    1 => factors[0].clone(), // downgrade
                    _ => FuncArg::Term(factors)
                }
            }
            // TODO: drop +0?
            &FuncArg::SubExpr(ref ts) => {
                let mut terms = vec![];
                flatten_and_normalize_expr(ts, &mut terms);
                terms.sort(); // TODO: merge during sort

                if terms.len() == 0 {
                    return FuncArg::SubExpr(terms);
                }

                // merge coefficients of similar terms
                let mut newterms = vec![terms[0].clone()];
                for x in terms.iter().skip(1) {
                    let mut newterm = false;
                    match (x, newterms.last_mut().unwrap()) {
                        (&FuncArg::Term(ref t1), &mut FuncArg::Term(ref mut t2)) => {
                            // treat the case where the term doesn't have a coefficient
                            assert!(t1.len() > 0 && t2.len() > 0);

                            let mut pos1;
                            let mut num1;
                            let mut den1;
                            let (mut l1, l11) = t1.split_at(t1.len() - 1);
                            match l11[0] {
                                FuncArg::Num(pos,num,den) => { pos1 = pos; num1 = num; den1 = den; },
                                _ => { l1 = t1; pos1 = true; num1 = 1; den1 = 1; }
                            }

                            {
                                let l2 = match t2.last() {
                                    Some(&FuncArg::Num(..)) => &t2[..t2.len() - 1],
                                    _ => &t2[..]
                                };

                                if l1 != l2 { newterm = true; }
                            }

                            if !newterm {
                                // should we add the terms?
                                match t2.last_mut() {
                                    Some(&mut FuncArg::Num(ref mut pos, ref mut num, ref mut den)) => 
                                        add_fractions(pos, num, den, pos1, num1, den1),
                                    _ => newterm = true  
                                }
                                if newterm {
                                    // add 1
                                    add_one(&mut pos1, &mut num1, &mut den1);
                                    t2.push(FuncArg::Num( pos1, num1 ,den1 ));
                                    newterm = false;
                                }
                            }
                        },
                        // x + x/2
                        // (1+x) + (1+x)/2
                        (ref a, &mut FuncArg::Term(ref mut t2)) => {
                            assert!(t2.len() > 0);

                            if **a == t2[0] && t2.len() == 2 {
                                match t2[1] {
                                    FuncArg::Num(ref mut pos, ref mut num, ref mut den) => { add_one(pos, num, den); },
                                    _ => { newterm = true; }
                                }
                            } else {
                                newterm = true;
                            }
                        },
                        (&FuncArg::Term(ref t2), ref mut a) => {
                            assert!(t2.len() > 0);

                            if **a == t2[0] && t2.len() == 2 {
                                match t2[1] {
                                    FuncArg::Num(mut pos, mut num, mut den) => {
                                        add_one(&mut pos, &mut num, &mut den);
                                        **a = FuncArg::Term(vec![a.clone(), FuncArg::Num(pos, num, den)]);
                                    },
                                    _ => { newterm = true; }
                                }
                            } else {
                                newterm = true;
                            }
                        },
                        (&FuncArg::Num(pos1, num1, den1), 
                            &mut FuncArg::Num(ref mut pos, ref mut num, ref mut den)) => {
                            add_fractions(pos, num, den, pos1, num1, den1);
                        },
                        (ref a1, ref mut a2) if a1 == a2 => { 
                                **a2 = FuncArg::Term(vec![x.clone(), FuncArg::Num(true,2,1)] ) 
                            },
                        _ => {newterm = true}
                    }

                    if newterm {
                        newterms.push(x.clone());
                    }

                    // filter +0
                    // TODO: also filter from unnormalized term
                    match newterms.last() {
                        Some(&FuncArg::Num(_, 0, _)) => { newterms.pop(); }
                        _ => {}
                    }
                }

                match newterms.len() {
                    0 => FuncArg::Num(true,0,1),
                    1 => newterms[0].clone(),
                    _ => FuncArg::SubExpr(newterms)
                }
            }
            &ref o => o.clone() 
        }.apply_builtin_functions(false)

    }
}

impl Func {
    pub fn normalize(&self) -> Func {
        Func { name: self.name.clone(), args: self.args.iter().map(|x| x.normalize()).collect() }
    }
}

fn flatten_and_normalize_term(terms: &[FuncArg], res: &mut Vec<FuncArg>) {
    for x in terms {
        match x {
            &FuncArg::Term(ref f) => flatten_and_normalize_term(f, res),
            _ => res.push(x.normalize())
        }
    }
}

fn flatten_and_normalize_expr(expr: &[FuncArg], res: &mut Vec<FuncArg>) {
    for x in expr {
        match x {
            &FuncArg::SubExpr(ref f) => flatten_and_normalize_expr(f, res),
            _ => res.push(x.normalize())
        }
    }
}