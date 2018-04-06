use poly::raw::MultivariatePolynomial;
use structure::{Element, VarName};

fn to_monomial(e: &Element, exp: &mut [u64]) -> i64 {
    match *e {
        Element::Var(ref x) => {
            exp[*x as usize] = 1;
            1
        }
        Element::Num(_, pos, num, 1) => {
            // TODO: fraction should be split
            if pos {
                num as i64
            } else {
                -(num as i64)
            }
        }
        Element::Pow(_, ref p) => {
            let (ref b, ref e) = **p;
            if let Element::Var(ref x) = *b {
                if let Element::Num(_, true, n, 1) = *e {
                    exp[*x as usize] = n;
                    return 1;
                }
            }
            panic!("{} not allowed in monomial", e);
        }
        Element::Term(_, ref args) => {
            let mut c = 1;
            for x in args {
                c *= to_monomial(x, exp);
            }
            c
        }
        _ => panic!("{} not allowed in monomial", e),
    }
}

pub fn to_rational_polynomial(e: &Element, num_vars: usize) -> MultivariatePolynomial<i64, u64> {
    match *e {
        Element::SubExpr(_, ref args) => {
            let mut a = MultivariatePolynomial::with_nvars(num_vars);
            for x in args {
                let mut exp = vec![0; num_vars];
                let c = to_monomial(x, &mut exp);
                a.append_monomial(c, exp);
            }
            a
        }
        Element::Var(ref x) => {
            let mut exp = vec![0; num_vars];
            exp[*x as usize] = 1;
            MultivariatePolynomial::from_monomial(1, exp)
        }
        Element::Num(_, pos, num, 1) => MultivariatePolynomial::from_constant_with_nvars(
            if pos { num as i64 } else { -(num as i64) }, num_vars)
        , // TODO: fraction should be split
        Element::Term(..) => {
            let mut exp = vec![0; num_vars];
            let c = to_monomial(e, &mut exp);
            MultivariatePolynomial::from_monomial(c, exp)
        }
        Element::Pow(..) => {
            let mut exp = vec![0; num_vars];
            to_monomial(e, &mut exp);
            MultivariatePolynomial::from_monomial(1, exp)
        }
        _ => panic!("{} not allowed in polynomial", e),
    }
}

pub fn to_expression(p: MultivariatePolynomial<i64, u64>) -> Element {
    let mut terms = vec![];
    for v in p.into_iter() {
        let mut factors = vec![];
        for (name, pow) in v.exponents.iter().enumerate() {
            if *pow == 1 {
                factors.push(Element::Var(name as VarName));
            } else {
                if *pow > 1 {
                    factors.push(Element::Pow(
                        false,
                        Box::new((
                            Element::Var(name as VarName),
                            Element::Num(false, true, *pow, 1),
                        )),
                    ));
                }
            }
        }

        if *v.coefficient < 0 {
            factors.push(Element::Num(false, false, -*v.coefficient as u64, 1));
        } else {
            factors.push(Element::Num(false, true, *v.coefficient as u64, 1));
        }

        terms.push(Element::Term(true, factors));
    }
    Element::SubExpr(true, terms)
}
