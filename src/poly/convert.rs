use num_traits::One;
use poly::exponent::Exponent;
use poly::raw::MultivariatePolynomial;
use poly::ring::Ring;
use std::fmt;
use structure::{fmt_varname, Element, GlobalVarInfo, VarName};
use number::Number;

fn to_monomial(e: &Element, exp: &mut [u32]) -> Result<Number, String> {
    match *e {
        Element::Var(ref x) => {
            exp[*x as usize] = 1;
            Ok(Number::one())
        }
        Element::Num(_, ref nn@Number::SmallInt(_)) | Element::Num(_, ref nn@Number::BigInt(_)) => {
            Ok(nn.clone())
        }
        Element::Pow(_, ref p) => {
            let (ref b, ref e) = **p;
            if let Element::Var(ref x) = *b {
                if let Element::Num(_, Number::SmallInt(n)) = *e {
                    if n > 0 {
                        exp[*x as usize] = n as u32;
                        return Ok(Number::one());
                    }
                }
            }
            Err(format!("{} not allowed in monomial", e))
        }
        Element::Term(_, ref args) => {
            let mut c = Number::one();
            for x in args {
                c *= to_monomial(x, exp)?;
            }
            Ok(c)
        }
        _ => Err(format!("{} not allowed in monomial", e)),
    }
}

pub fn to_rational_polynomial(
    e: &Element,
    num_vars: usize,
) -> Result<MultivariatePolynomial<Number, u32>, String> {
    match *e {
        Element::SubExpr(_, ref args) => {
            let mut a = MultivariatePolynomial::with_nvars(num_vars);
            for x in args {
                let mut exp = vec![0; num_vars];
                let c = to_monomial(x, &mut exp)?;
                a.append_monomial(c, exp);
            }
            Ok(a)
        }
        Element::Var(ref x) => {
            let mut exp = vec![0; num_vars];
            exp[*x as usize] = 1;
            Ok(MultivariatePolynomial::from_monomial(Number::one(), exp))
        }
        Element::Num(_, ref nn@Number::SmallInt(_)) | Element::Num(_, ref nn@Number::BigInt(_)) => {
            Ok(MultivariatePolynomial::from_constant_with_nvars(
            nn.clone(), num_vars))
        }
        Element::Term(..) => {
            let mut exp = vec![0; num_vars];
            let c = to_monomial(e, &mut exp)?;
            Ok(MultivariatePolynomial::from_monomial(c, exp))
        }
        Element::Pow(..) => {
            let mut exp = vec![0; num_vars];
            to_monomial(e, &mut exp)?;
            Ok(MultivariatePolynomial::from_monomial(Number::one(), exp))
        }
        _ => Err(format!("{} not allowed in polynomial", e)),
    }
}

pub fn to_expression(p: MultivariatePolynomial<Number, u32>) -> Element {
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
                            Element::Num(false, Number::SmallInt(*pow as isize)),
                        )),
                    ));
                }
            }
        }

        factors.push(Element::Num(false, v.coefficient.clone()));
        terms.push(Element::Term(true, factors));
    }
    Element::SubExpr(true, terms)
}

pub struct PolyPrinter<'a, R: 'a + Ring, E: Exponent> {
    pub poly: &'a MultivariatePolynomial<R, E>,
    pub var_info: &'a GlobalVarInfo,
}

impl<'a, R: 'a + Ring + fmt::Display, E: Exponent + One + fmt::Display> fmt::Display
    for PolyPrinter<'a, R, E>
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.poly.fmt_output(f, self.var_info)
    }
}

impl<R: Ring + fmt::Display, E: Exponent + One + fmt::Display> MultivariatePolynomial<R, E> {
    fn fmt_output(&self, f: &mut fmt::Formatter, var_info: &GlobalVarInfo) -> fmt::Result {
        let mut is_first_term = true;
        for monomial in self {
            if monomial.coefficient.is_zero() {
                continue;
            }
            let mut is_first_factor = true;
            if monomial.coefficient.eq(&R::one()) {
                if !is_first_term {
                    write!(f, "+")?;
                }
            } else if monomial.coefficient.eq(&R::one().neg()) {
                write!(f, "-")?;
            } else {
                if is_first_term {
                    write!(f, "{}", monomial.coefficient)?;
                } else {
                    write!(f, "+{}", monomial.coefficient)?;
                }
                is_first_factor = false;
            }
            is_first_term = false;
            for (i, e) in monomial.exponents.into_iter().enumerate() {
                if e.is_zero() {
                    continue;
                }
                if is_first_factor {
                    is_first_factor = false;
                } else {
                    write!(f, "*")?;
                }
                fmt_varname(&(i as VarName), f, var_info)?;
                if e.ne(&E::one()) {
                    write!(f, "^{}", e)?;
                }
            }
            if is_first_factor {
                write!(f, "1")?;
            }
        }
        if is_first_term {
            write!(f, "0")?;
        }
        Ok(())
    }
}
