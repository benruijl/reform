use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use num_traits::{One, Zero};
use number::Number;
use poly::raw::MultivariatePolynomial;
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::fmt;
use std::io::{Error, Read, Write};
use std::ops::{Add, Div, Mul, Neg, Sub};
use structure::{fmt_varname, Element, GlobalVarInfo, VarName};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Polynomial {
    poly: MultivariatePolynomial<Number, u32>,
    varmap: HashMap<VarName, usize>, // map from names to internal name
    inv_varmap: Vec<VarName>,
    varcount: usize,
}

impl Polynomial {
    pub fn new() -> Polynomial {
        Polynomial {
            poly: MultivariatePolynomial::new(),
            varmap: HashMap::new(),
            inv_varmap: vec![],
            varcount: 0,
        }
    }

    fn to_monomial(
        e: &Element,
        exp: &mut Vec<u32>,
        varmap: &mut HashMap<VarName, usize>,
        inv_varmap: &mut Vec<VarName>,
        varcount: &mut usize,
    ) -> Result<Number, String> {
        match *e {
            Element::Var(ref x, Number::SmallInt(e)) if e > 0 => {
                match varmap.entry(*x) {
                    Entry::Occupied(v) => {
                        exp[*v.get()] = e as u32;
                    }
                    Entry::Vacant(mut v) => {
                        v.insert(*varcount);
                        inv_varmap.push(*x);
                        *varcount += 1;
                        exp.push(e as u32);
                    }
                }

                Ok(Number::one())
            }
            Element::Num(_, ref nn @ Number::SmallInt(_))
            | Element::Num(_, ref nn @ Number::BigInt(_)) => Ok(nn.clone()),
            Element::Pow(_, ref p) => {
                let (ref b, ref ex) = **p;
                if let Element::Var(ref x, Number::SmallInt(ee1)) = *b {
                    if let Element::Num(_, Number::SmallInt(n)) = *ex {
                        if n > 0 {
                            match varmap.entry(*x) {
                                Entry::Occupied(v) => {
                                    exp[*v.get()] = (n * ee1) as u32;
                                }
                                Entry::Vacant(mut v) => {
                                    v.insert(*varcount);
                                    inv_varmap.push(*x);
                                    *varcount += 1;
                                    exp.push((n * ee1) as u32);
                                }
                            }
                            return Ok(Number::one());
                        }
                    }
                }
                Err(format!("{} not allowed in monomial", e))
            }
            Element::Term(_, ref args) => {
                let mut c = Number::one();
                for x in args {
                    c *= Polynomial::to_monomial(x, exp, varmap, inv_varmap, varcount)?;
                }
                Ok(c)
            }
            _ => Err(format!("{} not allowed in monomial", e)),
        }
    }

    pub fn from(e: &Element) -> Result<Polynomial, String> {
        let mut varcount = 0;
        let mut varmap = HashMap::new();
        let mut inv_varmap = vec![];

        match *e {
            Element::SubExpr(_, ref args) => {
                let mut monomials = Vec::with_capacity(args.len());
                for x in args {
                    let mut exp = vec![0; varcount];
                    let coeff = Polynomial::to_monomial(
                        x,
                        &mut exp,
                        &mut varmap,
                        &mut inv_varmap,
                        &mut varcount,
                    )?;
                    monomials.push((coeff, exp));
                }

                let mut poly = MultivariatePolynomial::with_nvars(varcount);

                for (c, mut e) in monomials {
                    if e.len() < varcount {
                        e.resize(varcount, 0);
                    }
                    poly.append_monomial(c, e);
                }

                Ok(Polynomial {
                    poly,
                    varmap,
                    inv_varmap,
                    varcount,
                })
            }
            Element::Var(ref x, Number::SmallInt(e)) if e > 0 => {
                let mut exp = vec![e as u32];
                varmap.insert(*x, 0);
                inv_varmap.push(*x);
                Ok(Polynomial {
                    poly: MultivariatePolynomial::from_monomial(Number::one(), exp),
                    varmap: varmap,
                    inv_varmap: inv_varmap,
                    varcount: 1,
                })
            }
            Element::Num(_, ref nn @ Number::SmallInt(_))
            | Element::Num(_, ref nn @ Number::BigInt(_)) => Ok(Polynomial {
                poly: MultivariatePolynomial::from_constant_with_nvars(nn.clone(), 0),
                varmap: varmap,
                inv_varmap: inv_varmap,
                varcount: 0,
            }),
            Element::Term(..) | Element::Pow(..) => {
                let mut exp = vec![];
                let c = Polynomial::to_monomial(
                    e,
                    &mut exp,
                    &mut varmap,
                    &mut inv_varmap,
                    &mut varcount,
                )?;
                let mut poly = MultivariatePolynomial::from_monomial(c, exp);
                Ok(Polynomial {
                    poly,
                    varmap,
                    inv_varmap,
                    varcount,
                })
            }
            _ => Err(format!("{} not allowed in polynomial", e)),
        }
    }

    pub fn cloned_one(&self) -> Polynomial {
        Polynomial {
            poly: MultivariatePolynomial::from_constant_with_nvars(Number::one(), self.varcount),
            varmap: self.varmap.clone(),
            inv_varmap: self.inv_varmap.clone(),
            varcount: self.varcount,
        }
    }

    pub fn to_expression(self) -> Element {
        let mut terms = vec![];
        for v in self.poly.into_iter() {
            let mut factors = vec![];
            for (name, pow) in v.exponents.iter().enumerate() {
                if *pow >= 1 {
                    factors.push(Element::Var(
                        self.inv_varmap[name],
                        Number::SmallInt(*pow as isize),
                    ));
                }
            }

            factors.push(Element::Num(false, v.coefficient.clone()));
            terms.push(Element::Term(true, factors));
        }
        Element::SubExpr(true, terms)
    }

    /// Unify the variable maps between two polynomials
    pub fn unify_varmaps(&mut self, other: &mut Polynomial) {
        if self.varmap == other.varmap {
            return;
        }

        if self.varcount < other.varcount {
            return other.unify_varmaps(self);
        }

        let mut map = HashMap::new(); // index map

        let mut varcount = self.varcount;

        // merge 'other' map into self
        for (k1, v1) in &other.varmap {
            match self.varmap.entry(*k1) {
                Entry::Occupied(o) => {
                    map.insert(*v1, *o.get());
                }
                Entry::Vacant(mut v) => {
                    // new variable
                    self.inv_varmap.push(*k1);
                    map.insert(*v1, varcount);
                    v.insert(varcount);
                    varcount += 1;
                }
            }
        }

        if varcount > self.varcount {
            // we need to reconstruct the exponent in `self`
            let mut newexp = vec![0; varcount * other.poly.nterms];

            for t in 0..self.poly.nterms {
                newexp[t * varcount..t * varcount + self.varcount]
                    .copy_from_slice(self.poly.exponents(t));
            }

            self.poly.exponents = newexp;
            self.poly.nvars = varcount;
            self.varcount = varcount;
        }

        // reconstruct 'other' with correct monomial ordering
        let mut newother = MultivariatePolynomial::with_nvars(varcount);
        for t in 0..other.poly.nterms {
            let mut newexp = vec![0; varcount];
            for e in 0..other.varcount {
                newexp[*map.get(&e).unwrap()] = other.poly.exponents(t)[e];
            }
            newother.append_monomial(other.poly.coefficients[t].clone(), newexp);
        }

        other.varmap = self.varmap.clone();
        other.inv_varmap = self.inv_varmap.clone();
        other.poly = newother;
        other.varcount = varcount;
    }

    fn fmt_output(&self, f: &mut fmt::Formatter, var_info: &GlobalVarInfo) -> fmt::Result {
        let mut is_first_term = true;
        for monomial in &self.poly {
            if monomial.coefficient.is_zero() {
                continue;
            }
            let mut is_first_factor = true;
            if monomial.coefficient.eq(&Number::one()) {
                if !is_first_term {
                    write!(f, "+")?;
                }
            } else if monomial.coefficient.eq(&Number::one().neg()) {
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
                fmt_varname(&self.inv_varmap[i], f, var_info)?;
                if !e.is_one() {
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

    pub fn gcd(&mut self, b: &mut Polynomial) -> Polynomial {
        self.unify_varmaps(b);
        Polynomial {
            poly: MultivariatePolynomial::gcd(&self.poly, &b.poly),
            varmap: self.varmap.clone(),
            inv_varmap: self.inv_varmap.clone(),
            varcount: self.varcount.clone(),
        }
    }

    pub fn long_division(&mut self, div: &mut Polynomial) -> (Polynomial, Polynomial) {
        self.unify_varmaps(div);

        let (q, r) = self.poly.long_division(&div.poly);

        (
            Polynomial {
                poly: q,
                varmap: self.varmap.clone(),
                inv_varmap: self.inv_varmap.clone(),
                varcount: self.varcount.clone(),
            },
            Polynomial {
                poly: r,
                varmap: self.varmap.clone(),
                inv_varmap: self.inv_varmap.clone(),
                varcount: self.varcount.clone(),
            },
        )
    }
}

impl Mul for Polynomial {
    type Output = Self;

    fn mul(mut self, mut other: Self) -> Self::Output {
        self.unify_varmaps(&mut other);

        Polynomial {
            poly: self.poly * &other.poly,
            varmap: self.varmap,
            inv_varmap: self.inv_varmap,
            varcount: self.varcount,
        }
    }
}

impl Mul<Number> for Polynomial {
    type Output = Self;

    fn mul(mut self, other: Number) -> Self::Output {
        for c in &mut self.poly.coefficients {
            *c *= other.clone();
        }
        self
    }
}

impl Div for Polynomial {
    type Output = Self;

    fn div(mut self, mut other: Self) -> Self::Output {
        self.unify_varmaps(&mut other);

        Polynomial {
            poly: self.poly.long_division(&other.poly).0,
            varmap: self.varmap,
            inv_varmap: self.inv_varmap,
            varcount: self.varcount,
        }
    }
}

impl Add for Polynomial {
    type Output = Self;

    fn add(mut self, mut other: Self) -> Self::Output {
        self.unify_varmaps(&mut other);

        Polynomial {
            poly: self.poly + other.poly,
            varmap: self.varmap,
            inv_varmap: self.inv_varmap,
            varcount: self.varcount,
        }
    }
}

impl Sub for Polynomial {
    type Output = Self;

    fn sub(mut self, mut other: Self) -> Self::Output {
        self.unify_varmaps(&mut other);

        Polynomial {
            poly: self.poly - other.poly,
            varmap: self.varmap,
            inv_varmap: self.inv_varmap,
            varcount: self.varcount,
        }
    }
}

impl Neg for Polynomial {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Polynomial {
            poly: self.poly.neg(),
            varmap: self.varmap,
            inv_varmap: self.inv_varmap,
            varcount: self.varcount,
        }
    }
}

impl Zero for Polynomial {
    #[inline]
    fn zero() -> Self {
        Self::new()
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.poly.nterms == 0
    }
}

impl Polynomial {
    pub fn serialize(&self, buffer: &mut Write) -> usize {
        let len = 4 + self.inv_varmap.len() * 4;
        buffer
            .write_u32::<LittleEndian>(self.inv_varmap.len() as u32)
            .unwrap();
        for x in &self.inv_varmap {
            buffer.write_u32::<LittleEndian>(*x).unwrap();
        }

        len + self.poly.serialize(buffer)
    }

    pub fn deserialize(buffer: &mut Read) -> Result<Polynomial, Error> {
        let len = buffer.read_u32::<LittleEndian>().unwrap() as usize;
        let mut v = Vec::with_capacity(len);
        for _ in 0..len {
            v.push(buffer.read_u32::<LittleEndian>().unwrap());
        }

        let p = MultivariatePolynomial::deserialize(buffer)?;
        let mut hm = HashMap::new();
        for (i, x) in v.iter().enumerate() {
            hm.insert(*x, i);
        }
        Ok(Polynomial {
            poly: p,
            varmap: hm,
            inv_varmap: v,
            varcount: len,
        })
    }
}

pub struct PolyPrinter<'a> {
    pub poly: &'a Polynomial,
    pub var_info: &'a GlobalVarInfo,
}

impl<'a> fmt::Display for PolyPrinter<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.poly.fmt_output(f, self.var_info)
    }
}

#[test]
fn serialize() {
    let mut a = MultivariatePolynomial::from_monomial(Number::SmallInt(100), vec![0, 0]);
    a.append_monomial(Number::SmallInt(100), vec![1, 0]);

    let mut b = MultivariatePolynomial::from_monomial(Number::SmallInt(-3), vec![2, 3]);
    b.append_monomial(Number::SmallInt(1), vec![1, 0]);

    let mut m = HashMap::new();
    m.insert(1, 0);
    m.insert(2, 1);
    let im = vec![1, 2];

    let ap = Polynomial {
        poly: a,
        varmap: m.clone(),
        inv_varmap: im.clone(),
        varcount: 2,
    };

    let bp = Polynomial {
        poly: b,
        varmap: m.clone(),
        inv_varmap: im.clone(),
        varcount: 2,
    };

    let elem = Element::RationalPolynomialCoefficient(false, Box::new((ap, bp)));

    let mut buffer = vec![];
    elem.serialize(&mut buffer);

    assert_eq!(elem, Element::deserialize(&mut buffer.as_slice()).unwrap())
}
