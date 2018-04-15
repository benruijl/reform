use num_traits;
use num_traits::{checked_pow, One, Zero};
use rug::{Integer, Rational};
use std::cmp::Ordering;
use std::fmt;
use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub};
use tools::GCD;

#[macro_export]
macro_rules! DUMMY_NUM {
    () => {
        Number::zero()
    };
}

const DOWNGRADE_LIMIT: isize = 4294967296; // if a bigint is smaller than this number, we downgrade

/// A number is either a small number consisting of machine sized
/// integers or a big number, using GMP.
///
/// The mathematical operations on a number automatically upgrade
/// and downgrade to bigint/smallint etc.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Number {
    SmallInt(isize),
    BigInt(Integer),
    SmallRat(isize, isize),
    BigRat(Box<Rational>),
}

impl Number {
    pub fn normalize_inplace(&mut self) -> bool {
        *self = match *self {
            Number::SmallInt(_) => return false,
            Number::SmallRat(ref mut n, ref mut d) => {
                if *d == 1 {
                    Number::SmallInt(*n)
                } else if *d < 0 {
                    *d = -*d;
                    *n = -*n;
                    return true;
                } else {
                    return false;
                }
            }
            Number::BigInt(ref i) => {
                if *i < DOWNGRADE_LIMIT && *i > -DOWNGRADE_LIMIT {
                    Number::SmallInt(i.to_isize().expect("Number too large to downgrade"))
                } else {
                    return false;
                }
            }
            Number::BigRat(ref mut r) => {
                if *r.denom() != 1 {
                    return false;
                }
                Number::BigInt(r.numer().clone()) // FIXME: prevent clone
            }
        };
        true
    }
}

impl fmt::Display for Number {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Number::SmallInt(i) => write!(f, "{}", i),
            Number::SmallRat(n, d) => write!(f, "{}/{}", n, d),
            Number::BigInt(ref i) => write!(f, "{}", i.to_string_radix(10)),
            Number::BigRat(ref r) => write!(f, "{}", r.to_string_radix(10)),
        }
    }
}

impl Zero for Number {
    fn zero() -> Number {
        Number::SmallInt(0)
    }

    fn is_zero(&self) -> bool {
        match *self {
            Number::SmallInt(i) => i == 0,
            Number::BigInt(ref i) => *i == 0, // TODO: is this fast?
            Number::SmallRat(n, _d) => n == 0,
            Number::BigRat(ref f) => *f.numer() == 0 && *f.denom() == 1,
        }
    }
}

impl One for Number {
    fn one() -> Number {
        Number::SmallInt(1)
    }

    fn is_one(&self) -> bool {
        match *self {
            Number::SmallInt(i) => i == 1,
            Number::BigInt(ref i) => *i == 1,
            Number::SmallRat(n, _d) => n == 1,
            Number::BigRat(ref f) => *f.numer() == 1 && *f.denom() == 1,
        }
    }
}

impl Neg for Number {
    type Output = Number;

    fn neg(self) -> Self::Output {
        match self {
            Number::SmallInt(i) => Number::SmallInt(-i),
            Number::BigInt(i) => Number::BigInt(-i),
            Number::SmallRat(n, d) => Number::SmallRat(-n, d),
            Number::BigRat(f) => Number::BigRat(Box::new(-*f)),
        }
    }
}

impl PartialOrd for Number {
    fn partial_cmp(&self, rhs: &Number) -> Option<Ordering> {
        use self::Number::*;
        match (self, rhs) {
            (&SmallInt(ref i1), SmallInt(ref i2)) => i1.partial_cmp(i2),
            (&SmallInt(ref i1), BigInt(ref i2)) => Integer::from(i1.clone()).partial_cmp(i2),
            (&SmallInt(ref i1), SmallRat(n2, d2)) => (i1 * d2).partial_cmp(n2), // TODO: check for overflow
            (&SmallInt(ref i1), BigRat(ref f2)) => Rational::from(*i1).partial_cmp(&**f2),
            (&BigInt(ref i1), SmallInt(i2)) => i1.partial_cmp(&Integer::from(*i2)),
            (&BigInt(ref i1), BigInt(ref i2)) => i1.partial_cmp(i2),
            (&BigInt(ref i1), SmallRat(n2, d2)) => (i1 * Integer::from(*d2)).partial_cmp(n2),
            (&BigInt(ref i1), BigRat(ref f2)) => i1.partial_cmp(&**f2),
            (&SmallRat(n1, d1), SmallInt(i2)) => n1.partial_cmp(&(i2 * d1)), // TODO: check for overflow
            (&SmallRat(n1, d1), BigInt(ref i2)) => n1.partial_cmp(&(i2 * Integer::from(d1))),
            (&SmallRat(n1, d1), SmallRat(n2, d2)) => {
                // TODO: improve
                if n1 < 0 && *n2 > 0 {
                    return Some(Ordering::Less);
                }
                if n1 > 0 && *n2 < 0 {
                    return Some(Ordering::Greater);
                }

                (Number::SmallInt(n1) * Number::SmallInt(*d2))
                    .partial_cmp(&(Number::SmallInt(*n2) * Number::SmallInt(d1)))
            }
            (&SmallRat(n1, d1), BigRat(ref f2)) => Rational::from((n1, d1)).partial_cmp(&**f2),
            (&BigRat(ref f1), SmallInt(i2)) => (**f1).partial_cmp(&Rational::from(*i2)),
            (&BigRat(ref f1), BigInt(ref i2)) => (**f1).partial_cmp(&Rational::from(i2)),
            (&BigRat(ref f1), SmallRat(n2, d2)) => (**f1).partial_cmp(&Rational::from((*n2, *d2))),
            (&BigRat(ref f1), BigRat(ref f2)) => f1.partial_cmp(f2),
        }
    }
}

impl Add for Number {
    type Output = Self;

    fn add(self, rhs: Number) -> Number {
        use self::Number::*;
        match (self, rhs) {
            (SmallInt(i1), SmallInt(i2)) => match i1.checked_add(i2) {
                Some(x) => SmallInt(x),
                None => BigInt(Integer::from(i1) + Integer::from(i2)),
            },
            (SmallInt(i1), BigInt(i2)) | (BigInt(i2), SmallInt(i1)) => {
                BigInt(Integer::from(i1) + i2)
            }
            (SmallInt(i1), SmallRat(n2, d2)) | (SmallRat(n2, d2), SmallInt(i1)) => {
                match i1.checked_mul(d2) {
                    Some(num1) => match n2.checked_add(num1) {
                        Some(num) => Number::SmallRat(num, d2),
                        None => {
                            Number::BigRat(Box::new(Rational::from(i1) + Rational::from((n2, d2))))
                        }
                    },
                    None => Number::BigRat(Box::new(Rational::from(i1) + Rational::from((n2, d2)))),
                }
            }
            (SmallRat(n1, d1), SmallRat(n2, d2)) => match d2.checked_mul(d1 / GCD::gcd(d1, d2)) {
                Some(lcm) => match n2.checked_mul(lcm / d2) {
                    Some(num2) => match n1.checked_mul(lcm / d1) {
                        Some(num1) => match num1.checked_add(num2) {
                            Some(num) => {
                                if num % lcm == 0 {
                                    Number::SmallInt(num / lcm)
                                } else {
                                    Number::SmallRat(num, lcm)
                                }
                            }
                            None => Number::BigRat(Box::new(
                                Rational::from((n1, d1)) + Rational::from((n2, d2)),
                            )),
                        },
                        None => Number::BigRat(Box::new(
                            Rational::from((n1, d1)) + Rational::from((n2, d2)),
                        )),
                    },
                    None => Number::BigRat(Box::new(
                        Rational::from((n1, d1)) + Rational::from((n2, d2)),
                    )),
                },
                None => Number::BigRat(Box::new(
                    Rational::from((n1, d1)) + Rational::from((n2, d2)),
                )),
            },
            (SmallInt(i1), BigRat(f2)) | (BigRat(f2), SmallInt(i1)) => {
                Number::BigRat(Box::new(*f2 + Rational::from(i1)))
            }
            (BigInt(i1), BigInt(i2)) => BigInt(i1 + i2),
            (BigInt(i1), SmallRat(n2, d2)) | (SmallRat(n2, d2), BigInt(i1)) => {
                Number::BigRat(Box::new(Rational::from(i1) + Rational::from((n2, d2))))
            }
            (BigInt(i1), BigRat(f2)) | (BigRat(f2), BigInt(i1)) => {
                Number::BigRat(Box::new(*f2 + Rational::from(i1)))
            }
            (BigRat(f1), SmallRat(n2, d2)) | (SmallRat(n2, d2), BigRat(f1)) => {
                Number::BigRat(Box::new(*f1 + Rational::from((n2, d2))))
            }
            (BigRat(f1), BigRat(f2)) => BigRat(Box::new(*f1 + *f2)),
        }
    }
}

impl Sub for Number {
    type Output = Self;

    fn sub(self, rhs: Number) -> Number {
        self + (-rhs)
    }
}

impl Mul for Number {
    type Output = Self;

    fn mul(self, rhs: Number) -> Number {
        use self::Number::*;
        match (self, rhs) {
            (SmallInt(i1), SmallInt(i2)) => match i1.checked_mul(i2) {
                Some(x) => SmallInt(x),
                None => BigInt(Integer::from(i1) * Integer::from(i2)),
            },
            (SmallInt(i1), BigInt(i2)) | (BigInt(i2), SmallInt(i1)) => {
                BigInt(Integer::from(i1) * i2)
            }
            (SmallInt(i1), SmallRat(n2, mut d2)) | (SmallRat(n2, mut d2), SmallInt(i1)) => {
                let gcd = GCD::gcd(i1, d2);
                d2 /= gcd;

                match n2.checked_mul(i1 / gcd) {
                    Some(x) => if d2 == 1 {
                        Number::SmallInt(x)
                    } else {
                        Number::SmallRat(x, d2)
                    },
                    None => if d2 == 1 {
                        Number::BigInt(Integer::from(n2) * Integer::from(i1 / gcd))
                    } else {
                        Number::BigRat(Box::new(Rational::from((
                            Integer::from(n2) * Integer::from(i1 / gcd),
                            d2,
                        ))))
                    },
                }
            }
            (SmallRat(n1, d1), SmallRat(n2, d2)) => {
                let gcd1 = GCD::gcd(n1, d2);
                let gcd2 = GCD::gcd(n2, d1);

                match (n2 / gcd2).checked_mul(n1 / gcd1) {
                    Some(nn) => match (d1 / gcd2).checked_mul(d2 / gcd1) {
                        Some(nd) => Number::SmallRat(nn, nd),
                        None => Number::BigRat(Box::new(Rational::from((
                            nn,
                            Integer::from(d1 / gcd2) * Integer::from(d2 / gcd1),
                        )))),
                    },
                    None => Number::BigRat(Box::new(Rational::from((
                        Integer::from(n1 / gcd1) * Integer::from(n2 / gcd2),
                        Integer::from(d1 / gcd2) * Integer::from(d2 / gcd1),
                    )))),
                }
            }
            (SmallInt(i1), BigRat(f2)) | (BigRat(f2), SmallInt(i1)) => {
                Number::BigRat(Box::new(*f2 * Rational::from(i1)))
            }
            (BigInt(i1), BigInt(i2)) => BigInt(i1 * i2),
            (BigInt(i1), SmallRat(n2, d2)) | (SmallRat(n2, d2), BigInt(i1)) => {
                Number::BigRat(Box::new(Rational::from(i1) * Rational::from((n2, d2))))
            }
            (BigInt(i1), BigRat(f2)) | (BigRat(f2), BigInt(i1)) => {
                Number::BigRat(Box::new(*f2 * Rational::from(i1)))
            }
            (BigRat(f1), SmallRat(n2, d2)) | (SmallRat(n2, d2), BigRat(f1)) => {
                Number::BigRat(Box::new(*f1 * Rational::from((n2, d2))))
            }
            (BigRat(f1), BigRat(f2)) => BigRat(Box::new(*f1 * *f2)),
        }
    }
}

impl num_traits::Pow<u32> for Number {
    type Output = Self;

    fn pow(self, rhs: u32) -> Number {
        use self::Number::*;
        use rug::ops::Pow;
        match self {
            SmallInt(i) => match checked_pow(i, rhs as usize) {
                Some(x) => SmallInt(x),
                None => BigInt(Integer::from(i).pow(rhs)),
            },
            BigInt(i) => BigInt(i.pow(rhs)),
            SmallRat(n, d) => match checked_pow(n, rhs as usize) {
                Some(n1) => match checked_pow(d, rhs as usize) {
                    Some(d1) => SmallRat(n1, d1),
                    None => BigRat(Box::new(Rational::from((n1, Integer::from(d).pow(rhs))))),
                },
                None => BigRat(Box::new(Rational::from((n, d)).pow(rhs))),
            },
            BigRat(f) => BigRat(Box::new(f.pow(rhs))),
        }
    }
}

impl MulAssign for Number {
    fn mul_assign(&mut self, rhs: Number) {
        *self = self.clone() * rhs; // TODO: optimize
    }
}

impl AddAssign for Number {
    fn add_assign(&mut self, rhs: Number) {
        *self = self.clone() + rhs; // TODO: optimize
    }
}
