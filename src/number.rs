use num_traits::{One, Zero};
use rug::{Integer, Rational};
use std::fmt;
use std::ops::{Add, Mul, Sub};

const DOWNGRADE_LIMIT: usize = 4294967296; // if a bigint is smaller than this number, we downgrade

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
    BigRat(Rational),
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
            Number::SmallRat(n, d) => n == 0,
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
            Number::SmallRat(n, d) => n == 1,
            Number::BigRat(ref f) => *f.numer() == 1 && *f.denom() == 1,
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
            (SmallInt(i1), BigInt(i2)) => BigInt(Integer::from(i1) + i2),
            (SmallInt(i1), SmallRat(n2, d2)) => unimplemented!(),
            (SmallInt(i1), BigRat(f2)) => unimplemented!(),
            (BigInt(i1), SmallInt(i2)) => unimplemented!(),
            (BigInt(i1), BigInt(i2)) => BigInt(i1 + i2),
            (BigInt(i1), SmallRat(n2, d2)) => unimplemented!(),
            (BigInt(i1), BigRat(f2)) => unimplemented!(),
            (SmallRat(n1, d1), SmallInt(i2)) => unimplemented!(),
            (SmallRat(n1, d1), BigInt(i2)) => unimplemented!(),
            (SmallRat(n1, d1), SmallRat(n2, d2)) => unimplemented!(),
            (SmallRat(n1, d1), BigRat(f2)) => unimplemented!(),
            (BigRat(f1), SmallInt(i2)) => unimplemented!(),
            (BigRat(f1), BigInt(i2)) => unimplemented!(),
            (BigRat(f1), SmallRat(n2, d2)) => unimplemented!(),
            (BigRat(f1), BigRat(f2)) => unimplemented!(),
        }
    }
}

impl Sub for Number {
    type Output = Self;

    fn sub(self, rhs: Number) -> Number {
        use self::Number::*;
        match (self, rhs) {
            (SmallInt(i1), SmallInt(i2)) => match i1.checked_sub(i2) {
                Some(x) => SmallInt(x),
                None => BigInt(Integer::from(i1) - Integer::from(i2)),
            },
            (SmallInt(i1), BigInt(i2)) => BigInt(Integer::from(i1) - i2),
            (SmallInt(i1), SmallRat(n2, d2)) => unimplemented!(),
            (SmallInt(i1), BigRat(f2)) => unimplemented!(),
            (BigInt(i1), SmallInt(i2)) => unimplemented!(),
            (BigInt(i1), BigInt(i2)) => BigInt(i1 + i2),
            (BigInt(i1), SmallRat(n2, d2)) => unimplemented!(),
            (BigInt(i1), BigRat(f2)) => unimplemented!(),
            (SmallRat(n1, d1), SmallInt(i2)) => unimplemented!(),
            (SmallRat(n1, d1), BigInt(i2)) => unimplemented!(),
            (SmallRat(n1, d1), SmallRat(n2, d2)) => unimplemented!(),
            (SmallRat(n1, d1), BigRat(f2)) => unimplemented!(),
            (BigRat(f1), SmallInt(i2)) => unimplemented!(),
            (BigRat(f1), BigInt(i2)) => unimplemented!(),
            (BigRat(f1), SmallRat(n2, d2)) => unimplemented!(),
            (BigRat(f1), BigRat(f2)) => unimplemented!(),
        }
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
            (SmallInt(i1), BigInt(i2)) => BigInt(Integer::from(i1) * i2),
            (SmallInt(i1), SmallRat(n2, d2)) => unimplemented!(),
            (SmallInt(i1), BigRat(f2)) => unimplemented!(),
            (BigInt(i1), SmallInt(i2)) => unimplemented!(),
            (BigInt(i1), BigInt(i2)) => BigInt(i1 * i2),
            (BigInt(i1), SmallRat(n2, d2)) => unimplemented!(),
            (BigInt(i1), BigRat(f2)) => unimplemented!(),
            (SmallRat(n1, d1), SmallInt(i2)) => unimplemented!(),
            (SmallRat(n1, d1), BigInt(i2)) => unimplemented!(),
            (SmallRat(n1, d1), SmallRat(n2, d2)) => unimplemented!(),
            (SmallRat(n1, d1), BigRat(f2)) => unimplemented!(),
            (BigRat(f1), SmallInt(i2)) => unimplemented!(),
            (BigRat(f1), BigInt(i2)) => unimplemented!(),
            (BigRat(f1), SmallRat(n2, d2)) => unimplemented!(),
            (BigRat(f1), BigRat(f2)) => unimplemented!(),
        }
    }
}
