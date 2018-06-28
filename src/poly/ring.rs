use num_traits::{One, Pow, Zero};
use number::Number;
use poly::raw::finitefield::FiniteField;
use poly::raw::zp::ufield;
use rug::Integer;
use std::fmt::{Debug, Display};
use std::hash::Hash;
use std::ops::{Div, MulAssign, Neg, Rem};
use tools::GCD;

pub trait MulModNum {
    fn mul_num(&self, n: ufield) -> Self;
    fn mod_num(&self, n: ufield) -> Self;
}

pub trait ToFiniteField {
    fn to_finite_field(&self, p: ufield) -> FiniteField;
    fn from_finite_field(&FiniteField) -> Self;
}

/// Trait for rings.
pub trait Ring:
   // Copy
    Zero
    + Hash
    + One
    + Debug
    + Display
    + MulModNum
    + GCD
    + Pow<u32, Output = Self>
    + MulAssign
    + Neg<Output = Self>
    + Div<Output = Self>
    + Rem<Output = Self>
    + ToFiniteField
    + Eq
    + Clone
{
}

impl<
        T: Zero
            + Hash
            + One
            + Debug
            + Display
            + MulModNum
            + GCD
            + Pow<u32, Output = Self>
            + MulAssign
            + Neg<Output = Self>
            + Div<Output = Self>
            + Rem<Output = Self>
            + ToFiniteField
            + Eq
            + Clone,
    > Ring for T
{
}

impl ToFiniteField for i64 {
    fn to_finite_field(&self, p: ufield) -> FiniteField {
        FiniteField::from_i64(*self, p)
    }

    fn from_finite_field(ff: &FiniteField) -> i64 {
        if ff.n > ff.p / 2 {
            ff.n as i64 - ff.p as i64
        } else {
            ff.n as i64
        }
    }
}

impl MulModNum for i64 {
    fn mul_num(&self, n: ufield) -> i64 {
        self * (n as i64)
    }

    fn mod_num(&self, n: ufield) -> i64 {
        self % (n as i64)
    }
}

impl MulModNum for Number {
    fn mul_num(&self, n: ufield) -> Number {
        self.clone() * Number::SmallInt(n as isize)
    }

    fn mod_num(&self, n: ufield) -> Number {
        self.clone() % Number::SmallInt(n as isize)
    }
}

impl ToFiniteField for Number {
    fn to_finite_field(&self, p: ufield) -> FiniteField {
        match *self {
            Number::SmallInt(i) => FiniteField::from_i64(i as i64, p),
            Number::BigInt(ref i) => {
                FiniteField::from_i64((i.clone() % Integer::from(p)).to_i64().unwrap(), p)
            }
            _ => unreachable!(),
        }
    }

    fn from_finite_field(ff: &FiniteField) -> Number {
        Number::SmallInt(if ff.n > ff.p / 2 {
            ff.n as isize - ff.p as isize
        } else {
            ff.n as isize
        })
    }
}
