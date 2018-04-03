use num_traits::cast::AsPrimitive;
use num_traits::{One, Pow, Zero};
use poly::raw::finitefield::FiniteField;
use std::fmt::{Debug, Display};
use std::ops::{Div, Neg, Rem};

pub trait MulNum {
    fn mul_num(&self, n: usize) -> Self;
}

pub trait ToFiniteField {
    fn to_finite_field(&self, p: usize) -> FiniteField;
    fn from_finite_field(&FiniteField) -> Self;
}

/// Trait for rings.
pub trait Ring:
    Copy
    + Zero
    + One
    + Debug
    + Display
    + MulNum
    + AsPrimitive<usize>
    + Pow<usize, Output = Self>
    + Neg<Output = Self>
    + Div<Output = Self>
    + Rem<Output = Self>
    + ToFiniteField
    + Eq
    + Clone
{
}

impl<
        T: Copy
            + Zero
            + One
            + Debug
            + Display
            + MulNum
            + AsPrimitive<usize>
            + Pow<usize, Output = Self>
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
    fn to_finite_field(&self, p: usize) -> FiniteField {
        if *self < 0 {
            FiniteField::new((-*self / p as i64 + *self + 1) as usize, p)
        } else {
            FiniteField::new(*self as usize, p)
        }
    }

    fn from_finite_field(ff: &FiniteField) -> i64 {
        ff.n as i64
    }
}

impl MulNum for i64 {
    fn mul_num(&self, n: usize) -> i64 {
        self * (n as i64)
    }
}
