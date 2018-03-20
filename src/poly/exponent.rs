use std::ops::Sub;
use num_traits::{CheckedAdd, One, Zero};
use num_traits::cast::AsPrimitive;

/// Trait for exponents in polynomials.
pub trait Exponent
    : Zero + One + AsPrimitive<usize> + CheckedAdd + Sub<Output = Self> + Ord + Clone
    {
}

impl<T: Zero + One + AsPrimitive<usize> + CheckedAdd + Sub<Output = Self> + Ord + Clone> Exponent
    for T
{
}
