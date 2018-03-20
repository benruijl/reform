use std::ops::Sub;
use num_traits::{CheckedAdd, One, Zero};
use num_traits::cast::AsPrimitive;
use std::hash::Hash;

/// Trait for exponents in polynomials.
pub trait Exponent
    : Hash + Zero + One + AsPrimitive<usize> + CheckedAdd + Sub<Output = Self> + Ord + Clone
    {
}

impl<
    T: Hash + Zero + One + AsPrimitive<usize> + CheckedAdd + Sub<Output = Self> + Ord + Clone,
> Exponent for T
{
}
