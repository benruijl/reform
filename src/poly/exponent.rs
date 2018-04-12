use std::ops::Sub;
use num_traits::{CheckedAdd, One, Zero};
use num_traits::cast::{FromPrimitive, AsPrimitive};
use std::hash::Hash;
use std::fmt::{Debug, Display};

/// Trait for exponents in polynomials.
pub trait Exponent
    : Hash
    + Zero
    + Debug
    + Display
    + One
    + FromPrimitive
    + AsPrimitive<u32>
    + CheckedAdd
    + Sub<Output = Self>
    + Ord
    + Clone {
}

impl<
    T: Hash
        + Zero
        + Debug
        + Display
        + One
        + FromPrimitive
        + AsPrimitive<u32>
        + CheckedAdd
        + Sub<Output = Self>
        + Ord
        + Clone,
> Exponent for T
{
}
