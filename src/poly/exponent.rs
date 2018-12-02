use num_traits::cast::{AsPrimitive, FromPrimitive};
use num_traits::{CheckedAdd, One, Zero};
use std::fmt::{Debug, Display};
use std::hash::Hash;
use std::ops::Sub;

/// Trait for exponents in polynomials.
pub trait Exponent:
    Hash
    + Zero
    + Debug
    + Display
    + One
    + FromPrimitive
    + AsPrimitive<u32>
    + CheckedAdd
    + Sub<Output = Self>
    + Ord
    + Clone
{
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
