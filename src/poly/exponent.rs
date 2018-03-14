use std::ops::Sub;

use num_traits::{CheckedAdd, Zero};

/// Trait for exponents in polynomials.
pub trait Exponent: Zero + CheckedAdd + Sub<Output = Self> + Ord + Clone {}

impl<T: Zero + CheckedAdd + Sub<Output = Self> + Ord + Clone> Exponent for T {}
