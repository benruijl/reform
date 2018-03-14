use std::ops::{Div, Neg, Rem};

use num_traits::{One, Zero};

/// Trait for rings.
pub trait Ring
    : Zero + One + Neg<Output = Self> + Div<Output = Self> + Rem<Output = Self> + Eq + Clone
    {
}

impl<T: Zero + One + Neg<Output = Self> + Div<Output = Self> + Rem<Output = Self> + Eq + Clone> Ring
    for T
{
}
