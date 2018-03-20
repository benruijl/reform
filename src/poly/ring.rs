use std::ops::{Div, Neg, Rem};

use num_traits::{One, Pow, Zero};

/// Trait for rings.
pub trait Ring
    : Copy
    + Zero
    + One
    + Pow<usize>
    + Neg<Output = Self>
    + Div<Output = Self>
    + Rem<Output = Self>
    + Eq
    + Clone {
}

impl<
    T: Copy
        + Zero
        + One
        + Pow<usize>
        + Neg<Output = Self>
        + Div<Output = Self>
        + Rem<Output = Self>
        + Eq
        + Clone,
> Ring for T
{
}
