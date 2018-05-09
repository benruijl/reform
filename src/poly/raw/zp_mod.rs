//! Routines for modulo operation.

/// Abstraction of modulo operation.
pub trait Modulus<N, M>: Copy {
    /// Returns the modulo.
    fn value(&self) -> M;

    /// Modulo operation giving `x % modulo`.
    fn modulous(&self, x: N) -> N;
}

// Implementation for primitives.

impl Modulus<u64, u32> for u32 {
    #[inline]
    fn value(&self) -> u32 {
        *self
    }

    #[inline]
    fn modulous(&self, x: u64) -> u64 {
        x % u64::from(*self)
    }
}
