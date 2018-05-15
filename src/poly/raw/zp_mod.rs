//! Routines for modulo operation.

use fastdivide;

/// Abstraction of modulo operation.
pub trait Modulus<N, M>: Copy {
    /// Returns the modulo.
    fn value(&self) -> M;

    /// Modulo operation giving `x % modulo`.
    fn modulus(&self, x: N) -> N;
}

// Implementation for primitives.

impl Modulus<u64, u32> for u32 {
    #[inline]
    fn value(&self) -> u32 {
        *self
    }

    #[inline]
    fn modulus(&self, x: u64) -> u64 {
        x % u64::from(*self)
    }
}

/// Fast modulo operation for `u64 % u32`.
pub struct FastModulus6432 {
    n: u32,
    magic: fastdivide::DividerU64,
}

impl FastModulus6432 {
    /// Construct a fast modulo operation.
    #[inline]
    pub fn from(n: u32) -> FastModulus6432 {
        FastModulus6432 {
            n,
            magic: fastdivide::DividerU64::divide_by(u64::from(n)),
        }
    }
}

impl<'a> Modulus<u64, u32> for &'a FastModulus6432 {
    #[inline]
    fn value(&self) -> u32 {
        self.n
    }

    #[inline]
    fn modulus(&self, x: u64) -> u64 {
        // TODO: for now DividerU64 is used, but is it possible to make use of the fact that
        // the modulo fits in u32?
        let division = self.magic.divide(x);
        x - division * u64::from(self.n)
    }
}
