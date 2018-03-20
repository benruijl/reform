use num_traits::{One, Zero};
use std::ops::{Add, Div, Mul, Neg, Rem};
use std::fmt;

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct FiniteField {
    n: usize,
    p: usize,
}

impl FiniteField {
    pub fn new(n: usize, p: usize) -> FiniteField {
        FiniteField { n, p }
    }

    /// Change the prime (size) of the finite field.
    pub fn set_prime(&mut self, p: usize) {
        self.p = p;
        self.n = self.n % p;
    }

    // Compute the multiplicative inverse of an element in the field.
    pub fn inverse(&self, n: usize) -> usize {
        let mut t = 0isize;
        let mut newt = 1isize;
        let mut r = self.p as isize;
        let mut newr = n as isize;

        while newr != 0 {
            let q = r / newr;
            let mut tmp = t;
            t = newt;
            newt = tmp - q * newt;
            tmp = r;
            r = newr;
            newr = tmp - q * newr;
        }
        if r > 1 {
            panic!("{} is not invertible in ring of size {}", n, self.p);
        }
        if t < 0 {
            t += n as isize;
        }

        t as usize
    }
}

impl fmt::Display for FiniteField {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.n)
    }
}

impl Mul for FiniteField {
    type Output = Self;

    fn mul(self, other: Self) -> Self::Output {
        assert_eq!(self.p, other.p);
        FiniteField {
            n: (self.n * other.n) % self.p,
            p: self.p,
        }
    }
}

impl Add for FiniteField {
    type Output = Self;

    fn add(self, other: Self) -> Self::Output {
        assert_eq!(self.p, other.p);
        FiniteField {
            n: (self.n + other.n) % self.p,
            p: self.p,
        }
    }
}

impl Zero for FiniteField {
    fn zero() -> Self {
        FiniteField { n: 0, p: 1 }
    }

    fn is_zero(&self) -> bool {
        self.n == 0
    }
}

impl One for FiniteField {
    fn one() -> FiniteField {
        FiniteField { n: 1, p: 1 }
    }
}

impl Neg for FiniteField {
    type Output = Self;

    fn neg(self) -> Self::Output {
        FiniteField {
            n: self.p - self.n,
            p: self.p,
        }
    }
}

impl Div for FiniteField {
    type Output = Self;

    fn div(self, other: FiniteField) -> Self::Output {
        FiniteField {
            n: self.n * other.inverse(other.n) % self.p,
            p: self.p,
        }
    }
}

impl Rem for FiniteField {
    type Output = Self;

    fn rem(self, _other: Self) -> Self::Output {
        return FiniteField::zero();
    }
}
