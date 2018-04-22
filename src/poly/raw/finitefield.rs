use num_traits::cast::AsPrimitive;
use num_traits::{One, Pow, Zero};
use poly::raw::zp;
use poly::ring::{MulModNum, ToFiniteField};
use std::fmt;
use std::ops::{Add, Div, Mul, MulAssign, Neg, Rem, Sub};
use tools::GCD;

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct FiniteField {
    pub n: usize,
    pub p: usize,
}

impl FiniteField {
    pub fn new(n: usize, p: usize) -> FiniteField {
        FiniteField { n: n % p, p: p }
    }

    /// Change the prime (size) of the finite field.
    pub fn set_prime(&mut self, p: usize) {
        self.p = p;
        self.n = self.n % p;
    }

    // Compute the multiplicative inverse of an element in the field.
    pub fn inverse(n: usize, p: usize) -> usize {
        zp::inv(n, p)
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
            n: zp::mul(self.n, other.n, self.p),
            p: self.p,
        }
    }
}

impl MulAssign for FiniteField {
    fn mul_assign(&mut self, other: Self) {
        assert_eq!(self.p, other.p);
        self.n = zp::mul(self.n, other.n, self.p);
    }
}

impl Add for FiniteField {
    type Output = Self;

    fn add(self, other: Self) -> Self::Output {
        assert_eq!(self.p, other.p);
        FiniteField {
            n: zp::add(self.n, other.n, self.p),
            p: self.p,
        }
    }
}

impl Sub for FiniteField {
    type Output = Self;

    fn sub(self, other: Self) -> Self::Output {
        assert_eq!(self.p, other.p);

        FiniteField {
            n: zp::sub(self.n, other.n, self.p),
            p: self.p,
        }
    }
}

impl Zero for FiniteField {
    fn zero() -> Self {
        FiniteField { n: 0, p: 2 }
    }

    fn is_zero(&self) -> bool {
        self.n == 0
    }
}

impl One for FiniteField {
    fn one() -> FiniteField {
        FiniteField { n: 1, p: 2 }
    }

    fn is_one(&self) -> bool {
        self.n == 1
    }
}

impl Neg for FiniteField {
    type Output = Self;

    fn neg(self) -> Self::Output {
        FiniteField {
            n: zp::neg(self.n, self.p),
            p: self.p,
        }
    }
}

impl Div for FiniteField {
    type Output = Self;

    fn div(self, other: FiniteField) -> Self::Output {
        assert_eq!(self.p, other.p);
        FiniteField {
            n: zp::mul(self.n, zp::inv(other.n % self.p, self.p), self.p),
            p: self.p,
        }
    }
}

impl Div<usize> for FiniteField {
    type Output = Self;

    fn div(self, other: usize) -> Self::Output {
        FiniteField {
            n: zp::mul(self.n, zp::inv(other % self.p, self.p), self.p),
            p: self.p,
        }
    }
}

impl Mul<usize> for FiniteField {
    type Output = Self;

    fn mul(self, other: usize) -> Self::Output {
        FiniteField {
            n: zp::mul(self.n, other % self.p, self.p),
            p: self.p,
        }
    }
}

impl MulModNum for FiniteField {
    fn mul_num(&self, n: usize) -> FiniteField {
        self.clone() * n
    }

    fn mod_num(&self, n: usize) -> FiniteField {
        self.clone() % FiniteField::new(n, self.p)
    }
}

impl Rem for FiniteField {
    type Output = Self;

    fn rem(self, _other: Self) -> Self::Output {
        return FiniteField::zero();
    }
}

impl Pow<u32> for FiniteField {
    type Output = Self;

    fn pow(self, e: u32) -> Self::Output {
        FiniteField::new(zp::pow(self.n, e, self.p), self.p)
    }
}

impl ToFiniteField for FiniteField {
    fn to_finite_field(&self, p: usize) -> FiniteField {
        FiniteField::new(self.n, p)
    }

    fn from_finite_field(ff: &FiniteField) -> FiniteField {
        ff.clone()
    }
}

impl AsPrimitive<usize> for FiniteField {
    fn as_(self) -> usize {
        self.n
    }
}

impl GCD for FiniteField {
    fn gcd(a: FiniteField, b: FiniteField) -> FiniteField {
        assert_eq!(a.p, b.p);
        if a == b {
            a
        } else {
            FiniteField::new(1, a.p)
        }
    }
}
