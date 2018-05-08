use num_traits::cast::AsPrimitive;
use num_traits::{One, Pow, Zero};
use poly::raw::zp;
use poly::raw::zp::ufield;
use poly::ring::{MulModNum, ToFiniteField};
use std::fmt;
use std::ops::{Add, Div, Mul, MulAssign, Neg, Rem, Sub};
use tools::GCD;

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct FiniteField {
    pub n: ufield,
    pub p: ufield,
}

impl FiniteField {
    pub fn new(n: ufield, p: ufield) -> FiniteField {
        FiniteField { n: n % p, p: p }
    }

    pub fn from_i64(n: i64, p: ufield) -> FiniteField {
        // TODO: this code is not safe on 32-bit machines
        if n < 0 {
            // note that the remainder % will be negative
            FiniteField {
                n: (p as i64 + (n % p as i64)) as ufield,
                p: p,
            }
        } else {
            FiniteField {
                n: (n % p as i64) as ufield,
                p: p,
            }
        }
    }

    pub fn from_u64(n: u64, p: ufield) -> FiniteField {
        FiniteField {
            n: (n % p as u64) as ufield,
            p: p,
        }
    }

    /// Change the prime (size) of the finite field.
    pub fn set_prime(&mut self, p: ufield) {
        self.p = p;
        self.n = self.n % p;
    }

    // Compute the multiplicative inverse of an element in the field.
    pub fn inverse(n: ufield, p: ufield) -> ufield {
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
        debug_assert_eq!(self.p, other.p);
        FiniteField {
            n: zp::mul(self.n, other.n, self.p),
            p: self.p,
        }
    }
}

impl MulAssign for FiniteField {
    fn mul_assign(&mut self, other: Self) {
        debug_assert_eq!(self.p, other.p);
        self.n = zp::mul(self.n, other.n, self.p);
    }
}

impl Add for FiniteField {
    type Output = Self;

    fn add(self, other: Self) -> Self::Output {
        debug_assert_eq!(self.p, other.p);
        FiniteField {
            n: zp::add(self.n, other.n, self.p),
            p: self.p,
        }
    }
}

impl Sub for FiniteField {
    type Output = Self;

    fn sub(self, other: Self) -> Self::Output {
        debug_assert_eq!(self.p, other.p);

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
        debug_assert_eq!(self.p, other.p);
        FiniteField {
            n: zp::mul(self.n, zp::inv(other.n % self.p, self.p), self.p),
            p: self.p,
        }
    }
}

impl Div<ufield> for FiniteField {
    type Output = Self;

    fn div(self, other: ufield) -> Self::Output {
        FiniteField {
            n: zp::mul(self.n, zp::inv(other % self.p, self.p), self.p),
            p: self.p,
        }
    }
}

impl Mul<ufield> for FiniteField {
    type Output = Self;

    fn mul(self, other: ufield) -> Self::Output {
        FiniteField {
            n: zp::mul(self.n, other % self.p, self.p),
            p: self.p,
        }
    }
}

impl MulModNum for FiniteField {
    fn mul_num(&self, n: ufield) -> FiniteField {
        self.clone() * n
    }

    fn mod_num(&self, n: ufield) -> FiniteField {
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
    fn to_finite_field(&self, p: ufield) -> FiniteField {
        FiniteField::new(self.n, p)
    }

    fn from_finite_field(ff: &FiniteField) -> FiniteField {
        ff.clone()
    }
}

impl AsPrimitive<ufield> for FiniteField {
    fn as_(self) -> ufield {
        self.n
    }
}

impl GCD for FiniteField {
    fn gcd(a: FiniteField, b: FiniteField) -> FiniteField {
        debug_assert_eq!(a.p, b.p);
        if a == b {
            a
        } else {
            FiniteField::new(1, a.p)
        }
    }
}
