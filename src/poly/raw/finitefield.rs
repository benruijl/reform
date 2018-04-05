use num_traits::cast::AsPrimitive;
use num_traits::{One, Pow, Zero};
use poly::ring::{MulModNum, ToFiniteField};
use std::fmt;
use std::ops::{Add, Div, Mul, Neg, Rem, Sub};
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
        let mut t = 0isize;
        let mut newt = 1isize;
        let mut r = p as isize;
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
            panic!("{} is not invertible in ring of size {}", n, p);
        }

        while t < 0 {
            t += p as isize;
        }

        t as usize
    }

    /// Use Garner's algorithm for the Chinese remainder theorem
    /// to reconstruct an x that satisfies n1 = x % p1 and n2 = x % p2.
    /// The x will be in the range [-p1*p2/2,p1*p2/2].
    pub fn chinese_remainder(n1: usize, n2: usize, p1: usize, p2: usize) -> isize {
        if n1 > n2 {
            return FiniteField::chinese_remainder(n2, n1, p2, p1);
        }

        let gamma1 = FiniteField::inverse(p1 % p2, p2);

        // convert to mixed-radix notation
        let v1 = ((n2 - n1) * gamma1) % p2;

        // convert to standard representation
        let r = v1 * p1 + n1;
        if r > p1 * p2 / 2 {
            r as isize - (p1 * p2) as isize // TODO: could overflow!
        } else {
            r as isize
        }
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

impl Sub for FiniteField {
    type Output = Self;

    fn sub(self, other: Self) -> Self::Output {
        assert_eq!(self.p, other.p);

        FiniteField {
            n: if self.n >= other.n {
                (self.n - other.n) % self.p
            } else {
                (self.n + self.p - other.n) % self.p
            },
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
            n: self.p - self.n,
            p: self.p,
        }
    }
}

impl Div for FiniteField {
    type Output = Self;

    fn div(self, other: FiniteField) -> Self::Output {
        FiniteField {
            n: self.n * FiniteField::inverse(other.n, other.p) % self.p,
            p: self.p,
        }
    }
}

impl Div<usize> for FiniteField {
    type Output = Self;

    fn div(self, other: usize) -> Self::Output {
        FiniteField {
            n: self.n * FiniteField::inverse(other % self.p, self.p) % self.p,
            p: self.p,
        }
    }
}

impl Mul<usize> for FiniteField {
    type Output = Self;

    fn mul(self, other: usize) -> Self::Output {
        FiniteField {
            n: self.n * (other % self.p) % self.p,
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

impl Pow<usize> for FiniteField {
    type Output = Self;

    fn pow(self, e: usize) -> Self::Output {
        let mut r = FiniteField::new(1, self.p);
        for _ in 0..e {
            r = r * self;
        }
        r
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
