use num_traits::{One, Pow, Zero};
use std::fmt;
use std::ops::{Add, Div, Mul, Neg, Rem};
use tools::GCD;

use num_traits::cast::AsPrimitive;

use poly::raw::finitefield::FiniteField;
use poly::raw::zp::ufield;
use poly::ring::{MulModNum, ToFiniteField};

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct Fraction {
    num: isize,
    den: usize,
}

impl Fraction {
    pub fn new(num: isize, den: usize) -> Fraction {
        Fraction { num, den }
    }
}

impl fmt::Display for Fraction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}/{}", self.num, self.den)
    }
}

impl Mul for Fraction {
    type Output = Self;

    fn mul(self, other: Self) -> Self::Output {
        let gcd1 = GCD::gcd(
            if self.num >= 0 {
                self.num as usize
            } else {
                -self.num as usize
            },
            other.den,
        );
        let gcd2 = GCD::gcd(
            if other.num >= 0 {
                other.num as usize
            } else {
                -other.num as usize
            },
            self.den,
        );
        let num = (self.num / (gcd1 as isize)) * (other.num / (gcd2 as isize));
        let den = (self.den / gcd2) * (other.den / gcd1);

        Fraction { num, den }
    }
}

impl Add for Fraction {
    type Output = Self;

    fn add(self, other: Self) -> Self::Output {
        Fraction {
            // TODO: use gcd
            num: self.num * (other.den as isize) + other.num * (self.den as isize),
            den: self.den * other.den,
        }
    }
}

impl Zero for Fraction {
    fn zero() -> Self {
        Fraction { num: 0, den: 1 }
    }

    fn is_zero(&self) -> bool {
        self.num == 0
    }
}

impl One for Fraction {
    fn one() -> Fraction {
        Fraction { num: 1, den: 1 }
    }
}

impl Neg for Fraction {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Fraction {
            num: -self.num,
            den: self.den,
        }
    }
}

impl Div for Fraction {
    type Output = Self;

    fn div(self, other: Fraction) -> Self::Output {
        let gcd1 = GCD::gcd(
            if self.num >= 0 {
                self.num as usize
            } else {
                -self.num as usize
            },
            if other.num >= 0 {
                other.num as usize
            } else {
                -other.num as usize
            },
        );
        let gcd2 = GCD::gcd(self.den, other.den);

        if other.num < 0 {
            Fraction {
                num: -(self.num / (gcd1 as isize)) * ((other.den as isize) / (gcd2 as isize)),
                den: (self.den / gcd2) * ((-other.num as usize) / gcd1),
            }
        } else {
            Fraction {
                num: (self.num / (gcd1 as isize)) * ((other.den as isize) / (gcd2 as isize)),
                den: (self.den / gcd2) * ((other.num as usize) / gcd1),
            }
        }
    }
}

impl Div<usize> for Fraction {
    type Output = Self;

    fn div(self, other: usize) -> Self::Output {
        let gcd = GCD::gcd(self.num, other as isize) as usize;

        Fraction {
            num: self.num / gcd as isize,
            den: self.den * (other / gcd),
        }
    }
}

impl Mul<usize> for Fraction {
    type Output = Self;

    fn mul(self, other: usize) -> Self::Output {
        let gcd = GCD::gcd(self.den, other);

        Fraction {
            num: self.num * ((other / gcd) as isize),
            den: self.den / gcd,
        }
    }
}

impl MulModNum for Fraction {
    fn mul_num(&self, n: ufield) -> Fraction {
        self.clone() * (n as usize)
    }

    fn mod_num(&self, n: ufield) -> Fraction {
        self.clone() % Fraction::new(n as isize, 1)
    }
}

impl Rem for Fraction {
    type Output = Self;

    fn rem(self, _other: Self) -> Self::Output {
        return Fraction::zero();
    }
}

impl Pow<usize> for Fraction {
    type Output = Self;

    fn pow(self, e: usize) -> Self::Output {
        let mut r = Fraction::one();
        for _ in 0..e {
            r = r * self;
        }
        r
    }
}

impl ToFiniteField for Fraction {
    fn to_finite_field(&self, p: ufield) -> FiniteField {
        FiniteField::from_i64(self.num as i64, p) / FiniteField::from_u64(self.den as u64, p)
    }

    fn from_finite_field(ff: &FiniteField) -> Fraction {
        Fraction {
            num: ff.n as isize,
            den: 1,
        }
    }
}

impl AsPrimitive<usize> for Fraction {
    fn as_(self) -> usize {
        unreachable!("Cannot convert fraction to integer");
    }
}
