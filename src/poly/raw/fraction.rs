use num_traits::{One, Pow, Zero};
use std::fmt;
use std::ops::{Add, Div, Mul, Neg, Rem};
use tools::gcd;

use num_traits::cast::AsPrimitive;

use poly::raw::finitefield::FiniteField;
use poly::ring::ToFiniteField;

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
        let gcd1 = gcd(
            if self.num >= 0 {
                self.num as usize
            } else {
                -self.num as usize
            },
            other.den,
        );
        let gcd2 = gcd(
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
        let gcd1 = gcd(
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
        let gcd2 = gcd(self.den, other.den);

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

impl Rem for Fraction {
    type Output = Self;

    fn rem(self, _other: Self) -> Self::Output {
        return Fraction::zero();
    }
}

impl Pow<usize> for Fraction {
    type Output = Self;

    fn pow(self, e: usize) -> Self::Output {
        let mut r = self.clone();
        for _ in 0..e {
            r = r * r;
        }
        r
    }
}

impl ToFiniteField for Fraction {
    fn to_finite_field(&self, p: usize) -> FiniteField {
        if self.num < 0 {
            FiniteField::new((-self.num / p as isize + self.num + 1) as usize, p)
                / FiniteField::new(self.den, p)
        } else {
            FiniteField::new(self.num as usize, p) / FiniteField::new(self.den, p)
        }
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
