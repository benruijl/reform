use num_traits;
use num_traits::{checked_pow, Inv, One, Zero};
use rug::ops::Pow;
use rug::{Integer, Rational};
use std::cmp::Ordering;
use std::fmt;
use std::mem;
use std::ops::{Add, AddAssign, Div, Mul, MulAssign, Neg, Rem, Sub};
use tools::GCD;

#[macro_export]
macro_rules! DUMMY_NUM {
    () => {
        Number::zero()
    };
}

const DOWNGRADE_LIMIT: isize = 4294967296; // if a bigint is smaller than this number, we downgrade

/// A number is either a small number consisting of machine sized
/// integers or a big number, using GMP.
///
/// The mathematical operations on a number automatically upgrade
/// and downgrade to bigint/smallint etc.
/// TODO: hash should take into account that some bigints can be equal to smallint?
#[derive(Debug, Clone, Hash)]
pub enum Number {
    SmallInt(isize),
    BigInt(Integer),
    SmallRat(isize, isize),
    BigRat(Box<Rational>),
}

impl Number {
    pub fn normalize_inplace(&mut self) -> bool {
        *self = match *self {
            Number::SmallInt(_) => return false,
            Number::SmallRat(ref mut n, ref mut d) => {
                if *d == 1 {
                    Number::SmallInt(*n)
                } else if *d < 0 {
                    *d = -*d;
                    *n = -*n;

                    if *d == 1 {
                        Number::SmallInt(*n)
                    } else {
                        return true;
                    }
                } else {
                    return false;
                }
            }
            Number::BigInt(ref i) => {
                if *i < DOWNGRADE_LIMIT && *i > -DOWNGRADE_LIMIT {
                    Number::SmallInt(i.to_isize().expect("Number too large to downgrade"))
                } else {
                    return false;
                }
            }
            Number::BigRat(ref mut r) => {
                if *r.denom() != 1 {
                    return false;
                }
                if *r.numer() < DOWNGRADE_LIMIT && *r.numer() > -DOWNGRADE_LIMIT {
                    Number::SmallInt(r.numer().to_isize().expect("Number too large to downgrade"))
                } else {
                    Number::BigInt(mem::replace(&mut **r, Rational::new()).into_numer_denom().0)
                }
            }
        };
        true
    }

    #[inline]
    pub fn normalized(mut self) -> Self {
        self.normalize_inplace();
        self
    }

    /// Returns the factorial of the number.
    pub fn factorial(self) -> Number {
        match self {
            Number::SmallInt(n) => {
                #[cfg(target_pointer_width = "32")]
                {
                    if n <= 12 {
                        let mut r = 1;
                        for k in 2..=n {
                            r *= k;
                        }
                        return Number::SmallInt(r);
                    }
                }
                #[cfg(target_pointer_width = "64")]
                {
                    if n <= 20 {
                        let mut r = 1;
                        for k in 2..=n {
                            r *= k;
                        }
                        return Number::SmallInt(r);
                    }
                }
                let mut r = Number::SmallInt(1);
                for k in 2..n + 1 {
                    r *= Number::SmallInt(k);
                }
                r
            }
            Number::SmallRat(..) => panic!("Cannot take factorial of fraction"),
            Number::BigInt(..) => unimplemented!(), // rug does not support it?
            Number::BigRat(..) => panic!("Cannot take factorial of fraction"),
        }
    }

    pub fn abs(&self) -> Number {
        match self {
            Number::SmallInt(i) => match i.checked_abs() {
                Some(x) => Number::SmallInt(x),
                None => -self.clone(),
            },
            Number::SmallRat(n, d) => match n.checked_abs() {
                Some(x) => Number::SmallRat(x, *d),
                None => Number::BigRat(Box::new(Rational::from((
                    -Integer::from(*n),
                    Integer::from(*d),
                )))),
            },
            Number::BigInt(ref i) => Number::BigInt(i.clone().abs()),
            Number::BigRat(ref r) => Number::BigRat(Box::new(r.clone().abs())),
        }
    }
}

impl PartialEq for Number {
    /// Compare numbers. Big integers can also match small integers.
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Number::SmallInt(i1), Number::SmallInt(i2)) => i1 == i2,
            (Number::BigInt(i1), Number::BigInt(i2)) => i1 == i2,
            (Number::SmallInt(i1), Number::BigInt(i2)) => i1 == i2,
            (Number::BigInt(i1), Number::SmallInt(i2)) => i1 == i2,
            (Number::SmallRat(i1, d1), Number::SmallRat(i2, d2)) => i1 == i2 && d1 == d2,
            (Number::BigRat(i1), Number::BigRat(i2)) => i1 == i2,
            _ => false,
        }
    }
}

impl Eq for Number {}

impl fmt::Display for Number {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Number::SmallInt(i) => write!(f, "{}", i),
            Number::SmallRat(n, d) => write!(f, "{}/{}", n, d),
            Number::BigInt(ref i) => write!(f, "{}", i.to_string_radix(10)),
            Number::BigRat(ref r) => write!(f, "{}", r.to_string_radix(10)),
        }
    }
}

impl Zero for Number {
    #[inline]
    fn zero() -> Number {
        Number::SmallInt(0)
    }

    #[inline]
    fn is_zero(&self) -> bool {
        match *self {
            Number::SmallInt(i) => i == 0,
            Number::BigInt(ref i) => *i == 0, // TODO: is this fast?
            Number::SmallRat(n, _d) => n == 0,
            Number::BigRat(ref f) => *f.numer() == 0 && *f.denom() == 1,
        }
    }
}

impl GCD for Number {
    fn gcd(a: Number, b: Number) -> Number {
        use self::Number::*;
        match (a, b) {
            (SmallInt(i1), SmallInt(i2)) => SmallInt(GCD::gcd(i1, i2)),
            (SmallInt(i1), BigInt(i2)) | (BigInt(i2), SmallInt(i1)) => {
                BigInt(i2.gcd(&Integer::from(i1)))
            }
            (BigInt(i1), BigInt(i2)) => BigInt(i1.gcd(&i2)),
            (x, y) => unreachable!(format!("Cannot compute gcd of {:?} and {:?}", x, y)),
        }
    }
}

impl One for Number {
    #[inline]
    fn one() -> Number {
        Number::SmallInt(1)
    }

    #[inline]
    fn is_one(&self) -> bool {
        match *self {
            Number::SmallInt(i) => i == 1,
            Number::BigInt(ref i) => *i == 1,
            Number::SmallRat(n, _d) => n == 1,
            Number::BigRat(ref f) => *f.numer() == 1 && *f.denom() == 1,
        }
    }
}

impl Neg for Number {
    type Output = Number;

    fn neg(self) -> Self::Output {
        match self {
            Number::SmallInt(i) => {
                if i == isize::min_value() {
                    Number::BigInt(-Integer::from(i))
                } else {
                    Number::SmallInt(-i)
                }
            }
            Number::BigInt(i) => Number::BigInt(-i),
            Number::SmallRat(n, d) => {
                if n == isize::min_value() {
                    Number::BigRat(Box::new(Rational::from((
                        -Integer::from(n),
                        Integer::from(d),
                    ))))
                } else {
                    Number::SmallRat(-n, d)
                }
            }
            Number::BigRat(f) => Number::BigRat(Box::new(-*f)),
        }
    }
}

impl Inv for Number {
    type Output = Number;

    fn inv(self) -> Self::Output {
        match self {
            Number::SmallInt(i) => Number::SmallRat(1, i),
            Number::BigInt(i) => Number::BigRat(Box::new(Rational::from((1, i)))),
            Number::SmallRat(n, d) => Number::SmallRat(d, n),
            Number::BigRat(f) => Number::BigRat(Box::new((*f).recip())),
        }
    }
}

impl PartialOrd for Number {
    #[inline]
    fn partial_cmp(&self, rhs: &Number) -> Option<Ordering> {
        use self::Number::*;
        match (self, rhs) {
            (&SmallInt(ref i1), SmallInt(ref i2)) => i1.partial_cmp(i2),
            (&SmallInt(ref i1), BigInt(ref i2)) => Integer::from(*i1).partial_cmp(i2),
            (&SmallInt(ref i1), SmallRat(n2, d2)) => (i1 * d2).partial_cmp(n2), // TODO: check for overflow
            (&SmallInt(ref i1), BigRat(ref f2)) => Rational::from(*i1).partial_cmp(&**f2),
            (&BigInt(ref i1), SmallInt(i2)) => i1.partial_cmp(i2),
            (&BigInt(ref i1), BigInt(ref i2)) => i1.partial_cmp(i2),
            (&BigInt(ref i1), SmallRat(n2, d2)) => (i1 * Integer::from(*d2)).partial_cmp(n2),
            (&BigInt(ref i1), BigRat(ref f2)) => i1.partial_cmp(&**f2),
            (&SmallRat(n1, d1), SmallInt(i2)) => n1.partial_cmp(&(i2 * d1)), // TODO: check for overflow
            (&SmallRat(n1, d1), BigInt(ref i2)) => n1.partial_cmp(&(i2 * Integer::from(d1))),
            (&SmallRat(n1, d1), SmallRat(n2, d2)) => {
                // TODO: improve
                if n1 < 0 && *n2 > 0 {
                    return Some(Ordering::Less);
                }
                if n1 > 0 && *n2 < 0 {
                    return Some(Ordering::Greater);
                }

                (Number::SmallInt(n1) * Number::SmallInt(*d2))
                    .partial_cmp(&(Number::SmallInt(*n2) * Number::SmallInt(d1)))
            }
            (&SmallRat(n1, d1), BigRat(ref f2)) => Rational::from((n1, d1)).partial_cmp(&**f2),
            (&BigRat(ref f1), SmallInt(i2)) => (**f1).partial_cmp(&Rational::from(*i2)),
            (&BigRat(ref f1), BigInt(ref i2)) => (**f1).partial_cmp(&Rational::from(i2)),
            (&BigRat(ref f1), SmallRat(n2, d2)) => (**f1).partial_cmp(&Rational::from((*n2, *d2))),
            (&BigRat(ref f1), BigRat(ref f2)) => f1.partial_cmp(f2),
        }
    }
}

impl Ord for Number {
    #[inline]
    fn cmp(&self, other: &Number) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl Number {
    fn add_full(self, rhs: Number) -> Number {
        use self::Number::*;
        match (self, rhs) {
            (SmallInt(i1), SmallInt(i2)) => match i1.checked_add(i2) {
                Some(x) => SmallInt(x),
                None => BigInt(Integer::from(i1) + Integer::from(i2)),
            },
            (SmallInt(i1), BigInt(i2)) | (BigInt(i2), SmallInt(i1)) => {
                BigInt(Integer::from(i1) + i2)
            }
            (SmallInt(i1), SmallRat(n2, d2)) | (SmallRat(n2, d2), SmallInt(i1)) => match i1
                .checked_mul(d2)
            {
                Some(num1) => match n2.checked_add(num1) {
                    Some(num) => Number::SmallRat(num, d2).normalized(),
                    None => Number::BigRat(Box::new(Rational::from(i1) + Rational::from((n2, d2))))
                        .normalized(),
                },
                None => Number::BigRat(Box::new(Rational::from(i1) + Rational::from((n2, d2))))
                    .normalized(),
            },
            (SmallRat(n1, d1), SmallRat(n2, d2)) => match d2.checked_mul(d1 / GCD::gcd(d1, d2)) {
                Some(lcm) => match n2.checked_mul(lcm / d2) {
                    Some(num2) => match n1.checked_mul(lcm / d1) {
                        Some(num1) => match num1.checked_add(num2) {
                            Some(num) => {
                                if num % lcm == 0 {
                                    Number::SmallInt(num / lcm)
                                } else {
                                    Number::SmallRat(num, lcm)
                                }
                            }
                            None => Number::BigRat(Box::new(
                                Rational::from((n1, d1)) + Rational::from((n2, d2)),
                            )),
                        },
                        None => Number::BigRat(Box::new(
                            Rational::from((n1, d1)) + Rational::from((n2, d2)),
                        )),
                    },
                    None => Number::BigRat(Box::new(
                        Rational::from((n1, d1)) + Rational::from((n2, d2)),
                    )),
                },
                None => Number::BigRat(Box::new(
                    Rational::from((n1, d1)) + Rational::from((n2, d2)),
                )),
            },
            (SmallInt(i1), BigRat(f2)) | (BigRat(f2), SmallInt(i1)) => {
                Number::BigRat(Box::new(*f2 + Rational::from(i1)))
            }
            (BigInt(i1), BigInt(i2)) => BigInt(i1 + i2),
            (BigInt(i1), SmallRat(n2, d2)) | (SmallRat(n2, d2), BigInt(i1)) => {
                Number::BigRat(Box::new(Rational::from(i1) + Rational::from((n2, d2))))
            }
            (BigInt(i1), BigRat(f2)) | (BigRat(f2), BigInt(i1)) => {
                Number::BigRat(Box::new(*f2 + Rational::from(i1)))
            }
            (BigRat(f1), SmallRat(n2, d2)) | (SmallRat(n2, d2), BigRat(f1)) => {
                Number::BigRat(Box::new(*f1 + Rational::from((n2, d2))))
            }
            (BigRat(f1), BigRat(f2)) => BigRat(Box::new(*f1 + *f2)),
        }
    }
}

impl Add for Number {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Number) -> Number {
        use self::Number::*;
        match (self, rhs) {
            (SmallInt(i1), SmallInt(i2)) => match i1.checked_add(i2) {
                Some(x) => SmallInt(x),
                None => BigInt(Integer::from(i1) + Integer::from(i2)),
            },
            (lhs, rhs1) => lhs.add_full(rhs1),
        }
    }
}

impl Sub for Number {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: Number) -> Number {
        self + (-rhs)
    }
}

impl Mul for Number {
    type Output = Self;

    fn mul(self, rhs: Number) -> Number {
        use self::Number::*;
        match (self, rhs) {
            (SmallInt(i1), SmallInt(i2)) => match i1.checked_mul(i2) {
                Some(x) => SmallInt(x),
                None => BigInt(Integer::from(i1) * Integer::from(i2)),
            },
            (SmallInt(i1), BigInt(i2)) | (BigInt(i2), SmallInt(i1)) => {
                BigInt(Integer::from(i1) * i2)
            }
            (SmallInt(i1), SmallRat(n2, mut d2)) | (SmallRat(n2, mut d2), SmallInt(i1)) => {
                let gcd = GCD::gcd(i1, d2);
                d2 /= gcd;

                match n2.checked_mul(i1 / gcd) {
                    Some(x) => {
                        if d2 == 1 {
                            Number::SmallInt(x)
                        } else {
                            Number::SmallRat(x, d2).normalized()
                        }
                    }
                    None => {
                        if d2 == 1 {
                            Number::BigInt(Integer::from(n2) * Integer::from(i1 / gcd))
                        } else {
                            Number::BigRat(Box::new(Rational::from((
                                Integer::from(n2) * Integer::from(i1 / gcd),
                                d2,
                            ))))
                        }
                    }
                }
            }
            (SmallRat(n1, d1), SmallRat(n2, d2)) => {
                let gcd1 = GCD::gcd(n1, d2);
                let gcd2 = GCD::gcd(n2, d1);

                match (n2 / gcd2).checked_mul(n1 / gcd1) {
                    Some(nn) => match (d1 / gcd2).checked_mul(d2 / gcd1) {
                        Some(nd) => Number::SmallRat(nn, nd),
                        None => Number::BigRat(Box::new(Rational::from((
                            nn,
                            Integer::from(d1 / gcd2) * Integer::from(d2 / gcd1),
                        )))),
                    },
                    None => Number::BigRat(Box::new(Rational::from((
                        Integer::from(n1 / gcd1) * Integer::from(n2 / gcd2),
                        Integer::from(d1 / gcd2) * Integer::from(d2 / gcd1),
                    )))),
                }
            }
            (SmallInt(i1), BigRat(f2)) | (BigRat(f2), SmallInt(i1)) => {
                Number::BigRat(Box::new(*f2 * Rational::from(i1))).normalized()
            }
            (BigInt(i1), BigInt(i2)) => BigInt(i1 * i2),
            (BigInt(i1), SmallRat(n2, d2)) | (SmallRat(n2, d2), BigInt(i1)) => {
                Number::BigRat(Box::new(Rational::from(i1) * Rational::from((n2, d2)))).normalized()
            }
            (BigInt(i1), BigRat(f2)) | (BigRat(f2), BigInt(i1)) => {
                Number::BigRat(Box::new(*f2 * Rational::from(i1))).normalized()
            }
            (BigRat(f1), SmallRat(n2, d2)) | (SmallRat(n2, d2), BigRat(f1)) => {
                Number::BigRat(Box::new(*f1 * Rational::from((n2, d2)))).normalized()
            }
            (BigRat(f1), BigRat(f2)) => BigRat(Box::new(*f1 * *f2)).normalized(),
        }
    }
}

impl Div for Number {
    type Output = Self;

    #[inline]
    fn div(self, rhs: Number) -> Number {
        self * rhs.inv() // TODO: optimize
    }
}

impl Rem for Number {
    type Output = Self;

    fn rem(self, rhs: Number) -> Number {
        use self::Number::*;
        match (self, rhs) {
            (SmallInt(i1), SmallInt(i2)) => SmallInt(i1 % i2), // TODO: make positive?
            (SmallInt(i1), BigInt(i2)) => BigInt(Integer::from(i1) % i2),
            (BigInt(i1), SmallInt(i2)) => BigInt(i1 % Integer::from(i2)),
            (BigInt(i1), BigInt(i2)) => BigInt(i1 % i2),
            (x, y) => unreachable!(format!("Cannot compute remainder {:?} rem {:?}", x, y)),
        }
    }
}

impl num_traits::Pow<u32> for Number {
    type Output = Self;

    fn pow(self, rhs: u32) -> Number {
        use self::Number::*;
        match self {
            SmallInt(i) => match checked_pow(i, rhs as usize) {
                Some(x) => SmallInt(x),
                None => BigInt(Integer::from(i).pow(rhs)),
            },
            BigInt(i) => BigInt(i.pow(rhs)),
            SmallRat(n, d) => match checked_pow(n, rhs as usize) {
                Some(n1) => match checked_pow(d, rhs as usize) {
                    Some(d1) => SmallRat(n1, d1),
                    None => BigRat(Box::new(Rational::from((n1, Integer::from(d).pow(rhs))))),
                },
                None => BigRat(Box::new(Rational::from((n, d)).pow(rhs))),
            },
            BigRat(f) => BigRat(Box::new(f.pow(rhs))),
        }
    }
}

impl MulAssign for Number {
    #[inline]
    fn mul_assign(&mut self, rhs: Number) {
        use self::Number::*;

        // work around a borrow checker issue
        *self = match (&mut *self, rhs) {
            (SmallInt(ref mut i1), SmallInt(i2)) => match i1.checked_mul(i2) {
                Some(x) => {
                    *i1 = x;
                    return;
                }
                None => BigInt(Integer::from(*i1) * Integer::from(i2)),
            },
            (SmallInt(ref mut i1), BigInt(ref mut i2)) => {
                *i2 *= Integer::from(*i1);
                BigInt(mem::replace(i2, Integer::new()))
            }
            (BigInt(ref mut i2), SmallInt(i1)) => {
                *i2 *= Integer::from(i1);
                return;
            }
            (BigInt(ref mut i1), BigInt(ref mut i2)) => {
                *i1 *= mem::replace(i2, Integer::new());
                return;
            }
            (BigRat(ref mut f1), BigRat(ref mut f2)) => {
                **f1 *= mem::replace(&mut **f2, Rational::new());
                return;
            }
            (a, b) => mem::replace(a, Number::one()) * b, // TODO: optimize further
        };
    }
}

impl AddAssign for Number {
    #[inline]
    fn add_assign(&mut self, rhs: Number) {
        use self::Number::*;

        // work around a borrow checker issue
        *self = match (&mut *self, rhs) {
            (SmallInt(ref mut i1), SmallInt(i2)) => match i1.checked_add(i2) {
                Some(x) => {
                    *i1 = x;
                    return;
                }
                None => BigInt(Integer::from(*i1) + Integer::from(i2)),
            },
            (SmallInt(ref mut i1), BigInt(ref mut i2)) => {
                *i2 += Integer::from(*i1);
                BigInt(mem::replace(i2, Integer::new()))
            }
            (BigInt(ref mut i2), SmallInt(i1)) => {
                *i2 += Integer::from(i1);
                return;
            }
            (BigInt(ref mut i1), BigInt(ref mut i2)) => {
                *i1 += mem::replace(i2, Integer::new());
                return;
            }
            (BigRat(ref mut f1), BigRat(ref mut f2)) => {
                **f1 += mem::replace(&mut **f2, Rational::new());
                return;
            }
            (a, b) => mem::replace(a, Number::one()) + b, // TODO: optimize further
        };
    }
}

/// Use Garner's algorithm for the Chinese remainder theorem
/// to reconstruct an x that satisfies n1 = x % p1 and n2 = x % p2.
/// The x will be in the range [-p1*p2/2,p1*p2/2].
pub fn chinese_remainder(n1: Number, n2: Number, p1: Number, p2: Number) -> Number {
    if n1 > n2 {
        return chinese_remainder(n2, n1, p2, p1);
    }

    // convert to mixed-radix notation
    let gamma1 = match (&p1, &p2) {
        (Number::SmallInt(i1), Number::SmallInt(i2)) => {
            let ii1 = Integer::from(i1.clone());
            let ii2 = Integer::from(i2.clone());
            Number::BigInt(
                (ii1.clone() % ii2.clone())
                    .invert(&ii2)
                    .expect(&format!("Could not invert {} in {}", ii1, ii2)),
            )
        }
        (Number::BigInt(i1), Number::BigInt(i2)) => Number::BigInt(
            (i1.clone() % i2.clone())
                .invert(i2)
                .expect(&format!("Could not invert {} in {}", i1, i2)),
        ),
        (Number::BigInt(i1), Number::SmallInt(i2)) => {
            let ii2 = Integer::from(i2.clone());
            Number::BigInt(
                (i1.clone() % ii2.clone())
                    .invert(&ii2)
                    .expect(&format!("Could not invert {} in {}", i1, i2)),
            )
        }
        (Number::SmallInt(i1), Number::BigInt(i2)) => {
            let ii1 = Integer::from(i1.clone());
            Number::BigInt(
                (ii1.clone() % i2.clone())
                    .invert(i2)
                    .expect(&format!("Could not invert {} in {}", i1, i2)),
            )
        }
        _ => unreachable!(),
    };

    let v1 = ((n2.clone() - n1.clone()) * gamma1.clone()) % p2.clone();

    // convert to standard representation
    let mut r = v1 * p1.clone() + n1;
    r.normalize_inplace(); // potentially downgrade from bigint
    if r.clone() * Number::SmallInt(2) > p1.clone() * p2.clone() {
        r - p1 * p2
    } else {
        r
    }
}
