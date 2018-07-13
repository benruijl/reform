use poly::exponent::Exponent;
use poly::raw::multivar::MultivariateMonomialView;
use poly::ring::Ring;
use std::cmp::Ordering;
use std::mem;
use std::ops::{Add, Div, Mul, Neg, Sub};

/// A monomial class. Equality and ordering is only considering the exponent.
#[derive(Debug, Clone)]
pub struct Monomial<R: Ring, E: Exponent> {
    pub coefficient: R,
    pub exponents: Vec<E>,
}

impl<R: Ring, E: Exponent> Monomial<R, E> {
    #[inline]
    pub fn new(coefficient: R, exponents: Vec<E>) -> Monomial<R, E> {
        Monomial {
            coefficient,
            exponents,
        }
    }

    #[inline]
    pub fn divides(&self, other: &Monomial<R, E>) -> bool {
        self.exponents
            .iter()
            .zip(&other.exponents)
            .all(|(a, b)| a >= b)
            && (other.coefficient.is_one()
                || (self.coefficient.clone() % other.coefficient.clone()).is_zero())
    }
}

impl<R: Ring, E: Exponent> Div for Monomial<R, E> {
    type Output = Self;

    fn div(mut self, mut other: Self) -> Self::Output {
        for (ee, er) in self.exponents.iter_mut().zip(other.exponents.drain(..)) {
            *ee = *ee - er;
        }

        Monomial {
            coefficient: self.coefficient / other.coefficient,
            exponents: mem::replace(&mut self.exponents, vec![]),
        }
    }
}

impl<'a, R: Ring, E: Exponent> Div<&'a Monomial<R, E>> for Monomial<R, E> {
    type Output = Self;

    fn div(mut self, other: &Self) -> Self::Output {
        for (ee, er) in self.exponents.iter_mut().zip(&other.exponents) {
            *ee = *ee - *er;
        }

        Monomial {
            coefficient: self.coefficient / other.coefficient.clone(),
            exponents: mem::replace(&mut self.exponents, vec![]),
        }
    }
}

impl<R: Ring, E: Exponent> Mul for Monomial<R, E> {
    type Output = Self;

    fn mul(mut self, mut other: Self) -> Self::Output {
        for (ee, er) in self.exponents.iter_mut().zip(other.exponents.drain(..)) {
            *ee = *ee + er;
        }

        Monomial {
            coefficient: self.coefficient * other.coefficient,
            exponents: mem::replace(&mut self.exponents, vec![]),
        }
    }
}

impl<'a, R: Ring, E: Exponent> Mul<&'a Monomial<R, E>> for Monomial<R, E> {
    type Output = Self;

    fn mul(mut self, other: &Self) -> Self::Output {
        for (ee, er) in self.exponents.iter_mut().zip(&other.exponents) {
            *ee = *ee + *er;
        }

        Monomial {
            coefficient: self.coefficient * other.coefficient.clone(),
            exponents: mem::replace(&mut self.exponents, vec![]),
        }
    }
}

impl<'a, R: Ring, E: Exponent> Mul<MultivariateMonomialView<'a, R, E>> for Monomial<R, E> {
    type Output = Self;

    fn mul(mut self, other: MultivariateMonomialView<R, E>) -> Self::Output {
        for (ee, er) in self.exponents.iter_mut().zip(other.exponents) {
            *ee = *ee + *er;
        }

        Monomial {
            coefficient: self.coefficient * other.coefficient.clone(),
            exponents: mem::replace(&mut self.exponents, vec![]),
        }
    }
}

impl<R: Ring, E: Exponent> Add for Monomial<R, E> {
    type Output = Self;

    fn add(mut self, other: Self) -> Self::Output {
        debug_assert_eq!(self.exponents, other.exponents);
        Monomial {
            coefficient: self.coefficient + other.coefficient,
            exponents: mem::replace(&mut self.exponents, vec![]),
        }
    }
}

impl<R: Ring, E: Exponent> Sub for Monomial<R, E> {
    type Output = Self;

    fn sub(mut self, other: Self) -> Self::Output {
        debug_assert_eq!(self.exponents, other.exponents);
        Monomial {
            coefficient: self.coefficient + (-other.coefficient),
            exponents: mem::replace(&mut self.exponents, vec![]),
        }
    }
}

impl<R: Ring, E: Exponent> Neg for Monomial<R, E> {
    type Output = Self;

    fn neg(mut self) -> Self::Output {
        Monomial {
            coefficient: -self.coefficient,
            exponents: mem::replace(&mut self.exponents, vec![]),
        }
    }
}

impl<R: Ring, E: Exponent> PartialOrd for Monomial<R, E> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.exponents.partial_cmp(&other.exponents)
    }
}

impl<R: Ring, E: Exponent> Ord for Monomial<R, E> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl<R: Ring, E: Exponent> PartialEq for Monomial<R, E> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.exponents.eq(&other.exponents)
    }
}

impl<R: Ring, E: Exponent> Eq for Monomial<R, E> {}
