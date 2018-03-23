use std::cmp::Ordering;
use std::fmt;
use std::mem;
use std::ops::{Add, Mul, Neg, Sub};
use tools::gcd;
use std::collections::HashMap;

use num_traits::{pow, One, Zero};

use poly::exponent::Exponent;
use poly::ring::Ring;

use poly::raw::finitefield::FiniteField;
use rand;
use rand::distributions::{Range, Sample};

/// Multivariate polynomial with a degree sparse and variable dense representation.
#[derive(Clone)]
pub struct MultivariatePolynomial<R: Ring, E: Exponent> {
    // Data format: the i-th monomial is stored as coefficients[i] and
    // exponents[i * nvars .. (i + 1) * nvars]. Keep coefficients.len() == nterms and
    // exponents.len() == nterms * nvars. Terms are always expanded and sorted by the exponents via
    // cmp_exponents().
    coefficients: Vec<R>,
    exponents: Vec<E>,
    nterms: usize,
    nvars: usize,
}

impl<R: Ring, E: Exponent> MultivariatePolynomial<R, E> {
    /// Constructs a zero polynomial.
    #[inline]
    pub fn new() -> Self {
        Self {
            coefficients: Vec::new(),
            exponents: Vec::new(),
            nterms: 0,
            nvars: 0,
        }
    }

    /// Constructs a zero polynomial with the given number of variables.
    #[inline]
    pub fn with_nvars(nvars: usize) -> Self {
        Self {
            coefficients: Vec::new(),
            exponents: Vec::new(),
            nterms: 0,
            nvars: nvars,
        }
    }

    /// Constructs a constant polynomial with the given number of variables.
    #[inline]
    pub fn from_constant_with_nvars(constant: R, nvars: usize) -> Self {
        if constant.is_zero() {
            return Self::with_nvars(nvars);
        }
        Self {
            coefficients: vec![constant],
            exponents: vec![E::zero(); nvars],
            nterms: 1,
            nvars: nvars,
        }
    }

    /// Constructs a polynomial with a single term.
    #[inline]
    pub fn from_monomial(coefficient: R, exponents: Vec<E>) -> Self {
        if coefficient.is_zero() {
            return Self::with_nvars(exponents.len());
        }
        Self {
            coefficients: vec![coefficient],
            nvars: exponents.len(),
            exponents: exponents,
            nterms: 1,
        }
    }

    pub fn to_finite_field(&self, p: usize) -> MultivariatePolynomial<FiniteField, E> {
        let newc = self.coefficients
            .iter()
            .map(|x| x.to_finite_field(p))
            .collect();

        let mut a = MultivariatePolynomial::new();
        a.exponents = self.exponents.clone();
        a.coefficients = newc;
        a.nterms = self.nterms;
        a.nvars = self.nvars;
        a
    }

    /// Returns the number of terms in the polynomial.
    #[inline]
    pub fn nterms(&self) -> usize {
        return self.nterms;
    }

    /// Returns the number of variables in the polynomial.
    #[inline]
    pub fn nvars(&self) -> usize {
        return self.nvars;
    }

    /// Returns true if the polynomial is constant.
    #[inline]
    pub fn is_constant(&self) -> bool {
        if self.is_zero() {
            return true;
        }
        if self.nterms >= 2 {
            return false;
        }
        debug_assert!(!self.coefficients.first().unwrap().is_zero());
        return self.exponents.iter().all(|e| e.is_zero());
    }

    /// Returns the slice for the exponents of the specified monomial.
    #[inline]
    fn exponents(&self, index: usize) -> &[E] {
        &self.exponents[index * self.nvars..(index + 1) * self.nvars]
    }

    fn last_exponents(&self) -> &[E] {
        &self.exponents[(self.nterms - 1) * self.nvars..self.nterms * self.nvars]
    }

    /// Returns the mutable slice for the exponents of the specified monomial.
    #[inline]
    fn exponents_mut(&mut self, index: usize) -> &mut [E] {
        &mut self.exponents[index * self.nvars..(index + 1) * self.nvars]
    }

    /// Compares exponent vectors of two monomials.
    #[inline]
    fn cmp_exponents(a: &[E], b: &[E]) -> Ordering {
        debug_assert!(a.len() == b.len());
        // TODO: Introduce other term orders.
        a.cmp(b)
    }

    /// Appends a monomial to the polynomial.
    pub fn append_monomial(&mut self, coefficient: R, mut exponents: Vec<E>) {
        if coefficient.is_zero() {
            return;
        }
        if self.nvars != exponents.len() {
            panic!(
                "nvars mismatched: got {}, expected {}",
                exponents.len(),
                self.nvars
            );
        }
        // Linear search to find the insert-point.
        // TODO: Binary search.
        for i in 0..self.nterms {
            let c;
            {
                let a = self.exponents(i);
                let b = &exponents[..];
                c = Self::cmp_exponents(a, b);
            }
            if c == Ordering::Equal {
                // Add the two coefficients.
                let mut new_coeff =
                    mem::replace(&mut self.coefficients[i], R::zero()).add(coefficient);
                if new_coeff.is_zero() {
                    // The coefficient becomes zero. Remove this monomial.
                    self.coefficients.remove(i);
                    let i = i * self.nvars;
                    self.exponents.splice(i..i + self.nvars, Vec::new());
                    self.nterms -= 1;
                } else {
                    // Set the new coefficient.
                    mem::swap(&mut self.coefficients[i], &mut new_coeff);
                }
                return;
            } else if c == Ordering::Greater {
                // Insert the monomial at this point.
                self.coefficients.insert(i, coefficient);
                let i = i * self.nvars;
                self.exponents.splice(i..i, exponents);
                self.nterms += 1;
                return;
            }
        }
        // Push the monomial at the last.
        self.coefficients.push(coefficient);
        self.exponents.append(&mut exponents);
        self.nterms += 1;
    }
}

impl<R: Ring, E: Exponent> Default for MultivariatePolynomial<R, E> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

/// View object for a term in a multivariate polynomial.
#[derive(Clone, Debug)]
pub struct MultivariateMonomialView<'a, R: 'a, E: 'a> {
    pub coefficient: &'a R,
    pub exponents: &'a [E],
}

/// Iterator over terms in a multivariate polynomial.
pub struct MultivariateMonomialViewIterator<'a, R: 'a + Ring, E: 'a + Exponent> {
    poly: &'a MultivariatePolynomial<R, E>,
    index: usize,
}

impl<'a, R: Ring, E: Exponent> Iterator for MultivariateMonomialViewIterator<'a, R, E> {
    type Item = MultivariateMonomialView<'a, R, E>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.index == self.poly.nterms {
            None
        } else {
            let view = MultivariateMonomialView {
                coefficient: &self.poly.coefficients[self.index],
                exponents: self.poly.exponents(self.index),
            };
            self.index += 1;
            Some(view)
        }
    }
}

impl<'a, R: Ring, E: Exponent> IntoIterator for &'a MultivariatePolynomial<R, E> {
    type Item = MultivariateMonomialView<'a, R, E>;
    type IntoIter = MultivariateMonomialViewIterator<'a, R, E>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        Self::IntoIter {
            poly: self,
            index: 0,
        }
    }
}

impl<R: Ring + fmt::Debug, E: Exponent + fmt::Debug> fmt::Debug for MultivariatePolynomial<R, E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.is_zero() {
            return write!(f, "[]");
        }
        let mut first = true;
        write!(f, "[ ")?;
        for monomial in self {
            if first {
                first = false;
            } else {
                write!(f, ", ")?;
            }
            write!(
                f,
                "{{ {:?}, {:?} }}",
                monomial.coefficient, monomial.exponents
            )?;
        }
        write!(f, " ]")
    }
}

impl<R: Ring + fmt::Display, E: Exponent + One + fmt::Display> fmt::Display
    for MultivariatePolynomial<R, E>
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut is_first_term = true;
        for monomial in self {
            if monomial.coefficient.is_zero() {
                continue;
            }
            let mut is_first_factor = true;
            if monomial.coefficient.eq(&R::one()) {
                if !is_first_term {
                    write!(f, "+")?;
                }
            } else if monomial.coefficient.eq(&R::one().neg()) {
                write!(f, "-")?;
            } else {
                if is_first_term {
                    write!(f, "({})", monomial.coefficient)?;
                } else {
                    write!(f, "+({})", monomial.coefficient)?;
                }
                is_first_factor = false;
            }
            is_first_term = false;
            for (i, e) in monomial.exponents.into_iter().enumerate() {
                if e.is_zero() {
                    continue;
                }
                if is_first_factor {
                    is_first_factor = false;
                } else {
                    write!(f, "*")?;
                }
                write!(f, "x{}", i)?;
                if e.ne(&E::one()) {
                    write!(f, "^{}", e)?;
                }
            }
            if is_first_factor {
                write!(f, "1")?;
            }
        }
        if is_first_term {
            write!(f, "0")?;
        }
        Ok(())
    }
}

impl<R: Ring + PartialEq, E: Exponent> PartialEq for MultivariatePolynomial<R, E> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        if self.nvars != other.nvars {
            if self.is_zero() && other.is_zero() {
                // Both are 0.
                return true;
            }
            if self.is_zero() || other.is_zero() {
                // One of them is 0.
                return false;
            }
            panic!("nvars mismatched");
        }
        if self.nterms != other.nterms {
            return false;
        }
        self.exponents.eq(&other.exponents) && self.coefficients.eq(&other.coefficients)
    }
}

impl<R: Ring + Eq, E: Exponent> Eq for MultivariatePolynomial<R, E> {}

impl<R: Ring, E: Exponent> Zero for MultivariatePolynomial<R, E> {
    #[inline]
    fn zero() -> Self {
        Self::new()
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.nterms == 0
    }
}

impl<R: Ring, E: Exponent> Add for MultivariatePolynomial<R, E> {
    type Output = Self;

    fn add(mut self, mut other: Self) -> Self::Output {
        if self.is_zero() {
            return other;
        }
        if other.is_zero() {
            return self;
        }
        if self.nvars != other.nvars {
            panic!("nvars mismatched");
        }

        // Merge the two polynomials, which are assumed to be already sorted.

        let mut new_coefficients = Vec::new();
        let mut new_exponents: Vec<E> = Vec::new();
        let mut new_nterms = 0;
        let mut i = 0;
        let mut j = 0;

        while i < self.nterms && j < other.nterms {
            let c = Self::cmp_exponents(self.exponents(i), other.exponents(j));
            match c {
                Ordering::Less => {
                    Self::add_push(
                        &mut new_coefficients,
                        &mut new_exponents,
                        &mut new_nterms,
                        &mut self,
                        i,
                    );
                    i += 1;
                }
                Ordering::Greater => {
                    Self::add_push(
                        &mut new_coefficients,
                        &mut new_exponents,
                        &mut new_nterms,
                        &mut other,
                        j,
                    );
                    j += 1;
                }
                Ordering::Equal => {
                    let c1 = mem::replace(&mut self.coefficients[i], R::zero());
                    let c2 = mem::replace(&mut other.coefficients[j], R::zero());
                    let mut new_c = c1.add(c2);
                    if !new_c.is_zero() {
                        mem::swap(&mut self.coefficients[i], &mut new_c);
                        Self::add_push(
                            &mut new_coefficients,
                            &mut new_exponents,
                            &mut new_nterms,
                            &mut self,
                            i,
                        );
                    }
                    i += 1;
                    j += 1;
                }
            }
        }

        while i < self.nterms {
            Self::add_push(
                &mut new_coefficients,
                &mut new_exponents,
                &mut new_nterms,
                &mut self,
                i,
            );
            i += 1;
        }

        while j < other.nterms {
            Self::add_push(
                &mut new_coefficients,
                &mut new_exponents,
                &mut new_nterms,
                &mut other,
                j,
            );
            j += 1;
        }

        Self {
            coefficients: new_coefficients,
            exponents: new_exponents,
            nterms: new_nterms,
            nvars: self.nvars,
        }
    }
}

impl<R: Ring, E: Exponent> MultivariatePolynomial<R, E> {
    #[inline(always)]
    fn add_push(
        new_coefficients: &mut Vec<R>,
        new_exponents: &mut Vec<E>,
        new_nterms: &mut usize,
        source: &mut Self,
        i: usize,
    ) {
        new_coefficients.push(mem::replace(&mut source.coefficients[i], R::zero()));
        new_exponents.reserve(source.nvars);
        for e in source.exponents_mut(i) {
            new_exponents.push(mem::replace(e, E::zero()));
        }
        *new_nterms += 1;
    }
}

impl<R: Ring, E: Exponent> Sub for MultivariatePolynomial<R, E> {
    type Output = Self;

    fn sub(self, other: Self) -> Self::Output {
        self.add(other.neg())
    }
}

impl<R: Ring, E: Exponent> Neg for MultivariatePolynomial<R, E> {
    type Output = Self;
    fn neg(mut self) -> Self::Output {
        // Negate coefficients of all terms.
        for c in &mut self.coefficients {
            let mut new_c = mem::replace(c, R::zero()).neg();
            mem::swap(c, &mut new_c);
        }
        self
    }
}

impl<R: Ring, E: Exponent> Mul for MultivariatePolynomial<R, E> {
    type Output = Self;

    fn mul(self, other: Self) -> Self::Output {
        if self.is_zero() {
            return Self::with_nvars(other.nvars);
        }
        if other.is_zero() {
            return Self::with_nvars(self.nvars);
        }
        if self.nvars != other.nvars {
            panic!("nvars mismatched");
        }
        // TODO: this is a quick implementation. To be improved.
        let mut new_poly = Self::with_nvars(self.nvars);
        for m in &other {
            let p = self.clone().mul_monomial(m.coefficient, m.exponents);
            new_poly = new_poly.add(p);
        }
        new_poly
    }
}

impl<R: Ring, E: Exponent> Mul<R> for MultivariatePolynomial<R, E> {
    type Output = Self;

    fn mul(self, other: R) -> Self::Output {
        let mut res = self.clone();
        for c in &mut res.coefficients {
            *c = c.clone() * other.clone();
        }
        res
    }
}

impl<R: Ring, E: Exponent> MultivariatePolynomial<R, E> {
    #[inline]
    fn mul_monomial(mut self, coefficient: &R, exponents: &[E]) -> Self {
        debug_assert!(self.nvars == exponents.len());
        debug_assert!(self.nterms > 0);
        debug_assert!(!coefficient.is_zero());
        for c in &mut self.coefficients {
            let mut new_c = mem::replace(c, R::zero()).mul(coefficient.clone());
            mem::swap(c, &mut new_c);
        }
        for i in 0..self.nterms {
            let ee = self.exponents_mut(i);
            for (e1, e2) in ee.iter_mut().zip(exponents) {
                *e1 = e1.checked_add(e2).expect("overflow in adding exponents");
            }
        }
        self
    }

    #[inline]
    fn divexact_monomial(
        dividend_coefficient: &R,
        dividend_exponents: &[E],
        divisor_coefficient: &R,
        divisor_exponents: &[E],
        result_coefficient: &mut R,
        result_exponents: &mut [E],
    ) -> bool {
        debug_assert!(dividend_exponents.len() == divisor_exponents.len());
        debug_assert!(dividend_exponents.len() == result_exponents.len());
        if dividend_exponents
            .iter()
            .zip(divisor_exponents.iter())
            .any(|(a, b)| a.cmp(b) == Ordering::Less)
        {
            return false;
        }
        if !dividend_coefficient
            .clone()
            .rem(divisor_coefficient.clone())
            .is_zero()
        {
            return false;
        }
        *result_coefficient = divisor_coefficient.clone().div(divisor_coefficient.clone());
        for (i, e) in result_exponents.iter_mut().enumerate() {
            *e = dividend_exponents[i]
                .clone()
                .sub(divisor_exponents[i].clone());
        }
        return true;
    }

    // Get the highest degree of the first variable in the leading monomial.
    pub fn ldegree(&self) -> E {
        self.last_exponents()[0].clone()
    }

    /// Get the highest degree of the leading monomial.
    pub fn ldegree_max(&self) -> E {
        self.last_exponents().iter().max().unwrap().clone()
    }

    /// Get the leading coefficient.
    pub fn lcoeff(&self) -> R {
        self.coefficients.last().unwrap().clone()
    }

    /// Get the leading coefficient viewed as a polynomial
    /// in all variables except the last.
    pub fn lcoeff_last(&self) -> MultivariatePolynomial<R, E> {
        // the last variable should have the least sorting priority,
        // so the last term should still be the lcoeff
        let last = self.last_exponents();

        let mut res = MultivariatePolynomial::with_nvars(self.nvars);
        for t in (0..self.nterms() - 1).rev() {
            if (0..self.nvars - 1).all(|i| self.exponents(t)[i] == last[i]) {
                let mut e = vec![E::zero(); self.nvars];
                e[self.nvars - 1] = self.exponents(t)[self.nvars - 1];
                res.append_monomial(self.coefficients[t], e);
            } else {
                break;
            }
        }

        res
    }

    /// Replace a variable `x' in the polynomial by an element from
    /// the ring `v'.
    pub fn replace(&self, n: usize, v: R) -> MultivariatePolynomial<R, E> {
        let mut res = MultivariatePolynomial::with_nvars(self.nvars);
        for t in 0..self.nterms {
            let mut c = self.coefficients[t] * pow(v, self.exponents(t)[n].as_());
            let mut e = self.exponents(t).to_vec();
            e[n] = E::zero();

            res.append_monomial(c, e);
        }

        res
    }

    /// Replace a list of variables in the polynomial by elements from
    /// the ring `v'.
    pub fn replace_multiple(&self, r: &[(usize, R)]) -> MultivariatePolynomial<R, E> {
        let mut res = MultivariatePolynomial::with_nvars(self.nvars);
        for t in 0..self.nterms {
            let mut e = self.exponents(t).to_vec();

            let mut c = self.coefficients[t];
            for &(n, v) in r {
                c = c * pow(v.clone(), self.exponents(t)[n].as_());
                e[n] = E::zero();
            }

            res.append_monomial(c, e);
        }

        res
    }

    /// Get the content from the coefficients.
    pub fn content(&self) -> R {
        if self.coefficients.is_empty() {
            return R::zero();
        }
        let mut c = self.coefficients.first().unwrap().clone();
        for cc in self.coefficients.iter().skip(1) {
            c = gcd(c, cc.clone());
        }
        c
    }

    /// Get the content of a multivariate polynomial viewed as a
    /// univariate polynomial in `x`.
    pub fn univariate_content(&self, x: usize) -> MultivariatePolynomial<R, E> {
        if self.coefficients.is_empty() {
            return MultivariatePolynomial::new();
        }

        // get maximum degree for variable x
        let mut maxdeg = 0;
        for t in 0..self.nterms {
            let d = self.exponents(t)[x].as_();
            if d > maxdeg {
                maxdeg = d.clone();
            }
        }

        // construct the coefficient per power of x
        let mut result = None;
        for d in 0..maxdeg + 1 {
            let mut a = MultivariatePolynomial::new();
            for t in 0..self.nterms {
                if self.exponents(t)[x].as_() == d {
                    let mut e = self.exponents(t).to_vec();
                    e[x] = E::zero();
                    a.append_monomial(self.coefficients[t].clone(), e);
                }
            }

            result = match result {
                Some(x) => Some(MultivariatePolynomial::gcd(&a, &x)),
                None => Some(a),
            };
        }

        result.unwrap()
    }

    /// Create a univariate polynomial out of a multivariate one.
    /// TODO: allow a MultivariatePolynomial as a coefficient
    pub fn to_univariate_polynomial(&self, x: usize) -> Vec<(MultivariatePolynomial<R, E>, usize)> {
        if self.coefficients.is_empty() {
            return vec![];
        }

        // get maximum degree for variable x
        let mut maxdeg = 0;
        for t in 0..self.nterms {
            let d = self.exponents(t)[x].as_();
            if d > maxdeg {
                maxdeg = d.clone();
            }
        }

        // construct the coefficient per power of x
        let mut result = vec![];
        for d in 0..maxdeg + 1 {
            let mut a = MultivariatePolynomial::new();
            for t in 0..self.nterms {
                if self.exponents(t)[x].as_() == d {
                    let mut e = self.exponents(t).to_vec();
                    e[x] = E::zero();
                    a.append_monomial(self.coefficients[t].clone(), e);
                }
            }

            if !a.is_zero() {
                result.push((a, d));
            }
        }

        result
    }

    /// Get the content of a multivariate polynomial viewed as a
    /// mutlivariate polynomial in all variables except `x`.
    pub fn multivariate_content(&self, x: usize) -> MultivariatePolynomial<R, E> {
        if self.coefficients.is_empty() {
            return MultivariatePolynomial::new();
        }

        let mut tm: HashMap<Vec<E>, MultivariatePolynomial<R, E>> = HashMap::new();
        for t in 0..self.nterms {
            let mut e = self.exponents(t).to_vec();
            let mut me = vec![E::zero(); self.nvars];
            me[x] = e[x].clone();
            e[x] = E::zero();

            tm.entry(e)
                .or_insert_with(|| MultivariatePolynomial::with_nvars(self.nvars))
                .append_monomial(self.coefficients[t].clone(), me);
        }

        let mut gcd = MultivariatePolynomial::from_monomial(
            self.coefficients[0].clone(),
            self.exponents(0).to_vec(),
        );
        for (_, tt) in tm {
            gcd = MultivariatePolynomial::gcd(&gcd, &tt);
        }

        gcd
    }

    /// Long division for univariate polynomial.
    pub fn long_division(
        &self,
        div: &MultivariatePolynomial<R, E>,
    ) -> (MultivariatePolynomial<R, E>, MultivariatePolynomial<R, E>) {
        if div.is_zero() {
            panic!("Cannot divide by 0 polynomial");
        }

        // TODO: check for univariateness

        let mut q = MultivariatePolynomial::with_nvars(self.nvars);
        let mut r = self.clone();

        while !r.is_zero() && r.ldegree() >= div.ldegree() {
            let tc =
                r.coefficients.last().unwrap().clone() / div.coefficients.last().unwrap().clone();

            if tc.is_zero() {
                panic!("Cannot do long division in a ring. Use a field.");
            }

            let tp: Vec<E> = r.last_exponents()
                .iter()
                .zip(div.last_exponents())
                .map(|(e1, e2)| e1.clone() - e2.clone())
                .collect();

            q.append_monomial(tc.clone(), tp.clone());
            r = r - MultivariatePolynomial::from_monomial(tc, tp) * div.clone(); // TODO: we shouldn't clone div
        }

        (q, r)
    }

    /// Compute the univariate GCD using Euclid's algorithm. The result is normalized to 1.
    pub fn univariate_gcd(
        a: &MultivariatePolynomial<R, E>,
        b: &MultivariatePolynomial<R, E>,
    ) -> MultivariatePolynomial<R, E> {
        let mut c = a.clone();
        let mut d = b.clone();
        if a.ldegree() < b.ldegree() {
            mem::swap(&mut c, &mut d);
        }

        let mut r = c.long_division(&d).1;
        while !r.is_zero() {
            c = d;
            d = r;
            r = c.long_division(&d).1;
        }

        // normalize the gcd
        let l = d.coefficients.last().unwrap().clone();
        for x in &mut d.coefficients {
            *x = x.clone() / l.clone();
        }

        d
    }

    /// Compute the gcd shape of two polynomials in a finite field by filling in random
    /// numbers.
    fn gcd_shape_modular(
        a: &MultivariatePolynomial<FiniteField, E>,
        b: &MultivariatePolynomial<FiniteField, E>,
        n: usize,         // number of active vars
        dx: &mut [usize], // degree bounds
    ) -> Option<MultivariatePolynomial<R, E>> {
        // TODO: "If the gcd of the inputs has content in x n return Fail.""
        // what do they mean? we don't know this gcd yet...

        let gamma = MultivariatePolynomial::univariate_gcd(&a.lcoeff_last(), &b.lcoeff_last());

        let mut rng = rand::thread_rng();
        let mut range = Range::new(1, a.coefficients[0].p);
        let v = loop {
            let a = FiniteField::new(range.sample(&mut rng), a.coefficients[0].p);
            if gamma.replace(n - 1, a).nterms() != 0 {
                break a;
            }
        };

        let av = a.replace(n - 1, v);
        let bv = b.replace(n - 1, v);

        let gv = if n > 2 {
            match MultivariatePolynomial::gcd_shape_modular(&av, &bv, n - 1, dx) {
                Some(x) => x,
                None => return None,
            }
        } else {
            let gg = MultivariatePolynomial::univariate_gcd(&av, &bv);
            if gg.ldegree().as_() > dx[0] {
                return None;
            }
            dx[0] = gg.ldegree().as_(); // update degree bound
            gg
        };

        // TODO

        None
    }

    /// Compute the gcd of two multivariate polynomials using Zippel's algorithm.
    pub fn gcd(
        a: &MultivariatePolynomial<R, E>,
        b: &MultivariatePolynomial<R, E>,
    ) -> MultivariatePolynomial<R, E> {
        // TODO: check if a and b are monic
        // TODO: get degree bounds on gcd. how? lowest of highest in a and b
        assert_eq!(a.nvars, b.nvars);

        let mut rng = rand::thread_rng();
        let mut bounds = vec![0; a.nvars]; // FIXME

        // compute scaling factor
        let gamma = gcd(a.ldegree().as_(), b.ldegree().as_());

        let primes = [
            4254797, 4255213, 4255609, 4256009, 4254799, 4255249, 4255619, 4256029, 4254821,
            4255301, 4255637, 4256051, 4254853, 4255313, 4255673, 4256089, 4254869, 4255351,
            4255679, 4256101, 4254883, 4255369, 4255697, 4256117, 4254911, 4255387, 4255739,
            4256141, 4254949, 4255399, 4255747, 4256159, 4254961, 4255403, 4255751, 4256167,
            4254983, 4255429, 4255781, 4256191, 4255039, 4255439, 4255789, 4256227, 4255057,
            4255451, 4255807, 4256233,
        ];

        let mut pi = 0;

        'newfirstprime: loop {
            for _ in pi..primes.len() {
                if gamma % primes[pi] != 0 {
                    break;
                }
                pi += 1;
            }

            let p = primes[pi];

            let gammap = FiniteField::new(gamma, p);
            let ap = a.to_finite_field(p);
            let bp = b.to_finite_field(p);

            println!("{:?} {:?} {}", ap, bp, p);

            // calculate modular gcd image
            let mut gp = loop {
                if let Some(x) =
                    MultivariatePolynomial::gcd_shape_modular(&ap, &bp, ap.nvars, &mut bounds)
                {
                    break x;
                }
            };

            bounds[0] = gp.last_exponents()[0].as_();

            // construct a new assumed form
            // we have to find the proper normalization
            let mut gf = gp.clone();

            // construct the univariate polynomial
            let gfu = gf.to_univariate_polynomial(0);

            // find a coefficient of x1 in gf that is a monomial (single scaling)
            let mut single_scale = None;
            let mut nx = 0; // count the minimal number of samples needed
            for &(ref c, ref e) in &gfu {
                if c.nterms > nx {
                    nx = c.nterms;
                }
                if c.nterms == 1 {
                    single_scale = Some(e);
                }
            }

            // In the case of multiple scaling, we need an additional sample
            // TODO: is this correct?
            if single_scale == None {
                nx += 1;
            }

            let gpc = gp.lcoeff();
            let mut gm = gp * (gammap / gpc);
            let mut m = p; // used for CRT

            let mut old_gm = MultivariatePolynomial::new();

            // add new primes until we can reconstruct the full gcd
            'newprime: loop {
                if gm == old_gm {
                    // divide by lcoeff and convert from finite field
                    let gmc = gm.lcoeff();
                    let mut gc = MultivariatePolynomial::new();
                    gc.nterms = gm.nterms;
                    gc.nvars = gm.nvars;
                    gc.exponents = gm.exponents.clone();
                    gc.coefficients = gm.coefficients
                        .iter()
                        .map(|x| R::from_finite_field(&(x.clone() / gmc.clone())))
                        .collect();

                    if a.long_division(&gc).1 == MultivariatePolynomial::new()
                        && b.long_division(&gc).1 == MultivariatePolynomial::new()
                    {
                        return gc;
                    }

                    // if it does not divide, we need more primes
                }

                old_gm = gm.clone();

                for _ in pi..primes.len() {
                    if gamma % primes[pi] != 0 {
                        break;
                    }
                    pi += 1;
                }

                let p = primes[pi];

                let gammap = FiniteField::new(gamma, p);
                let ap = a.to_finite_field(p);
                let bp = b.to_finite_field(p);
                let mut range = Range::new(1, p);

                let mut S = vec![]; // coefficients for the linear system
                let mut ni = 0;
                let mut failure_count = 0;
                'newimage: loop {
                    // generate random numbers for all non-leading variables
                    let (r, a1, b1) = loop {
                        let r: Vec<(usize, FiniteField)> = (1..a.nvars)
                            .map(|i| (i, FiniteField::new(range.sample(&mut rng), p)))
                            .collect();

                        let a1 = ap.replace_multiple(&r);
                        let b1 = bp.replace_multiple(&r);

                        if a1.ldegree() == a.ldegree() && b1.ldegree() == b.ldegree() {
                            break (r, a1, b1);
                        }
                    };

                    let g1 = MultivariatePolynomial::univariate_gcd(&a1, &b1);

                    if g1.ldegree().as_() < bounds[0] {
                        // original image and form and degree bounds are unlucky
                        // change the bound and try a new prime
                        bounds[0] = g1.ldegree().as_();
                        continue 'newfirstprime;
                    }

                    if g1.ldegree().as_() > bounds[0] {
                        failure_count += 1;

                        if failure_count > 2 || failure_count > ni {
                            // p is likely unlucky
                            continue 'newprime;
                        }
                        continue;
                    }

                    // check if the single scaling is there, if we had a single scale
                    if let Some(d) = single_scale {
                        if !(0..g1.nterms).any(|i| g1.exponents(i)[0].as_() == *d) {
                            // the scaling term is missing, so the assumed form is wrong
                            continue 'newfirstprime;
                        }
                    }

                    S.push((r, g1));
                    ni += 1;

                    // make sure we have at least nx images
                    if ni < nx {
                        continue 'newimage;
                    }

                    // construct the linear system
                    let mut gfm = vec![];

                    for (i, &(ref c, ref e)) in gfu.iter().enumerate() {
                        for (j, &(ref r, ref g)) in S.iter().enumerate() {
                            let mut row = vec![];

                            assert_eq!(g.nterms, gfu.len());

                            // the first elements in the row come from the shape
                            for ii in 0..gfu.len() {
                                if i == ii {
                                    // note that we ignore the coefficient of the shape
                                    for t in 0..c.nterms {
                                        let mut coeff = FiniteField::new(1, p);
                                        for &(n, v) in r.iter() {
                                            coeff = coeff * pow(v.clone(), c.exponents(t)[n].as_());
                                        }
                                        row.push(coeff.n);
                                    }
                                } else {
                                    for t in 0..c.nterms {
                                        row.push(0);
                                    }
                                }
                            }

                            // add the coefficient from the image
                            for ii in 0..g.nterms {
                                if ii == i {
                                    row.push(g.coefficients[i].n);
                                } else {
                                    row.push(0);
                                }
                            }

                            gfm.push(row);
                        }
                    }

                    // solve for S and call the result gp
                    gp = MultivariatePolynomial::new();

                    // if inconsistent: continue `newfirstprime
                    // underdetermined and same degree 3 times? bad prime: continue 'newprime
                    // else: more images: continue 'newimage

                    // correct?
                    break;
                }

                // scale the new image
                let gpc = gp.content();
                gp = gp * (gammap / gpc);

                // use chinese remainder theorem to merge coefficients
                for (gmc, gpc) in gm.coefficients.iter_mut().zip(gp.coefficients) {
                    *gmc = FiniteField::new(
                        FiniteField::chinese_remainder(gmc.n, gpc.n, gmc.p, gpc.p),
                        m * p,
                    );
                }

                m = m * p;
            }
        }
    }
}
