use num_traits::sign::abs;
use num_traits::{One, Signed, Zero};
use number::Number;
use poly::polynomial::Polynomial;
use std::cmp::Ordering;
use std::mem;
use std::ops::Rem;
use structure::NumOrder;

// a SliceRef has either a borrowed slice,
// or a vector of borrowed arguments.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum SliceRef<'a, T: 'a> {
    BorrowedSlice(&'a [T]),
    OwnedSlice(Vec<&'a T>),
}

//impl<'a, T: 'a> Index<usize> for SliceRef<'a, T> {
//    type Output = T;
impl<'a, T: 'a> SliceRef<'a, T> {
    pub fn index(&self, index: usize) -> &'a T {
        match *self {
            SliceRef::BorrowedSlice(t) => &t[index],
            SliceRef::OwnedSlice(ref t) => t[index],
        }
    }

    pub fn len(&self) -> usize {
        match *self {
            SliceRef::BorrowedSlice(t) => t.len(),
            SliceRef::OwnedSlice(ref t) => t.len(),
        }
    }
}

pub const MAXHEAP: usize = 16;

// a modified version of the Heap from the permutohedron crate
#[derive(Debug)]
pub struct Heap<T> {
    pub data: Vec<T>,
    // c, and n: u8 is enough range.
    // u32 performs better for n, u8 for c.
    // n: == !0 at start, 0 after first permutation is emitted
    n: u32,
    // c[x] is the counter for the (x + 1) th location
    c: [u8; MAXHEAP - 1],
}

impl<T> Heap<T> {
    /// Create a new `Heap`.
    pub fn new(data: Vec<T>) -> Self {
        assert!(data.len() <= MAXHEAP);
        Heap {
            data: data,
            c: [0; MAXHEAP - 1],
            n: !0,
        }
    }

    /// Step the internal data into the next permutation and return
    /// a reference to it. Return `None` when all permutations
    /// have been visited.
    ///
    /// Note that for *n* elements there are *n!* (*n* factorial) permutations.
    pub fn next_permutation(&mut self) -> Option<&Vec<T>> {
        if self.n == !0 {
            self.n = 0;
            Some(&self.data)
        } else {
            while 1 + (self.n as usize) < self.data.len() {
                let n = self.n as u8;
                let nu = self.n as usize;
                let c = &mut self.c;
                if c[nu] <= n {
                    // `n` acts like the current length - 2 of the slice we are permuting
                    // `c[n]` acts like `i` in the recursive algorithm
                    let j = if nu % 2 == 0 { c[nu] as usize } else { 0 };
                    self.data.swap(j, nu + 1);
                    c[nu] += 1;
                    self.n = 0;
                    return Some(&self.data);
                } else {
                    c[nu] = 0;
                    self.n += 1;
                }
            }
            None
        }
    }
}

pub trait GCD {
    fn gcd(a: Self, b: Self) -> Self;
}

pub fn gcd_unsigned<T: Copy + Zero + Rem<Output = T> + PartialEq>(mut a: T, mut b: T) -> T {
    let mut c;
    while !a.is_zero() {
        c = a;
        a = b % a;
        b = c;
    }
    b
}

pub fn gcd_signed<T: Copy + Signed + Zero + Rem<Output = T> + PartialEq>(a: T, b: T) -> T {
    abs(gcd_unsigned(a, b))
}

impl GCD for u64 {
    fn gcd(a: u64, b: u64) -> u64 {
        gcd_unsigned(a, b)
    }
}

impl GCD for usize {
    fn gcd(a: usize, b: usize) -> usize {
        gcd_unsigned(a, b)
    }
}

impl GCD for isize {
    fn gcd(a: isize, b: isize) -> isize {
        gcd_signed(a, b)
    }
}

impl GCD for i32 {
    fn gcd(a: i32, b: i32) -> i32 {
        gcd_signed(a, b)
    }
}

impl GCD for i64 {
    fn gcd(a: i64, b: i64) -> i64 {
        gcd_signed(a, b)
    }
}

pub fn lcm(a: u64, b: u64) -> u64 {
    (a / GCD::gcd(a, b)) * b
}

pub fn normalize_fraction(pos: &mut bool, num: &mut u64, den: &mut u64) {
    if *num == 0 {
        *pos = true;
    }

    if *den == 0 {
        panic!("Division by 0 in fraction: {}/0", *num);
    }

    let gcd = GCD::gcd(*num, *den);
    *num /= gcd;
    *den /= gcd;
}

// multiply two normalized fractions
pub fn mul_fractions(
    pos: &mut bool,
    num: &mut u64,
    den: &mut u64,
    pos1: bool,
    mut num1: u64,
    mut den1: u64,
) {
    *pos = (*pos & pos1) || (!*pos && !pos1); // xnor
                                              // gcd(num,den) is always 1
    let gcd0 = GCD::gcd(num1, den1);
    num1 /= gcd0;
    den1 /= gcd0;

    let gcd1 = GCD::gcd(*num, den1);
    let gcd2 = GCD::gcd(num1, *den);
    *num = (*num / gcd1) * (num1 / gcd2);
    *den = (*den / gcd2) * (den1 / gcd1);
}

// add two normalized fractions
pub fn add_fractions(
    pos: &mut bool,
    num: &mut u64,
    den: &mut u64,
    pos1: bool,
    num1: u64,
    den1: u64,
) {
    let lcm = lcm(*den, den1);
    let num2 = num1 * (lcm / den1);
    *num *= lcm / *den;
    match (*pos, pos1, num2 >= *num) {
        (true, false, true) => {
            *num = num2 - *num;
            if *num != 0 {
                *pos = false;
            }
        }
        (true, false, false) => {
            *num -= num2;
        }
        (false, true, true) => {
            *num = num2 - *num;
            *pos = true;
        }
        (false, true, false) => {
            *num -= num2;
        }
        _ => {
            *num += num2;
        }
    }
    *den = lcm;
}

pub fn exp_fraction(pos: &mut bool, num: &mut u64, den: &mut u64, pow: u64) {
    if pow == 0 {
        *pos = true;
        *num = 1;
        *den = 1;
        return;
    }

    *pos |= pow % 2 == 0;
    let oldnum = *num;
    let oldden = *den;
    // FIXME: slow
    for _ in 1..pow {
        *num *= oldnum;
        *den *= oldden;
    }
}

// add one to an already normalized fraction
pub fn add_one(pos: &mut bool, num: &mut u64, den: &mut u64) {
    if !*pos && num <= den {
        *pos = true;
        *num = *den - *num;
    } else {
        if *pos {
            *num += *den;
        } else {
            *num -= *den;
        }
    }
}

pub fn num_cmp(
    mut pos: bool,
    mut num: u64,
    mut den: u64,
    pos1: bool,
    num1: u64,
    den1: u64,
) -> NumOrder {
    if pos == pos1 && num == num1 && den == den1 {
        return NumOrder::Equal;
    }
    if !pos && pos1 {
        return NumOrder::Smaller;
    }
    if pos && !pos1 {
        return NumOrder::Greater;
    }

    if den == den1 {
        if num < num1 {
            return NumOrder::Smaller;
        } else {
            return NumOrder::Greater;
        }
    }

    mul_fractions(&mut pos, &mut num, &mut den, true, den1, num1);
    if (num < den && pos) || (num > den && !pos) {
        return NumOrder::Smaller; // TODO: check
    }
    NumOrder::Greater
}

pub fn is_number_in_range(num: &Number, num1: &Number, rel: &NumOrder) -> bool {
    let rel1 = num.partial_cmp(num1).unwrap();
    match (rel, rel1) {
        (&NumOrder::Greater, Ordering::Greater)
        | (&NumOrder::GreaterEqual, Ordering::Greater)
        | (&NumOrder::GreaterEqual, Ordering::Equal)
        | (&NumOrder::Smaller, Ordering::Less)
        | (&NumOrder::SmallerEqual, Ordering::Less)
        | (&NumOrder::SmallerEqual, Ordering::Equal)
        | (&NumOrder::Equal, Ordering::Equal) => true,
        _ => false,
    }
}

pub fn ncr(n: u64, mut k: u64) -> u64 {
    if k > n {
        return 0;
    }
    if k * 2 > n {
        k = n - k
    }
    let mut res = 1;
    for i in 1..k + 1 {
        res *= n - k + i;
        res /= i;
    }
    res
}

#[derive(Debug)]
pub struct CombinationsWithReplacement<T> {
    data: Vec<T>,
    indices: Vec<usize>,
    init: bool,
}

impl<T: Clone> CombinationsWithReplacement<T> {
    pub fn new(data: Vec<T>, r: usize) -> CombinationsWithReplacement<T> {
        CombinationsWithReplacement {
            data: data,
            indices: vec![0; r],
            init: true,
        }
    }

    pub fn get_inner(&mut self) -> &mut Vec<T> {
        &mut self.data
    }
}

impl<T: Clone> Iterator for CombinationsWithReplacement<T> {
    type Item = (Number, Vec<T>);

    fn next(&mut self) -> Option<Self::Item> {
        if self.data.len() == 0 {
            return None;
        }

        if self.init {
            self.init = false;
            return Some((
                Number::one(),
                self.indices.iter().map(|i| self.data[*i].clone()).collect(),
            ));
        }

        let mut i = self.indices.len() - 1;
        loop {
            if self.indices[i] != self.data.len() - 1 {
                let p = self.indices[i];
                for j in i..self.indices.len() {
                    self.indices[j] = p + 1;
                }

                // count the number of duplicates
                let mut counter = vec![0; self.data.len()];
                for j in &self.indices {
                    counter[*j] += 1;
                }

                let mut factor = Number::SmallInt(self.indices.len() as isize).factorial();

                for x in counter.into_iter().filter(|&x| x >= 2) {
                    factor = factor / Number::SmallInt(x as isize).factorial();
                }

                return Some((
                    factor,
                    self.indices.iter().map(|i| self.data[*i].clone()).collect(),
                ));
            }

            if i == 0 {
                return None;
            }
            i -= 1;
        }
    }
}

pub fn add_num_poly(n: &mut Number, num: &mut Polynomial, den: &mut Polynomial) {
    // TODO: normalize when adding fractions!
    match n {
        Number::SmallInt(_) => {
            *num = mem::replace(num, Polynomial::new()) + den.clone() * n.clone();
        } // TODO: improve
        Number::BigInt(_) => {
            *num = mem::replace(num, Polynomial::new()) + den.clone() * n.clone();
        }
        Number::SmallRat(ref num1, ref den1) => {
            let newden = den.clone() * Number::SmallInt(den1.clone());
            *num = num.clone() * Number::SmallInt(den1.clone())
                + den.clone() * Number::SmallInt(num1.clone());
            *den = newden;
        }
        Number::BigRat(ref nd) => {
            let newden = den.clone() * Number::BigInt(nd.denom().clone());
            *num = num.clone() * Number::BigInt(nd.denom().clone())
                + den.clone() * Number::BigInt(nd.numer().clone());
            *den = newden;
        }
    }
}
