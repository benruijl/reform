use structure::{Element, NumOrder};
use std::mem;

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

// TODO: use num package?
pub fn gcd(mut a: u64, mut b: u64) -> u64 {
    let mut c;
    while a != 0 {
        c = a;
        a = b % a;
        b = c;
    }
    b
}

pub fn lcm(a: u64, b: u64) -> u64 {
    (a / gcd(a, b)) * b
}

pub fn normalize_fraction(pos: &mut bool, num: &mut u64, den: &mut u64) {
    if *num == 0 {
        *pos = true;
    }

    if *den == 0 {
        panic!("Division by 0 in fraction: {}/0", *num);
    }

    let gcd = gcd(*num, *den);
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
    let gcd0 = gcd(num1, den1);
    num1 /= gcd0;
    den1 /= gcd0;

    let gcd1 = gcd(*num, den1);
    let gcd2 = gcd(num1, *den);
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

pub fn add_terms(dest: &mut Element, to_add: &[Element]) {
    match *dest {
        Element::SubExpr(..) => {
            unreachable!("Subexpression should be filtered earlier");
        }
        Element::Term(ref mut dirty, ref mut t) => {
            for x in to_add.iter() {
                t.push(x.clone());
            }
            *dirty = true;
        }
        ref mut a => {
            let mut res = to_add.to_owned();
            res.push(mem::replace(a, DUMMY_ELEM!()));
            *a = Element::Term(true, res);
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

pub fn is_number_in_range(
    pos: bool,
    num: u64,
    den: u64,
    pos1: bool,
    num1: u64,
    den1: u64,
    rel: &NumOrder,
) -> bool {
    let rel1 = num_cmp(pos, num, den, pos1, num1, den1);
    match (rel, rel1) {
        (&NumOrder::Greater, NumOrder::Greater)
        | (&NumOrder::GreaterEqual, NumOrder::Greater)
        | (&NumOrder::GreaterEqual, NumOrder::Equal)
        | (&NumOrder::Smaller, NumOrder::Smaller)
        | (&NumOrder::SmallerEqual, NumOrder::Smaller)
        | (&NumOrder::SmallerEqual, NumOrder::Equal)
        | (&NumOrder::Equal, NumOrder::Equal) => true,
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

// return unnormalized exponentiated form
pub fn exponentiate(factors: &[Element], pow: u64) -> Element {
    if factors.is_empty() {
        return Element::SubExpr(
            true,
            vec![Element::Term(true, vec![Element::Num(false, true, 1, 1)])],
        );
    }

    let exp = |i, res: &mut Vec<_>| {
        let cmb = ncr(pow, i as u64);
        match exponentiate(&factors[1..], pow - i) {
            Element::SubExpr(_, ts) => for x in ts {
                match x {
                    Element::Term(_, mut fs) => {
                        if i > 0 {
                            fs.push(Element::Pow(
                                true,
                                Box::new((factors[0].clone(), Element::Num(false, true, i, 1))),
                            ));
                            fs.push(Element::Num(false, true, cmb, 1));
                        }
                        res.push(Element::Term(true, fs));
                    }
                    _ => unreachable!(),
                }
            },
            _ => unreachable!(),
        }
    };

    let mut res = vec![];
    if factors.len() == 1 {
        exp(pow, &mut res);
    } else {
        for i in 0..pow + 1 {
            exp(i, &mut res);
        }
    }

    Element::SubExpr(true, res)
}
