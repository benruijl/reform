//! Modular arithmetic in Zp (commonly referred as GF(p)): each element x is in the range
//! `0 <= x < p < 2^N`, where p is a prime number and x is stored in an N-bit unsigned integer
//! whose type is declared as `ufield`.

pub use super::zp_mod::Modulus;
pub use super::zp_solve::{solve, LinearSolverError};

/// Type for numbers in Zp.
#[allow(non_camel_case_types)]
pub type ufield = u32;

/// Type used in intermediate stages. Must have twice the size of `ufield`.
#[allow(non_camel_case_types)]
pub type ucomp = u64;

/// Computes `x + y` in Zp.
#[inline]
pub fn add<M: Modulus<ucomp, ufield>>(x: ufield, y: ufield, p: M) -> ufield {
    debug_assert!(p.value() > 0);
    debug_assert!(x < p.value());
    debug_assert!(y < p.value());
    let xx = ucomp::from(x);
    let yy = ucomp::from(y);
    let pp = ucomp::from(p.value());
    let mut zz = xx + yy;
    if zz >= pp {
        zz -= pp;
    }
    debug_assert!(zz < pp);
    zz as ufield
}

/// Computes `x - y` in Zp.
#[inline]
pub fn sub<M: Modulus<ucomp, ufield>>(x: ufield, y: ufield, p: M) -> ufield {
    debug_assert!(p.value() > 0);
    debug_assert!(x < p.value());
    debug_assert!(y < p.value());
    let xx = ucomp::from(x);
    let yy = ucomp::from(y);
    let pp = ucomp::from(p.value());
    let zz = if xx >= yy { xx - yy } else { xx + pp - yy };
    debug_assert!(zz < pp);
    zz as ufield
}

/// Computes `x * y` in Zp.
#[inline]
pub fn mul<M: Modulus<ucomp, ufield>>(x: ufield, y: ufield, p: M) -> ufield {
    debug_assert!(p.value() > 0);
    debug_assert!(x < p.value());
    debug_assert!(y < p.value());
    let xx = ucomp::from(x);
    let yy = ucomp::from(y);
    let zz = p.modulous(xx * yy);
    debug_assert!(zz < ucomp::from(p.value()));
    zz as ufield
}

/// Computes `-x` in Zp.
#[inline]
pub fn neg<M: Modulus<ucomp, ufield>>(x: ufield, p: M) -> ufield {
    debug_assert!(p.value() > 0);
    debug_assert!(x < p.value());
    if x == 0 {
        0
    } else {
        p.value() - x
    }
}

/// Computes `1/x` in Zp.
#[inline]
pub fn inv<M: Modulus<ucomp, ufield>>(x: ufield, p: M) -> ufield {
    debug_assert!(x > 0);
    debug_assert!(p.value() > 0);
    debug_assert!(x < p.value());
    assert!(x != 0, "0 is not invertible");
    // by the extended Euclidean algorithm: a x + b p = gcd(x, p) = 1 or a x = 1 (mod p)
    // taken from https://www.di-mgt.com.au/euclidean.html#code-modinv, which is based on Knuth
    // vol. 2, Algorithm X
    let mut u1: ufield = 1;
    let mut u3 = x;
    let mut v1: ufield = 0;
    let mut v3 = p.value();
    let mut even_iter: bool = true;
    while v3 != 0 {
        let q = u3 / v3;
        let t3 = u3 % v3;
        let t1 = u1 + q * v1;
        u1 = v1;
        v1 = t1;
        u3 = v3;
        v3 = t3;
        even_iter = !even_iter;
    }
    debug_assert!(u3 == 1);
    if even_iter {
        u1
    } else {
        p.value() - u1
    }
}

/// Computes `x^n` in Zp.
pub fn pow<M: Modulus<ucomp, ufield>>(x: ufield, mut n: u32, p: M) -> ufield {
    debug_assert!(p.value() > 0);
    debug_assert!(x < p.value());
    if x == 0 {
        if n == 0 {
            return 1;
        } else {
            return 0;
        }
    }
    if n == 0 {
        return 1;
    }
    if n == 1 {
        return x;
    }
    if n == 2 {
        return mul(x, x, p);
    }
    if n < 6 {
        // (n-1) multiplications
        let mut r = x;
        for _ in 1..n {
            r = mul(r, x, p);
        }
        return r;
    }
    // naive exponentiation by squaring
    let mut r: ucomp = 1;
    let mut b = ucomp::from(x);
    while n != 0 {
        if n & 1 != 0 {
            r = p.modulous(r * b);
        }
        b = p.modulous(b * b);
        n >>= 1;
    }
    r as ufield
}

#[test]
fn test_add() {
    fn check_add(x: u8, y: u8, p: u8) {
        let x64 = u64::from(x);
        let y64 = u64::from(y);
        let p64 = u64::from(p);
        let z64 = u64::from(add(ufield::from(x), ufield::from(y), ufield::from(p)));
        assert_eq!(z64, (x64 + y64) % p64);
    }

    check_add(100, 200, 251);
    check_add(100, 151, 251);
    check_add(100, 100, 251);
}

#[test]
fn test_sub() {
    fn check_sub(x: u8, y: u8, p: u8) {
        let x64 = u64::from(x);
        let y64 = u64::from(y);
        let p64 = u64::from(p);
        let z64 = u64::from(sub(ufield::from(x), ufield::from(y), ufield::from(p)));
        assert_eq!(z64, (p64 + x64 - y64) % p64);
    }

    check_sub(100, 200, 251);
    check_sub(200, 100, 251);
}

#[test]
fn test_mul() {
    fn check_mul(x: u8, y: u8, p: u8) {
        let x64 = u64::from(x);
        let y64 = u64::from(y);
        let p64 = u64::from(p);
        let z64 = u64::from(mul(ufield::from(x), ufield::from(y), ufield::from(p)));
        assert_eq!(z64, x64 * y64 % p64);
    }

    check_mul(100, 200, 251);
    check_mul(11, 23, 251);
    check_mul(10, 20, 251);

    check_mul(250, 250, 251);
    check_mul(250, 2, 251);
    check_mul(2, 250, 251);
    check_mul(16, 16, 251);
    check_mul(128, 2, 251);
    check_mul(2, 128, 251);

    check_mul(0, 0, 251);
    check_mul(0, 1, 251);
    check_mul(0, 250, 251);
    check_mul(1, 0, 251);
    check_mul(250, 0, 251);
}

#[test]
fn test_neg() {
    fn check_neg(x: ufield, p: ufield) {
        let z = neg(x, p);
        assert_eq!(add(x, z, p), 0);
    }

    check_neg(0, 251);
    check_neg(1, 251);
    check_neg(2, 251);
    check_neg(10, 251);
    check_neg(16, 251);
    check_neg(31, 251);
    check_neg(100, 251);
    check_neg(200, 251);
    check_neg(249, 251);
    check_neg(250, 251);
}

#[test]
fn test_inv() {
    fn check_inv(x: ufield, p: ufield) {
        let z = inv(x, p);
        assert_eq!(mul(x, z, p), 1);
    }

    check_inv(1, 251);
    check_inv(2, 251);
    check_inv(10, 251);
    check_inv(16, 251);
    check_inv(31, 251);
    check_inv(100, 251);
    check_inv(200, 251);
    check_inv(249, 251);
    check_inv(250, 251);
}

#[test]
fn test_pow() {
    fn check_pow(x: u8, n: u8, p: u8) {
        let x64 = u64::from(x);
        let n32 = u32::from(n);
        let p64 = u64::from(p);
        let z64 = u64::from(pow(ufield::from(x), u32::from(n), ufield::from(p)));
        assert_eq!(z64, x64.pow(n32) % p64);
    }

    check_pow(0, 0, 251);
    check_pow(1, 0, 251);
    check_pow(2, 0, 251);
    check_pow(0, 1, 251);
    check_pow(1, 1, 251);
    check_pow(2, 1, 251);
    check_pow(0, 2, 251);
    check_pow(1, 2, 251);
    check_pow(2, 2, 251);

    for x in 2..6 {
        for n in 3..21 {
            check_pow(x, n, 233);
            check_pow(x, n, 239);
            check_pow(x, n, 241);
            check_pow(x, n, 251);
        }
    }

    check_pow(10, 3, 251);
    check_pow(10, 4, 251);
    check_pow(10, 5, 251);
    check_pow(10, 6, 251);

    check_pow(101, 3, 251);
    check_pow(101, 4, 251);
    check_pow(101, 5, 251);
    check_pow(101, 6, 251);
}
