#![feature(test)]
extern crate test;

extern crate reform;

use test::Bencher;

use reform::poly::raw::zp;
use reform::poly::raw::zp::{ufield, FastModulus};

#[bench]
fn zp_pow5(b: &mut Bencher) {
    let x: ufield = 12345678;
    let n = 5;
    let p: ufield = 1073741789;
    let p = &FastModulus::from(p);
    b.iter(|| zp::pow(x, n, p));
}

#[bench]
fn zp_pow9(b: &mut Bencher) {
    let x: ufield = 12345678;
    let n = 9;
    let p: ufield = 1073741789;
    let p = &FastModulus::from(p);
    b.iter(|| zp::pow(x, n, p));
}

#[bench]
fn zp_pow1729(b: &mut Bencher) {
    let x: ufield = 12345678;
    let n = 1729;
    let p: ufield = 1073741789;
    let p = &FastModulus::from(p);
    b.iter(|| zp::pow(x, n, p));
}

#[bench]
fn zp_pow61057(b: &mut Bencher) {
    let x: ufield = 12345678;
    let n = 61057;
    let p: ufield = 1073741789;
    let p = &FastModulus::from(p);
    b.iter(|| zp::pow(x, n, p));
}

#[bench]
fn zp_pow65535(b: &mut Bencher) {
    let x: ufield = 12345678;
    let n = 65535;
    let p: ufield = 1073741789;
    let p = &FastModulus::from(p);
    b.iter(|| zp::pow(x, n, p));
}

#[bench]
fn zp_pow65536(b: &mut Bencher) {
    let x: ufield = 12345678;
    let n = 65536;
    let p: ufield = 1073741789;
    let p = &FastModulus::from(p);
    b.iter(|| zp::pow(x, n, p));
}
