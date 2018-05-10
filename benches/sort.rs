#![feature(test)]
extern crate test;

extern crate reform;

use test::Bencher;

use reform::number::Number;
use reform::structure::{Element, VarInfo, VarName};

#[bench]
fn add_two_expr_empty(b: &mut Bencher) {
    let (e1, e2, _) = add_two_expr_setup(1000);
    b.iter(|| {
        let e1 = e1.clone();
        let e2 = e2.clone();
        // do nothing; only overheads for cloning
        (e1, e2)
    });
}

#[bench]
fn add_two_expr(b: &mut Bencher) {
    let (e1, e2, var_info) = add_two_expr_setup(1000);
    b.iter(|| {
        let e1 = e1.clone();
        let e2 = e2.clone();
        // add two expressions
        let mut sum = Element::SubExpr(true, vec![e1, e2]);
        sum.normalize_inplace(&var_info.global_info);
        sum
    });
}

fn add_two_expr_setup(n: usize) -> (Element<VarName>, Element<VarName>, VarInfo) {
    // create n symbols x1, x2, ... in xx
    let mut var_info = VarInfo::new();
    let mut xx = Vec::new();
    for i in 1..2 * n + 1 {
        let mut xi = format!("x{}", i)
            .parse::<Element<String>>()
            .unwrap()
            .to_element(&mut var_info);
        xi.normalize_inplace(&var_info.global_info);
        xx.push(xi);
    }
    // create two expressions
    let mut v1 = Vec::new();
    let mut v2 = Vec::new();
    for (i, x) in xx.iter().enumerate() {
        if i & 1 == 0 {
            v1.push(x.clone());
        } else {
            v2.push(x.clone());
        }
    }
    let mut e1 = Element::SubExpr(true, v1);
    let mut e2 = Element::SubExpr(true, v2);
    e1.normalize_inplace(&var_info.global_info);
    e2.normalize_inplace(&var_info.global_info);
    (e1, e2, var_info)
}

#[bench]
fn expand_expr_empty(b: &mut Bencher) {
    let (e, _) = expand_expr_setup(8, 4);
    b.iter(|| {
        let e = e.clone();
        // do nothing; only overheads for cloning
        e
    });
}

#[bench]
fn expand_expr(b: &mut Bencher) {
    let (e, var_info) = expand_expr_setup(8, 4);
    b.iter(|| {
        let e = e.clone();
        // expand the expression
        e.expand(&var_info.global_info);
        e
    });
}

fn expand_expr_setup(n: usize, p: isize) -> (Element<VarName>, VarInfo) {
    // create a power of a polynomial
    let (e, _, var_info) = add_two_expr_setup(n);
    let e = Element::Pow(true, Box::new((e, Element::Num(true, Number::SmallInt(p)))));
    (e, var_info)
}
