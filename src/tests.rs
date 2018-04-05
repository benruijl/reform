#[cfg(test)]
mod tests {
    use module;
    use number::Number;
    use parser;
    use poly::raw::MultivariatePolynomial;
    use poly::raw::finitefield::FiniteField;
    use tools;

    #[test]
    fn simple_match() {
        let mut program = parser::parse_string(
            r#"
            expr F = f(1);
            {
                id f(x?) = 1;
            }
"#,
        );
        module::do_program(&mut program, false, 0, 1);
        assert_eq!(program.get_result("F"), "1");
    }

    #[test]
    fn repeat() {
        let mut program = parser::parse_string(
            r#"
            expr F = f(6);
            {
                repeat id f(x?{>0}) = x?*f(x?-1);
                id f(0) = 1;
            }
"#,
        );
        module::do_program(&mut program, false, 0, 1);
        assert_eq!(program.get_result("F"), "720");
    }

    #[test]
    fn bigint() {
        let a = Number::SmallInt(300000000000);
        let b = Number::SmallInt(500000000000);
        println!("{:?}", a * b);
    }

    #[test]
    fn long_division() {
        // (x^3-2x-4) = (x-3)*(x^2+x+3)+5
        let mut a = MultivariatePolynomial::from_monomial(1, vec![3]);
        a.append_monomial(-2, vec![2]);
        a.append_monomial(-4, vec![0]);

        let mut b = MultivariatePolynomial::from_monomial(1, vec![1]);
        b.append_monomial(-3, vec![0]);

        let mut q = MultivariatePolynomial::from_monomial(1, vec![2]);
        q.append_monomial(1, vec![1]);
        q.append_monomial(3, vec![0]);

        let r = MultivariatePolynomial::from_monomial(5, vec![0]);

        assert_eq!(a.long_division(&b), (q, r));
    }

    /*#[test]
    fn univariate_gcd() {
        // gcd(x^3-2x^2-4,x-3) = 1
        let mut a = MultivariatePolynomial::from_monomial(1, vec![3]);
        a.append_monomial(-2, vec![2]);
        a.append_monomial(-4, vec![0]);

        let mut b = MultivariatePolynomial::from_monomial(1, vec![1]);
        b.append_monomial(-3, vec![0]);

        assert_eq!(
            MultivariatePolynomial::gcd(&a, &b),
            MultivariatePolynomial::from_monomial(1, vec![0])
        );
    }

    #[test]
    fn univariate_gcd2() {
        // gcd(1 + 3 x + 3 x^2 + x^3, x^3 + x) mod 2 = 1 + 2x + x^2 mod 2 = 1 + x^2
        let mut a = MultivariatePolynomial::from_monomial(FiniteField::new(1, 2), vec![3]);
        a.append_monomial(FiniteField::new(3, 2), vec![2]);
        a.append_monomial(FiniteField::new(3, 2), vec![1]);
        a.append_monomial(FiniteField::new(1, 2), vec![0]);

        let mut b = MultivariatePolynomial::from_monomial(FiniteField::new(1, 2), vec![3]);
        b.append_monomial(FiniteField::new(1, 2), vec![1]);

        let mut res = MultivariatePolynomial::from_monomial(FiniteField::new(1, 2), vec![2]);
        res.append_monomial(FiniteField::new(1, 2), vec![0]);

        assert_eq!(MultivariatePolynomial::univariate_gcd(&a, &b), res);
    }

    #[test]
    fn content() {
        // content(6+12x+9x^2) = 3
        let mut a = MultivariatePolynomial::from_monomial(9, vec![2]);
        a.append_monomial(12, vec![1]);
        a.append_monomial(6, vec![0]);

        assert_eq!(MultivariatePolynomial::content(&a), 3);
    }*/

    #[test]
    fn replace() {
        // x^3+2x*y+4*x mod 5 ; x = 3
        let mut a = MultivariatePolynomial::from_monomial(FiniteField::new(1, 5), vec![3, 0]);
        a.append_monomial(FiniteField::new(2, 5), vec![1, 1]);
        a.append_monomial(FiniteField::new(4, 5), vec![1, 0]);

        let mut res = MultivariatePolynomial::from_monomial(FiniteField::new(1, 5), vec![0, 1]);
        res.append_monomial(FiniteField::new(4, 5), vec![0, 0]);

        assert_eq!(
            MultivariatePolynomial::replace(&a, 0, FiniteField::new(3, 5)),
            res
        );
    }

    #[test]
    fn chinese_remainder() {
        assert_eq!(FiniteField::chinese_remainder(5, 30, 11, 31), -94);
    }

    #[test]
    fn numgcd() {
        assert_eq!(tools::GCD::gcd(-16, -4), 4);
    }

    #[test]
    fn gcd() {
        // gcd(1+2*x+x^2,1+x)=1+x
        let mut a = MultivariatePolynomial::from_monomial(1, vec![2]);
        a.append_monomial(2, vec![1]);
        a.append_monomial(1, vec![0]);

        let mut b = MultivariatePolynomial::from_monomial(1, vec![1]);
        b.append_monomial(1, vec![0]);

        assert_eq!(MultivariatePolynomial::<i64, usize>::gcd(&a, &b), b);
    }

    #[test]
    fn gcd2() {
        // gcd(2+4*x+2x^2,2+2x)=2+2x
        let mut a = MultivariatePolynomial::from_monomial(2, vec![2]);
        a.append_monomial(4, vec![1]);
        a.append_monomial(2, vec![0]);

        let mut b = MultivariatePolynomial::from_monomial(2, vec![1]);
        b.append_monomial(2, vec![0]);

        assert_eq!(MultivariatePolynomial::<i64, usize>::gcd(&a, &b), b);
    }

    #[test]
    fn gcd3() {
        // gcd(1+2*x+x^2+y+2*x*y+x^2*y,1+x+y+x*y)=1+x+y+x*y
        // note the content: (1+y)
        let mut a = MultivariatePolynomial::from_monomial(1, vec![2, 1]);
        a.append_monomial(1, vec![2, 0]);
        a.append_monomial(2, vec![1, 1]);
        a.append_monomial(2, vec![1, 0]);
        a.append_monomial(1, vec![0, 1]);
        a.append_monomial(1, vec![0, 0]);

        let mut b = MultivariatePolynomial::from_monomial(1, vec![1, 1]);
        b.append_monomial(1, vec![1, 0]);
        b.append_monomial(1, vec![0, 1]);
        b.append_monomial(1, vec![0, 0]);

        assert_eq!(MultivariatePolynomial::<i64, usize>::gcd(&a, &b), b);
    }

    #[test]
    fn gcd4() {
        // gcd(3*x*y,x)=x
        let a = MultivariatePolynomial::from_monomial(3, vec![1, 1]);

        let b = MultivariatePolynomial::from_monomial(1, vec![1, 0]);

        assert_eq!(MultivariatePolynomial::<i64, usize>::gcd(&a, &b), b);
    }

    #[test]
    fn gcd5() {
        // gcd(3*x*y,x*y)=x*y
        let a = MultivariatePolynomial::from_monomial(3, vec![1, 1]);

        let b = MultivariatePolynomial::from_monomial(1, vec![1, 1]);

        assert_eq!(MultivariatePolynomial::<i64, usize>::gcd(&a, &b), b);
    }

    #[test]
    fn gcd6() {
        // gcd(2+x+2*x*y+x^2*y,3+x+3*x*y+x^2*y)=1+x*y
        let mut a = MultivariatePolynomial::from_monomial(1, vec![2, 1]);
        a.append_monomial(2, vec![1, 1]);
        a.append_monomial(1, vec![1, 0]);
        a.append_monomial(2, vec![0, 0]);

        let mut b = MultivariatePolynomial::from_monomial(1, vec![2, 1]);
        b.append_monomial(3, vec![1, 1]);
        b.append_monomial(1, vec![1, 0]);
        b.append_monomial(3, vec![0, 0]);

        let mut res = MultivariatePolynomial::from_monomial(1, vec![1, 1]);
        res.append_monomial(1, vec![0, 0]);

        assert_eq!(MultivariatePolynomial::<i64, usize>::gcd(&a, &b), res);
    }

    #[test]
    fn gcd7() {
        // gcd with single scaling that requires multiple images
        //gcd(50x^3+50x^4+100y+100xy-49x^3y+x^4y-100y^2-x^3y^2,
        //    50x^3+50x^4+100y+100xy+51x^3y+x^4y+100y^2+x^3y^2)
        // = 50x^3+100y+x^3y
        let mut a = MultivariatePolynomial::from_monomial(50, vec![3, 0]);
        a.append_monomial(50, vec![4, 0]);
        a.append_monomial(100, vec![0, 1]);
        a.append_monomial(100, vec![1, 1]);
        a.append_monomial(-49, vec![3, 1]);
        a.append_monomial(1, vec![4, 1]);
        a.append_monomial(-100, vec![0, 2]);
        a.append_monomial(-1, vec![3, 2]);

        let mut b = MultivariatePolynomial::from_monomial(50, vec![3, 0]);
        b.append_monomial(50, vec![4, 0]);
        b.append_monomial(100, vec![0, 1]);
        b.append_monomial(100, vec![1, 1]);
        b.append_monomial(51, vec![3, 1]);
        b.append_monomial(1, vec![4, 1]);
        b.append_monomial(100, vec![0, 2]);
        b.append_monomial(1, vec![3, 2]);

        let mut res = MultivariatePolynomial::from_monomial(50, vec![3, 0]);
        res.append_monomial(100, vec![0, 1]);
        res.append_monomial(1, vec![3, 1]);

        assert_eq!(MultivariatePolynomial::<i64, usize>::gcd(&a, &b), res);
    }

    #[test]
    fn gcd8() {
        // gcd with multiple scaling
        //gcd(100-170x-270x^2+12y+30xy+18x^2y,
        //    100-370x+270x^2+12y+6xy-18x^2y)
        // = 100-270x+12y+18xy
        let mut a = MultivariatePolynomial::from_monomial(100, vec![0, 0]);
        a.append_monomial(-170, vec![1, 0]);
        a.append_monomial(-270, vec![2, 0]);
        a.append_monomial(12, vec![0, 1]);
        a.append_monomial(30, vec![1, 1]);
        a.append_monomial(18, vec![2, 1]);

        let mut b = MultivariatePolynomial::from_monomial(100, vec![0, 0]);
        b.append_monomial(-370, vec![1, 0]);
        b.append_monomial(270, vec![2, 0]);
        b.append_monomial(12, vec![0, 1]);
        b.append_monomial(6, vec![1, 1]);
        b.append_monomial(-18, vec![2, 1]);

        let mut res = MultivariatePolynomial::from_monomial(100, vec![0, 0]);
        res.append_monomial(-270, vec![1, 0]);
        res.append_monomial(12, vec![0, 1]);
        res.append_monomial(18, vec![1, 1]);

        assert_eq!(MultivariatePolynomial::<i64, usize>::gcd(&a, &b), res);
    }

    #[test]
    fn gcd9() {
        // gcd with multiple scaling
        //gcd(100 + 100 x - 90 x^3 - 90 x^4 + 12 y + 12 x y + 3 x^3 y^2 + 3 x^4 y^2,
        //    100 - 100 x - 90 x^3 + 90 x^4 + 12 y - 12 x y + 3 x^3 y^2 - 3 x^4 y^2)
        // = 100 - 90 x^3 + 12 y + 3 x^3 y^2
        let mut a = MultivariatePolynomial::from_monomial(100, vec![0, 0]);
        a.append_monomial(100, vec![1, 0]);
        a.append_monomial(-90, vec![3, 0]);
        a.append_monomial(-90, vec![4, 0]);
        a.append_monomial(12, vec![0, 1]);
        a.append_monomial(12, vec![1, 1]);
        a.append_monomial(3, vec![3, 2]);
        a.append_monomial(3, vec![4, 2]);

        let mut b = MultivariatePolynomial::from_monomial(100, vec![0, 0]);
        b.append_monomial(-100, vec![1, 0]);
        b.append_monomial(-90, vec![3, 0]);
        b.append_monomial(90, vec![4, 0]);
        b.append_monomial(12, vec![0, 1]);
        b.append_monomial(-12, vec![1, 1]);
        b.append_monomial(3, vec![3, 2]);
        b.append_monomial(-3, vec![4, 2]);

        let mut res = MultivariatePolynomial::from_monomial(100, vec![0, 0]);
        res.append_monomial(-90, vec![3, 0]);
        res.append_monomial(12, vec![0, 1]);
        res.append_monomial(3, vec![3, 2]);

        assert_eq!(MultivariatePolynomial::<i64, usize>::gcd(&a, &b), res);
    }

}
