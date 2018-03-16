#[cfg(test)]
mod tests {
    use module;
    use number::Number;
    use parser;
    use poly::raw::MultivariatePolynomial;
    use poly::raw::fraction::Fraction;
    use poly::raw::finitefield::FiniteField;
    use num_traits::One;

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

    #[test]
    fn univariate_gcd() {
        // gcd(x^3-2x^2-4,x-3) = 1
        let mut a = MultivariatePolynomial::from_monomial(Fraction::one(), vec![3]);
        a.append_monomial(Fraction::new(-2, 1), vec![2]);
        a.append_monomial(Fraction::new(-4, 1), vec![0]);

        let mut b = MultivariatePolynomial::from_monomial(Fraction::one(), vec![1]);
        b.append_monomial(Fraction::new(-3, 1), vec![0]);

        assert_eq!(
            MultivariatePolynomial::univariate_gcd(&a, &b),
            MultivariatePolynomial::from_monomial(Fraction::one(), vec![0])
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
    }

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

}
