#[cfg(test)]
mod tests {
    use module;
    use parser;
    use poly::raw::MultivariatePolynomial;

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

}
