#[cfg(test)]
mod tests {
    use module;
    use parser;

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
}
