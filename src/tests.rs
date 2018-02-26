// broken
/*
#[cfg(test)]
mod tests {
    use super::*;
    use module;
    use parser;
    use normalize;
    use tools;
    use structure;
    use id;

    #[test]
    fn simple_match() {
        let mut program = parser::parse_string(b"IN = f(1); id f(x?) = 1; sort;");
        module::do_program(&mut program);
        assert_eq!(program.input.to_string(), "1");
    }

    #[test]
    fn repeat() {
        let mut program = parser::parse_string(
            b"IN = f(6); repeat id f(x?{>0}) = x?*f(x?-1); id f(0) = 1; sort;",
        );
        module::do_program(&mut program);
        assert_eq!(program.input.to_string(), "720");
    }
}
*/
