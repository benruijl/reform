extern crate pest;

use number::Number;
use rug::{Integer, Rational};
use std::fs::File;
use std::io::prelude::*;
use std::str::FromStr;
use structure::{
    Element, FunctionAttributes, IdentityStatement, IdentityStatementMode, IfCondition, Module,
    Ordering, PrintMode, Procedure, Program, Statement,
};

use pest::Parser;

#[cfg(debug_assertions)]
const _GRAMMAR: &'static str = include_str!("grammar.pest");

#[derive(Parser)]
#[grammar = "parser/grammar.pest"]
struct ReformParser;

fn parse_number(e: pest::iterators::Pair<Rule>) -> Number {
    if e.as_rule() != Rule::number {
        unreachable!("Cannot parse {:#?} as number", e);
    }

    let mut ee = e.into_inner();
    let sign_or_num = ee.next().unwrap();

    let mut sign = 1;

    let mut num = String::new();
    match sign_or_num.as_rule() {
        Rule::op_unary_plus => {}
        Rule::op_unary_minus => {
            sign = -1;
        }
        Rule::integer => {
            num = sign_or_num.into_span().as_str().to_string();
        }
        x => unreachable!("Unexpected {:#?}", x),
    }

    if num.is_empty() {
        let eee = ee.next().unwrap();
        num = eee.into_span().as_str().to_string();
    }

    match ee.next() {
        Some(x) => {
            let den = x.into_span().as_str().to_string();
            Number::BigRat(Box::new(Rational::from((
                sign * num.parse::<Integer>().unwrap(),
                den.parse::<Integer>().unwrap(),
            ))))
        }
        None => Number::BigInt(sign * num.parse::<Integer>().unwrap()),
    }
}

fn parse_dollar(dollar: pest::iterators::Pair<Rule>) -> Element<String> {
    let name = dollar.into_span().as_str().to_string();
    // FIXME: indices
    Element::Dollar(name, vec![])
}

fn parse_function(e: pest::iterators::Pair<Rule>) -> Element<String> {
    if e.as_rule() != Rule::function {
        unreachable!("Cannot parse {:#?} as function", e);
    }

    let mut ee = e.into_inner();
    let name = ee.next().unwrap().into_span().as_str().to_string();

    let mut args = vec![];
    // func args
    for arg in ee.next().unwrap().into_inner() {
        // funcargs
        let a = arg.into_inner().next().unwrap();
        match a.as_rule() {
            // funcarg
            Rule::expression => args.push(parse_expr(a)),
            Rule::wildarg => {
                let name = a
                    .into_inner()
                    .next()
                    .unwrap()
                    .into_span()
                    .as_str()
                    .to_string();
                args.push(Element::VariableArgument(name));
            }
            x => unreachable!("{:#?}", x),
        }
    }

    Element::Fn(true, name, args)
}

fn parse_primary(e: pest::iterators::Pair<Rule>) -> Element<String> {
    let mut ee = e.into_inner();
    let p = ee.next().unwrap();
    match p.as_rule() {
        Rule::number => {
            return Element::Num(true, parse_number(p));
        }
        Rule::identity => {
            let mut ee = p.into_span().as_str().to_string();
            Element::Var(ee, Number::SmallInt(1))
        }
        Rule::wildcard => {
            let mut ee = p.into_inner();
            let name = ee.next().unwrap().into_span().as_str().to_string();

            let mut constraints = vec![];
            if let Some(constraint) = ee.next() {
                let constraint_type = constraint.into_inner().next().unwrap();
                match constraint_type.as_rule() {
                    Rule::range_constraint => {
                        let mut range_constraint = constraint_type.into_inner();

                        let ordering = match range_constraint.next().unwrap().into_span().as_str() {
                            "==" => Ordering::Equal,
                            ">=" => Ordering::GreaterEqual,
                            ">" => Ordering::Greater,
                            "<=" => Ordering::SmallerEqual,
                            "<" => Ordering::Smaller,
                            _ => unreachable!(),
                        };

                        let num = parse_number(range_constraint.next().unwrap());
                        constraints.push(Element::NumberRange(num, ordering));
                    }
                    Rule::builtin_constraint => unimplemented!(),
                    _ => unreachable!("Unexpected {:#?}", constraint_type),
                }
            }

            Element::Wildcard(name, constraints)
        }
        Rule::dollar => parse_dollar(p),
        Rule::function => parse_function(p),
        Rule::expression => parse_expr(p),
        x => unimplemented!("{:?}", x),
    }
}

fn parse_factor(e: pest::iterators::Pair<Rule>) -> Element<String> {
    if e.as_rule() != Rule::factor {
        unreachable!("Cannot parse {:?} as factor", e);
    }

    let mut ee = e.into_inner();
    let factor = ee.next().unwrap();

    match factor.as_rule() {
        Rule::primary => parse_primary(factor),
        Rule::power => {
            // for now, no exponent
            let mut pow = factor.into_inner();
            let prim = pow.next().unwrap();
            parse_primary(prim)
        }
        x => unimplemented!("{:?}", x),
    }
}

fn parse_term(term: pest::iterators::Pair<Rule>) -> Element<String> {
    let mut factors = vec![];
    for fs in term.into_inner() {
        if fs.as_rule() == Rule::op_times {
            continue;
        }

        if fs.as_rule() == Rule::op_divide {
            // TODO: give pest-style error message?
            unimplemented!("Division of non-numbers is not supported at this time")
        }

        factors.push(parse_factor(fs));
    }
    Element::Term(true, factors)
}

fn parse_expr(e: pest::iterators::Pair<Rule>) -> Element<String> {
    if e.as_rule() != Rule::expression {
        unreachable!("Cannot parse {:?} as Element", e);
    }

    let mut terms = vec![];
    let mut sign = 1;
    for ts in e.into_inner() {
        match ts.as_rule() {
            Rule::term => {
                let mut factors = parse_term(ts);
                if sign == -1 {
                    if let Element::Term(_, ref mut fs) = factors {
                        fs.push(Element::Num(false, Number::SmallInt(-1)));
                    }
                }
                terms.push(factors)
            }
            Rule::op_plus => {
                sign = 1;
            }
            Rule::op_minus => {
                sign = -1;
            }
            _ => unimplemented!("{:?}", ts),
        }
    }
    Element::SubExpr(true, terms)
}

fn parse_statements(e: pest::iterators::Pair<Rule>) -> Statement<String> {
    match e.as_rule() {
        Rule::expr_statement => {
            let mut r = e.into_inner();
            let id = r.next().unwrap().into_span().as_str().to_string();

            Statement::NewExpression(id, parse_expr(r.next().unwrap()))
        }
        Rule::assign_statement => {
            let mut r = e.into_inner();
            let dollar = parse_dollar(r.next().unwrap());
            let rhs = parse_expr(r.next().unwrap());

            Statement::Assign(dollar, rhs)
        }
        Rule::inside_statement => {
            unimplemented!();
            /*let mut r = e.into_inner();
            let dollar = parse_dollar(r.next().unwrap());
            let rhs = parse_expr(r.next().unwrap());

            Statement::Inside(dollar, rhs)*/
        }
        Rule::mod_block => {
            let mut r = e.into_inner().peekable();
            if r.peek().unwrap().as_rule() == Rule::module_name {
                unimplemented!()
            }

            let mut module = vec![];
            for exec_statement in r {
                let child = exec_statement.into_inner().next().unwrap();
                module.push(parse_statements(child));
            }

            Statement::Module(Module {
                name: "mod".to_owned(),
                active_exprs: vec![],
                exclude_exprs: vec![],
                statements: module,
            })
        }
        Rule::repeat_block => {
            let exec_block = e.into_inner().next().unwrap().into_inner();

            let mut repeat = vec![];
            for exec_statement in exec_block {
                let child = exec_statement.into_inner().next().unwrap();
                repeat.push(parse_statements(child));
            }

            Statement::Repeat(repeat)
        }
        Rule::id_statement => {
            // TODO: mode
            let mut ids = e.into_inner();
            let lhs = parse_expr(ids.next().unwrap());
            let rhs = parse_expr(ids.next().unwrap());
            Statement::IdentityStatement(IdentityStatement {
                mode: IdentityStatementMode::Once,
                contains_dollar: true,
                lhs,
                rhs,
            })
        }
        _ => unreachable!("Unrecognized statement {:#?}", e),
    }
}

pub fn parse_file(filename: &str) -> Program {
    let mut file = File::open(filename).expect("Unable to open the file");
    let mut s = String::new();
    file.read_to_string(&mut s)
        .expect("Unable to read from the file");

    let mut pairs = ReformParser::parse(Rule::start, &s).unwrap_or_else(|e| panic!("{}", e));

    let start = pairs.next().unwrap();

    let mut statements = Vec::with_capacity(10); // FIXME: get len?
    if start.as_rule() == Rule::start {
        for inner_pair in start.into_inner() {
            if inner_pair.as_rule() == Rule::global_statement {
                for x in inner_pair.into_inner() {
                    statements.push(parse_statements(x));
                }
            }
        }

        println!("statements: {:#?}", statements);
    }

    // TODO: Do the conversion to VarName straight away
    Program::new(statements, vec![])
}
