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
    let mut ee = dollar.into_inner();
    let name = ee.next().unwrap().into_span().as_str().to_string();

    let mut args = vec![];
    // func args
    if let Some(args_it) = ee.next() {
        for arg in args_it.into_inner() {
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
    }

    Element::Dollar(name, args)
}

fn parse_identity(n: pest::iterators::Pair<Rule>) -> Element<String> {
    let name = n.into_span().as_str().to_string();
    Element::Var(name, Number::SmallInt(1))
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
            Rule::comparison => args.push(parse_comparison(a)),
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

fn parse_comparison(e: pest::iterators::Pair<Rule>) -> Element<String> {
    let mut ee = e.into_inner();
    let lhs = parse_expr(ee.next().unwrap());
    let ordering = match ee.next().unwrap().into_span().as_str() {
        "==" => Ordering::Equal,
        ">=" => Ordering::GreaterEqual,
        ">" => Ordering::Greater,
        "<=" => Ordering::SmallerEqual,
        "<" => Ordering::Smaller,
        _ => unreachable!(),
    };
    let rhs = parse_expr(ee.next().unwrap());
    Element::Comparison(true, Box::new((lhs, rhs)), ordering)
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
                    Rule::set_constraint => {
                        for set_constraint_type in constraint_type.into_inner() {
                            match set_constraint_type.as_rule() {
                                Rule::range_constraint => {
                                    let mut range_constraint = set_constraint_type.into_inner();
                                    let ordering =
                                        match range_constraint.next().unwrap().into_span().as_str()
                                        {
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
                                Rule::primary => {
                                    constraints.push(parse_primary(set_constraint_type));
                                }
                                _ => unreachable!(),
                            }
                        }
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
            let mut pow = factor.into_inner();
            let base = parse_primary(pow.next().unwrap());

            match pow.next() {
                Some(x) => {
                    assert!(x.as_rule() == Rule::op_power);
                    let exp = parse_factor(pow.next().unwrap());
                    Element::Pow(true, Box::new((base, exp)))
                }
                None => base,
            }
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

fn parse_statement(e: pest::iterators::Pair<Rule>) -> Statement<String> {
    match e.as_rule() {
        Rule::expr_statement => {
            let mut r = e.into_inner();
            let id = r.next().unwrap().into_span().as_str().to_string();

            Statement::NewExpression(id, parse_expr(r.next().unwrap()))
        }
        Rule::fn_statement => {
            let mut r = e.into_inner();
            let id = r.next().unwrap().into_span().as_str().to_string();

            let mut args = vec![];
            for a in r.next().unwrap().into_inner() {
                args.push(a.into_span().as_str().to_string());
            }

            let exp = parse_expr(r.next().unwrap());

            Statement::NewFunction(id, args, exp)
        }
        Rule::assign_statement => {
            let mut r = e.into_inner();
            let dollar = parse_dollar(r.next().unwrap());
            let rhs = parse_expr(r.next().unwrap());

            Statement::Assign(dollar, rhs)
        }
        Rule::attrib_statement => {
            let mut r = e.into_inner();

            let func_i = r.next().unwrap();
            let func = match func_i.as_rule() {
                Rule::dollar => parse_dollar(func_i),
                Rule::identity => parse_identity(func_i),
                _ => unreachable!(),
            };

            let mut attribs = vec![];
            for a in r {
                match a.into_span().as_str().to_lowercase().as_str() {
                    "linear" => attribs.push(FunctionAttributes::Linear),
                    "symmetric" => attribs.push(FunctionAttributes::Symmetric),
                    "noncommutative" => attribs.push(FunctionAttributes::NonCommutative),
                    "nonlocal" => attribs.push(FunctionAttributes::NonLocal),
                    x => unreachable!("Unexpected option {:?}", x),
                }
            }

            Statement::Attrib(func, attribs)
        }
        Rule::call_statement => {
            let mut r = e.into_inner();

            let id = r.next().unwrap().into_span().as_str().to_string();

            let mut args = vec![];
            for a in r.next().unwrap().into_inner() {
                args.push(parse_expr(a));
            }

            Statement::Call(id, args)
        }
        Rule::inside_statement => {
            let mut r = e.into_inner().peekable();

            let mut funcs = vec![];
            loop {
                match r.peek().map(|x| x.as_rule()) {
                    Some(Rule::dollar) => funcs.push(parse_dollar(r.next().unwrap())),
                    Some(Rule::exec_statement) => {
                        break;
                    }
                    _ => unreachable!(),
                }
            }

            let mut sts = vec![];
            for exec_statement in r {
                for st in exec_statement.into_inner() {
                    sts.push(parse_statement(st));
                }
            }
            Statement::Inside(funcs, sts)
        }
        Rule::argument_statement => {
            let mut r = e.into_inner().peekable();

            let mut funcs = vec![];
            loop {
                match r.peek().map(|x| x.as_rule()) {
                    Some(Rule::dollar) => funcs.push(parse_dollar(r.next().unwrap())),
                    Some(Rule::identity) => funcs.push(parse_identity(r.next().unwrap())),
                    Some(Rule::exec_statement) => {
                        break;
                    }
                    _ => unreachable!(),
                }
            }

            let mut sts = vec![];
            for exec_statement in r {
                for st in exec_statement.into_inner() {
                    sts.push(parse_statement(st));
                }
            }

            Statement::Argument(funcs, sts)
        }
        Rule::for_statement => {
            let mut r = e.into_inner();

            let mut d = parse_dollar(r.next().unwrap());

            let mut range = vec![];
            let mut statements = vec![];
            for x in r {
                match x.as_rule() {
                    Rule::dollar => range.push(parse_dollar(x)),
                    Rule::identity => range.push(Element::Var(
                        x.into_span().as_str().to_string(),
                        Number::SmallInt(1),
                    )),
                    Rule::exec_statement => {
                        let child = x.into_inner().next().unwrap();
                        statements.push(parse_statement(child));
                    }
                    _ => unreachable!(),
                }
            }

            Statement::ForIn(d, range, statements)
        }
        Rule::for_in_range_statement => {
            let mut r = e.into_inner();

            let mut d = parse_dollar(r.next().unwrap());
            let lb = parse_expr(r.next().unwrap());
            let ub = parse_expr(r.next().unwrap());

            let mut statements = vec![];
            for exec_statement in r {
                let es = exec_statement.into_inner().next().unwrap();
                statements.push(parse_statement(es));
            }

            Statement::ForInRange(d, lb, ub, statements)
        }
        Rule::matchassign_statement => {
            let mut r = e.into_inner();
            let mut m = parse_expr(r.next().unwrap());

            let mut sts = vec![];
            for exec_statement in r {
                for st in exec_statement.into_inner() {
                    sts.push(parse_statement(st));
                }
            }

            Statement::MatchAssign(m, sts)
        }
        Rule::multiply_statement => Statement::Multiply(parse_expr(e.into_inner().next().unwrap())),
        Rule::maximum_statement => Statement::Maximum(parse_dollar(e.into_inner().next().unwrap())),
        Rule::replaceby_statement => {
            Statement::ReplaceBy(parse_dollar(e.into_inner().next().unwrap()))
        }
        Rule::collect_statement => Statement::Collect(
            e.into_inner()
                .next()
                .unwrap()
                .into_span()
                .as_str()
                .to_string(),
        ),
        Rule::splitarg_statement => Statement::SplitArg(
            e.into_inner()
                .next()
                .unwrap()
                .into_span()
                .as_str()
                .to_string(),
        ),
        Rule::symmetrize_statement => Statement::Symmetrize(
            e.into_inner()
                .next()
                .unwrap()
                .into_span()
                .as_str()
                .to_string(),
        ),
        Rule::print_statement => {
            let mut ds = vec![];
            let mut print_opt = PrintMode::Form;
            for d in e.into_inner() {
                match d.as_rule() {
                    Rule::dollar | Rule::identity => ds.push(d.into_span().as_str().to_string()),
                    Rule::print_opt => match d.into_span().as_str().to_lowercase().as_str() {
                        "mathematica" => print_opt = PrintMode::Mathematica,
                        _ => {}
                    },
                    _ => unreachable!(),
                }
            }

            Statement::Print(print_opt, ds)
        }
        Rule::mod_block => {
            let mut r = e.into_inner().peekable();
            let name = if r.peek().map(|x| x.as_rule()) == Some(Rule::module_name) {
                r.next().unwrap().into_span().as_str().to_string()
            } else {
                "mod".to_owned()
            };

            let mut active_exprs = vec![];
            if r.peek().map(|x| x.as_rule()) == Some(Rule::inc_expr_list) {
                for exp in r.next().unwrap().into_inner() {
                    active_exprs.push(exp.into_span().as_str().to_string());
                }
            }

            let mut exclude_exprs = vec![];
            if r.peek().map(|x| x.as_rule()) == Some(Rule::exc_expr_list) {
                for exp in r.next().unwrap().into_inner() {
                    exclude_exprs.push(exp.into_span().as_str().to_string());
                }
            }

            let mut statements = vec![];
            for exec_statement in r {
                let child = exec_statement.into_inner().next().unwrap();
                statements.push(parse_statement(child));
            }

            Statement::Module(Module {
                name,
                active_exprs,
                exclude_exprs,
                statements,
            })
        }
        Rule::expand_statement => Statement::Expand,
        Rule::discard_statement => Statement::Discard,
        Rule::repeat_block => {
            let exec_block = e.into_inner().next().unwrap().into_inner();

            let mut repeat = vec![];
            for exec_statement in exec_block {
                let child = exec_statement.into_inner().next().unwrap();
                repeat.push(parse_statement(child));
            }

            Statement::Repeat(repeat)
        }
        Rule::if_block | Rule::global_if_block => {
            let mut r = e.into_inner();

            let bool_statement = r.next().unwrap().into_inner().next().unwrap();
            let bool_stat = match bool_statement.as_rule() {
                Rule::comparison => {
                    let comp = parse_comparison(bool_statement);
                    if let Element::Comparison(_, es, c) = comp {
                        let (lhs, rhs) = { *es };
                        IfCondition::Comparison(lhs, rhs, c)
                    } else {
                        unreachable!()
                    }
                }
                Rule::bool_function => {
                    let bool_function = bool_statement.into_inner().next().unwrap();
                    match bool_function.as_rule() {
                        Rule::defined_func => {
                            let expr = parse_dollar(bool_function.into_inner().next().unwrap());
                            IfCondition::Defined(expr)
                        }
                        Rule::match_func => {
                            let expr = parse_expr(bool_function.into_inner().next().unwrap());
                            IfCondition::Match(expr)
                        }
                        _ => unreachable!(),
                    }
                }
                _ => unreachable!("{:#?}", bool_statement),
            };

            let trueblock_it = r.next().unwrap();
            let mut trueblock = vec![];
            for exec_statement in trueblock_it.into_inner() {
                let child = exec_statement.into_inner().next().unwrap();
                trueblock.push(parse_statement(child));
            }

            let mut falseblock = vec![];

            if let Some(x) = r.next() {
                for exec_statement in x.into_inner() {
                    let child = exec_statement.into_inner().next().unwrap();
                    falseblock.push(parse_statement(child));
                }
            }

            Statement::IfElse(bool_stat, trueblock, falseblock)
        }
        Rule::id_statement => {
            let mut ids = e.into_inner().peekable();

            let mut id_mode = IdentityStatementMode::Once;
            if ids.peek().unwrap().as_rule() == Rule::id_mode {
                match ids
                    .next()
                    .unwrap()
                    .into_span()
                    .as_str()
                    .to_lowercase()
                    .as_str()
                {
                    "many" => id_mode = IdentityStatementMode::Many,
                    "all" => id_mode = IdentityStatementMode::All,
                    "once" => id_mode = IdentityStatementMode::Once,
                    _ => unreachable!(),
                }
            }

            let lhs = parse_term(ids.next().unwrap());
            let rhs = parse_expr(ids.next().unwrap());
            Statement::IdentityStatement(IdentityStatement {
                mode: id_mode,
                contains_dollar: true,
                lhs,
                rhs,
            })
        }
        _ => unreachable!("Unrecognized statement {:#?}", e),
    }
}

fn parse_proc(e: pest::iterators::Pair<Rule>) -> Procedure<String> {
    let mut ee = e.into_inner();
    let name = ee.next().unwrap().into_span().as_str().to_string();

    let mut args = vec![];
    for a in ee.next().unwrap().into_inner() {
        args.push(parse_identity(a))
    }

    // check for local arguments
    let mut local_args = vec![];

    let mut n = ee.next().unwrap();
    if n.as_rule() == Rule::proc_args {
        for a in n.into_inner() {
            local_args.push(parse_identity(a))
        }

        n = ee.next().unwrap();
    }

    let mut statements = vec![];

    for sts in n.into_inner() {
        statements.push(parse_statement(sts.into_inner().next().unwrap()));
    }

    Procedure {
        name,
        args,
        local_args,
        statements,
    }
}

fn parse_program(program: pest::iterators::Pair<Rule>) -> Program {
    let mut statements = Vec::with_capacity(10); // TODO: get length
    let mut procedures = vec![];
    if program.as_rule() == Rule::program {
        for proc_stat in program.into_inner() {
            match proc_stat.as_rule() {
                Rule::global_statement => {
                    statements.push(parse_statement(proc_stat.into_inner().next().unwrap()))
                }
                Rule::proc_block => procedures.push(parse_proc(proc_stat)),
                _ => unreachable!(),
            }
        }
    }

    // TODO: Do the conversion to VarName straight away
    Program::new(statements, procedures)
}

fn custom_error(e: pest::Error<Rule>) -> pest::Error<Rule> {
    e.renamed_rules(|rule| match *rule {
        Rule::op_unary_plus => "+".to_owned(),
        Rule::op_unary_minus => "-".to_owned(),
        Rule::op_plus => "+".to_owned(),
        Rule::op_minus => "-".to_owned(),
        Rule::op_times => "*".to_owned(),
        Rule::op_divide => "/".to_owned(),
        Rule::op_power => "^".to_owned(),
        Rule::op_ge => ">=".to_owned(),
        Rule::op_gt => ">".to_owned(),
        Rule::op_le => "<=".to_owned(),
        Rule::op_lt => "<".to_owned(),
        Rule::op_eq => "==".to_owned(),
        Rule::op_ne => "!=".to_owned(),
        Rule::op_logical_or => "||".to_owned(),
        Rule::op_logical_and => "&&".to_owned(),
        Rule::op_logical_not => "!".to_owned(),
        Rule::global_statement => "global statement".to_owned(),
        Rule::dollar => "dollar variable".to_owned(),
        Rule::identity => "expression or algebraic variable name".to_owned(),
        Rule::factor => "algebraic factor".to_owned(),
        Rule::exec_statement => "module statement".to_owned(),
        Rule::primary => "wildcard, variable name, or dollar variable".to_owned(),
        Rule::range_constraint => "number constraint".to_owned(),
        Rule::exec_block => "module statement(s)".to_owned(),
        Rule::program => "procedure definition or global statement".to_owned(),
        x => format!("{:#?}", x),
    })
}

pub fn parse_file(filename: &str) -> Program {
    let mut file = File::open(filename).expect("Unable to open the file");
    let mut s = String::new();
    file.read_to_string(&mut s)
        .expect("Unable to read from the file");

    let mut p =
        ReformParser::parse(Rule::program, &s).unwrap_or_else(|e| panic!("{}", custom_error(e)));
    parse_program(p.next().unwrap())
}

/// Parses a reFORM program.
#[cfg(test)]
pub fn parse_string(s: &str) -> Program {
    let mut p =
        ReformParser::parse(Rule::program, s).unwrap_or_else(|e| panic!("{}", custom_error(e)));
    parse_program(p.next().unwrap())
}

impl FromStr for Program {
    type Err = (String);
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        ReformParser::parse(Rule::program, s)
            .map_err(|e| custom_error(e).to_string())
            .and_then(|mut p| Ok(parse_program(p.next().unwrap())))
    }
}

impl FromStr for Element<String> {
    type Err = (String);
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        ReformParser::parse(Rule::expression, s)
            .map_err(|e| custom_error(e).to_string())
            .and_then(|mut p| Ok(parse_expr(p.next().unwrap())))
    }
}
