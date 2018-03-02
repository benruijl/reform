use std::io::prelude::*;
use std::fs::File;
use structure::{Element, IdentityStatement, IdentityStatementMode, Module, NumOrder, Procedure,
                Program, Statement};

use combine::char::*;
use combine::*;
use combine::primitives::Stream;
use combine::State;

// parse a reform file
pub fn parse_file(filename: &str) -> Program {
    let mut f = File::open(filename).expect(&format!("Unable to open file {:?}", filename));
    let mut s = String::new();
    f.read_to_string(&mut s).expect("Unable to read file");

    match program().parse(State::new(&s[..])) {
        Ok((v, _)) => v,
        Err(err) => {
            error!("{}", err);
            panic!();
        }
    }
}

parser!{
   fn linecomment[I]()(I) -> ()
    where [I: Stream<Item=char>]
{
    try(string("//"))
        .and(skip_many(satisfy(|c| c != '\n')))
        .map(|_| ())
}
}

parser!{
   fn blockcomment[I]()(I) -> ()
    where [I: Stream<Item=char>]
{
    try(string("/*"))
        .and(skip_many(not_followed_by(string("*/")).and(any())))
        .and(string("*/"))
        .map(|_| ())
}
}

parser!{
   fn skipnocode[I]()(I) -> ()
    where [I: Stream<Item=char>]
{
    skip_many(skip_many1(space()).or(linecomment()).or(blockcomment()))
}
}

parser!{
   fn keyword[I](c: &'static str)(I) -> (&'static str)
    where [I: Stream<Item=char>]
{
    try(string_cmp(c, |l: char, r: char| {
        l.eq_ignore_ascii_case(&r)
    })).skip(not_followed_by(alpha_num()))
        .skip(skipnocode())
}
}

parser!{
   fn lex_char[I](c: char)(I) -> (char)
    where [I: Stream<Item=char>]
{
    char(*c).skip(skipnocode())
}
}

parser!{
   fn varname[I]()(I) -> (String)
    where [I: Stream<Item=char>]
{
    (many1(letter()), many(alpha_num().or(char('_'))))
        .skip(spaces())
        .map(|(mut f, r): (String, String)| {
            f.push_str(&r);
            f
        })
        .expected("Function or variable name")
}
}

parser!{
   fn program[I]()(I) -> Program
    where [I: Stream<Item=char>]
{
    let procedure = struct_parser!{
        Procedure {
            _: keyword("procedure"),
            name: varname(),
            args: lex_char('(').with(sep_by(expr(), lex_char(','))).skip(skipnocode()),
            local_args: optional(lex_char(';').with(sep_by(expr(), lex_char(',')))).map(
                |x : Option<Vec<Element<String>>>| x.unwrap_or(vec![])).skip(skipnocode()),
            _: lex_char(')').with(lex_char(';')),
            statements: many(statement()),
            _: keyword("endprocedure").with(lex_char(';'))
        }
    };

    let module = struct_parser!{
        Module {
            name: value("test".to_string()),
            global_statements: many(global_statement()),
            statements: between(lex_char('{'), lex_char('}'), many(statement())),
        }
    };

    let input = keyword("IN")
        .with(lex_char('='))
        .with(expr())
        .skip(lex_char(';'));

    skipnocode()
        .with((input, many(procedure), many(module)))
        .skip(eof())
        .map(
            |(e, p, m): (Element<String>, Vec<Procedure<String>>, Vec<Module<String>>)| {
                Program::new(e, m, p)
            },
        )
}
}

parser!{
   fn statementend[I]()(I) -> (char)
    where [I: Stream<Item=char>]
{
    lex_char(';').skip(skipnocode())
}
}

parser!{
   fn dollarvar[I]()(I) -> (Element<String>)
    where [I: Stream<Item=char>]
{
    char('$')
        .with(varname())
        .and(optional(between(lex_char('['), lex_char(']'), expr())))
        .map(|(x, ind)| Element::Dollar('$'.to_string() + &x, ind.map(Box::new)))
}
}

parser!{
   fn global_statement[I]()(I) -> Statement<String>
    where [I: Stream<Item=char>]
{
    let assign = (dollarvar(), lex_char('=').with(expr()).skip(statementend()))
        .map(|(d, e)| Statement::Assign(d, e));
    let collect = keyword("collect")
        .with(varname())
        .skip(statementend())
        .map(|x| Statement::Collect(x));

    choice!(assign, collect)
}
}

parser!{
   fn statement[I]()(I) -> Statement<String>
    where [I: Stream<Item=char>]
{
    let assign = (dollarvar(), lex_char('=').with(expr()).skip(statementend()))
        .map(|(d, e)| Statement::Assign(d, e));
    let symmetrize = keyword("symmetrize")
        .with(varname())
        .skip(statementend())
        .map(|x| Statement::Symmetrize(x));
    let multiply = keyword("multiply")
        .with(expr())
        .skip(statementend())
        .map(|x| Statement::Multiply(x));
    let splitarg = keyword("splitarg")
        .with(varname())
        .skip(statementend())
        .map(|x| Statement::SplitArg(x));
    let expand = keyword("expand")
        .skip(statementend())
        .map(|_| Statement::Expand);
    let print = keyword("print")
        .skip(statementend())
        .map(|_| Statement::Print);
    let maximum = keyword("maximum")
        .with(dollarvar())
        .skip(statementend())
        .map(|x| Statement::Maximum(x));
    let call_procedure = (
        keyword("call").with(varname()),
        between(lex_char('('), lex_char(')'), sep_by(expr(), lex_char(','))),
    ).skip(statementend())
        .map(|(name, args): (String, Vec<Element<String>>)| Statement::Call(name, args));

    let idmode =
        optional(choice!(keyword("once"), keyword("all"), keyword("many"))).map(|x| match x {
            Some("all") => IdentityStatementMode::All,
            Some("many") => IdentityStatementMode::Many,
            _ => IdentityStatementMode::Once,
        });
    let idstatement = struct_parser!{
        IdentityStatement {
            _: keyword("id"),
            mode: idmode,
            lhs: expr(),
            _: lex_char('='),
            rhs: expr(),
            _: statementend()
        }
    }.map(|x| Statement::IdentityStatement(x));

    let repeat = keyword("repeat").with(choice!(
        statementend()
            .with(many(statement()))
            .skip(keyword("endrepeat"))
            .skip(statementend())
            .map(|x| Statement::Repeat(x)),
        statement().map(|x| Statement::Repeat(vec![x]))
    ));

    let ifclause = between(
        lex_char('('),
        lex_char(')'),
        keyword("match").with(between(lex_char('('), lex_char(')'), expr())),
    );
    let ifelse = (keyword("if").with(ifclause)
        ,choice!(statementend().with(many(statement())).skip(keyword("endif")).skip(statementend()),
        statement().map(|x: Statement<String>| vec![x])),
        optional(keyword("else").with(choice!(statementend().with(many(statement())).skip(keyword("endif")).skip(statementend()),
        statement().map(|x: Statement<String>| vec![x]))))
        .map(|x : Option<Vec<Statement<String>>>| x.unwrap_or(vec![]))). // parse the else
        map(|(q,x,e) : (Element<String>, Vec<Statement<String>>, Vec<Statement<String>>)|
            Statement::IfElse(q, x, e));

    choice!(
        call_procedure,
        assign,
        maximum,
        print,
        ifelse,
        expand,
        multiply,
        repeat,
        idstatement,
        splitarg,
        symmetrize
    )
}
}

parser!{
   fn number[I]()(I) -> Element<String>
    where [I: Stream<Item=char>]
{
    (
        optional(char('-')).map(|x| x.is_none()),
        many1(digit()).map(|d: String| d.parse::<u64>().unwrap()),
        optional(char('/').with(many1(digit())))
            .map(|x| x.map(|y: String| y.parse::<u64>().unwrap()).unwrap_or(1)),
    ).map(|(sign, num, den): (bool, u64, u64)| Element::Num(true, sign, num, den))
        .skip(skipnocode())
}
}

parser!{
   fn factor[I]()(I) -> Element<String>
    where [I: Stream<Item=char>]
{
    let funcarg = between(lex_char('('), lex_char(')'), sep_by(expr(), lex_char(',')));

    let numorder = choice!(
        try(string(">=")).map(|_| NumOrder::GreaterEqual),
        string(">").map(|_| NumOrder::Greater),
        string("==").map(|_| NumOrder::Equal),
        try(string("<=")).map(|_| NumOrder::SmallerEqual),
        string("<").map(|_| NumOrder::Smaller)
    ).skip(spaces());
    let numrange = (numorder, number()).map(|(r, b)| match b {
        Element::Num(_, pos, num, den) => Element::NumberRange(pos, num, den, r),
        _ => unreachable!(),
    });
    let set = between(
        lex_char('{'),
        lex_char('}'),
        sep_by(choice!(expr(), numrange), lex_char(',')),
    );
    let variableargument =
        (char('?'), varname()).map(|(_, v)| Element::VariableArgument("?".to_owned() + &v));

    // read the variable name and then see if it is a wildcard, a NamedFunction or variable
    let namedfactor = varname()
        .and(choice!(
            lex_char('?')
                .and(optional(set).map(|x| x.unwrap_or(vec![])))
                .map(|(_, s)| Element::Wildcard(String::new(), s)),
            funcarg.map(|fa| Element::Fn(true, String::new(), fa)),
            value(1).map(|_| Element::Var(String::new()))
        ))
        .map(|(name, mut res)| {
            match res {
                Element::Wildcard(ref mut n, ..) | Element::Var(ref mut n) => *n = name,
                Element::Fn(_, ref mut n, ..) => *n = name,
                _ => unreachable!(),
            }
            res
        });

    choice!(
        number(),
        dollarvar(),
        namedfactor,
        variableargument,
        parenexpr()
    )
}
}

parser!{
   fn parenexpr[I]()(I) -> Element<String>
    where [I: Stream<Item=char>]
{
    between(lex_char('('), lex_char(')'), sep_by1(expr(), lex_char('+')))
        .map(|x: Vec<Element<String>>| Element::SubExpr(true, x))
}
}

parser!{
   fn powfactor[I]()(I) -> Element<String>
    where [I: Stream<Item=char>]
{
    // TODO: support a^b^c? use chainl?
    factor()
        .and(optional(lex_char('^').with(factor())))
        .map(|(b, e)| match e {
            Some(ee) => Element::Pow(true, Box::new((b, ee))),
            _ => b,
        })
}
}

parser!{
   fn terms[I]()(I) -> Element<String>
    where [I: Stream<Item=char>]
{
    sep_by1(powfactor(), lex_char('*')).map(|x: Vec<Element<String>>| Element::Term(true, x))
}
}

parser!{
   fn minexpr[I]()(I) -> Element<String>
    where [I: Stream<Item=char>]
{
    lex_char('-')
        .with(choice!(parenexpr(), terms()))
        .map(|mut x| {
            match x {
                Element::Term(_, ref mut f) => f.push(Element::Num(false, false, 1, 1)),
                _ => x = Element::Term(true, vec![x, Element::Num(false, false, 1, 1)]),
            };
            x
        })
}
}

parser!{
   fn expr[I]()(I) -> Element<String>
    where [I: Stream<Item=char>]
{
    (
        optional(lex_char('+')).with(choice!(minexpr(), terms())),
        many(choice!(minexpr(), lex_char('+').with(terms()))),
    ).map(|(x, mut y): (Element<String>, Vec<Element<String>>)| {
            Element::SubExpr(true, {
                y.push(x);
                y
            })
        })
        .skip(spaces())
}
}
