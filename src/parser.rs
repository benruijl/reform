use std::io::prelude::*;
use std::fs::File;
use structure::*;

use combine::char::*;
use combine::*;
use combine::primitives::Stream;
use combine::State;
use std::ascii::AsciiExt;

// parse a reform file
pub fn parse_file(filename: &str) -> Program {
    let mut f = File::open(filename).expect(&format!("Unable to open file {:?}", filename));
    let mut s = String::new();
    f.read_to_string(&mut s).expect("Unable to read file");
  
    match program().parse(State::new(&s[..])) {
        Ok((v, _)) => v,
        Err(err) => { error!("{}", err); panic!(); }
    }
}

pub fn parse_term(input: &str) -> Element {
    expr().skip(eof()).parse(State::new(input)).ok().unwrap().0
}

parser!{
   fn program[I]()(I) -> Program
    where [I: Stream<Item=char>]
{
    // skip spaces and comments
    let linecomment = || try(string("//")).and(skip_many(satisfy(|c| c != '\n'))).map(|_| ());
    let blockcomment = || try(string("/*")).and(skip_many(not_followed_by(string("*/")).and(any()))).and(string("*/")).map(|_| ());
    let skipnocode = || skip_many(skip_many1(space()).or(linecomment()).or(blockcomment()));

    let lex_char = |c| char(c).skip(skipnocode());
    let keyword = |c| try(string_cmp(c, |l,r| l.eq_ignore_ascii_case(&r))).skip(not_followed_by(alpha_num())).skip(skipnocode());
    let varname = || (many1(letter()), many(alpha_num())).skip(spaces())
    .map(|(mut f, r) : (String, String)| { f.push_str(&r); f}).expected("function or variable name");

    let procedure = || struct_parser!{
        Procedure {
            _: keyword("procedure"),
            name: varname(),
            args: lex_char('(').with(sep_by(expr(), lex_char(','))).skip(skipnocode()),
            local_args: optional(lex_char(';').with(sep_by(expr(), lex_char(',')))).map(|x| x.unwrap_or(vec![])).skip(skipnocode()),
            _: lex_char(')').with(lex_char(';')),
            statements: many(statement()),
            _: keyword("endprocedure").with(lex_char(';'))
        }
    };

    let module = || struct_parser!{
        Module {
            name: value("test".to_string()),
            statements: many(statement()),
            global_statements: value(vec![]),
            _: keyword("sort").with(lex_char(';'))
        }
    };

    let input = keyword("IN").with(lex_char('=')).with(expr()).skip(lex_char(';'));

    skipnocode().with((input, many(procedure()), many(module()))).skip(eof()).map(|(e,p,m)| Program::new(e, m, p))
}
}

parser!{
   fn statement[I]()(I) -> Statement
    where [I: Stream<Item=char>]
{
    let lex_char = |c| char(c).skip(spaces());
    let varname = || (many1(letter()), many(alpha_num())).skip(spaces())
        .map(|(mut f, r) : (String, String)| { f.push_str(&r); f}).expected("function or variable name");

    // skip spaces and comments
    let linecomment = || try(string("//")).and(skip_many(satisfy(|c| c != '\n'))).map(|_| ());
    let blockcomment = || try(string("/*")).and(skip_many(not_followed_by(string("*/")).and(any()))).and(string("*/")).map(|_| ());
    let skipnocode = || skip_many(skip_many1(space()).or(linecomment()).or(blockcomment()));

    let keyword = |c| try(string_cmp(c, |l,r| l.eq_ignore_ascii_case(&r))).skip(not_followed_by(alpha_num())).skip(skipnocode());
    
    let statementend = || lex_char(';').skip(skipnocode());

    let symmetrize = || keyword("symmetrize").with(varname()).skip(statementend()).map(|x| Statement::Symmetrize(VarName::Name(x)));
    let multiply = || keyword("multiply").with(expr()).skip(statementend()).map(|x| Statement::Multiply(x));
    let splitarg = || keyword("splitarg").with(varname()).skip(statementend()).map(|x| Statement::SplitArg(VarName::Name(x)));
    let expand = || keyword("expand").skip(statementend()).map(|_| Statement::Expand);
    let print = || keyword("print").skip(statementend()).map(|_| Statement::Print);
    let collect = || keyword("collect").with(varname()).skip(statementend()).map(|x| Statement::Collect(VarName::Name(x)));
    let call_procedure = || (keyword("call").with(varname()), between(lex_char('('), lex_char(')'), sep_by(expr(), lex_char(',')))).
        skip(statementend()).map(|(name, args)| Statement::Call(name, args));

    let idmode = optional(choice!(keyword("once"), keyword("all"), keyword("many"))).map(|x| match x {
                    Some("all") => IdentityStatementMode::All,
                    Some("many") => IdentityStatementMode::Many,
                    _ => IdentityStatementMode::Once
                });
    let idstatement = || struct_parser!{
        IdentityStatement {
            _: keyword("id"),
            mode: idmode,
            lhs: expr(),
            _: lex_char('='),
            rhs: expr(),
            _: statementend()
        }
    }.map(|x| Statement::IdentityStatement(x));

    let repeat = || keyword("repeat").with(
        choice!(statementend().with(many(statement())).skip(keyword("endrepeat")).skip(statementend()).map(|x| Statement::Repeat(x)),
            statement().map(|x| Statement::Repeat(vec![x]))
        ));

    let ifclause = || between(lex_char('('),lex_char(')'), keyword("match").with(
        between(lex_char('('),lex_char(')'), expr())));
    let ifelse = || (keyword("if").with(ifclause())
        ,choice!(statementend().with(many(statement())).skip(keyword("endif")).skip(statementend()),
        statement().map(|x| vec![x])),
        optional(keyword("else").with(choice!(statementend().with(many(statement())).skip(keyword("endif")).skip(statementend()),
        statement().map(|x| vec![x])))).map(|x| x.unwrap_or(vec![]))). // parse the else
        map(|(q,x,e)| Statement::IfElse(q, x, e));

    choice!(call_procedure(), print(), ifelse(), expand(), multiply(), repeat(), idstatement(), collect(), splitarg(), symmetrize()).skip(skipnocode())
}
}

parser!{
   fn expr[I]()(I) -> Element
    where [I: Stream<Item=char>]
{
    let lex_char = |c| char(c).skip(spaces());
    let varname = || (many1(letter()), many(alpha_num())).skip(spaces())
        .map(|(mut f, r) : (String, String)| { f.push_str(&r); f}).expected("function or variable name");
  
    let comma_list = || sep_by(expr(), lex_char(','));
    let funcarg = || between(lex_char('('), lex_char(')'), comma_list());

    let number = || (optional(char('-')).map(|x| x.is_none()), 
        many1(digit()).map(|d : String| d.parse::<u64>().unwrap()), 
        optional(char('/').with(many1(digit()))).map(|x| x.map(|y : String| y.parse::<u64>().unwrap()).unwrap_or(1) 
    )).map(|(sign, num, den)| Element::Num(true, sign, num, den));

    let numorder = || choice!(try(string(">=")).map(|_| NumOrder::GreaterEqual), 
    string(">").map(|_| NumOrder::Greater), string("==").map(|_| NumOrder::Equal), 
    try(string("<=")).map(|_| NumOrder::SmallerEqual), string("<").map(|_| NumOrder::Smaller)).skip(spaces());
    let numrange = || (numorder(), number()).map(|(r,b)| match b {
        Element::Num(_,pos,num,den) => Element::NumberRange(pos,num,den,r),
        _ => unreachable!()
    });
    let set = || between(lex_char('{'), lex_char('}'), sep_by(choice!(expr(), numrange()), lex_char(',')));
    let variableargument = || (char('?'), varname()).map(|x| Element::VariableArgument(VarName::Name("?".to_owned() + &x.1)));

    // read the variable name and then see if it is a wildcard, a function or variable
    let namedfactor = || varname().and(choice!(lex_char('?').and(optional(set()).map(|x| x.unwrap_or(vec![]))).
        map(|(_, s)| Element::Wildcard(VarName::ID(1), s)),
        funcarg().map(|fa| Element::Fn(true, Func{ name: VarName::ID(1), args: fa })),
        value(1).map(|_| Element::Var(VarName::ID(1))))).map(|(name, mut res)| {
            match res {
                Element::Wildcard(ref mut n, ..) => *n = VarName::Name(name),
                Element::Fn(_, Func { name: ref mut n, .. } ) => *n = VarName::Name(name),
                Element::Var(ref mut n) => *n = VarName::Name(name),
                _ => unreachable!()
            }
            res
        });

    let parenexpr = || between(lex_char('('), lex_char(')'), sep_by1(expr(), lex_char('+'))).
        map(|x : Vec<Element>| Element::SubExpr(true, x));
    let factor = || choice!(number(), namedfactor(), variableargument(), parenexpr());

    // TODO: support a^b^c? use chainl?
    let powfactor = || factor().and(optional(lex_char('^').with(factor()))).map(|(b, e)| match e {
        Some(ee) => Element::Pow(true, Box::new(b), Box::new(ee)),
        _ => b
    });

    let terms = || sep_by1(powfactor(), lex_char('*')).map(|x : Vec<Element>| Element::Term(true, x));
    let minexpr = || lex_char('-').with(choice!(parenexpr(), terms())).map(|mut x| { match x {
        Element::Term(_, ref mut f) => f.push(Element::Num(false,false,1,1)),
        _ => { x = Element::Term(true, vec![x,Element::Num(false,false,1,1)])}
    }; x});
    let expr_full = || (optional(lex_char('+')).with(choice!(minexpr(), terms())),
        many(choice!(minexpr(), lex_char('+').with(terms())))).
        map(|(x, mut y) : (Element, Vec<Element>)| Element::SubExpr(true, {y.push(x); y}));

    expr_full().skip(spaces())
}
}
