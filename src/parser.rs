use structure::{FuncArg,Func,IdentityStatementMode,Statement,Module,IdentityStatement,NumOrder};
use nom::{digit,alpha,alphanumeric,GetInput};
use std;
use std::str;
use std::str::FromStr;
use std::io::prelude::*;
use std::fs::File;

named!(builtin <String>, do_parse!(f: map_res!(alt_complete!(tag!("dd_") |tag!("delta_") 
	| tag!("theta_") | tag!("pow_")), std::str::from_utf8) >> (f.to_owned())));

// varname: alpha + alphanumeric
named!(varname <String>, do_parse!(
	first: map_res!(alpha, std::str::from_utf8) >>
  rest: opt!(complete!(map_res!(alphanumeric, std::str::from_utf8))) >>
	(
    match rest {
		Some(vv) => first.to_owned() + vv,
		None => first.to_owned()
	} )
	
));

named!(pub exprparen <FuncArg>, ws!(delimited!(char!('('), expression, char!(')'))));

named!(minusexpr <FuncArg>, do_parse!(ws!(tag!("-")) >>
	g: map!(alt_complete!(term | funcarg),|x| match x { 
		FuncArg::Term(mut g) => FuncArg::Term( { g.push(FuncArg::Num(false,1,1)); g } ), 
		a => FuncArg::Term(vec![a, FuncArg::Num(false,1,1)])
	}) >> (g)
));

named!(pub expression <FuncArg>, do_parse!(
  opt!(tag!("+")) >>
  first : alt_complete!(minusexpr | term | funcarg) >>
  rest: many0!(
    alt_complete!(do_parse!(ws!(tag!("+")) >> f: alt_complete!(term | funcarg) >> (f)) 
    | minusexpr
   )) >>
  (match rest.len() {
  	0 => first,
  	_ => FuncArg::SubExpr({let mut a = vec![first]; a.extend(rest); a})
  	})

  	
));

named!(term <FuncArg>, map!(separated_nonempty_list_complete!(char!('*'), funcarg), |x| if x.len() == 1 { x[0].clone() } else { FuncArg::Term(x) } ));
named!(variable <FuncArg>, map!(ws!(varname),|v| FuncArg::Var(v)));
named!(funcarg <FuncArg>, alt_complete!(map!(function, |x| FuncArg::Fn(x)) | exprparen | numberdiv | numbersimple | rangedwildcard | wildcard | variable));

named!(number <(bool,u64)>, do_parse!(pos: opt!(tag!("-")) >>  val: map_res!(map_res!(ws!(digit), str::from_utf8), FromStr::from_str) >> 
    (match pos { Some(_) => false, _ => true}, val) ));

named!(numbersimple <FuncArg>, do_parse!(
    num: number >>
    (FuncArg::Num(num.0, num.1, 1))));

named!(numberdiv <FuncArg>, do_parse!(
    num: number >> // make optional?
    ws!(tag!("/")) >>
    den : number >>
    (FuncArg::Num((num.0 & den.0) || (!num.0 && !den.0) , num.1, den.1))
    )
);

named!(numorder <NumOrder>, ws!(
	alt_complete!(
	map!(tag!(">="), |_| NumOrder::GreaterEqual) |
	map!(tag!(">"), |_| NumOrder::Greater) |
	map!(tag!("=="), |_| NumOrder::Equal) |
	map!(tag!("<="), |_| NumOrder::SmallerEqual) |
	map!(tag!("<"), |_| NumOrder::Smaller)
	)));
named!(numrange <FuncArg>, do_parse!(no: numorder >> num: alt_complete!(numberdiv | numbersimple) >> (match num {
	FuncArg::Num(pos, num, den) => FuncArg::NumberRange(pos, num, den, no), _ => unreachable!() })));
named!(set <Vec<FuncArg>>, ws!(delimited!(char!('{'), separated_list!(char!(','), alt_complete!(expression | numrange)), char!('}'))));
named!(wildcard <FuncArg>, do_parse!(name: ws!(varname) >> ws!(tag!("?")) >> r: opt!(set) >> 
    (FuncArg::Wildcard(name, match r { Some(a) => a, None => vec![]}))));

//named!(wildcard <FuncArg>, do_parse!(name: ws!(varname) >> ws!(tag!("?")) >> (FuncArg::Wildcard(name))));
named!(rangedwildcard <FuncArg>, do_parse!(ws!(tag!("?")) >> name: ws!(varname) >> (FuncArg::VariableArgument(name))));

named!(pub splitarg <Statement>, do_parse!(ws!(tag!("splitarg")) >> name: ws!(varname) >> ws!(tag!(";")) >> ( Statement::SplitArg(name) ) ) );
named!(pub print <Statement>, do_parse!(ws!(tag!("print")) >> ws!(tag!(";")) >> ( Statement::Print ) ) );
named!(pub expand <Statement>, do_parse!(ws!(tag!("expand")) >> ws!(tag!(";")) >> ( Statement::Expand ) ) );
named!(pub multiply <Statement>, do_parse!(ws!(tag!("multiply")) >> e: ws!(expression) >> ws!(tag!(";")) >> ( Statement::Multiply(e) ) ) );

named!(repeatblock <Statement>, do_parse!(
    ws!(tag!("repeat;")) >>
    sts : many0!(complete!(statement)) >>
    ws!(tag!("endrepeat;")) >>
   (Statement::Repeat(sts))
  )
);

named!(repeat <Statement>, do_parse!(
    ws!(tag_no_case!("repeat")) >>
    st: statement >>
   (Statement::Repeat(vec![st]))
  )
);


named!(pub idstatement <Statement>, do_parse!(
    ws!(tag!("id")) >>
    mode: ws!(map!(opt!(alt_complete!(
          map!(tag!("all"),|_|{ IdentityStatementMode::All}) | 
          map!(tag!("many"),|_|{ IdentityStatementMode::Many}))),
      |y : Option<IdentityStatementMode>| {y.unwrap_or(IdentityStatementMode::Once)})) >>
    lhs: term >>
    ws!(tag!("=")) >>
    rhs: expression >>
    ws!(tag!(";")) >>
   (Statement::IdentityStatement(IdentityStatement {mode, lhs, rhs}))
  )
);

named!(pub function <Func>, do_parse!(
  fnname : ws!(alt_complete!(builtin | varname)) >>
    args: ws!(delimited!(char!('('), separated_list!(char!(','), alt_complete!( expression | exprparen ) ), char!(')'))) >>
  (Func { name: fnname, args: args})
  )
);

named!(input <FuncArg>, do_parse!(ws!(tag!("IN")) >> ws!(tag!("=")) >> t: expression >> ws!(tag!(";")) >> (t)));

pub fn parse_file(filename: &str) -> Module {
  let mut f = File::open(filename).expect(&format!("Unable to open file {:?}", filename));
  let mut s  = vec![];
  f.read_to_end(&mut s).expect("Unable to read file");

  let a = parseform(&s);
  if let Some(ref r) = a.remaining_input() {
    if *r != [] {
      panic!("Could not parse file completely at: {}",  str::from_utf8(&r).expect("No utf-8"));
    }
  }

  a.to_result().expect("Module parsing error")
}

fn eol(chr: u8) -> bool { chr != b'\n' }
named!(comment, do_parse!(ws!(tag!("//")) >> a: take_while!(eol) >> (a))); // comment ends on line end or eof

named!(blockcomment, ws!(delimited!(tag!("/*"), take_until!("*/"), tag!("*/"))));


named!(statement <Statement>, do_parse!(
    many0!(alt_complete!(blockcomment | comment)) >>
    id: alt_complete!(repeatblock | repeat | multiply | idstatement | splitarg | expand | print) >>
    (id)
  )
);

// FIXME: why so complicated?
named!(parseform <Module>, do_parse!(
  input: input >> 
  ids : complete!(many0!(complete!(statement))) >>
  complete!(many0!(alt_complete!(blockcomment | comment))) >>
  (Module {input: input, statements : ids }))
);