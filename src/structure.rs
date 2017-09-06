use std::fmt;
use streaming::TermStreamer;
use std::collections::HashMap;
use std::mem;

pub const BUILTIN_FUNCTIONS :  &'static [&'static str] = &["delta_", "nargs_"];
pub const FUNCTION_DELTA : u64 = 0;
pub const FUNCTION_NARGS : u64 = 1;

#[derive(Debug)]
pub struct Program {
    pub input: TermStreamer,
    pub modules: Vec<Module>,
    inv_name_map: Vec<String>,
    name_map: HashMap<String, u64>
}

impl Program {
    fn replace_name(&mut self, name: &mut VarName) {
        let nm = &mut self.name_map;
        let inv = &mut self.inv_name_map;
        *name = match *name {
            VarName::Name(ref mut s) => VarName::ID(*nm.entry(s.clone()).or_insert_with(|| {
                inv.push(mem::replace(s, String::new()));
                (inv.len() - 1) as u64
            })),
            _ => return,
        }
    }

    pub fn new(input: Element, mut modules: Vec<Module>) -> Program {
        let mut prog =  Program {
            input: TermStreamer::new(),
            modules: vec![],
            inv_name_map: vec![],
            name_map: HashMap::new()
        };

        // insert built-in functions
        let mut i : u64 = 0;
        for x in BUILTIN_FUNCTIONS {
            prog.name_map.insert(x.to_string(), i);
            prog.inv_name_map.push(x.to_string());
            i += 1;
        }

        match input {
            Element::SubExpr(_, t) => for x in t {
                let mut nt = x.normalize();
                nt.var_to_id(&mut prog);
                prog.input.add_term_input(nt);
            },
            x => {
                let mut nt = x.normalize();
                nt.var_to_id(&mut prog);
                prog.input.add_term_input(nt);
            }
        }

        for m in &mut modules {
            for s in &mut m.statements {
                s.var_to_id(&mut prog);
            }
        }
        prog.modules = modules;
        prog
    }
}

#[derive(Debug)]
pub struct Module {
    pub name: String,
    pub statements: Vec<Statement>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum NumOrder {
    Greater,
    Smaller,
    Equal,
    GreaterEqual,
    SmallerEqual,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum VarName {
    ID(u64),
    Name(String),
}

// all the algebraic elements. A bool as the first
// argument is the dirty flag, which is set to true
// if a normalization needs to happen
// TODO: ignore dirty flag for equality and ordering
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Element {
    VariableArgument(VarName),             // ?a
    Wildcard(VarName, Vec<Element>),       // x?{...}
    Var(VarName),                          // x
    Pow(bool, Box<Element>, Box<Element>), // (1+x)^3
    NumberRange(bool, u64, u64, NumOrder), // >0, <=-5/2
    Fn(bool, Func),                        // f(...)
    Term(bool, Vec<Element>),
    SubExpr(bool, Vec<Element>),
    Num(bool, bool, u64, u64), // dirty, fraction (true=positive), make sure it is last for sorting
}

// TODO: move Func into Element?
#[derive(Debug, Clone, Eq, PartialEq, PartialOrd, Ord)]
pub struct Func {
    pub name: VarName,
    pub args: Vec<Element>,
}

#[derive(Debug, Clone, Eq, PartialEq, PartialOrd, Ord)]
pub enum Statement {
    IdentityStatement(IdentityStatement),
    SplitArg(VarName),
    Repeat(Vec<Statement>),
    IfElse(Element, Vec<Statement>, Vec<Statement>),
    Expand,
    Print,
    Multiply(Element),
    Symmetrize(VarName),
    // internal commands
    Jump(usize),          // unconditional jump
    Eval(Element, usize), // evaluate and jump if eval is false
    JumpIfChanged(usize), // jump and pop change flag
    PushChange,           // push a new change flag
}

#[derive(Debug)]
pub enum StatementResult<T> {
    Executed(T),
    NotExecuted(T),
    Done,
}

#[derive(Debug, Clone, Eq, PartialEq, PartialOrd, Ord)]
pub struct IdentityStatement {
    pub mode: IdentityStatementMode,
    pub lhs: Element,
    pub rhs: Element,
}


#[derive(Debug, Clone, Eq, PartialEq, PartialOrd, Ord)]
pub enum IdentityStatementMode {
    Once,
    Many,
    All,
}

impl fmt::Display for Module {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for (i, x) in self.statements.iter().enumerate() {
            write!(f, "{}: {}", i, x)?;
        }
        writeln!(f, "")
    }
}

impl fmt::Display for Statement {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Statement::IdentityStatement(ref id) => write!(f, "{}", id),
            Statement::SplitArg(ref name) => writeln!(f, "SplitArg {};", name),
            Statement::Expand => writeln!(f, "Expand;"),
            Statement::Print => writeln!(f, "Print;"),
            Statement::Multiply(ref x) => writeln!(f, "Multiply {};", x),
            Statement::Symmetrize(ref x) => writeln!(f, "Symmetrize {};", x),
            Statement::Repeat(ref ss) => if ss.len() == 1 {
                write!(f, "repeat {}", ss[0])
            } else {
                writeln!(f, "repeat;")?;

                for s in ss {
                    writeln!(f, "\t{}", s)?;
                }

                writeln!(f, "endrepeat;")
            },
            Statement::IfElse(ref cond, ref m, ref nm) => if nm.len() == 0 && m.len() == 1 {
                write!(f, "if (match({})) {};", cond, m[0])
            } else {
                writeln!(f, "if (match({}));", cond)?;

                for s in m {
                    writeln!(f, "\t{}", s)?;
                }

                if nm.len() > 0 {
                    writeln!(f, "else;")?;
                    for s in m {
                        writeln!(f, "\t{}", s)?;
                    }
                }

                writeln!(f, "endif;")
            },
            Statement::Jump(ref i) => writeln!(f, "JMP {}", i),
            Statement::Eval(ref n, ref i) => writeln!(f, "IF NOT {} JMP {}", n, i),
            Statement::JumpIfChanged(ref i) => writeln!(f, "JMP_CH {}", i),
            Statement::PushChange => writeln!(f, "PUSH_CH"),
        }
    }
}

impl fmt::Display for VarName {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            VarName::ID(id) => write!(f, "{}_", id),
            VarName::Name(ref s) => write!(f, "{}", s),
        }
    }
}

impl fmt::Display for NumOrder {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            NumOrder::Greater => write!(f, ">"),
            NumOrder::GreaterEqual => write!(f, ">="),
            NumOrder::Smaller => write!(f, "<"),
            NumOrder::SmallerEqual => write!(f, "<="),
            NumOrder::Equal => write!(f, "=="),
        }
    }
}

impl fmt::Display for IdentityStatement {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "id {} {} = {};", self.mode, self.lhs, self.rhs)
    }
}

impl fmt::Display for IdentityStatementMode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            IdentityStatementMode::Once => write!(f, "once"),
            IdentityStatementMode::Many => write!(f, "many"),
            IdentityStatementMode::All => write!(f, "all"),
        }
    }
}

impl fmt::Display for Element {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Element::VariableArgument(ref name) => write!(f, "?{}", name),
            &Element::Wildcard(ref name, ref restriction) => if restriction.len() == 0 {
                write!(f, "{}?", name)
            } else {
                write!(f, "{}?{{", name)?;
                match restriction.first() {
                    Some(x) => write!(f, "{}", x)?,
                    None => {}
                }
                for t in restriction.iter().skip(1) {
                    write!(f, ",{}", t)?
                }
                write!(f, "}}")
            },
            &Element::Var(ref name) => write!(f, "{}", name),
            &Element::Num(_, ref pos, ref num, ref den) => if *den == 1 {
                write!(f, "{}{}", if *pos { "" } else { "-" }, num)
            } else {
                write!(f, "{}{}/{}", if *pos { "" } else { "-" }, num, den)
            },
            &Element::NumberRange(ref pos, ref num, ref den, ref rel) => {
                write!(f, "{}", rel)?;
                if *den == 1 {
                    write!(f, "{}{}", if *pos { "" } else { "-" }, num)
                } else {
                    write!(f, "{}{}/{}", if *pos { "" } else { "-" }, num, den)
                }
            }
            &Element::Pow(_, ref e, ref p) => {
                match **e {
                    Element::SubExpr(..) | Element::Term(..) => write!(f, "({})", e)?,
                    _ => write!(f, "{}", e)?,
                };
                match **p {
                    Element::SubExpr(..) | Element::Term(..) => write!(f, "^({})", p),
                    _ => write!(f, "^{}", p),
                }
            }
            &Element::Fn(_, ref func) => func.fmt(f),
            &Element::Term(_, ref factors) => {
                match factors.first() {
                    Some(s @ &Element::SubExpr(..)) if factors.len() > 1 => write!(f, "({})", s)?,
                    Some(x) => write!(f, "{}", x)?,
                    None => {}
                }
                for t in factors.iter().skip(1) {
                    match t {
                        s @ &Element::SubExpr(..) => write!(f, "*({})", s)?,
                        _ => write!(f, "*{}", t)?,
                    }
                }
                write!(f, "")
            }
            &Element::SubExpr(_, ref terms) => {
                match terms.first() {
                    Some(x) => write!(f, "{}", x)?,
                    None => {}
                }
                for t in terms.iter().skip(1) {
                    write!(f, "+{}", t)?
                }
                write!(f, "")
            }
        }
    }
}

impl fmt::Display for Func {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}(", self.name)?;
        match self.args.first() {
            Some(x) => write!(f, "{}", x)?,
            None => {}
        }

        for x in self.args.iter().skip(1) {
            write!(f, ",{}", x)?;
        }

        write!(f, ")")
    }
}

impl Element {
    // replace a string name for a numerical ID
    pub fn var_to_id(&mut self, prog: &mut Program) {
        match *self {
            Element::Var(ref mut name) | Element::VariableArgument(ref mut name) => {
                prog.replace_name(name);
            }
            Element::Wildcard(ref mut name, ref mut restrictions) => {
                prog.replace_name(name);
                for x in restrictions {
                    x.var_to_id(prog);
                }
            }
            Element::Pow(_, ref mut b, ref mut e) => {
                b.var_to_id(prog);
                e.var_to_id(prog);
            }
            Element::Term(_, ref mut f) | Element::SubExpr(_, ref mut f) => for x in f {
                x.var_to_id(prog);
            },
            Element::Fn(
                _,
                Func {
                    ref mut name,
                    ref mut args,
                },
            ) => {
                prog.replace_name(name);
                for x in args {
                    x.var_to_id(prog);
                }
            }
            _ => {}
        }
    }
}

impl Statement {
    pub fn var_to_id(&mut self, prog: &mut Program) {
        match *self {
            Statement::IdentityStatement(IdentityStatement {
                mode: _,
                ref mut lhs,
                ref mut rhs,
            }) => {
                lhs.var_to_id(prog);
                rhs.var_to_id(prog);
            },
            Statement::Repeat(ref mut ss) => {
                for s in ss {
                    s.var_to_id(prog);
                }
            },
            Statement::IfElse(ref mut e, ref mut ss, ref mut sse) => {
                e.var_to_id(prog);
                for s in ss {
                    s.var_to_id(prog);
                }
                for s in sse {
                    s.var_to_id(prog);
                }
            },
            Statement::SplitArg(ref mut name) | Statement::Symmetrize(ref mut name) => {
                prog.replace_name(name);
            }
            _ => {}
        }
    }
}
