use std::fmt;

#[derive(Debug)]
pub struct Program {
    pub input: Element, // TODO: in future this is a stream of terms
    pub modules: Vec<Module>,
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

// TODO: rename
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Element {
    VariableArgument(String),              // ?a
    Wildcard(String, Vec<Element>),        // x?{...}
    Var(String),                           // x
    NumberRange(bool, u64, u64, NumOrder), // >0, <=-5/2
    Fn(Func),                              // f(...)
    Term(Vec<Element>),
    SubExpr(Vec<Element>),
    Num(bool, u64, u64), // fraction (true=positive), make sure it is last for sorting
}

// TODO: move Func into Element?
#[derive(Debug, Clone, Eq, PartialEq, PartialOrd, Ord)]
pub struct Func {
    pub name: String,
    pub args: Vec<Element>,
}

#[derive(Debug, Clone, Eq, PartialEq, PartialOrd, Ord)]
pub enum Statement {
    IdentityStatement(IdentityStatement),
    SplitArg(String),
    Repeat(Vec<Statement>),
    IfElse(Element, Vec<Statement>, Vec<Statement>),
    Expand,
    Print,
    Multiply(Element),
    Symmetrize(String),
    // internal commands
    Jump(usize), // unconditional jump
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
            &Element::Num(ref pos, ref num, ref den) => if *den == 1 {
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
            &Element::Fn(ref func) => func.fmt(f),
            &Element::Term(ref factors) => {
                match factors.first() {
                    Some(s @ &Element::SubExpr(_)) if factors.len() > 1 => write!(f, "({})", s)?,
                    Some(x) => write!(f, "{}", x)?,
                    None => {}
                }
                for t in factors.iter().skip(1) {
                    match t {
                        s @ &Element::SubExpr(_) => write!(f, "*({})", s)?,
                        _ => write!(f, "*{}", t)?,
                    }
                }
                write!(f, "")
            }
            &Element::SubExpr(ref terms) => {
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
