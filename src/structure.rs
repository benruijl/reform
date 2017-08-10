use std::fmt;

#[derive(Debug)]
pub struct Module {
  pub input : FuncArg, // TODO: in future this is a stream of terms
  pub statements : Vec<Statement>
}

#[derive(Debug,Clone,PartialEq,Eq,PartialOrd,Ord)]
pub enum NumOrder {
	Greater,
	Smaller,
	Equal,
	GreaterEqual,
	SmallerEqual
}

// TODO: rename
#[derive(Debug,Clone,PartialEq,Eq,PartialOrd,Ord)]
pub enum FuncArg {
    VariableArgument(String), // ?a
    Wildcard(String,Vec<FuncArg>), // x?{...}
    Var(String), // x
    NumberRange(bool,u64,u64,NumOrder), // >0, <=-5/2
    Fn(Func), // f(...)
    Term(Vec<FuncArg>),
    SubExpr(Vec<FuncArg>),
    Num(bool,u64,u64), // fraction (true=positive), make sure it is last for sorting
}

// TODO: move Func into FuncArg?
#[derive(Debug,Clone,Eq,PartialEq,PartialOrd,Ord)]
pub struct Func {
    pub name: String,
    pub args: Vec<FuncArg>
}

#[derive(Debug,Clone,Eq,PartialEq,PartialOrd,Ord)]
pub enum Statement {
	IdentityStatement(IdentityStatement),
	SplitArg(String),
	Repeat(Vec<Statement>),
	Expand,
	Print,
	Multiply(FuncArg),
	// internal commands
	JumpIfChanged(usize), // jump and pop change flag
	PushChange // push a new change flag
}

#[derive(Debug)]
pub enum StatementResult<T> {
	Executed(T),
	NotExecuted(T),
	Done
}

#[derive(Debug,Clone,Eq,PartialEq,PartialOrd,Ord)]
pub struct IdentityStatement {
	pub mode : IdentityStatementMode, 
	pub lhs: FuncArg, 
	pub rhs: FuncArg
}


#[derive(Debug,Clone,Eq,PartialEq,PartialOrd,Ord)]
pub enum IdentityStatementMode {
    Once,
    Many,
    All
}

impl fmt::Display for Module {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		for (i,x) in self.statements.iter().enumerate() {
			write!(f, "{}: {}", i,x)?;
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
            Statement::Multiply(ref x) => writeln!(f, "Multiply {}", x),
            Statement::Repeat(ref ss) => {
            	if ss.len() == 1 {
            		write!(f, "repeat {}", ss[0])
            	} else {
            		writeln!(f, "repeat;")?;

            		for s in ss {
            			writeln!(f, "\t{}", s)?;
            		}

            		writeln!(f, "endrepeat;")
            	}
            },
            Statement::JumpIfChanged(ref i) => writeln!(f, "JMP_CH {}", i),
            Statement::PushChange => writeln!(f, "PUSH_CH")
         }
    }
}

impl fmt::Display for NumOrder {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match *self {
			NumOrder::Greater => write!(f,">"),
			NumOrder::GreaterEqual => write!(f,">="),
			NumOrder::Smaller => write!(f,"<"),
			NumOrder::SmallerEqual => write!(f,"<="),
			NumOrder::Equal => write!(f,"==")
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
            IdentityStatementMode::All => write!(f, "all")
        }
    }
}

impl fmt::Display for FuncArg {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &FuncArg::VariableArgument(ref name) => write!(f, "?{}",name),
            &FuncArg::Wildcard(ref name, ref restriction) => {
            	if restriction.len() == 0 {
            		write!(f, "{}?", name)
            	} else {
            		write!(f, "{}?{{", name)?;
            		match restriction.first() {
	                    Some(x) => write!(f, "{}", x)?,
	                    None => {},
	                }
	                for t in restriction.iter().skip(1) {
	                    write!(f, ",{}", t)?
	                }
	                write!(f,"}}")
            	}
            },
            &FuncArg::Var(ref name) => write!(f, "{}", name),
            &FuncArg::Num(ref pos, ref num, ref den) => {
            	if *den == 1 {
					write!(f, "{}{}", if *pos { "" } else {"-"}, num)
            	} else {
					write!(f, "{}{}/{}", if *pos { "" } else {"-"}, num, den)
            	}
            },
            &FuncArg::NumberRange(ref pos, ref num, ref den, ref rel) => {
            	write!(f, "{}", rel)?;
            	if *den == 1 {
					write!(f, "{}{}", if *pos { "" } else {"-"}, num)
            	} else {
					write!(f, "{}{}/{}", if *pos { "" } else {"-"}, num, den)
            	}
            },
            &FuncArg::Fn(ref func) => func.fmt(f),
            &FuncArg::Term(ref factors) => {
                match factors.first() {
                	Some(s@&FuncArg::SubExpr(_)) if factors.len() > 1 => write!(f, "({})", s)?,
                    Some(x) => write!(f, "{}", x)?,
                    None => {},
                }
                for t in factors.iter().skip(1) {
                	match t {
                		s@&FuncArg::SubExpr(_) => write!(f, "*({})", s)?,
                		_ => write!(f, "*{}", t)?
                	}
                }
                write!(f,"")
            },
            &FuncArg::SubExpr(ref terms) => {
                match terms.first() {
                    Some(x) => write!(f, "{}", x)?,
                    None => {},
                }
                for t in terms.iter().skip(1) {
                    write!(f, "+{}", t)?
                }
                write!(f,"")
            }
        }
    }
}

impl fmt::Display for Func {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}(", self.name)?;
        match self.args.first() {
            Some(x) => write!(f, "{}", x)?,
            None => {},
        }

        for x in self.args.iter().skip(1) {
            write!(f, ",{}", x)?;
        }

        write!(f, ")")
    }
}