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
    pub procedures: Vec<Procedure>,
    pub var_info: VarInfo,
}

// keeps track of global state
#[derive(Debug)]
pub struct VarInfo {
    inv_name_map: Vec<String>,
    name_map: HashMap<String, u64>,
    local_map: HashMap<u64, u64>, // (temporary) map from ids to new ids in a procedure
}

impl VarInfo {
    fn empty() -> VarInfo {
        VarInfo { inv_name_map: vec![], name_map: HashMap::new(), local_map: HashMap::new() }
    }

    fn new() -> VarInfo {
        let mut inv_name_map = vec![];
        let mut name_map = HashMap::new();

        // insert built-in functions
        let mut i : u64 = 0;
        for x in BUILTIN_FUNCTIONS {
            name_map.insert(x.to_string(), i);
            inv_name_map.push(x.to_string());
            i += 1;
        }
        VarInfo { inv_name_map, name_map, local_map: HashMap::new() }
    }

    pub fn replace_name(&mut self, name: &mut VarName) {
        let nm = &mut self.name_map;
        let inv = &mut self.inv_name_map;
        let lm = &mut self.local_map;
        *name = match *name {
            VarName::Name(ref mut s) => VarName::ID(*nm.entry(s.clone()).or_insert_with(|| {
                inv.push(mem::replace(s, String::new()));
                (inv.len() - 1) as u64
            })),
            VarName::ID(v) => VarName::ID(*lm.get(&v).unwrap_or(&v)) // map local variable?
        }
    }

    pub fn add_local(&mut self, name: &str) {
        if let Some(y) = self.name_map.get(name) {
            self.local_map.insert(*y, self.name_map.len() as u64); // we have seen this variable before
        }
        self.name_map.insert(format!("{}_{}", name, self.inv_name_map.len() as u64), self.inv_name_map.len() as u64);
    }

    pub fn clear_local(&mut self) {
        self.local_map.clear();
    }
}

impl Program {
    pub fn new(input: Element, mut modules: Vec<Module>, mut procedures: Vec<Procedure>) -> Program {
        let mut prog =  Program {
            input: TermStreamer::new(),
            modules: vec![],
            procedures: vec![],
            var_info: VarInfo::new()
        };

        match input {
            Element::SubExpr(_, t) => for mut x in t {
                x.var_to_id(&mut prog.var_info);
                prog.input.add_term_input(x.normalize());
            },
            mut x => {
                x.var_to_id(&mut prog.var_info);
                prog.input.add_term_input(x.normalize());
            }
        }

        for m in &mut modules {
            for s in &mut m.statements {
                s.var_to_id(&mut prog.var_info);
            }
        }

        // NOTE: the names of the arguments are not substituted
        for m in &mut procedures {
            for s in &mut m.statements {
                s.var_to_id(&mut prog.var_info);
            }
        }

        prog.modules = modules;
        prog.procedures = procedures;
        prog
    }
}

#[derive(Debug)]
pub struct Module {
    pub name: String,
    pub statements: Vec<Statement>,
}

#[derive(Debug)]
pub struct Procedure {
    pub name: String,
    pub args: Vec<Element>,
    pub local_args: Vec<Element>,
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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
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
    Call(String, Vec<Element>),
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

impl fmt::Display for Procedure {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "procedure {}(", self.name)?;

        match self.args.first() {
            Some(x) => write!(f, "{}", x)?,
            None => {}
        }

        for x in self.args.iter().skip(1) {
            write!(f, ",{}", x)?;
        }

        if self.local_args.len() > 0 {
            write!(f, ";")?;
            match self.local_args.first() {
                Some(x) => write!(f, "{}", x)?,
                None => {}
            }

            for x in self.local_args.iter().skip(1) {
                write!(f, ",{}", x)?;
            }
        }
        writeln!(f, ");")?;

        for s in &self.statements {
            write!(f, "\t{}", s)?;
        }

        writeln!(f, "endprocedure;")
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
            Statement::Call(ref name, ref args) => {
                writeln!(f, "call {}(", name)?;

                match args.first() {
                    Some(x) => write!(f, "{}", x)?,
                    None => {}
                }

                for x in args.iter().skip(1) {
                    write!(f, ",{}", x)?;
                }

                writeln!(f, ");")
            },
            Statement::Jump(ref i) => writeln!(f, "JMP {}", i),
            Statement::Eval(ref n, ref i) => writeln!(f, "IF NOT {} JMP {}", n, i),
            Statement::JumpIfChanged(ref i) => writeln!(f, "JMP_CH {}", i),
            Statement::PushChange => writeln!(f, "PUSH_CH"),
        }
    }
}

impl VarName {
    fn fmt_output(&self, f: &mut fmt::Formatter, var_info: &VarInfo) -> fmt::Result {
        match *self {
            VarName::ID(id) => write!(f, "{}", var_info.inv_name_map[id as usize]),
            VarName::Name(ref s) => write!(f, "{}", s),
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

pub struct ElementPrinter<'a> {
    pub element: &'a Element,
    pub var_info: &'a VarInfo
}

impl<'a> fmt::Display for ElementPrinter<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.element.fmt_output(f, self.var_info)
    }
}

impl Element {
    pub fn fmt_output(&self, f: &mut fmt::Formatter, var_info: &VarInfo) -> fmt::Result {
        match self {
            &Element::VariableArgument(ref name) => {write!(f, "?")?; name.fmt_output(f, var_info) },
            &Element::Wildcard(ref name, ref restriction) => if restriction.len() == 0 {
                name.fmt_output(f, var_info)?;
                write!(f, "?")
            } else {
                name.fmt_output(f, var_info)?;
                write!(f, "?{{")?;
                match restriction.first() {
                    Some(x) => x.fmt_output(f, var_info)?,
                    None => {}
                }
                for t in restriction.iter().skip(1) {
                    t.fmt_output(f, var_info)?
                }
                write!(f, "}}")
            },
            &Element::Var(ref name) => name.fmt_output(f, var_info),
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
                    Element::SubExpr(..) | Element::Term(..) => { write!(f, "(")?; e.fmt_output(f, var_info)?; write!(f, ")")?  },
                    _ => e.fmt_output(f, var_info)?,
                };
                match **p {
                    Element::SubExpr(..) | Element::Term(..) => { write!(f, "^(")?; p.fmt_output(f, var_info)?; write!(f, ")")  },
                    _ => { write!(f, "^")?; p.fmt_output(f, var_info) },
                }
            }
            &Element::Fn(_, ref func) => func.fmt_output(f, var_info),
            &Element::Term(_, ref factors) => {
                match factors.first() {
                    Some(s @ &Element::SubExpr(..)) if factors.len() > 1 => { write!(f, "(")?; s.fmt_output(f, var_info)?; write!(f, ")")?  },
                    Some(x) => x.fmt_output(f, var_info)?,
                    None => {}
                }
                for t in factors.iter().skip(1) {
                    match t {
                        s @ &Element::SubExpr(..) => { write!(f, "*(")?; s.fmt_output(f, var_info)?; write!(f, ")")? },
                        _ => { write!(f, "*")?; t.fmt_output(f, var_info)? },
                    }
                }
                write!(f, "")
            }
            &Element::SubExpr(_, ref terms) => {
                match terms.first() {
                    Some(x) => x.fmt_output(f, var_info)?,
                    None => {}
                }
                for t in terms.iter().skip(1) {
                    write!(f, "+")?;
                    t.fmt_output(f, var_info)?
                }
                write!(f, "")
            }
        }
    }
}

impl fmt::Display for Element {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.fmt_output(f, &VarInfo::empty())
    }
}

impl Func {
    pub fn fmt_output(&self, f: &mut fmt::Formatter, var_info: &VarInfo) -> fmt::Result {
        self.name.fmt_output(f, var_info)?;
        write!(f, "(")?;
        match self.args.first() {
            Some(x) => x.fmt_output(f, var_info)?,
            None => {}
        }

        for x in self.args.iter().skip(1) {
            write!(f, ",")?;
            x.fmt_output(f, var_info)?;
        }

        write!(f, ")")
    }
}

impl fmt::Display for Func {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.fmt_output(f, &VarInfo::empty())
    }
}

impl Element {
    // replace a string name for a numerical ID
    pub fn var_to_id(&mut self, var_info: &mut VarInfo) {
        match *self {
            Element::Var(ref mut name) | Element::VariableArgument(ref mut name) => {
                var_info.replace_name(name);
            },
            Element::Wildcard(ref mut name, ref mut restrictions) => {
                var_info.replace_name(name);
                for x in restrictions {
                    x.var_to_id(var_info);
                }
            },
            Element::Pow(_, ref mut b, ref mut e) => {
                b.var_to_id(var_info);
                e.var_to_id(var_info);
            },
            Element::Term(_, ref mut f) | Element::SubExpr(_, ref mut f) => {
                for x in f {
                    x.var_to_id(var_info);
                }
            },
            Element::Fn(
                _,
                Func {
                    ref mut name,
                    ref mut args,
                },
            ) => {
                var_info.replace_name(name);
                for x in args {
                    x.var_to_id(var_info);
                }
            }
            _ => {}
        }
    }

    pub fn replace_var(&mut self, map: &HashMap<VarName, Element>) {
        *self = match *self {
            Element::Var(ref mut name) => {
                if let Some(x) = map.get(name) {
                    x.clone()
                } else {
                    return
                }
            },
            Element::Wildcard(ref mut name, ref mut restrictions) => {
                for x in restrictions {
                    x.replace_var(map);
                }
                return
            },
            Element::Pow(_, ref mut b, ref mut e) => {
                b.replace_var(map);
                e.replace_var(map);
                return
            }
            Element::Term(_, ref mut f) | Element::SubExpr(_, ref mut f) => {
            for x in f {
                x.replace_var(map);
                
            }
            return
            },
            Element::Fn(
                _,
                Func {
                    ref mut name,
                    ref mut args,
                },
            ) => {
                if let Some(x) = map.get(name) {
                    if let &Element::Var(ref y) = x {
                        *name = y.clone();
                    } else {
                        panic!("Cannot replace function name by generic expression");
                    }
                }

                for x in args {
                    x.replace_var(map);
                }
                return
            }
            _ => return
        }
    }
}

impl Statement {
    pub fn var_to_id(&mut self, var_info: &mut VarInfo) {
        match *self {
            Statement::IdentityStatement(IdentityStatement {
                mode: _,
                ref mut lhs,
                ref mut rhs,
            }) => {
                lhs.var_to_id(var_info);
                rhs.var_to_id(var_info);
            },
            Statement::Repeat(ref mut ss) => {
                for s in ss {
                    s.var_to_id(var_info);
                }
            },
            Statement::IfElse(ref mut e, ref mut ss, ref mut sse) => {
                e.var_to_id(var_info);
                for s in ss {
                    s.var_to_id(var_info);
                }
                for s in sse {
                    s.var_to_id(var_info);
                }
            },
            Statement::SplitArg(ref mut name) | Statement::Symmetrize(ref mut name) => {
                var_info.replace_name(name);
            },
            Statement::Multiply(ref mut e) => {
                e.var_to_id(var_info);
            },
            Statement::Call(_, ref mut es) => {
                for s in es {
                    s.var_to_id(var_info);
                }
            },
            _ => {}
        }
    }

    pub fn replace_var(&mut self, map: &HashMap<VarName, Element>) {
        match *self {
            Statement::IdentityStatement(IdentityStatement {
                mode: _,
                ref mut lhs,
                ref mut rhs,
            }) => {
                lhs.replace_var(map);
                rhs.replace_var(map);
            },
            Statement::Repeat(ref mut ss) => {
                for s in ss {
                    s.replace_var(map);
                }
            },
            Statement::IfElse(ref mut e, ref mut ss, ref mut sse) => {
                e.replace_var(map);
                for s in ss {
                    s.replace_var(map);
                }
                for s in sse {
                    s.replace_var(map);
                }
            },
            Statement::SplitArg(ref mut name) | Statement::Symmetrize(ref mut name) => {
                if let Some(x) = map.get(name) {
                    if let &Element::Var(ref y) = x {
                        *name = y.clone();
                    } else {
                        panic!("Cannot replace function name by generic expression");
                    }
                }
            }
            Statement::Multiply(ref mut e) => {
                e.replace_var(map);
            },
            Statement::Call(_, ref mut es) => {
                for s in es {
                    s.replace_var(map);
                }
            },
            _ => {}
        }
    }
}
