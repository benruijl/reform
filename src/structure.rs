use std::fmt;
use streaming::InputTermStreamer;
use std::collections::HashMap;
use std::cmp::Ordering;
use tools::num_cmp;

pub const BUILTIN_FUNCTIONS: &'static [&'static str] = &["delta_", "nargs_", "sum_", "mul_"];
pub const FUNCTION_DELTA: u32 = 0;
pub const FUNCTION_NARGS: u32 = 1;
pub const FUNCTION_SUM: u32 = 2;
pub const FUNCTION_MUL: u32 = 3;

pub type VarName = u32;

#[derive(Debug)]
pub struct Program {
    pub input: InputTermStreamer,
    pub modules: Vec<Module>,
    pub procedures: Vec<Procedure>,
    pub var_info: VarInfo,
}

// keeps track of global state
#[derive(Debug, Clone)]
pub struct VarInfo {
    inv_name_map: Vec<String>,
    name_map: HashMap<String, u32>,
    pub variables: HashMap<VarName, Element>, // local map of (dollar) variables
    pub global_variables: HashMap<VarName, Element>, // global map of (dollar) variables
}

impl VarInfo {
    pub fn empty() -> VarInfo {
        VarInfo {
            inv_name_map: vec![],
            name_map: HashMap::new(),
            variables: HashMap::new(),
            global_variables: HashMap::new(),
        }
    }

    pub fn new() -> VarInfo {
        let mut inv_name_map = vec![];
        let mut name_map = HashMap::new();

        // insert built-in functions
        let mut i: u32 = 0;
        for x in BUILTIN_FUNCTIONS {
            name_map.insert(x.to_string(), i);
            inv_name_map.push(x.to_string());
            i += 1;
        }
        VarInfo {
            inv_name_map,
            name_map,
            variables: HashMap::new(),
            global_variables: HashMap::new(),
        }
    }

    pub fn get_name(&mut self, s: &String) -> u32 {
        let nm = &mut self.name_map;
        let inv = &mut self.inv_name_map;
        *nm.entry(s.clone()).or_insert_with(|| {
            inv.push(s.clone());
            (inv.len() - 1) as u32
        })
    }

    pub fn add_local(&mut self, name: &VarName) -> VarName {
        let newvarid = self.inv_name_map.len() as u32;
        let newvarname = format!("{}_{}", name, newvarid);
        self.name_map.insert(newvarname.clone(), newvarid);
        self.inv_name_map.push(newvarname);
        newvarid
    }

    pub fn add_dollar(&mut self, name: VarName, value: Element) {
        self.variables.insert(name, value);
    }
}

impl Program {
    /// Create a new Program from the parser output.
    pub fn new(
        mut input: NamedElement,
        mut modules: Vec<NamedModule>,
        mut procedures: Vec<NamedProcedure>,
    ) -> Program {
        let mut prog = Program {
            input: InputTermStreamer::new(None),
            modules: vec![],
            procedures: vec![],
            var_info: VarInfo::new(),
        };

        // convert all the names to IDs

        let mut parsed_input = input.to_element(&mut prog.var_info);
        parsed_input.normalize_inplace();

        match parsed_input {
            Element::SubExpr(_, t) => for mut x in t {
                prog.input.add_term_input(x);
            },
            x => {
                prog.input.add_term_input(x);
            }
        }

        let mut parsed_modules = vec![];
        for m in &mut modules {
            parsed_modules.push(Module {
                name: m.name.clone(),
                statements: m.statements
                    .iter_mut()
                    .map(|s| s.to_statement(&mut prog.var_info))
                    .collect(),
                global_statements: m.global_statements
                    .iter_mut()
                    .map(|s| s.to_statement(&mut prog.var_info))
                    .collect(),
            });
        }

        // NOTE: the names of the arguments are not substituted
        let mut parsed_procedures = vec![];
        for m in &mut procedures {
            parsed_procedures.push(Procedure {
                name: m.name.clone(),
                args: m.args
                    .iter_mut()
                    .map(|s| s.to_element(&mut prog.var_info))
                    .collect(),
                local_args: m.local_args
                    .iter_mut()
                    .map(|s| s.to_element(&mut prog.var_info))
                    .collect(),
                statements: m.statements
                    .iter_mut()
                    .map(|s| s.to_statement(&mut prog.var_info))
                    .collect(),
            });
        }

        prog.modules = parsed_modules;
        prog.procedures = parsed_procedures;
        prog
    }
}

#[derive(Debug)]
pub struct NamedModule {
    pub name: String,
    pub statements: Vec<NamedStatement>,
    pub global_statements: Vec<NamedStatement>,
}

#[derive(Debug)]
pub struct NamedProcedure {
    pub name: String,
    pub args: Vec<NamedElement>,
    pub local_args: Vec<NamedElement>,
    pub statements: Vec<NamedStatement>,
}

#[derive(Debug)]
pub struct Module {
    pub name: String,
    pub statements: Vec<Statement>,
    pub global_statements: Vec<Statement>,
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

#[derive(Debug, Clone)]
pub enum NamedElement {
    VariableArgument(String),                     // ?a
    Wildcard(String, Vec<NamedElement>),          // x?{...}
    Dollar(String, Option<Box<NamedElement>>),    // $x[y]
    Var(String),                                  // x
    Pow(bool, Box<(NamedElement, NamedElement)>), // (1+x)^3; dirty, base, exponent
    NumberRange(bool, u64, u64, NumOrder),        // >0, <=-5/2
    Fn(bool, String, Vec<NamedElement>),          // f(...)
    Term(bool, Vec<NamedElement>),
    SubExpr(bool, Vec<NamedElement>),
    Num(bool, bool, u64, u64), // dirty, fraction (true=positive), make sure it is last for sorting
}

#[derive(Debug, Clone)]
pub enum NamedStatement {
    IdentityStatement(NamedIdentityStatement),
    SplitArg(String),
    Repeat(Vec<NamedStatement>),
    Argument(NamedElement, Vec<NamedStatement>),
    IfElse(NamedElement, Vec<NamedStatement>, Vec<NamedStatement>),
    Expand,
    Print,
    Multiply(NamedElement),
    Symmetrize(String),
    Collect(String),
    Assign(NamedElement, NamedElement),
    Maximum(NamedElement),
    Call(String, Vec<NamedElement>),
}

// all the algebraic elements. A bool as the first
// argument is the dirty flag, which is set to true
// if a normalization needs to happen
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Element {
    VariableArgument(VarName),             // ?a
    Wildcard(VarName, Vec<Element>),       // x?{...}
    Dollar(VarName, Option<Box<Element>>), // $x[y]
    Var(VarName),                          // x
    Pow(bool, Box<(Element, Element)>),    // (1+x)^3; dirty, base, exponent
    NumberRange(bool, u64, u64, NumOrder), // >0, <=-5/2
    Fn(bool, VarName, Vec<Element>),       // f(...)
    Term(bool, Vec<Element>),
    SubExpr(bool, Vec<Element>),
    Num(bool, bool, u64, u64), // dirty, fraction (true=positive), make sure it is last for sorting
}

impl Default for Element {
    fn default() -> Element {
        Element::Num(false, true, 1, 1)
    }
}

#[macro_export]
macro_rules! DUMMY_ELEM { () => (Element::Num(false, true, 1, 1)) }

#[derive(Debug, Clone, Eq, PartialEq, PartialOrd, Ord)]
pub enum Statement {
    IdentityStatement(IdentityStatement),
    SplitArg(VarName),
    Repeat(Vec<Statement>),
    Argument(Element, Vec<Statement>),
    IfElse(Element, Vec<Statement>, Vec<Statement>),
    Expand,
    Print,
    Multiply(Element),
    Symmetrize(VarName),
    Collect(VarName),
    Assign(Element, Element),
    Maximum(Element),
    Call(String, Vec<Element>),
    // internal commands
    Jump(usize),          // unconditional jump
    Eval(Element, usize), // evaluate and jump if eval is false
    JumpIfChanged(usize), // jump and pop change flag
    PushChange,           // push a new change flag
}
/*
impl PartialEq for Element {
     fn eq(&self, other: &Element) -> bool {
         match (self, other) {
             (&Element::Var(ref v), &Element::Var(ref v1)) => v == v1,
             (&Element::Fn(_, Func { ref name, ref args }), &Element::Fn(_, Func { ref name1, ref args1 }) => {
                 if name != name1 {
                     return false;
                 }
                 true
             },
             (&Element::Term(_, fs), &Element::Term(_, fs1)) => fs.cmp(fs1),
             (&Element::SubExpr(_, fs), &Element::SubExpr(_, fs1)) => fs.cmp(fs1),
             (&Num(_, pos, num, den), &Num(_, pos1, num1, den 1)) => ();
             _ => false//unreachable!("Unexpected elements in eq")
         }
        VariableArgument(VarName),             // ?a
    Wildcard(VarName, Vec<Element>),       // x?{...}
    Var(VarName),                          // x
    Pow(bool, Box<Element>, Box<Element>), // (1+x)^3
    NumberRange(bool, u64, u64, NumOrder), // >0, <=-5/2
    Fn(bool, Func),                        // f(...)
    Term(bool, Vec<Element>),
    SubExpr(bool, Vec<Element>),
    Num(bool, bool, u64, u64),  
     }
}*/

impl Ord for Element {
    fn cmp(&self, other: &Element) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

// implement a custom partial order that puts
// x and x*2 next to each other for term sorting
// and x and x^2 next to each other for
// coefficients are partially ignored and sorted at the back
impl PartialOrd for Element {
    fn partial_cmp(&self, other: &Element) -> Option<Ordering> {
        match (self, other) {
            (&Element::Fn(_, ref namea, ref argsa), &Element::Fn(_, ref nameb, ref argsb)) => {
                let k = namea.partial_cmp(nameb);
                match k {
                    Some(Ordering::Equal) => {}
                    _ => return k,
                }
                if argsa.len() != argsb.len() {
                    return argsa.len().partial_cmp(&argsb.len());
                }

                for (argsaa, argsbb) in argsa.iter().zip(argsb) {
                    let k = argsaa.partial_cmp(argsbb);
                    match k {
                        Some(Ordering::Equal) => {}
                        _ => return k,
                    }
                }
                Some(Ordering::Equal)
            }
            (&Element::Num(_, pos, num, den), &Element::Num(_, posa, numa, dena)) => {
                Some(match num_cmp(pos, num, den, posa, numa, dena) {
                    NumOrder::SmallerEqual | NumOrder::Smaller => Ordering::Less,
                    NumOrder::GreaterEqual | NumOrder::Greater => Ordering::Greater,
                    NumOrder::Equal => Ordering::Equal,
                })
            }
            (_, &Element::Num(..)) => Some(Ordering::Less),
            (&Element::Num(..), _) => Some(Ordering::Greater),
            (&Element::Pow(_, ref be1), &Element::Pow(_, ref be2)) => {
                let (ref b1, ref e1) = **be1;
                let (ref b2, ref e2) = **be2;
                let c = b1.partial_cmp(b2);
                match c {
                    Some(Ordering::Equal) => e1.partial_cmp(e2),
                    _ => c,
                }
            }
            (&Element::Pow(_, ref be), _) => {
                let (ref b, _) = **be;
                let c = b.partial_cmp(other);
                match c {
                    Some(Ordering::Equal) => Some(Ordering::Less),
                    _ => c,
                }
            }
            (_, &Element::Pow(_, ref be)) => {
                let (ref b, _) = **be;
                let c = self.partial_cmp(b);
                match c {
                    Some(Ordering::Equal) => Some(Ordering::Greater),
                    _ => c,
                }
            }
            (&Element::Term(_, ref ta), &Element::Term(_, ref tb)) => {
                let tamin = if let Some(&Element::Num(..)) = ta.last() {
                    ta.len() - 1
                } else {
                    ta.len()
                };
                let tbmin = if let Some(&Element::Num(..)) = tb.last() {
                    tb.len() - 1
                } else {
                    tb.len()
                };

                if tamin != tbmin {
                    return tamin.partial_cmp(&tbmin);
                }

                for (taa, tbb) in ta.iter().zip(tb) {
                    if let &Element::Num(..) = taa {
                        if let &Element::Num(..) = tbb {
                            //continue; // TODO: don't compare numbers on ground level
                        }
                    }

                    let k = taa.partial_cmp(tbb);
                    match k {
                        Some(Ordering::Equal) => {}
                        _ => return k,
                    }
                }
                Some(Ordering::Equal)
            }
            (_, &Element::Term(_, ref t)) => {
                if t.len() == 2 {
                    if let Element::Num(..) = t[1] {
                        return self.partial_cmp(&t[0]);
                    }
                }
                Some(Ordering::Less)
            }
            (&Element::Term(_, ref t), _) => {
                if t.len() == 2 {
                    if let Element::Num(..) = t[1] {
                        return t[0].partial_cmp(other);
                    }
                }
                Some(Ordering::Greater)
            }
            (&Element::Fn(..), _) => Some(Ordering::Less),
            (_, &Element::Fn(..)) => Some(Ordering::Greater),
            (&Element::SubExpr(_, ref ta), &Element::SubExpr(_, ref tb)) => {
                if ta.len() != tb.len() {
                    return ta.len().partial_cmp(&tb.len());
                }

                for (taa, tbb) in ta.iter().zip(tb) {
                    let k = taa.partial_cmp(tbb);
                    match k {
                        Some(Ordering::Equal) => {}
                        _ => return k,
                    }
                }
                Some(Ordering::Equal)
            }
            (&Element::SubExpr(..), _) => Some(Ordering::Less),
            (&Element::Var(ref a), &Element::Var(ref b)) => a.partial_cmp(b),
            _ => Some(Ordering::Less),
        }
    }
}

#[derive(Debug)]
pub enum StatementResult<T> {
    Executed(T),
    NotExecuted(T),
    NoChange,
    Done,
}

#[derive(Debug, Clone)]
pub struct NamedIdentityStatement {
    pub mode: IdentityStatementMode,
    pub lhs: NamedElement,
    pub rhs: NamedElement,
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
        for (i, x) in self.global_statements.iter().enumerate() {
            write!(f, "{}: {}", i, x)?;
        }
        writeln!(f, "{{")?;
        for (i, x) in self.statements.iter().enumerate() {
            write!(f, "{}: {}", i, x)?;
        }
        writeln!(f, "}}")
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
            Statement::Collect(ref x) => writeln!(f, "Collect {};", x),
            Statement::Repeat(ref ss) => if ss.len() == 1 {
                write!(f, "repeat {}", ss[0])
            } else {
                writeln!(f, "repeat;")?;

                for s in ss {
                    write!(f, "\t{}", s)?;
                }

                writeln!(f, "endrepeat;")
            },
            Statement::Argument(ref ff, ref ss) => {
                writeln!(f, "argument {};", ff)?;

                for s in ss {
                    write!(f, "\t{}", s)?;
                }

                writeln!(f, "endargument;")
            }
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
                write!(f, "call {}(", name)?;

                match args.first() {
                    Some(x) => write!(f, "{}", x)?,
                    None => {}
                }

                for x in args.iter().skip(1) {
                    write!(f, ",{}", x)?;
                }

                writeln!(f, ");")
            }
            Statement::Assign(ref d, ref e) => writeln!(f, "{}={};", d, e),
            Statement::Maximum(ref d) => writeln!(f, "Maximum {};", d),
            Statement::Jump(ref i) => writeln!(f, "JMP {}", i),
            Statement::Eval(ref n, ref i) => writeln!(f, "IF NOT {} JMP {}", n, i),
            Statement::JumpIfChanged(ref i) => writeln!(f, "JMP_CH {}", i),
            Statement::PushChange => writeln!(f, "PUSH_CH"),
        }
    }
}

fn fmt_varname(v: &VarName, f: &mut fmt::Formatter, var_info: &VarInfo) -> fmt::Result {
    if var_info.inv_name_map.len() == 0 {
        write!(f, "var_{}", v)
    } else {
        write!(f, "{}", var_info.inv_name_map[*v as usize])
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
    pub var_info: &'a VarInfo,
}

impl<'a> fmt::Display for ElementPrinter<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.element.fmt_output(f, self.var_info)
    }
}

impl Element {
    pub fn fmt_output(&self, f: &mut fmt::Formatter, var_info: &VarInfo) -> fmt::Result {
        match self {
            &Element::VariableArgument(ref name) => {
                write!(f, "?")?;
                fmt_varname(name, f, var_info)
            }
            &Element::Wildcard(ref name, ref restriction) => if restriction.len() == 0 {
                fmt_varname(name, f, var_info)?;
                write!(f, "?")
            } else {
                fmt_varname(name, f, var_info)?;
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
            &Element::Var(ref name) => fmt_varname(name, f, var_info),
            &Element::Dollar(ref name, ..) => {
                // TODO: print the index too
                fmt_varname(name, f, var_info)
            }
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
            &Element::Pow(_, ref be) => {
                let (ref b, ref e) = **be;
                match *b {
                    Element::SubExpr(..) | Element::Term(..) => {
                        write!(f, "(")?;
                        b.fmt_output(f, var_info)?;
                        write!(f, ")")?
                    }
                    _ => b.fmt_output(f, var_info)?,
                };
                match *e {
                    Element::SubExpr(..) | Element::Term(..) => {
                        write!(f, "^(")?;
                        e.fmt_output(f, var_info)?;
                        write!(f, ")")
                    }
                    _ => {
                        write!(f, "^")?;
                        e.fmt_output(f, var_info)
                    }
                }
            }
            &Element::Fn(_, ref name, ref args) => {
                fmt_varname(&name, f, var_info)?;
                write!(f, "(")?;
                match args.first() {
                    Some(x) => x.fmt_output(f, var_info)?,
                    None => {}
                }

                for x in args.iter().skip(1) {
                    write!(f, ",")?;
                    x.fmt_output(f, var_info)?;
                }

                write!(f, ")")
            }
            &Element::Term(_, ref factors) => {
                match factors.first() {
                    Some(s @ &Element::SubExpr(..)) if factors.len() > 1 => {
                        write!(f, "(")?;
                        s.fmt_output(f, var_info)?;
                        write!(f, ")")?
                    }
                    Some(x) => x.fmt_output(f, var_info)?,
                    None => {}
                }
                for t in factors.iter().skip(1) {
                    match t {
                        s @ &Element::SubExpr(..) => {
                            write!(f, "*(")?;
                            s.fmt_output(f, var_info)?;
                            write!(f, ")")?
                        }
                        _ => {
                            write!(f, "*")?;
                            t.fmt_output(f, var_info)?
                        }
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

impl NamedElement {
    // replace a string name for a numerical ID
    pub fn to_element(&mut self, var_info: &mut VarInfo) -> Element {
        match *self {
            NamedElement::NumberRange(s, n, d, ref c) => Element::NumberRange(s, n, d, c.clone()),
            NamedElement::Num(_, s, n, d) => Element::Num(true, s, n, d),
            NamedElement::Dollar(ref mut name, ref mut inds) => {
                Element::Dollar(var_info.get_name(name), {
                    match *inds {
                        Some(ref mut x) => Some(Box::new(x.to_element(var_info))),
                        None => None,
                    }
                })
            }
            NamedElement::Var(ref mut name) => Element::Var(var_info.get_name(name)),
            NamedElement::VariableArgument(ref mut name) => {
                Element::VariableArgument(var_info.get_name(name))
            }
            NamedElement::Wildcard(ref mut name, ref mut restrictions) => Element::Wildcard(
                var_info.get_name(name),
                restrictions
                    .iter_mut()
                    .map(|x| x.to_element(var_info))
                    .collect(),
            ),
            NamedElement::Pow(_, ref mut be) => {
                let (ref mut b, ref mut e) = *&mut **be;
                Element::Pow(
                    true,
                    Box::new((b.to_element(var_info), e.to_element(var_info))),
                )
            }
            NamedElement::Term(_, ref mut f) => {
                Element::Term(true, f.iter_mut().map(|x| x.to_element(var_info)).collect())
            }
            NamedElement::SubExpr(_, ref mut f) => {
                Element::SubExpr(true, f.iter_mut().map(|x| x.to_element(var_info)).collect())
            }
            NamedElement::Fn(_, ref mut name, ref mut args) => Element::Fn(
                true,
                var_info.get_name(name),
                args.iter_mut().map(|x| x.to_element(var_info)).collect(),
            ),
        }
    }
}

impl Element {
    pub fn replace_vars(&mut self, map: &HashMap<VarName, Element>, dollar_only: bool) -> bool {
        let mut changed = false;
        *self = match *self {
            Element::Var(ref mut name) => {
                if dollar_only {
                    return false;
                }
                if let Some(x) = map.get(name) {
                    x.clone()
                } else {
                    return false;
                }
            }
            Element::Dollar(ref mut name, ..) => {
                if let Some(x) = map.get(name) {
                    x.clone()
                } else {
                    return false;
                }
            }
            Element::Wildcard(_, ref mut restrictions) => {
                for x in restrictions {
                    changed |= x.replace_vars(map, dollar_only);
                }
                return changed;
            }
            Element::Pow(ref mut dirty, ref mut be) => {
                let (ref mut b, ref mut e) = *&mut **be;
                changed |= b.replace_vars(map, dollar_only);
                changed |= e.replace_vars(map, dollar_only);
                *dirty |= changed;
                return changed;
            }
            Element::Term(ref mut dirty, ref mut f)
            | Element::SubExpr(ref mut dirty, ref mut f) => {
                for x in f {
                    changed |= x.replace_vars(map, dollar_only);
                }
                *dirty |= changed;
                return changed;
            }
            Element::Fn(ref mut dirty, ref mut name, ref mut args) => {
                if !dollar_only {
                    if let Some(x) = map.get(name) {
                        if let &Element::Var(ref y) = x {
                            *name = y.clone();
                            changed = true
                        } else {
                            panic!("Cannot replace function name by generic expression");
                        }
                    }
                }

                for x in args {
                    changed |= x.replace_vars(map, dollar_only);
                }
                *dirty |= changed;
                return changed;
            }
            _ => return false,
        };
        true
    }

    // replace a (sub)element that appears literally by a new element
    pub fn replace(&mut self, orig: &Element, new: &Element) -> bool {
        if self == orig {
            *self = new.clone();
            return true;
        }

        match *self {
            Element::Pow(ref mut dirty, ref mut be) => {
                let (ref mut b, ref mut e) = *&mut **be;
                *dirty |= b.replace(orig, new);
                *dirty |= e.replace(orig, new);
                *dirty
            }
            Element::Term(ref mut dirty, ref mut f)
            | Element::SubExpr(ref mut dirty, ref mut f) => {
                for x in f {
                    *dirty |= x.replace(orig, new);
                }
                *dirty
            }
            Element::Fn(ref mut dirty, ref _name, ref mut args) => {
                for x in args {
                    *dirty |= x.replace(orig, new);
                }
                *dirty
            }
            _ => false,
        }
    }
}

impl NamedStatement {
    pub fn to_statement(&mut self, var_info: &mut VarInfo) -> Statement {
        match *self {
            NamedStatement::IdentityStatement(NamedIdentityStatement {
                ref mode,
                ref mut lhs,
                ref mut rhs,
            }) => Statement::IdentityStatement(IdentityStatement {
                mode: mode.clone(),
                lhs: lhs.to_element(var_info),
                rhs: rhs.to_element(var_info),
            }),
            NamedStatement::Repeat(ref mut ss) => {
                Statement::Repeat(ss.iter_mut().map(|s| s.to_statement(var_info)).collect())
            }
            NamedStatement::Argument(ref mut f, ref mut ss) => Statement::Argument(
                f.to_element(var_info),
                ss.iter_mut().map(|s| s.to_statement(var_info)).collect(),
            ),
            NamedStatement::IfElse(ref mut e, ref mut ss, ref mut sse) => Statement::IfElse(
                e.to_element(var_info),
                ss.iter_mut().map(|s| s.to_statement(var_info)).collect(),
                sse.iter_mut().map(|s| s.to_statement(var_info)).collect(),
            ),
            NamedStatement::SplitArg(ref name) => Statement::SplitArg(var_info.get_name(name)),
            NamedStatement::Symmetrize(ref name) => Statement::Symmetrize(var_info.get_name(name)),
            NamedStatement::Collect(ref name) => Statement::Collect(var_info.get_name(name)),
            NamedStatement::Multiply(ref mut e) => Statement::Multiply(e.to_element(var_info)),
            NamedStatement::Expand => Statement::Expand,
            NamedStatement::Print => Statement::Print,
            NamedStatement::Maximum(ref mut e) => Statement::Maximum(e.to_element(var_info)),
            NamedStatement::Call(ref name, ref mut es) => Statement::Call(
                name.clone(),
                es.iter_mut().map(|s| s.to_element(var_info)).collect(),
            ),
            NamedStatement::Assign(ref mut d, ref mut e) => {
                Statement::Assign(d.to_element(var_info), e.to_element(var_info))
            }
        }
    }
}

impl Statement {
    pub fn replace_vars(&mut self, map: &HashMap<VarName, Element>, dollar_only: bool) -> bool {
        let mut changed = false;
        match *self {
            Statement::IdentityStatement(IdentityStatement {
                mode: _,
                ref mut lhs,
                ref mut rhs,
            }) => {
                changed |= lhs.replace_vars(map, dollar_only);
                changed |= rhs.replace_vars(map, dollar_only);
            }
            Statement::Repeat(ref mut ss) => for s in ss {
                changed |= s.replace_vars(map, dollar_only);
            },
            Statement::IfElse(ref mut e, ref mut ss, ref mut sse) => {
                changed |= e.replace_vars(map, dollar_only);
                for s in ss {
                    changed |= s.replace_vars(map, dollar_only);
                }
                for s in sse {
                    changed |= s.replace_vars(map, dollar_only);
                }
            }
            Statement::SplitArg(ref mut name)
            | Statement::Symmetrize(ref mut name)
            | Statement::Collect(ref mut name) => {
                if let Some(x) = map.get(name) {
                    if let &Element::Var(ref y) = x {
                        *name = y.clone();
                    } else {
                        panic!("Cannot replace function name by generic expression");
                    }
                }
            }
            Statement::Multiply(ref mut e) => {
                changed |= e.replace_vars(map, dollar_only);
            }
            Statement::Call(_, ref mut es) => for s in es {
                changed |= s.replace_vars(map, dollar_only);
            },
            Statement::Assign(ref _d, ref mut e) => {
                // TODO: also change dollar variable?
                changed |= e.replace_vars(map, dollar_only);
            }
            _ => {}
        };
        changed
    }
}
