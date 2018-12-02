use chrono::prelude::*;
use num_traits::One;
use number::Number;
use poly::polynomial::PolyPrinter;
use poly::polynomial::Polynomial;
use std::cmp;
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::fmt;
use std::fmt::Write;
use std::mem;
use streaming::InputTermStreamer;

pub const BUILTIN_FUNCTIONS: &'static [&'static str] = &[
    "delta_", "nargs_", "sum_", "prod_", "rat_", "gcd_", "takearg_", "ifelse_", "term_", "list_",
    "time_", "date_",
];
pub const FUNCTION_DELTA: VarName = 0;
pub const FUNCTION_NARGS: VarName = 1;
pub const FUNCTION_SUM: VarName = 2;
pub const FUNCTION_PROD: VarName = 3;
pub const FUNCTION_RAT: VarName = 4;
pub const FUNCTION_GCD: VarName = 5;
pub const FUNCTION_TAKEARG: VarName = 6;
pub const FUNCTION_IFELSE: VarName = 7;
pub const FUNCTION_TERM: VarName = 8;
pub const FUNCTION_LIST: VarName = 9;
pub const FUNCTION_TIME: VarName = 10; // used for printing
pub const FUNCTION_DATE: VarName = 11; // used for printing

/// Trait for variable ID. Normally `VarName` or `String`.
pub trait Id: Ord + fmt::Debug {}
impl<T: Ord + fmt::Debug> Id for T {}

/// Internal ID numbers for variables.
pub type VarName = u32;
pub type Expression = (VarName, InputTermStreamer);

#[derive(Debug)]
pub struct Program {
    pub expressions: Vec<Expression>,
    pub statements: Vec<Statement>,
    pub procedures: Vec<Procedure>,
    pub var_info: VarInfo,
}

#[derive(Debug, Clone)]
pub enum PrintObject<ID: Id = VarName> {
    Literal(String),
    Variable(Element<ID>),
    Special(ID),
}

impl PrintObject<String> {
    fn to_element(&mut self, var_info: &mut VarInfo) -> PrintObject<VarName> {
        match self {
            PrintObject::Literal(x) => PrintObject::Literal(mem::replace(x, String::new())),
            PrintObject::Variable(id) => PrintObject::Variable(id.to_element(var_info)),
            PrintObject::Special(id) => PrintObject::Special(var_info.get_name(id)),
        }
    }
}

impl PrintObject<VarName> {
    fn print_direct(&self) -> String {
        match self {
            PrintObject::Literal(x) => x.clone(),
            PrintObject::Variable(_) => "{var}".to_owned(),
            PrintObject::Special(_) => "{special_}".to_owned(),
        }
    }

    pub fn print(
        &self,
        accum: &mut String,
        element: &Element,
        local_var_info: &mut LocalVarInfo,
        global_var_info: &GlobalVarInfo,
        print_mode: &PrintMode,
    ) {
        match self {
            PrintObject::Literal(x) => write!(accum, "{}", x.clone()).unwrap(),
            PrintObject::Variable(id) => {
                if let Some(x) = local_var_info.get_dollar(id) {
                    write!(
                        accum,
                        "{}",
                        ElementPrinter {
                            element: x,
                            var_info: global_var_info,
                            print_mode: *print_mode
                        }
                    )
                    .unwrap();
                } else {
                    panic!("Unknown dollar variable in print statement: {}", id);
                }
            }
            PrintObject::Special(id) => match *id {
                FUNCTION_DATE => {
                    write!(accum, "{}", Local::now().format("%Y-%m-%d %H:%M:%S%.3f")).unwrap()
                }
                FUNCTION_TIME => write!(accum, "{}", Local::now().format("%H:%M:%S%.3f")).unwrap(),
                FUNCTION_TERM => write!(
                    accum,
                    "{}",
                    ElementPrinter {
                        element,
                        var_info: global_var_info,
                        print_mode: *print_mode
                    }
                )
                .unwrap(),
                _ => unimplemented!("Expressions in format strings are not supported yet."),
            },
        }
    }
}

#[derive(Debug, Clone)]
pub enum IfCondition<ID: Id = VarName> {
    Match(Element<ID>),                             // if match(x?^2)
    Defined(Element<ID>),                           // if defined($a)
    Comparison(Element<ID>, Element<ID>, Ordering), // if x*y == x*y
}

impl IfCondition<String> {
    fn to_element(&mut self, var_info: &mut VarInfo) -> IfCondition {
        match self {
            IfCondition::Match(e) => IfCondition::Match(e.to_element(var_info)),
            IfCondition::Defined(e) => IfCondition::Defined(e.to_element(var_info)),
            IfCondition::Comparison(e1, e2, c) => {
                IfCondition::Comparison(e1.to_element(var_info), e2.to_element(var_info), c.clone())
            }
        }
    }
}

impl fmt::Display for IfCondition {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            IfCondition::Match(e) => write!(f, "match({})", e),
            IfCondition::Defined(e) => write!(f, "defined({})", e),
            IfCondition::Comparison(e1, e2, c) => write!(f, "{} {} {}", e1, c, e2),
        }
    }
}

impl IfCondition {
    pub fn contains_dollar(&self) -> bool {
        match self {
            IfCondition::Match(e) => e.contains_dollar(),
            IfCondition::Defined(_) => false,
            IfCondition::Comparison(e1, e2, _) => e1.contains_dollar() || e2.contains_dollar(),
        }
    }

    pub fn replace_dollar(&mut self, map: &HashMap<VarName, DollarVariableTable>) -> ReplaceResult {
        match self {
            IfCondition::Match(e) => e.replace_dollar(map),
            IfCondition::Defined(_) => ReplaceResult::empty(),
            IfCondition::Comparison(e1, e2, _) => e1.replace_dollar(map) | e2.replace_dollar(map),
        }
    }

    pub fn replace_elements(&mut self, map: &HashMap<VarName, Element>) -> bool {
        match self {
            IfCondition::Match(e) => e.replace_elements(map),
            IfCondition::Defined(_) => false,
            IfCondition::Comparison(e1, e2, _) => {
                e1.replace_elements(map) || e2.replace_elements(map)
            }
        }
    }

    pub fn normalize_inplace(&mut self, var_info: &GlobalVarInfo) {
        match self {
            IfCondition::Match(e) | IfCondition::Defined(e) => {
                e.normalize_inplace(var_info);
            }
            IfCondition::Comparison(e1, e2, _) => {
                e1.normalize_inplace(var_info);
                e2.normalize_inplace(var_info);
            }
        }
    }

    pub fn fmt_output(
        &self,
        f: &mut fmt::Formatter,
        print_mode: PrintMode,
        var_info: &GlobalVarInfo,
    ) -> fmt::Result {
        match self {
            IfCondition::Match(e) => {
                write!(f, "match(")?;
                e.fmt_output(f, print_mode, var_info)?;
                write!(f, ")")
            }
            IfCondition::Defined(e) => {
                write!(f, "defined(")?;
                e.fmt_output(f, print_mode, var_info)?;
                write!(f, ")")
            }
            IfCondition::Comparison(e1, e2, c) => {
                e1.fmt_output(f, print_mode, var_info)?;
                write!(f, " {} ", c)?;
                e2.fmt_output(f, print_mode, var_info)
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum FunctionAttributes {
    NonCommutative,
    Symmetric,
    Linear,
    NonLocal, // used for persistent dollar variables
}

impl fmt::Display for FunctionAttributes {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            FunctionAttributes::NonCommutative => write!(f, "NonCommutative"),
            FunctionAttributes::Symmetric => write!(f, "Symmetric"),
            FunctionAttributes::Linear => write!(f, "Linear"),
            FunctionAttributes::NonLocal => write!(f, "NonLocal"),
        }
    }
}

/// Keeps track of global state that is immutable during execution.
#[derive(Debug, Clone)]
pub struct GlobalVarInfo {
    inv_name_map: Vec<String>,
    name_map: HashMap<String, VarName>,
    pub func_attribs: HashMap<VarName, Vec<FunctionAttributes>>,
    pub user_functions: HashMap<VarName, (Vec<VarName>, Element)>,
    pub log_level: usize,
}

impl GlobalVarInfo {
    pub fn empty() -> GlobalVarInfo {
        GlobalVarInfo {
            inv_name_map: vec![],
            name_map: HashMap::new(),
            func_attribs: HashMap::new(),
            user_functions: HashMap::new(),
            log_level: 0,
        }
    }

    pub fn num_vars(&self) -> usize {
        self.name_map.len()
    }

    pub fn get_name(&self, var: VarName) -> &str {
        &self.inv_name_map[var as usize]
    }
}

type DollarVariableTable = HashMap<Vec<Element>, Element>;

/// Keep track of local state, such as the values for dollar variables.
#[derive(Debug, Clone)]
pub struct LocalVarInfo {
    pub variables: HashMap<VarName, DollarVariableTable>, // local map of (dollar) variables
    pub global_variables: HashMap<VarName, Element>,      // global map of (dollar) variables
}

impl LocalVarInfo {
    pub fn add_dollar(&mut self, dollar: Element, value: Element) {
        if let Element::Dollar(name, inds) = dollar {
            match self.variables.entry(name) {
                Entry::Occupied(mut a) => {
                    a.get_mut().insert(inds, value);
                }
                Entry::Vacant(mut a) => {
                    a.insert({
                        let mut hm = HashMap::new();
                        hm.insert(inds, value);
                        hm
                    });
                }
            };
        } else {
            panic!("Not a dollar variable");
        }
    }

    pub fn get_dollar_class(&mut self, dollar: &Element) -> Option<&mut DollarVariableTable> {
        if let Element::Dollar(ref name, _) = dollar {
            self.variables.get_mut(name)
        } else {
            panic!("Not a dollar variable");
        }
    }

    pub fn get_dollar(&self, dollar: &Element) -> Option<&Element> {
        if let Element::Dollar(ref name, ref inds) = dollar {
            self.variables.get(name).and_then(|x| x.get(inds))
        } else {
            panic!("{} is not a dollar variable", dollar);
        }
    }

    pub fn get_dollar_mut(&mut self, dollar: &Element) -> Option<&mut Element> {
        if let Element::Dollar(ref name, ref inds) = dollar {
            self.variables.get_mut(name).and_then(|x| x.get_mut(inds))
        } else {
            panic!("Not a dollar variable");
        }
    }

    pub fn get_dollar_from_name(&mut self, name: u32) -> Option<&mut Element> {
        self.variables
            .get_mut(&name)
            .and_then(|x| x.get_mut(&vec![]))
    }
}

#[derive(Debug, Clone)]
pub struct BorrowedVarInfo<'a> {
    pub global_info: &'a GlobalVarInfo,
    pub local_info: &'a LocalVarInfo,
}

/// Keep track of local state. This includes the global state as well
/// as the values for dollar variables.
#[derive(Debug, Clone)]
pub struct VarInfo {
    pub global_info: GlobalVarInfo,
    pub local_info: LocalVarInfo,
}

impl VarInfo {
    pub fn new() -> VarInfo {
        let mut inv_name_map = vec![];
        let mut name_map = HashMap::new();

        // insert built-in functions
        let mut i: VarName = 0;
        for x in BUILTIN_FUNCTIONS {
            name_map.insert(x.to_string(), i);
            inv_name_map.push(x.to_string());
            i += 1;
        }
        VarInfo {
            global_info: GlobalVarInfo {
                inv_name_map,
                name_map,
                func_attribs: HashMap::new(),
                user_functions: HashMap::new(),
                log_level: 0,
            },
            local_info: LocalVarInfo {
                variables: HashMap::new(),
                global_variables: HashMap::new(),
            },
        }
    }

    pub fn get_str_name(&mut self, s: &VarName) -> String {
        self.global_info.inv_name_map[s.clone() as usize].clone()
    }

    pub fn get_name(&mut self, s: &str) -> u32 {
        let nm = &mut self.global_info.name_map;
        let inv = &mut self.global_info.inv_name_map;
        *nm.entry(s.to_string()).or_insert_with(|| {
            inv.push(s.to_string());
            (inv.len() - 1) as VarName
        })
    }

    pub fn add_local(&mut self, name: &VarName) -> VarName {
        let newvarid = self.global_info.inv_name_map.len() as u32;
        let newvarname = format!("{}_{}", name, newvarid);
        self.global_info
            .name_map
            .insert(newvarname.clone(), newvarid);
        self.global_info.inv_name_map.push(newvarname);
        newvarid
    }
}

impl Program {
    /// Create a new Program from the parser output.
    pub fn new(
        mut statements: Vec<Statement<String>>,
        mut procedures: Vec<Procedure<String>>,
    ) -> Program {
        let mut prog = Program {
            expressions: vec![],
            statements: vec![],
            procedures: vec![],
            var_info: VarInfo::new(),
        };

        // convert all the names to IDs
        /*
                let mut parsed_input = input.to_element(&mut prog.var_info);
                parsed_input.normalize_inplace(&prog.var_info.global_info);

                match parsed_input {
                    Element::SubExpr(_, t) => for mut x in t {
                        prog.input.add_term_input(x);
                    },
                    x => {
                        prog.input.add_term_input(x);
                    }
                }
        */

        let parsed_statements = statements
            .iter_mut()
            .map(|s| s.to_statement(&mut prog.var_info))
            .collect();

        // NOTE: the names of the arguments are not substituted
        let mut parsed_procedures = vec![];
        for m in &mut procedures {
            parsed_procedures.push(Procedure {
                name: m.name.clone(),
                args: m
                    .args
                    .iter_mut()
                    .map(|s| {
                        let mut ns = s.to_element(&mut prog.var_info);
                        ns.normalize_inplace(&prog.var_info.global_info);
                        ns
                    })
                    .collect(),
                local_args: m
                    .local_args
                    .iter_mut()
                    .map(|s| {
                        let mut ns = s.to_element(&mut prog.var_info);
                        ns.normalize_inplace(&prog.var_info.global_info);
                        ns
                    })
                    .collect(),
                statements: m
                    .statements
                    .iter_mut()
                    .map(|s| s.to_statement(&mut prog.var_info))
                    .collect(),
            });
        }

        prog.statements = parsed_statements;
        prog.procedures = parsed_procedures;
        prog
    }

    /// Returns the string representation for the specified expression.
    #[cfg(test)]
    pub fn get_result(&mut self, name: &str) -> String {
        let exprname = self.var_info.get_name(name);
        for &mut (name1, ref mut input) in &mut self.expressions {
            if name1 == exprname {
                // NOTE: This code consumes the contents in the input stream.
                let mut terms = Vec::new();
                while let Some(x) = input.read_term() {
                    terms.push(x);
                }
                if terms.is_empty() {
                    return "0".to_string();
                } else {
                    let terms = if terms.len() == 1 {
                        terms.pop().unwrap()
                    } else {
                        Element::SubExpr(true, terms)
                    };
                    let printer = ElementPrinter {
                        element: &terms,
                        var_info: &self.var_info.global_info,
                        print_mode: PrintMode::Form,
                    };
                    return printer.to_string();
                }
            }
            break;
        }
        unreachable!("Could not find expression {}", name);
    }
}

#[derive(Debug, Clone)]
pub struct Module<ID: Id = VarName> {
    pub name: String,
    pub active_exprs: Vec<ID>,
    pub exclude_exprs: Vec<ID>,
    pub statements: Vec<Statement<ID>>,
}

#[derive(Debug)]
pub struct Procedure<ID: Id = VarName> {
    pub name: String,
    pub args: Vec<Element<ID>>,
    pub local_args: Vec<Element<ID>>,
    pub statements: Vec<Statement<ID>>,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Ordering {
    Greater,
    Smaller,
    Equal,
    GreaterEqual,
    SmallerEqual,
}

impl Ordering {
    pub fn cmp_rel(&self, rel: cmp::Ordering) -> bool {
        match (self, rel) {
            (Ordering::Greater, cmp::Ordering::Greater)
            | (Ordering::GreaterEqual, cmp::Ordering::Greater)
            | (Ordering::GreaterEqual, cmp::Ordering::Equal)
            | (Ordering::Smaller, cmp::Ordering::Less)
            | (Ordering::SmallerEqual, cmp::Ordering::Less)
            | (Ordering::SmallerEqual, cmp::Ordering::Equal)
            | (Ordering::Equal, cmp::Ordering::Equal) => true,
            _ => false,
        }
    }
}

bitflags! {
    pub struct ReplaceResult: u8 {
        const Replaced = 1; // variable substituted
        const Partially_Updated = 2; // dollar variable index was updated
        const NotReplaced = 4; // variable could not be substituted
    }
}

// all the algebraic elements. A bool as the first
// argument is the dirty flag, which is set to true
// if a normalization needs to happen
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Element<ID: Id = VarName> {
    VariableArgument(ID),                                        // ?a
    Wildcard(ID, Vec<Element<ID>>),                              // x?{...}
    FnWildcard(ID, Box<(Vec<Element<ID>>, Vec<Element<ID>>)>),   // f?{...}(...)
    Dollar(ID, Vec<Element<ID>>),                                // $x[y]
    Var(ID, Number),                                             // x^n
    Pow(bool, Box<(Element<ID>, Element<ID>)>),                  // (1+x)^3; dirty, base, exponent
    NumberRange(Number, Ordering),                               // >0, <=-5/2
    Comparison(bool, Box<(Element<ID>, Element<ID>)>, Ordering), // x < y, x >= y, $a == 2
    Fn(bool, ID, Vec<Element<ID>>),                              // f(...)
    Term(bool, Vec<Element<ID>>),
    SubExpr(bool, Vec<Element<ID>>),
    Num(bool, Number),
    RationalPolynomialCoefficient(bool, Box<(Polynomial, Polynomial)>),
}

impl<ID: Id> Default for Element<ID> {
    #[inline]
    fn default() -> Element<ID> {
        Element::Num(false, Number::one())
    }
}

#[derive(Debug, Clone)]
pub enum Statement<ID: Id = VarName> {
    Module(Module<ID>),
    NewExpression(ID, Element<ID>),
    NewFunction(ID, Vec<ID>, Element<ID>),
    IdentityStatement(IdentityStatement<ID>),
    SplitArg(ID),
    Repeat(Vec<Statement<ID>>),
    Argument(Vec<Element<ID>>, Vec<Statement<ID>>),
    Inside(Vec<Element<ID>>, Vec<Statement<ID>>),
    IfElse(IfCondition<ID>, Vec<Statement<ID>>, Vec<Statement<ID>>),
    ForIn(Element<ID>, Vec<Element<ID>>, Vec<Statement<ID>>),
    ForInRange(Element<ID>, Element<ID>, Element<ID>, Vec<Statement<ID>>),
    Expand,
    Print(PrintMode, Vec<PrintObject<ID>>),
    Multiply(Element<ID>),
    ReplaceBy(Element<ID>),
    Symmetrize(ID),
    Collect(ID),
    Extract(Element<ID>, Vec<ID>),
    MatchAssign(Element<ID>, Vec<Statement<ID>>),
    Assign(Element<ID>, Element<ID>),
    Maximum(Element<ID>),
    Call(String, Vec<Element<ID>>),
    Attrib(Element<ID>, Vec<FunctionAttributes>),
    Discard,
    // internal commands
    Jump(usize),              // unconditional jump
    Eval(IfCondition, usize), // evaluate and jump if eval is false
    JumpIfChanged(usize),     // jump and pop change flag
    PushChange,               // push a new change flag
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
    NumberRange(bool, u64, u64, Ordering), // >0, <=-5/2
    Fn(bool, Func),                        // f(...)
    Term(bool, Vec<Element>),
    SubExpr(bool, Vec<Element>),
    Num(bool, bool, u64, u64),
     }
}*/

//impl<ID: Id> Ord for Element<ID> {
//    fn cmp(&self, other: &Element<ID>) -> Ordering {
//        self.partial_cmp(other).unwrap()
//    }
//}

impl Element {
    /// Perform some quick comparison checks between certain `Element` variants.
    #[inline]
    fn simple_partial_cmp(
        &self,
        other: &Element,
        _var_info: &GlobalVarInfo,
        ground_level: bool,
    ) -> Option<cmp::Ordering> {
        match (self, other) {
            (&Element::Var(ref a, ref e1), &Element::Var(ref b, ref e2)) => {
                match a.partial_cmp(b) {
                    Some(cmp::Ordering::Equal) => {
                        if let Number::SmallInt(ref b1) = e1 {
                            if let Number::SmallInt(ref b2) = e2 {
                                return b1.partial_cmp(b2);
                            };
                        };
                        e1.partial_cmp(e2)
                    }
                    x => x,
                }
            }
            (Element::Var(..), &Element::Num(..)) => Some(cmp::Ordering::Less),
            (Element::Num(..), &Element::Var(..)) => Some(cmp::Ordering::Greater),
            (&Element::Num(_, ref n1), &Element::Num(_, ref n2)) => {
                if ground_level {
                    Some(cmp::Ordering::Equal)
                } else {
                    n1.partial_cmp(n2)
                }
            }
            (&Element::RationalPolynomialCoefficient(..), &Element::Num(..)) => {
                if ground_level {
                    Some(cmp::Ordering::Equal)
                } else {
                    Some(cmp::Ordering::Less)
                }
            }
            (&Element::Num(..), &Element::RationalPolynomialCoefficient(..)) => {
                if ground_level {
                    Some(cmp::Ordering::Equal)
                } else {
                    Some(cmp::Ordering::Less)
                }
            }
            (_, &Element::Num(..)) => Some(cmp::Ordering::Less),
            (&Element::Num(..), _) => Some(cmp::Ordering::Greater),
            //(&Element::SubExpr(..), &Element::SubExpr(..)) => None,
            //(&Element::Term(..), &Element::Term(..)) => None,
            /*(&Element::Fn(_, ref namea, _), &Element::Fn(_, ref nameb, _)) => {
                let k = namea.partial_cmp(nameb);
                match k {
                    Some(cmp::Ordering::Equal) => {}
                    _ => return k,
                }

                // for non-commutative functions, we keep the order
                if let Some(attribs) = var_info.func_attribs.get(namea) {
                    if attribs.contains(&FunctionAttributes::NonCommutative) {
                        return Some(cmp::Ordering::Greater);
                    }
                }
                None
            }*/
            /*(&Element::Fn(..), _) => Some(cmp::Ordering::Less),
            (_, &Element::Fn(..)) => Some(cmp::Ordering::Greater),
            (_, &Element::Term(..)) => None,
            (&Element::Term(..), _) => None,
            (&Element::SubExpr(..), _) => Some(cmp::Ordering::Less),*/
            _ => None,
        }
    }

    /// A custom partial order that is used to normalize a term.
    /// TODO: check consistency with partial_cmp!
    pub fn partial_cmp_factor(
        &self,
        other: &Element,
        var_info: &GlobalVarInfo,
    ) -> Option<cmp::Ordering> {
        match (self, other) {
            (&Element::Var(ref a, _), &Element::Var(ref b, _)) => a.partial_cmp(b),
            (&Element::Num(..), &Element::Num(..)) => Some(cmp::Ordering::Equal),
            (&Element::RationalPolynomialCoefficient(..), &Element::Num(..)) => {
                Some(cmp::Ordering::Equal)
            }
            (&Element::Num(..), &Element::RationalPolynomialCoefficient(..)) => {
                Some(cmp::Ordering::Equal)
            }
            (_, &Element::Num(..)) => Some(cmp::Ordering::Less),
            (&Element::Num(..), _) => Some(cmp::Ordering::Greater),
            (&Element::Fn(_, ref namea, ref argsa), &Element::Fn(_, ref nameb, ref argsb)) => {
                let k = namea.partial_cmp(nameb);
                match k {
                    Some(cmp::Ordering::Equal) => {}
                    _ => return k,
                }

                // for non-commutative functions, we keep the order
                if let Some(attribs) = var_info.func_attribs.get(namea) {
                    if attribs.contains(&FunctionAttributes::NonCommutative) {
                        return Some(cmp::Ordering::Greater);
                    }
                }

                if argsa.len() != argsb.len() {
                    return argsa.len().partial_cmp(&argsb.len());
                }

                for (argsaa, argsbb) in argsa.iter().zip(argsb) {
                    let k = argsaa
                        .simple_partial_cmp(argsbb, var_info, false)
                        .or_else(|| argsaa.partial_cmp(argsbb, var_info, false));
                    match k {
                        Some(cmp::Ordering::Equal) => {}
                        _ => return k,
                    }
                }
                Some(cmp::Ordering::Equal)
            }
            (
                &Element::RationalPolynomialCoefficient(..),
                &Element::RationalPolynomialCoefficient(..),
            ) => Some(cmp::Ordering::Equal),
            (_, &Element::RationalPolynomialCoefficient(..)) => Some(cmp::Ordering::Less),
            (&Element::RationalPolynomialCoefficient(..), _) => Some(cmp::Ordering::Greater),
            (&Element::Pow(_, ref be1), &Element::Pow(_, ref be2)) => {
                be1.0.partial_cmp(&be2.0, var_info, false)
            }
            (&Element::Pow(..), _) => Some(cmp::Ordering::Less),
            (_, &Element::Pow(..)) => Some(cmp::Ordering::Greater),
            (&Element::Fn(..), _) => Some(cmp::Ordering::Less),
            (_, &Element::Fn(..)) => Some(cmp::Ordering::Greater),
            (&Element::SubExpr(_, ref ta), &Element::SubExpr(_, ref tb)) => {
                if ta.len() != tb.len() {
                    return ta.len().partial_cmp(&tb.len());
                }

                for (taa, tbb) in ta.iter().zip(tb) {
                    let k = taa
                        .simple_partial_cmp(tbb, var_info, false)
                        .or_else(|| taa.partial_cmp(tbb, var_info, false));
                    match k {
                        Some(cmp::Ordering::Equal) => {}
                        _ => return k,
                    }
                }
                Some(cmp::Ordering::Equal)
            }
            (&Element::SubExpr(..), _) => Some(cmp::Ordering::Less),
            _ => Some(cmp::Ordering::Less),
        }
    }

    #[inline(always)]
    pub fn partial_cmp(
        &self,
        other: &Element,
        var_info: &GlobalVarInfo,
        ground_level: bool,
    ) -> Option<cmp::Ordering> {
        // try an inline partial comparsion first
        if let Element::Term(_, ref ta) = self {
            if let Element::Term(_, ref tb) = other {
                let mut tbi = tb.iter();
                for taa in ta.iter() {
                    if let Some(tbb) = tbi.next() {
                        let k = taa
                            .simple_partial_cmp(tbb, var_info, ground_level)
                            .or_else(|| taa.partial_cmp_full(tbb, var_info, ground_level));

                        match k {
                            Some(cmp::Ordering::Equal) => {}
                            _ => return k,
                        }
                    } else {
                        if ground_level {
                            match taa {
                                Element::Num(..) | Element::RationalPolynomialCoefficient(..) => {
                                    return Some(cmp::Ordering::Equal);
                                }
                                _ => {}
                            }
                        }
                        return Some(cmp::Ordering::Greater);
                    };
                }
                if let Some(tbb) = tbi.next() {
                    if ground_level {
                        match tbb {
                            Element::Num(..) | Element::RationalPolynomialCoefficient(..) => {
                                return Some(cmp::Ordering::Equal);
                            }
                            _ => {}
                        }
                    }
                    return Some(cmp::Ordering::Less);
                };
                return Some(cmp::Ordering::Equal);
            }
        }

        self.partial_cmp_full(other, var_info, ground_level)
    }

    /// A custom partial order that ignores coefficients for
    /// the ground level, i.e., x and x*2 are considered equal.
    pub fn partial_cmp_full(
        &self,
        other: &Element,
        var_info: &GlobalVarInfo,
        ground_level: bool,
    ) -> Option<cmp::Ordering> {
        match (self, other) {
            (&Element::Var(ref a, ref e1), &Element::Var(ref b, ref e2)) => {
                match a.partial_cmp(b) {
                    Some(cmp::Ordering::Equal) => e1.partial_cmp(e2),
                    x => x,
                }
            }
            (&Element::Term(_, ref ta), &Element::Term(_, ref tb)) => {
                //
                // The next code is a bit simpler for the compiler and makes
                // the benchmark gcd almost 3% faster than the code that
                // follows and is commented out. It seems that the compiler
                // cannot optimize the main match in the loop very well.
                // Possibly the packing into an Option and then unpacking may
                // not be optimal? The for loop avoids this for one iterator.
                //
                let mut tbi = tb.iter();
                for taa in ta.iter() {
                    if let Some(tbb) = tbi.next() {
                        let k = taa
                            .simple_partial_cmp(tbb, var_info, ground_level)
                            .or_else(|| taa.partial_cmp(tbb, var_info, ground_level));

                        match k {
                            Some(cmp::Ordering::Equal) => {}
                            _ => return k,
                        }
                    } else {
                        if ground_level {
                            match taa {
                                Element::Num(..) | Element::RationalPolynomialCoefficient(..) => {
                                    return Some(cmp::Ordering::Equal);
                                }
                                _ => {}
                            }
                        }
                        return Some(cmp::Ordering::Greater);
                    };
                }
                if let Some(tbb) = tbi.next() {
                    if ground_level {
                        match tbb {
                            Element::Num(..) | Element::RationalPolynomialCoefficient(..) => {
                                return Some(cmp::Ordering::Equal);
                            }
                            _ => {}
                        }
                    }
                    return Some(cmp::Ordering::Less);
                };
                return Some(cmp::Ordering::Equal);
                /*
                                let mut tai = ta.iter();
                                let mut tbi = tb.iter();

                                loop {
                                    match (tai.next(), tbi.next()) {
                                        (Some(taa), Some(tbb)) => {
                                            // since we keep ground_level the check of the coeff will yield equal
                                            let k = taa
                                                .simple_partial_cmp(tbb, var_info, ground_level)
                                                .or_else(|| taa.partial_cmp(tbb, var_info, ground_level));

                                            match k {
                                                Some(cmp::Ordering::Equal) => {}
                                                _ => return k,
                                            }
                                        }
                                        (Some(taa), None) => {
                                            if ground_level {
                                                match taa {
                                                    Element::Num(..)
                                                    | Element::RationalPolynomialCoefficient(..) => {
                                                        return Some(cmp::Ordering::Equal);
                                                    }
                                                    _ => {}
                                                }
                                            }
                                            return Some(cmp::Ordering::Greater);
                                        }
                                        (None, Some(tbb)) => {
                                            if ground_level {
                                                match tbb {
                                                    Element::Num(..)
                                                    | Element::RationalPolynomialCoefficient(..) => {
                                                        return Some(cmp::Ordering::Equal);
                                                    }
                                                    _ => {}
                                                }
                                            }
                                            return Some(cmp::Ordering::Less);
                                        }
                                        (None, None) => return Some(cmp::Ordering::Equal),
                                    }
                                }
                */
            }
            (&Element::Num(_, ref n1), &Element::Num(_, ref n2)) => {
                if ground_level {
                    Some(cmp::Ordering::Equal)
                } else {
                    n1.partial_cmp(n2)
                }
            }
            (_, &Element::Term(_, ref t)) => match self
                .simple_partial_cmp(&t[0], var_info, false)
                .or_else(|| self.partial_cmp(&t[0], var_info, false))
            {
                Some(cmp::Ordering::Equal) => {
                    if t.len() == 2 {
                        match t[1] {
                            Element::Num(..) | Element::RationalPolynomialCoefficient(..) => {
                                Some(cmp::Ordering::Equal)
                            }
                            _ => Some(cmp::Ordering::Less),
                        }
                    } else {
                        Some(cmp::Ordering::Less)
                    }
                }
                x => x,
            },
            (&Element::Term(_, ref t), _) => match t[0]
                .simple_partial_cmp(other, var_info, false)
                .or_else(|| t[0].partial_cmp(other, var_info, false))
            {
                Some(cmp::Ordering::Equal) => {
                    if t.len() == 2 {
                        match t[1] {
                            Element::Num(..) | Element::RationalPolynomialCoefficient(..) => {
                                Some(cmp::Ordering::Equal)
                            }
                            _ => Some(cmp::Ordering::Greater),
                        }
                    } else {
                        Some(cmp::Ordering::Greater)
                    }
                }
                x => x,
            },
            (&Element::RationalPolynomialCoefficient(..), &Element::Num(..)) => {
                if ground_level {
                    Some(cmp::Ordering::Equal)
                } else {
                    Some(cmp::Ordering::Less)
                }
            }
            (&Element::Num(..), &Element::RationalPolynomialCoefficient(..)) => {
                if ground_level {
                    Some(cmp::Ordering::Equal)
                } else {
                    Some(cmp::Ordering::Less)
                }
            }
            (&Element::Fn(_, ref namea, ref argsa), &Element::Fn(_, ref nameb, ref argsb)) => {
                let k = namea.partial_cmp(nameb);
                match k {
                    Some(cmp::Ordering::Equal) => {}
                    _ => return k,
                }

                if argsa.len() != argsb.len() {
                    return argsa.len().partial_cmp(&argsb.len());
                }

                for (argsaa, argsbb) in argsa.iter().zip(argsb) {
                    let k = argsaa
                        .simple_partial_cmp(argsbb, var_info, false)
                        .or_else(|| argsaa.partial_cmp(argsbb, var_info, false));
                    match k {
                        Some(cmp::Ordering::Equal) => {}
                        _ => return k,
                    }
                }
                Some(cmp::Ordering::Equal)
            }
            (_, &Element::Num(..)) => Some(cmp::Ordering::Less),
            (&Element::Num(..), _) => Some(cmp::Ordering::Greater),
            // TODO: if we allow polyratfuns in functions, we should add a partial_cmp between them
            (
                &Element::RationalPolynomialCoefficient(..),
                &Element::RationalPolynomialCoefficient(..),
            ) => Some(cmp::Ordering::Equal),
            (_, &Element::RationalPolynomialCoefficient(..)) => Some(cmp::Ordering::Less),
            (&Element::RationalPolynomialCoefficient(..), _) => Some(cmp::Ordering::Greater),
            (&Element::Pow(_, ref be1), &Element::Pow(_, ref be2)) => {
                let (ref b1, ref e1) = **be1;
                let (ref b2, ref e2) = **be2;
                let c = b1.partial_cmp(b2, var_info, false);
                match c {
                    Some(cmp::Ordering::Equal) => e1.partial_cmp(e2, var_info, false),
                    _ => c,
                }
            }
            (&Element::Pow(_, ref be), _) => {
                let (ref b, _) = **be;
                let c = b.partial_cmp(other, var_info, false);
                match c {
                    Some(cmp::Ordering::Equal) => Some(cmp::Ordering::Less),
                    _ => c,
                }
            }
            (_, &Element::Pow(_, ref be)) => {
                let (ref b, _) = **be;
                let c = self.partial_cmp(b, var_info, false);
                match c {
                    Some(cmp::Ordering::Equal) => Some(cmp::Ordering::Greater),
                    _ => c,
                }
            }
            (&Element::Fn(..), _) => Some(cmp::Ordering::Less),
            (_, &Element::Fn(..)) => Some(cmp::Ordering::Greater),
            (&Element::SubExpr(_, ref ta), &Element::SubExpr(_, ref tb)) => {
                if ta.len() != tb.len() {
                    return ta.len().partial_cmp(&tb.len());
                }

                for (taa, tbb) in ta.iter().zip(tb) {
                    let k = taa
                        .simple_partial_cmp(tbb, var_info, ground_level)
                        .or_else(|| taa.partial_cmp(tbb, var_info, ground_level));
                    match k {
                        Some(cmp::Ordering::Equal) => {}
                        _ => return k,
                    }
                }
                Some(cmp::Ordering::Equal)
            }
            (&Element::SubExpr(..), _) => Some(cmp::Ordering::Less),
            _ => Some(cmp::Ordering::Less),
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
pub struct IdentityStatement<ID: Id = VarName> {
    pub mode: IdentityStatementMode,
    pub contains_dollar: bool,
    pub lhs: Element<ID>,
    pub rhs: Element<ID>,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, PartialOrd, Ord)]
pub enum IdentityStatementMode {
    Once,
    Many,
    All,
}

impl fmt::Display for Module {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // TODO: add mod options
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
            Statement::Module(ref m) => writeln!(f, "{}", m),
            Statement::NewExpression(ref id, ref e) => writeln!(f, "expr {} = {};", id, e),
            Statement::NewFunction(ref id, ref args, ref e) => {
                writeln!(f, "fn {}({:?}) = {};", id, args, e)
            }
            Statement::IdentityStatement(ref id) => write!(f, "{}", id),
            Statement::SplitArg(ref name) => writeln!(f, "SplitArg {};", name),
            Statement::Expand => writeln!(f, "Expand;"),
            Statement::Print(ref mode, ref po) => {
                write!(f, "Print")?;
                match mode {
                    PrintMode::Form => {} // default
                    PrintMode::Mathematica => write!(f, " Mathematica")?,
                }

                for x in po {
                    write!(f, "{}", x.print_direct())?
                }
                writeln!(f, ";")
            }
            Statement::Multiply(ref x) => writeln!(f, "Multiply {};", x),
            Statement::ReplaceBy(ref x) => writeln!(f, "ReplaceBy {};", x),
            Statement::Symmetrize(ref x) => writeln!(f, "Symmetrize {};", x),
            Statement::Collect(ref x) => writeln!(f, "Collect {};", x),
            Statement::Extract(ref d, ref xs) => {
                writeln!(f, "Extract {} ", d)?;
                for x in xs {
                    write!(f, ",{}", x)?;
                }
                writeln!(f, "")
            }
            Statement::Repeat(ref ss) => {
                if ss.len() == 1 {
                    write!(f, "repeat {}", ss[0])
                } else {
                    writeln!(f, "repeat;")?;

                    for s in ss {
                        write!(f, "\t{}", s)?;
                    }

                    writeln!(f, "endrepeat;")
                }
            }
            Statement::Argument(ref ff, ref ss) => {
                writeln!(f, "argument ")?;

                for fff in ff {
                    writeln!(f, ",{}", fff)?;
                }

                for s in ss {
                    write!(f, "\t{}", s)?;
                }

                writeln!(f, "endargument;")
            }
            Statement::Inside(ref ff, ref ss) => {
                writeln!(f, "inside ")?;

                for fff in ff {
                    writeln!(f, ",{}", fff)?;
                }

                for s in ss {
                    write!(f, "\t{}", s)?;
                }

                writeln!(f, "endinside;")
            }
            Statement::IfElse(ref cond, ref m, ref nm) => {
                if nm.len() == 0 && m.len() == 1 {
                    write!(f, "if {} {};", cond, m[0])
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
                }
            }
            Statement::ForIn(ref d, ref l, ref m) => {
                write!(f, "for {} in {{", d)?;

                for li in l {
                    writeln!(f, ",{}", li)?;
                }

                writeln!(f, "}}")?;

                for s in m {
                    writeln!(f, "\t{}", s)?;
                }

                writeln!(f, "endfor;")
            }
            Statement::ForInRange(ref d, ref l, ref u, ref m) => {
                write!(f, "for {} in {}..{} {{", d, l, u)?;

                for s in m {
                    writeln!(f, "\t{}", s)?;
                }

                writeln!(f, "}}")
            }
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
            Statement::MatchAssign(ref e, ref ss) => {
                writeln!(f, "matchassign {} {{", e)?;
                for s in ss {
                    writeln!(f, "\t{}", s)?;
                }
                writeln!(f, "}}")
            }
            Statement::Assign(ref d, ref e) => writeln!(f, "{}={};", d, e),
            Statement::Attrib(ref ff, ref a) => {
                writeln!(f, "Attrib {}=", ff)?;
                match a.first() {
                    Some(x) => write!(f, "{}", x)?,
                    None => {}
                }

                for x in a.iter().skip(1) {
                    write!(f, "+{}", x)?;
                }
                writeln!(f, ";")
            }
            Statement::Discard => writeln!(f, "Discard;"),
            Statement::Maximum(ref d) => writeln!(f, "Maximum {};", d),
            Statement::Jump(ref i) => writeln!(f, "JMP {}", i),
            Statement::Eval(ref n, ref i) => writeln!(f, "IF NOT {} JMP {}", n, i),
            Statement::JumpIfChanged(ref i) => writeln!(f, "JMP_CH {}", i),
            Statement::PushChange => writeln!(f, "PUSH_CH"),
        }
    }
}

pub fn fmt_varname(v: &VarName, f: &mut fmt::Formatter, var_info: &GlobalVarInfo) -> fmt::Result {
    if var_info.inv_name_map.len() == 0 {
        write!(f, "var_{}", v)
    } else {
        write!(f, "{}", var_info.inv_name_map[*v as usize])
    }
}

impl fmt::Display for Ordering {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Ordering::Greater => write!(f, ">"),
            Ordering::GreaterEqual => write!(f, ">="),
            Ordering::Smaller => write!(f, "<"),
            Ordering::SmallerEqual => write!(f, "<="),
            Ordering::Equal => write!(f, "=="),
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

#[derive(Debug, Copy, Clone)]
pub enum PrintMode {
    Form,
    Mathematica,
}

pub struct ElementPrinter<'a> {
    pub element: &'a Element,
    pub var_info: &'a GlobalVarInfo,
    pub print_mode: PrintMode,
}

impl<'a> fmt::Display for ElementPrinter<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.element.fmt_output(f, self.print_mode, self.var_info)
    }
}

impl Element {
    pub fn fmt_output(
        &self,
        f: &mut fmt::Formatter,
        print_mode: PrintMode,
        var_info: &GlobalVarInfo,
    ) -> fmt::Result {
        match self {
            &Element::VariableArgument(ref name) => {
                write!(f, "?")?;
                fmt_varname(name, f, var_info)
            }
            &Element::Wildcard(ref name, ref restriction) => {
                if restriction.len() == 0 {
                    fmt_varname(name, f, var_info)?;
                    write!(f, "?")
                } else {
                    fmt_varname(name, f, var_info)?;
                    write!(f, "?{{")?;
                    match restriction.first() {
                        Some(x) => x.fmt_output(f, print_mode, var_info)?,
                        None => {}
                    }
                    for t in restriction.iter().skip(1) {
                        t.fmt_output(f, print_mode, var_info)?
                    }
                    write!(f, "}}")
                }
            }
            &Element::Var(ref name, ref e) => {
                if !e.is_one() {
                    fmt_varname(name, f, var_info)?;
                    write!(f, "^{}", e)
                } else {
                    fmt_varname(name, f, var_info)
                }
            }
            &Element::Dollar(ref name, ref inds) => {
                fmt_varname(name, f, var_info)?;
                if inds.len() > 0 {
                    write!(f, "[")?;

                    inds[0].fmt_output(f, print_mode, var_info)?;
                    for i in inds.iter().skip(1) {
                        write!(f, ",")?;
                        i.fmt_output(f, print_mode, var_info)?;
                    }
                    write!(f, "]")?;
                }
                write!(f, "")
            }
            &Element::Num(_, ref n) => write!(f, "{}", n),
            &Element::NumberRange(ref num, ref rel) => write!(f, "{}{}", num, rel),
            &Element::Comparison(_, ref b, ref rel) => write!(f, "{} {} {}", b.0, rel, b.1),
            &Element::Pow(_, ref be) => {
                let (ref b, ref e) = **be;
                match *b {
                    Element::SubExpr(..) | Element::Term(..) => {
                        write!(f, "(")?;
                        b.fmt_output(f, print_mode, var_info)?;
                        write!(f, ")")?
                    }
                    _ => b.fmt_output(f, print_mode, var_info)?,
                };
                match *e {
                    Element::SubExpr(..) | Element::Term(..) => {
                        write!(f, "^(")?;
                        e.fmt_output(f, print_mode, var_info)?;
                        write!(f, ")")
                    }
                    _ => {
                        write!(f, "^")?;
                        e.fmt_output(f, print_mode, var_info)
                    }
                }
            }
            &Element::Fn(_, ref name, ref args) => {
                fmt_varname(&name, f, var_info)?;

                match print_mode {
                    PrintMode::Form => write!(f, "(")?,
                    PrintMode::Mathematica => write!(f, "[")?,
                }

                match args.first() {
                    Some(x) => x.fmt_output(f, print_mode, var_info)?,
                    None => {}
                }

                for x in args.iter().skip(1) {
                    write!(f, ",")?;
                    x.fmt_output(f, print_mode, var_info)?;
                }

                match print_mode {
                    PrintMode::Form => write!(f, ")"),
                    PrintMode::Mathematica => write!(f, "]"),
                }
            }
            &Element::FnWildcard(ref name, ref b) => {
                let (restriction, args) = &**b;
                if restriction.len() == 0 {
                    fmt_varname(name, f, var_info)?;
                    write!(f, "?")?;
                } else {
                    fmt_varname(name, f, var_info)?;
                    write!(f, "?{{")?;
                    match restriction.first() {
                        Some(x) => x.fmt_output(f, print_mode, var_info)?,
                        None => {}
                    }
                    for t in restriction.iter().skip(1) {
                        t.fmt_output(f, print_mode, var_info)?
                    }
                    write!(f, "}}")?;
                }

                match print_mode {
                    PrintMode::Form => write!(f, "(")?,
                    PrintMode::Mathematica => write!(f, "[")?,
                }

                match args.first() {
                    Some(x) => x.fmt_output(f, print_mode, var_info)?,
                    None => {}
                }

                for x in args.iter().skip(1) {
                    write!(f, ",")?;
                    x.fmt_output(f, print_mode, var_info)?;
                }

                match print_mode {
                    PrintMode::Form => write!(f, ")"),
                    PrintMode::Mathematica => write!(f, "]"),
                }
            }
            &Element::Term(_, ref factors) => {
                match print_mode {
                    PrintMode::Form => {
                        if let Some(n @ Element::Num(..)) = factors.last() {
                            if factors.len() > 1 {
                                if let Element::Num(false, Number::SmallInt(-1)) = n {
                                    write!(f, "-")?;
                                } else {
                                    n.fmt_output(f, print_mode, var_info)?;
                                    write!(f, "*")?;
                                }
                            } else {
                                n.fmt_output(f, print_mode, var_info)?;
                                write!(f, "*")?;
                            }
                        }
                        match factors.first() {
                            Some(s @ &Element::SubExpr(..)) if factors.len() > 1 => {
                                write!(f, "(")?;
                                s.fmt_output(f, print_mode, var_info)?;
                                write!(f, ")")?
                            }
                            Some(x) => x.fmt_output(f, print_mode, var_info)?,
                            None => {}
                        }
                        for t in factors.iter().skip(1) {
                            match t {
                                s @ &Element::SubExpr(..) => {
                                    write!(f, "*(")?;
                                    s.fmt_output(f, print_mode, var_info)?;
                                    write!(f, ")")?
                                }
                                Element::Num(..) => {}
                                _ => {
                                    write!(f, "*")?;
                                    t.fmt_output(f, print_mode, var_info)?
                                }
                            }
                        }
                    }
                    PrintMode::Mathematica => {
                        if let Some(n @ Element::Num(..)) = factors.last() {
                            n.fmt_output(f, print_mode, var_info)?
                        }

                        for t in factors.iter() {
                            match t {
                                s @ &Element::SubExpr(..) => {
                                    write!(f, "(")?;
                                    s.fmt_output(f, print_mode, var_info)?;
                                    write!(f, ")")?
                                }
                                &Element::Num(..) => {}
                                _ => {
                                    write!(f, " ")?;
                                    t.fmt_output(f, print_mode, var_info)?
                                }
                            }
                        }
                    }
                }
                write!(f, "")
            }
            &Element::SubExpr(_, ref terms) => {
                match terms.first() {
                    Some(x) => x.fmt_output(f, print_mode, var_info)?,
                    None => {}
                }
                for t in terms.iter().skip(1) {
                    write!(f, "+")?;
                    t.fmt_output(f, print_mode, var_info)?
                }
                write!(f, "")
            }
            &Element::RationalPolynomialCoefficient(_, ref p) => match print_mode {
                PrintMode::Form => write!(
                    f,
                    "rat_({},{})",
                    PolyPrinter {
                        poly: &p.0,
                        var_info: var_info
                    },
                    PolyPrinter {
                        poly: &p.1,
                        var_info: var_info
                    }
                ),
                PrintMode::Mathematica => write!(
                    f,
                    "({})/({})",
                    PolyPrinter {
                        poly: &p.0,
                        var_info: var_info
                    },
                    PolyPrinter {
                        poly: &p.1,
                        var_info: var_info
                    }
                ),
            },
        }
    }
}

impl fmt::Display for Element {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.fmt_output(f, PrintMode::Form, &GlobalVarInfo::empty())
    }
}

impl Element<String> {
    /// Replaces string names by numerical IDs.
    pub fn to_element(&mut self, var_info: &mut VarInfo) -> Element {
        match *self {
            Element::NumberRange(ref n, ref c) => Element::NumberRange(n.clone(), c.clone()),
            Element::Comparison(_, ref mut b, ref c) => Element::Comparison(
                true,
                Box::new((b.0.to_element(var_info), b.1.to_element(var_info))),
                c.clone(),
            ),
            Element::Num(_, ref n) => Element::Num(true, n.clone()),
            Element::Dollar(ref mut name, ref mut inds) => Element::Dollar(
                var_info.get_name(name),
                inds.iter_mut().map(|x| x.to_element(var_info)).collect(),
            ),
            Element::FnWildcard(ref mut name, ref mut b) => Element::FnWildcard(
                var_info.get_name(name),
                Box::new((
                    b.0.iter_mut().map(|x| x.to_element(var_info)).collect(),
                    b.1.iter_mut().map(|x| x.to_element(var_info)).collect(),
                )),
            ),
            Element::Var(ref mut name, ref mut e) => {
                Element::Var(var_info.get_name(name), e.clone())
            }
            Element::VariableArgument(ref mut name) => {
                Element::VariableArgument(var_info.get_name(name))
            }
            Element::Wildcard(ref mut name, ref mut restrictions) => Element::Wildcard(
                var_info.get_name(name),
                restrictions
                    .iter_mut()
                    .map(|x| x.to_element(var_info))
                    .collect(),
            ),
            Element::Pow(_, ref mut be) => {
                let (ref mut b, ref mut e) = *&mut **be;
                Element::Pow(
                    true,
                    Box::new((b.to_element(var_info), e.to_element(var_info))),
                )
            }
            Element::Term(_, ref mut f) => {
                Element::Term(true, f.iter_mut().map(|x| x.to_element(var_info)).collect())
            }
            Element::SubExpr(_, ref mut f) => {
                Element::SubExpr(true, f.iter_mut().map(|x| x.to_element(var_info)).collect())
            }
            Element::Fn(_, ref mut name, ref mut args) => Element::Fn(
                true,
                var_info.get_name(name),
                args.iter_mut().map(|x| x.to_element(var_info)).collect(),
            ),
            Element::RationalPolynomialCoefficient(ref num, ref den) => {
                Element::RationalPolynomialCoefficient(num.clone(), den.clone())
            }
        }
    }
}

impl Element {
    #[inline]
    fn contains_dollar_simple(&self) -> Option<bool> {
        match *self {
            Element::Var(..) | Element::Num(..) => Some(false),
            Element::Dollar(..) => Some(true),
            Element::Wildcard(_, ref restrictions) => {
                if restrictions.is_empty() {
                    Some(false)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    pub fn contains_dollar(&self) -> bool {
        match *self {
            Element::Term(_, ref f) | Element::SubExpr(_, ref f) | Element::Fn(_, _, ref f) => {
                for x in f {
                    // TODO: first test all items with the simple test?
                    if x.contains_dollar_simple()
                        .unwrap_or_else(|| x.contains_dollar())
                    {
                        return true;
                    }
                }
                false
            }
            Element::FnWildcard(_, ref b) => {
                for x in b.0.iter().chain(&b.1) {
                    if x.contains_dollar_simple()
                        .unwrap_or_else(|| x.contains_dollar())
                    {
                        return true;
                    }
                }
                false
            }
            Element::Comparison(_, ref e, _) | Element::Pow(_, ref e) => {
                e.0.contains_dollar_simple()
                    .unwrap_or_else(|| e.0.contains_dollar())
                    || e.1
                        .contains_dollar_simple()
                        .unwrap_or_else(|| e.1.contains_dollar())
            }
            Element::Wildcard(_, ref restrictions) => {
                for x in restrictions {
                    if x.contains_dollar_simple()
                        .unwrap_or_else(|| x.contains_dollar())
                    {
                        return true;
                    }
                }
                false
            }
            Element::Dollar(..) => true,
            _ => false,
        }
    }

    pub fn replace_dollar(&mut self, map: &HashMap<VarName, DollarVariableTable>) -> ReplaceResult {
        let mut changed = ReplaceResult::empty();
        *self = match *self {
            Element::Dollar(ref mut name, ref mut inds) => {
                // TODO: make this a partial replacement?
                for i in inds.iter_mut() {
                    i.replace_dollar(map);
                }

                if let Some(x) = map.get(name).and_then(|x| x.get(inds)) {
                    changed = ReplaceResult::Replaced;
                    x.clone()
                } else {
                    return ReplaceResult::NotReplaced;
                }
            }
            Element::FnWildcard(_, ref mut b) => {
                let (restrictions, args) = &mut **b;
                for x in restrictions.iter_mut().chain(args) {
                    changed |= x.replace_dollar(map);
                }
                return changed;
            }
            Element::Comparison(ref mut dirty, ref mut e, _) => {
                changed |= e.0.replace_dollar(map);
                changed |= e.1.replace_dollar(map);
                *dirty |= changed.contains(ReplaceResult::Replaced);
                return changed;
            }
            Element::Wildcard(_, ref mut restrictions) => {
                for x in restrictions {
                    changed |= x.replace_dollar(map);
                }
                return changed;
            }
            Element::Pow(ref mut dirty, ref mut be) => {
                let (ref mut b, ref mut e) = *&mut **be;
                changed |= b.replace_dollar(map);
                changed |= e.replace_dollar(map);
                *dirty |= changed.contains(ReplaceResult::Replaced);
                return changed;
            }
            Element::Term(ref mut dirty, ref mut f)
            | Element::SubExpr(ref mut dirty, ref mut f) => {
                for x in f {
                    changed |= x.replace_dollar(map);
                }
                *dirty |= changed.contains(ReplaceResult::Replaced);
                return changed;
            }
            Element::Fn(ref mut dirty, _, ref mut args) => {
                for x in args {
                    changed |= x.replace_dollar(map);
                }
                *dirty |= changed.contains(ReplaceResult::Replaced);
                return changed;
            }
            _ => return changed,
        };
        changed
    }

    pub fn replace_elements(&mut self, map: &HashMap<VarName, Element>) -> bool {
        let mut changed = false;
        *self = match *self {
            Element::Var(ref mut name, ref pow) => {
                if let Some(x) = map.get(name) {
                    Element::Pow(
                        true,
                        Box::new((x.clone(), Element::Num(false, pow.clone()))),
                    )
                } else {
                    return false;
                }
            }
            Element::Dollar(ref mut name, ref mut inds) => {
                for i in inds.iter_mut() {
                    changed |= i.replace_elements(map);
                }

                // we can still replace a dollar variable, but only if
                // it does not have an index
                if inds.is_empty() {
                    if let Some(x) = map.get(name) {
                        x.clone()
                    } else {
                        return changed;
                    }
                } else {
                    return changed;
                }
            }
            Element::Comparison(ref mut dirty, ref mut e, _) => {
                changed |= e.0.replace_elements(map);
                changed |= e.1.replace_elements(map);
                *dirty |= changed;
                return changed;
            }
            Element::Wildcard(_, ref mut restrictions) => {
                for x in restrictions {
                    changed |= x.replace_elements(map);
                }
                return changed;
            }
            Element::Pow(ref mut dirty, ref mut be) => {
                let (ref mut b, ref mut e) = *&mut **be;
                changed |= b.replace_elements(map);
                changed |= e.replace_elements(map);
                *dirty |= changed;
                return changed;
            }
            Element::Term(ref mut dirty, ref mut f)
            | Element::SubExpr(ref mut dirty, ref mut f) => {
                for x in f {
                    changed |= x.replace_elements(map);
                }
                *dirty |= changed;
                return changed;
            }
            Element::Fn(ref mut dirty, ref mut name, ref mut args) => {
                if let Some(x) = map.get(name) {
                    if let &Element::Var(ref y, _) = x {
                        *name = y.clone();
                        changed = true
                    } else {
                        panic!("Cannot replace function name by generic expression");
                    }
                }

                for x in args {
                    changed |= x.replace_elements(map);
                }
                *dirty |= changed;
                return changed;
            }
            Element::FnWildcard(ref mut name, ref mut b) => {
                if let Some(x) = map.get(name) {
                    if let &Element::Var(ref y, _) = x {
                        *name = y.clone();
                        changed = true
                    } else {
                        panic!("Cannot replace function name by generic expression");
                    }
                }

                let (restrictions, args) = &mut **b;
                for x in restrictions.iter_mut().chain(args) {
                    changed |= x.replace_elements(map);
                }
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

impl Statement<String> {
    pub fn to_statement(&mut self, var_info: &mut VarInfo) -> Statement {
        match *self {
            Statement::Module(ref mut m) => Statement::Module(Module {
                name: m.name.clone(),
                active_exprs: m
                    .active_exprs
                    .iter()
                    .map(|n| var_info.get_name(n))
                    .collect(),
                exclude_exprs: m
                    .exclude_exprs
                    .iter()
                    .map(|n| var_info.get_name(n))
                    .collect(),
                statements: m
                    .statements
                    .iter_mut()
                    .map(|s| s.to_statement(var_info))
                    .collect(),
            }),
            Statement::NewExpression(ref name, ref mut e) => {
                Statement::NewExpression(var_info.get_name(name), e.to_element(var_info))
            }
            Statement::NewFunction(ref name, ref mut args, ref mut e) => Statement::NewFunction(
                var_info.get_name(name),
                args.iter_mut().map(|x| var_info.get_name(x)).collect(),
                e.to_element(var_info),
            ),
            Statement::IdentityStatement(IdentityStatement {
                ref mode,
                ref contains_dollar,
                ref mut lhs,
                ref mut rhs,
            }) => Statement::IdentityStatement(IdentityStatement {
                mode: mode.clone(),
                contains_dollar: *contains_dollar,
                lhs: lhs.to_element(var_info),
                rhs: rhs.to_element(var_info),
            }),
            Statement::Repeat(ref mut ss) => {
                Statement::Repeat(ss.iter_mut().map(|s| s.to_statement(var_info)).collect())
            }
            Statement::Argument(ref mut ff, ref mut ss) => Statement::Argument(
                ff.iter_mut().map(|x| x.to_element(var_info)).collect(),
                ss.iter_mut().map(|s| s.to_statement(var_info)).collect(),
            ),
            Statement::Inside(ref mut ff, ref mut ss) => Statement::Inside(
                ff.iter_mut().map(|f| f.to_element(var_info)).collect(),
                ss.iter_mut().map(|s| s.to_statement(var_info)).collect(),
            ),
            Statement::IfElse(ref mut e, ref mut ss, ref mut sse) => Statement::IfElse(
                e.to_element(var_info),
                ss.iter_mut().map(|s| s.to_statement(var_info)).collect(),
                sse.iter_mut().map(|s| s.to_statement(var_info)).collect(),
            ),
            Statement::MatchAssign(ref mut e, ref mut ss) => Statement::MatchAssign(
                e.to_element(var_info),
                ss.iter_mut().map(|s| s.to_statement(var_info)).collect(),
            ),
            Statement::ForIn(ref mut d, ref mut l, ref mut ss) => Statement::ForIn(
                d.to_element(var_info),
                l.iter_mut().map(|s| s.to_element(var_info)).collect(),
                ss.iter_mut().map(|s| s.to_statement(var_info)).collect(),
            ),
            Statement::ForInRange(ref mut d, ref mut l, ref mut u, ref mut ss) => {
                Statement::ForInRange(
                    d.to_element(var_info),
                    l.to_element(var_info),
                    u.to_element(var_info),
                    ss.iter_mut().map(|s| s.to_statement(var_info)).collect(),
                )
            }
            Statement::SplitArg(ref name) => Statement::SplitArg(var_info.get_name(name)),
            Statement::Symmetrize(ref name) => Statement::Symmetrize(var_info.get_name(name)),
            Statement::Collect(ref name) => Statement::Collect(var_info.get_name(name)),
            Statement::Extract(ref mut d, ref names) => Statement::Extract(
                d.to_element(var_info),
                names.iter().map(|name| var_info.get_name(name)).collect(),
            ),
            Statement::Multiply(ref mut e) => Statement::Multiply(e.to_element(var_info)),
            Statement::ReplaceBy(ref mut e) => Statement::ReplaceBy(e.to_element(var_info)),
            Statement::Expand => Statement::Expand,
            Statement::Print(ref mode, ref mut pos) => Statement::Print(
                mode.clone(),
                pos.iter_mut().map(|po| po.to_element(var_info)).collect(),
            ),
            Statement::Maximum(ref mut e) => Statement::Maximum(e.to_element(var_info)),
            Statement::Call(ref name, ref mut es) => Statement::Call(
                name.clone(),
                es.iter_mut().map(|s| s.to_element(var_info)).collect(),
            ),
            Statement::Assign(ref mut d, ref mut e) => {
                Statement::Assign(d.to_element(var_info), e.to_element(var_info))
            }
            Statement::Attrib(ref mut f, ref mut l) => {
                Statement::Attrib(f.to_element(var_info), mem::replace(l, vec![]))
            }
            Statement::Jump(x) => Statement::Jump(x),
            Statement::Eval(ref c, ref i) => Statement::Eval(c.clone(), *i),
            Statement::JumpIfChanged(i) => Statement::JumpIfChanged(i),
            Statement::PushChange => Statement::PushChange,
            Statement::Discard => Statement::Discard,
        }
    }
}

impl Statement {
    /// Check if a statement contains a dollar variable.
    pub fn contains_dollar(&self) -> bool {
        match *self {
            Statement::IdentityStatement(IdentityStatement {
                mode: _,
                contains_dollar,
                lhs: _,
                rhs: _,
            }) => contains_dollar,
            Statement::Module(Module { ref statements, .. }) => {
                for s in statements {
                    if s.contains_dollar() {
                        return true;
                    }
                }
                false
            }
            Statement::Repeat(ref ss) => {
                for s in ss {
                    if s.contains_dollar() {
                        return true;
                    }
                }
                false
            }
            Statement::IfElse(ref e, ref ss, ref sse) => {
                if e.contains_dollar() {
                    return true;
                }
                for s in ss {
                    if s.contains_dollar() {
                        return true;
                    }
                }
                for s in sse {
                    if s.contains_dollar() {
                        return true;
                    }
                }
                false
            }
            Statement::Multiply(ref e) | Statement::ReplaceBy(ref e) => e.contains_dollar(),
            Statement::Call(_, ref es) => {
                for s in es {
                    if s.contains_dollar() {
                        return true;
                    }
                }
                false
            }
            Statement::Assign(ref _d, ref e) => e.contains_dollar(),
            Statement::Argument(ref ds, ref ss) => {
                for s in ds {
                    if s.contains_dollar() {
                        return true;
                    }
                }

                for s in ss {
                    if s.contains_dollar() {
                        return true;
                    }
                }
                false
            }
            Statement::Inside(.., ref ss) => {
                for s in ss {
                    if s.contains_dollar() {
                        return true;
                    }
                }
                false
            }
            Statement::ForIn(_, ref l, ref ss) => {
                for e in l {
                    if e.contains_dollar() {
                        return true;
                    }
                }
                for s in ss {
                    if s.contains_dollar() {
                        return true;
                    }
                }
                false
            }
            Statement::ForInRange(_, ref l, ref u, ref ss) => {
                if l.contains_dollar() || u.contains_dollar() {
                    return true;
                }
                for s in ss {
                    if s.contains_dollar() {
                        return true;
                    }
                }
                false
            }
            Statement::Eval(ref c, _) => c.contains_dollar(),
            _ => false,
        }
    }

    pub fn replace_dollar(&mut self, map: &HashMap<VarName, DollarVariableTable>) -> ReplaceResult {
        let mut changed = ReplaceResult::empty();
        match *self {
            Statement::Module(Module {
                ref mut statements, ..
            }) => {
                for s in statements {
                    changed |= s.replace_dollar(map);
                }
            }
            Statement::IdentityStatement(IdentityStatement {
                mode: _,
                ref mut contains_dollar,
                ref mut lhs,
                ref mut rhs,
            }) => {
                if *contains_dollar {
                    changed |= lhs.replace_dollar(map);
                    changed |= rhs.replace_dollar(map);

                    // we have a dollar variable left if there are unreplaced dollars
                    *contains_dollar = changed.contains(ReplaceResult::NotReplaced);
                }
            }
            Statement::Repeat(ref mut ss) => {
                for s in ss {
                    changed |= s.replace_dollar(map);
                }
            }
            Statement::MatchAssign(ref mut e, ref mut ss) => {
                changed |= e.replace_dollar(map);
                for s in ss {
                    changed |= s.replace_dollar(map);
                }
            }
            Statement::IfElse(ref mut e, ref mut ss, ref mut sse) => {
                changed |= e.replace_dollar(map);
                for s in ss {
                    changed |= s.replace_dollar(map);
                }
                for s in sse {
                    changed |= s.replace_dollar(map);
                }
            }
            Statement::Multiply(ref mut e) | Statement::ReplaceBy(ref mut e) => {
                changed |= e.replace_dollar(map);
            }
            Statement::Call(_, ref mut es) => {
                for s in es {
                    changed |= s.replace_dollar(map);
                }
            }
            Statement::Assign(ref mut d, ref mut e) => {
                if let Element::Dollar(_id, ref mut inds) = d {
                    for i in inds {
                        changed |= i.replace_dollar(map);
                    }
                }
                changed |= e.replace_dollar(map);
            }
            Statement::Argument(ref mut ds, ref mut ss) => {
                for s in ds {
                    changed |= s.replace_dollar(map);
                }
                for s in ss {
                    changed |= s.replace_dollar(map);
                }
            }
            Statement::Inside(ref _d, ref mut ss) => {
                for s in ss {
                    changed |= s.replace_dollar(map);
                }
            }
            Statement::ForIn(_, ref mut l, ref mut ss) => {
                for e in l {
                    changed |= e.replace_dollar(map);
                }
                for s in ss {
                    changed |= s.replace_dollar(map);
                }
            }
            Statement::ForInRange(_, ref mut l, ref mut u, ref mut ss) => {
                changed |= l.replace_dollar(map);
                changed |= u.replace_dollar(map);
                for s in ss {
                    changed |= s.replace_dollar(map);
                }
            }
            Statement::Eval(ref mut c, _) => {
                changed |= c.replace_dollar(map);
            }
            _ => {}
        };
        changed
    }

    pub fn replace_elements(&mut self, map: &HashMap<VarName, Element>) -> bool {
        let mut changed = false;
        match *self {
            Statement::Module(Module {
                ref mut statements, ..
            }) => {
                for s in statements {
                    changed |= s.replace_elements(map);
                }
            }
            Statement::IdentityStatement(IdentityStatement {
                mode: _,
                contains_dollar: _,
                ref mut lhs,
                ref mut rhs,
            }) => {
                changed |= lhs.replace_elements(map);
                changed |= rhs.replace_elements(map);
            }
            Statement::Repeat(ref mut ss) => {
                for s in ss {
                    changed |= s.replace_elements(map);
                }
            }
            Statement::MatchAssign(ref mut e, ref mut ss) => {
                changed |= e.replace_elements(map);
                for s in ss {
                    changed |= s.replace_elements(map);
                }
            }
            Statement::IfElse(ref mut e, ref mut ss, ref mut sse) => {
                changed |= e.replace_elements(map);
                for s in ss {
                    changed |= s.replace_elements(map);
                }
                for s in sse {
                    changed |= s.replace_elements(map);
                }
            }
            Statement::SplitArg(ref mut name)
            | Statement::Symmetrize(ref mut name)
            | Statement::Collect(ref mut name) => {
                if let Some(x) = map.get(name) {
                    if let &Element::Var(ref y, _) = x {
                        *name = y.clone();
                    } else {
                        panic!("Cannot replace function name by generic expression");
                    }
                }
            }
            Statement::Extract(_, ref mut names) => {
                for name in names {
                    if let Some(x) = map.get(name) {
                        if let &Element::Var(ref y, _) = x {
                            *name = y.clone();
                        } else {
                            panic!("Cannot replace function name by generic expression");
                        }
                    }
                }
            }
            Statement::Multiply(ref mut e) | Statement::ReplaceBy(ref mut e) => {
                changed |= e.replace_elements(map);
            }
            Statement::Call(_, ref mut es) => {
                for s in es {
                    changed |= s.replace_elements(map);
                }
            }
            Statement::Assign(ref mut d, ref mut e) => {
                if let Element::Dollar(_id, ref mut inds) = d {
                    for i in inds {
                        changed |= i.replace_elements(map);
                    }
                }
                changed |= e.replace_elements(map);
            }
            Statement::Argument(ref mut ds, ref mut ss) => {
                for s in ds {
                    changed |= s.replace_elements(map);
                }
                for s in ss {
                    changed |= s.replace_elements(map);
                }
            }
            Statement::Inside(ref _d, ref mut ss) => {
                for s in ss {
                    changed |= s.replace_elements(map);
                }
            }
            Statement::ForIn(_, ref mut l, ref mut ss) => {
                for e in l {
                    changed |= e.replace_elements(map);
                }
                for s in ss {
                    changed |= s.replace_elements(map);
                }
            }
            Statement::ForInRange(_, ref mut l, ref mut u, ref mut ss) => {
                changed |= l.replace_elements(map);
                changed |= u.replace_elements(map);
                for s in ss {
                    changed |= s.replace_elements(map);
                }
            }
            _ => {}
        };
        changed
    }

    pub fn normalize(&mut self, var_info: &GlobalVarInfo) {
        match *self {
            Statement::Module(Module {
                ref mut statements, ..
            }) => {
                for s in statements {
                    s.normalize(var_info);
                }
            }
            Statement::IdentityStatement(IdentityStatement {
                ref mut lhs,
                ref mut rhs,
                ..
            }) => {
                lhs.normalize_inplace(var_info);
                rhs.normalize_inplace(var_info);
            }
            Statement::IfElse(ref mut cond, ref mut trueblock, ref mut falseblock) => {
                cond.normalize_inplace(var_info);
                for s in trueblock {
                    s.normalize(var_info);
                }
                for s in falseblock {
                    s.normalize(var_info);
                }
            }
            Statement::Eval(ref mut e, _) => {
                e.normalize_inplace(var_info);
            }
            Statement::Multiply(ref mut e) | Statement::ReplaceBy(ref mut e) => {
                e.normalize_inplace(var_info);
            }
            Statement::Assign(ref mut d, ref mut e) => {
                d.normalize_inplace(var_info);
                e.normalize_inplace(var_info);
            }
            Statement::Argument(ref mut ds, ref mut ss) => {
                for s in ds {
                    s.normalize_inplace(var_info);
                }
                for s in ss {
                    s.normalize(var_info);
                }
            }
            Statement::Inside(_, ref mut ss) => {
                for s in ss {
                    s.normalize(var_info);
                }
            }
            Statement::Call(_, ref mut ss) => {
                for s in ss {
                    s.normalize_inplace(var_info);
                }
            }
            Statement::ForIn(ref mut d, ref mut l, ref mut ss) => {
                d.normalize_inplace(var_info);
                for e in l {
                    e.normalize_inplace(var_info);
                }
                for s in ss {
                    s.normalize(var_info);
                }
            }
            Statement::ForInRange(ref mut d, ref mut l, ref mut u, ref mut ss) => {
                d.normalize_inplace(var_info);
                u.normalize_inplace(var_info);
                l.normalize_inplace(var_info);
                for s in ss {
                    s.normalize(var_info);
                }
            }
            Statement::MatchAssign(ref mut pat, ref mut ss) => {
                pat.normalize_inplace(var_info);
                for s in ss {
                    s.normalize(var_info);
                }
            }
            Statement::NewExpression(_, ref mut rhs)
            | Statement::NewFunction(_, _, ref mut rhs) => {
                rhs.normalize_inplace(var_info);
            }
            _ => {}
        }
    }
}
