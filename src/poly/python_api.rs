use cpython::{exc, PyErr, PyResult};
use number::Number;
use poly::polynomial;
use poly::polynomial::PolyPrinter;
use std::cell::RefCell;
use std::ops::{Add, Div, Mul, Neg, Sub};
use std::str::FromStr;
use structure;
use structure::{
    BorrowedVarInfo, Element, ElementPrinter, IdentityStatement, IdentityStatementMode, PrintMode,
    StatementResult,
};

fn clone_varmap(a: &structure::VarInfo, b: &structure::VarInfo) -> structure::VarInfo {
    if a.global_info.num_vars() > b.global_info.num_vars() {
        a.clone()
    } else {
        b.clone()
    }
}

py_module_initializer!(reform, initreform, PyInit_reform, |py, m| {
    m.add(
        py,
        "__doc__",
        "A module for interaction with reform expressions",
    )?;
    m.add_class::<VarInfo>(py)?;
    m.add_class::<Polynomial>(py)?;
    m.add_class::<RationalPolynomial>(py)?;
    m.add_class::<Expression>(py)?;
    Ok(())
});

py_class!(class VarInfo |py| {
    data var_info: RefCell<structure::VarInfo>;

    def __new__(_cls) -> PyResult<VarInfo> {
        VarInfo::create_instance(py,  RefCell::new(structure::VarInfo::new()))
    }
});

py_class!(class Polynomial |py| {
    data poly: RefCell<polynomial::Polynomial>;
    data var_info: structure::VarInfo;
    def __new__(_cls, arg: &str, var_info: &VarInfo) -> PyResult<Polynomial> {
        let mut e = Element::<String>::from_str(arg).map_err(|m| PyErr::new::<exc::ValueError, _>(py, m))?;
        let mut ne = e.to_element(&mut var_info.var_info(py).borrow_mut());
        ne.normalize_inplace(&var_info.var_info(py).borrow().global_info);

        let poly = polynomial::Polynomial::from(&ne).map_err(|m| PyErr::new::<exc::ValueError, _>(py, m))?;
        Polynomial::create_instance(py, RefCell::new(poly), var_info.var_info(py).borrow().clone())
    }

    def __copy__(&self) -> PyResult<Polynomial> {
        Polynomial::create_instance(py, RefCell::new(self.poly(py).borrow().clone()), self.var_info(py).clone())
    }

    def __str__(&self) -> PyResult<String> {
        Ok(format!("{}", PolyPrinter { poly: &self.poly(py).borrow(), var_info: &self.var_info(py).global_info }))
    }

    def __add__(lhs, rhs) -> PyResult<Polynomial> {
        let lhsp = lhs.extract::<Polynomial>(py)?;
        let rhsp = rhs.extract::<Polynomial>(py)?;

        let r = lhsp.poly(py).borrow().clone().add(rhsp.poly(py).borrow().clone());

        Polynomial::create_instance(py, RefCell::new(r), clone_varmap(&lhsp.var_info(py), &rhsp.var_info(py)))
    }

    def __sub__(lhs, rhs) -> PyResult<Polynomial> {
        let lhsp = lhs.extract::<Polynomial>(py)?;
        let rhsp = rhs.extract::<Polynomial>(py)?;

        let r = lhsp.poly(py).borrow().clone().sub(rhsp.poly(py).borrow().clone());

        Polynomial::create_instance(py, RefCell::new(r), clone_varmap(&lhsp.var_info(py), &rhsp.var_info(py)))
    }

    def div(&self, other: &Polynomial) -> PyResult<Polynomial> {
        let r = self.poly(py).borrow().clone().div(other.poly(py).borrow().clone());

        Polynomial::create_instance(py, RefCell::new(r), clone_varmap(&self.var_info(py), &other.var_info(py)))
    }

    def __mul__(lhs, rhs) -> PyResult<Polynomial> {
        let lhsp = lhs.extract::<Polynomial>(py)?;
        let rhsp = rhs.extract::<Polynomial>(py)?;

        let r = lhsp.poly(py).borrow().clone().mul(rhsp.poly(py).borrow().clone());

        Polynomial::create_instance(py, RefCell::new(r), clone_varmap(&lhsp.var_info(py), &rhsp.var_info(py)))
    }

    def __neg__(&self) -> PyResult<Polynomial> {
        let r = self.poly(py).borrow().clone().neg();
        Polynomial::create_instance(py, RefCell::new(r), self.var_info(py).clone())
    }

    def gcd(&self, other: &Polynomial) -> PyResult<Polynomial> {
        for x in self.poly(py).borrow().poly.coefficients.iter().chain(&other.poly(py).borrow().poly.coefficients) {
            match x {
                Number::SmallRat(..) | Number::BigRat(..) =>
                    return Err(PyErr::new::<exc::ValueError, _>(py, "Cannot take gcd of polynomial with rational coefficients yet. Please have a look at RationalPolynomial.")),
                _ => {}
            }
        }

        // FIXME: we are modifying the original polynomials
        if self.poly(py).as_ptr() != other.poly(py).as_ptr() {
            Polynomial::create_instance(py, RefCell::new(self.poly(py).borrow_mut().gcd(&mut other.poly(py).borrow_mut())),
                clone_varmap(&self.var_info(py), &other.var_info(py)))
        } else {
            let mut c = other.poly(py).borrow().clone();
            Polynomial::create_instance(py, RefCell::new(self.poly(py).borrow_mut().gcd(&mut c)),
                clone_varmap(&self.var_info(py), &other.var_info(py)))
        }
    }

    def to_expression(&self) -> PyResult<Expression> {
        let mut ne = self.poly(py).borrow().to_expression();
        ne.normalize_inplace(&self.var_info(py).global_info);
        Expression::create_instance(py, RefCell::new(ne), self.var_info(py).clone())
    }
});

py_class!(class RationalPolynomial |py| {
    data num: Polynomial;
    data den: Polynomial;
    def __new__(_cls, num: &Polynomial, den: &Polynomial) -> PyResult<RationalPolynomial> {
        let np = num.__copy__(py)?;
        let dp = den.__copy__(py)?;
        polynomial::rationalpolynomial_normalize(&mut np.poly(py).borrow_mut(), &mut dp.poly(py).borrow_mut());

        RationalPolynomial::create_instance(py, np, dp)
    }

    def __copy__(&self) -> PyResult<RationalPolynomial> {
        RationalPolynomial::create_instance(py, self.num(py).__copy__(py)?, self.den(py).__copy__(py)?)
    }

    def __str__(&self) -> PyResult<String> {
        Ok(format!("({})/({})", self.num(py).__str__(py)?, self.den(py).__str__(py)?))
    }

    def __neg__(&self) -> PyResult<RationalPolynomial> {
        let r = self.num(py).clone().__neg__(py)?;
        RationalPolynomial::create_instance(py, r, self.den(py).__copy__(py)?)
    }

    def __mul__(lhs, rhs) -> PyResult<RationalPolynomial> {
        let lhsp = lhs.extract::<RationalPolynomial>(py)?;
        let rhsp = rhs.extract::<RationalPolynomial>(py)?;

        let num = lhsp.num(py).__copy__(py)?;
        let den = lhsp.den(py).__copy__(py)?;
        let num1 = rhsp.num(py).__copy__(py)?;
        let den1 = rhsp.den(py).__copy__(py)?;

        polynomial::rationalpolynomial_mul(&mut num.poly(py).borrow_mut(),
            &mut den.poly(py).borrow_mut(),
            &mut num1.poly(py).borrow_mut(),
            &mut den1.poly(py).borrow_mut());

        RationalPolynomial::create_instance(py, num, den)
    }

    def __add__(lhs, rhs) -> PyResult<RationalPolynomial> {
        let lhsp = lhs.extract::<RationalPolynomial>(py)?;
        let rhsp = rhs.extract::<RationalPolynomial>(py)?;

        let num = lhsp.num(py).__copy__(py)?;
        let den = lhsp.den(py).__copy__(py)?;
        let num1 = rhsp.num(py).__copy__(py)?;
        let den1 = rhsp.den(py).__copy__(py)?;

        polynomial::rationalpolynomial_add(&mut num.poly(py).borrow_mut(),
            &mut den.poly(py).borrow_mut(),
            &mut num1.poly(py).borrow_mut(),
            &mut den1.poly(py).borrow_mut());

        RationalPolynomial::create_instance(py, num, den)
    }

    def __sub__(lhs, rhs) -> PyResult<RationalPolynomial> {
        let lhsp = lhs.extract::<RationalPolynomial>(py)?;
        let rhsp = rhs.extract::<RationalPolynomial>(py)?;

        let num = lhsp.num(py).__copy__(py)?;
        let den = lhsp.den(py).__copy__(py)?;
        let num1 = rhsp.num(py).__copy__(py)?;
        let den1 = rhsp.den(py).__copy__(py)?;

        polynomial::rationalpolynomial_sub(&mut num.poly(py).borrow_mut(),
            &mut den.poly(py).borrow_mut(),
            &mut num1.poly(py).borrow_mut(),
            &mut den1.poly(py).borrow_mut());

        RationalPolynomial::create_instance(py, num, den)
    }

    def div(&self, rhs: &RationalPolynomial) -> PyResult<RationalPolynomial> {
        let num = self.num(py).__copy__(py)?;
        let den = self.den(py).__copy__(py)?;
        let num1 = rhs.num(py).__copy__(py)?;
        let den1 = rhs.den(py).__copy__(py)?;

        polynomial::rationalpolynomial_div(&mut num.poly(py).borrow_mut(),
            &mut den.poly(py).borrow_mut(),
            &mut num1.poly(py).borrow_mut(),
            &mut den1.poly(py).borrow_mut());

        RationalPolynomial::create_instance(py, num, den)
    }

});

py_class!(class Expression |py| {
    data expr: RefCell<Element>;
    data var_info: structure::VarInfo;
    def __new__(_cls, arg: &str, var_info: &VarInfo) -> PyResult<Expression> {
        let mut e = Element::<String>::from_str(arg).map_err(|m| PyErr::new::<exc::ValueError, _>(py, m))?;
        let mut ne = e.to_element(&mut var_info.var_info(py).borrow_mut());
        ne.normalize_inplace(&var_info.var_info(py).borrow().global_info);

        Expression::create_instance(py, RefCell::new(ne), var_info.var_info(py).borrow().clone())
    }

    def __copy__(&self) -> PyResult<Expression> {
        Expression::create_instance(py, RefCell::new(self.expr(py).borrow().clone()), self.var_info(py).clone())
    }

    def __str__(&self) -> PyResult<String> {
        Ok(format!("{}",  ElementPrinter { element: &self.expr(py).borrow(), var_info: &self.var_info(py).global_info, print_mode: PrintMode::Form }))
    }

    def __add__(lhs, rhs) -> PyResult<Expression> {
        let lhsp = lhs.extract::<Expression>(py)?;
        let rhsp = rhs.extract::<Expression>(py)?;

        let mut r = Element::SubExpr(true, vec![lhsp.expr(py).borrow().clone(), rhsp.expr(py).borrow().clone()]);
        let vi = clone_varmap(&lhsp.var_info(py), &rhsp.var_info(py));
        r.normalize_inplace(&vi.global_info);

        Expression::create_instance(py, RefCell::new(r), vi)
    }

    def __sub__(lhs, rhs) -> PyResult<Expression> {
        let lhsp = lhs.extract::<Expression>(py)?;
        let rhsp = rhs.extract::<Expression>(py)?;

        let mut r = Element::SubExpr(true, vec![lhsp.expr(py).borrow().clone(),
                        Element::Term(true, vec![rhsp.expr(py).borrow().clone(), Element::Num(false, Number::SmallInt(-1))])]);
        let vi = clone_varmap(&lhsp.var_info(py), &rhsp.var_info(py));
        r.normalize_inplace(&vi.global_info);

        Expression::create_instance(py, RefCell::new(r), vi)
    }

    def __mul__(lhs, rhs) -> PyResult<Expression> {
        let lhsp = lhs.extract::<Expression>(py)?;
        let rhsp = rhs.extract::<Expression>(py)?;

        let mut r = Element::Term(true, vec![lhsp.expr(py).borrow().clone(), rhsp.expr(py).borrow().clone()]);
        let vi = clone_varmap(&lhsp.var_info(py), &rhsp.var_info(py));
        r.normalize_inplace(&vi.global_info);

        Expression::create_instance(py, RefCell::new(r), vi)
    }

    def __neg__(&self) -> PyResult<Expression> {
        let mut r = Element::Term(true, vec![self.expr(py).borrow().clone(), Element::Num(false, Number::SmallInt(-1))]);
        r.normalize_inplace(&self.var_info(py).global_info);
        Expression::create_instance(py, RefCell::new(r), self.var_info(py).clone())
    }

    def expand(&self) -> PyResult<Expression> {
        let r = self.expr(py).borrow().clone().expand(&self.var_info(py).global_info);
        Expression::create_instance(py, RefCell::new(r), self.var_info(py).clone())
    }

    def id(&self, lhs: &str, rhs: &str, var_info: &VarInfo) -> PyResult<Expression> {
        let mut lhs = Element::<String>::from_str(lhs)
                        .map_err(|m| PyErr::new::<exc::ValueError, _>(py, m))?
                        .to_element(&mut var_info.var_info(py).borrow_mut());
        lhs.normalize_inplace(&var_info.var_info(py).borrow().global_info);

        let mut rhs = Element::<String>::from_str(rhs)
                        .map_err(|m| PyErr::new::<exc::ValueError, _>(py, m))?
                        .to_element(&mut var_info.var_info(py).borrow_mut());
        rhs.normalize_inplace(&var_info.var_info(py).borrow().global_info);

        let e = &self.expr(py).borrow();

        let bi = BorrowedVarInfo {
            global_info: &self.var_info(py).global_info,
            local_info: &self.var_info(py).local_info
        } ;

        let v = match **e {
            Element::SubExpr(_, ref ts) => ts.iter().collect(),
            _ => vec![&**e]
        };


        let ids = IdentityStatement {
            mode: IdentityStatementMode::Many,
            lhs,
            rhs,
            contains_dollar: false
        };

        let mut res = vec![];
        for term in v {
            let mut idsi = ids.to_iter(term, &bi);
            loop {
                match idsi.next() {
                    StatementResult::Executed(r) | StatementResult::NotExecuted(r) => res.push(r.clone()),
                    StatementResult::NoChange => {res.push(term.clone()); break},
                    StatementResult::Done => {break}
                }
            }
        }

        let mut r = Element::SubExpr(true, res);
        r.normalize_inplace(&self.var_info(py).global_info);
        Expression::create_instance(py, RefCell::new(r), var_info.var_info(py).borrow().clone())
    }

    def to_polynomial(&self) -> PyResult<Polynomial> {
        let poly = polynomial::Polynomial::from(&self.expr(py).borrow()).map_err(|m| PyErr::new::<exc::ValueError, _>(py, m))?;
        Polynomial::create_instance(py, RefCell::new(poly), self.var_info(py).clone())
    }

});
