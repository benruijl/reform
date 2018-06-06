use cpython::PyResult;
use poly::polynomial;
use poly::polynomial::PolyPrinter;
use std::cell::RefCell;
use std::ops::{Add, Mul};
use std::str::FromStr;
use structure::{Element, GlobalVarInfo, VarInfo};

py_module_initializer!(reform, initreform, PyInit_reform, |py, m| {
    m.add(
        py,
        "__doc__",
        "A module for interaction with reform expressions",
    )?;
    m.add_class::<Polynomial>(py)?;
    Ok(())
});

py_class!(class Polynomial |py| {
    data poly: RefCell<polynomial::Polynomial>;
    data var_info: GlobalVarInfo;
    def __new__(_cls, arg: &str) -> PyResult<Polynomial> {
        let mut e = Element::<String>::from_str(arg).unwrap(); // TODO: convert to PyResult
        let mut vi = VarInfo::new();
        let mut ne = e.to_element(&mut vi);
        ne.normalize_inplace(&vi.global_info);

        let poly = polynomial::Polynomial::from(&ne).unwrap();
        Polynomial::create_instance(py, RefCell::new(poly), vi.global_info)
    }

    def __str__(&self) -> PyResult<String> {
        Ok(format!("{}", PolyPrinter { poly: &self.poly(py).borrow(), var_info: &self.var_info(py) }))
    }

    def __add__(lhs, rhs) -> PyResult<Polynomial> {
        let lhsp = lhs.extract::<Polynomial>(py)?;
        let rhsp = rhs.extract::<Polynomial>(py)?;

        // unify the variable names first
        lhsp.poly(py).borrow_mut().unify_varmaps(&mut rhsp.poly(py).borrow_mut());
        let r = lhsp.poly(py).borrow().clone().add(rhsp.poly(py).borrow().clone());

        Polynomial::create_instance(py, RefCell::new(r), lhsp.var_info(py).clone())
    }

    def __mul__(lhs, rhs) -> PyResult<Polynomial> {
        let lhsp = lhs.extract::<Polynomial>(py)?;
        let rhsp = rhs.extract::<Polynomial>(py)?;

        // unify the variable names first
        lhsp.poly(py).borrow_mut().unify_varmaps(&mut rhsp.poly(py).borrow_mut());
        let r = lhsp.poly(py).borrow().clone().mul(rhsp.poly(py).borrow().clone());

        Polynomial::create_instance(py, RefCell::new(r), lhsp.var_info(py).clone())
    }

    def gcd(&self, other: &Polynomial) -> PyResult<Polynomial> {
       Polynomial::create_instance(py, RefCell::new(self.poly(py).borrow_mut().gcd(&mut other.poly(py).borrow_mut())), self.var_info(py).clone())
    }
});
