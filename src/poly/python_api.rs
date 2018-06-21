use cpython::PyResult;
use poly::polynomial;
use poly::polynomial::PolyPrinter;
use std::cell::RefCell;
use std::ops::{Add, Div, Mul, Neg, Sub};
use std::str::FromStr;
use structure;
use structure::Element;

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
        let mut e = Element::<String>::from_str(arg).unwrap(); // TODO: convert to PyResult
        let mut ne = e.to_element(&mut var_info.var_info(py).borrow_mut());
        ne.normalize_inplace(&var_info.var_info(py).borrow().global_info);

        let poly = polynomial::Polynomial::from(&ne).unwrap();
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

        // unify the variable names first if lhs != rhs
        if lhsp.poly(py).as_ptr() != rhsp.poly(py).as_ptr() {
            lhsp.poly(py).borrow_mut().unify_varmaps(&mut rhsp.poly(py).borrow_mut());
        }
        let r = lhsp.poly(py).borrow().clone().add(rhsp.poly(py).borrow().clone());

        Polynomial::create_instance(py, RefCell::new(r), clone_varmap(&lhsp.var_info(py), &rhsp.var_info(py)))
    }

    def __sub__(lhs, rhs) -> PyResult<Polynomial> {
        let lhsp = lhs.extract::<Polynomial>(py)?;
        let rhsp = rhs.extract::<Polynomial>(py)?;

        // unify the variable names first if lhs != rhs
        if lhsp.poly(py).as_ptr() != rhsp.poly(py).as_ptr() {
            lhsp.poly(py).borrow_mut().unify_varmaps(&mut rhsp.poly(py).borrow_mut());
        }
        let r = lhsp.poly(py).borrow().clone().sub(rhsp.poly(py).borrow().clone());

        Polynomial::create_instance(py, RefCell::new(r), clone_varmap(&lhsp.var_info(py), &rhsp.var_info(py)))
    }

    def div(&self, other: &Polynomial) -> PyResult<Polynomial> {
        // unify the variable names first if lhs != rhs
        if self.poly(py).as_ptr() != other.poly(py).as_ptr() {
            self.poly(py).borrow_mut().unify_varmaps(&mut other.poly(py).borrow_mut());
        }
        let r = self.poly(py).borrow().clone().div(other.poly(py).borrow().clone());

        Polynomial::create_instance(py, RefCell::new(r), clone_varmap(&self.var_info(py), &other.var_info(py)))
    }

    def __mul__(lhs, rhs) -> PyResult<Polynomial> {
        let lhsp = lhs.extract::<Polynomial>(py)?;
        let rhsp = rhs.extract::<Polynomial>(py)?;

        // unify the variable names first if lhs != rhs
        if lhsp.poly(py).as_ptr() != rhsp.poly(py).as_ptr() {
            lhsp.poly(py).borrow_mut().unify_varmaps(&mut rhsp.poly(py).borrow_mut());
        }
        let r = lhsp.poly(py).borrow().clone().mul(rhsp.poly(py).borrow().clone());

        Polynomial::create_instance(py, RefCell::new(r), clone_varmap(&lhsp.var_info(py), &rhsp.var_info(py)))
    }

    def __neg__(&self) -> PyResult<Polynomial> {
        let r = self.poly(py).borrow().clone().neg();
        Polynomial::create_instance(py, RefCell::new(r), self.var_info(py).clone())
    }

    def gcd(&self, other: &Polynomial) -> PyResult<Polynomial> {
        if self.poly(py).as_ptr() != other.poly(py).as_ptr() {
            Polynomial::create_instance(py, RefCell::new(self.poly(py).borrow_mut().gcd(&mut other.poly(py).borrow_mut())),
                clone_varmap(&self.var_info(py), &other.var_info(py)))
        } else {
            let mut c = other.poly(py).borrow().clone(); // TODO: move the varmap merge out of the gcd routine, so we don't have to copy
            Polynomial::create_instance(py, RefCell::new(self.poly(py).borrow_mut().gcd(&mut c)),
                clone_varmap(&self.var_info(py), &other.var_info(py)))
        }
    }
});
