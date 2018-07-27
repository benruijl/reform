use libc::c_char;
use poly::polynomial;
use poly::polynomial::PolyPrinter;
use std::ffi::{CStr, CString};
use std::ops::{Add, Div, Mul, Neg, Sub};
use std::str;
use std::str::FromStr;
use structure::{Element, VarInfo};

#[derive(Clone)]
pub struct Polynomial<'a> {
    poly: polynomial::Polynomial,
    var_info: &'a VarInfo,
}

#[derive(Clone)]
pub struct RationalPolynomial<'a> {
    num: Polynomial<'a>,
    den: Polynomial<'a>,
}

impl<'a> RationalPolynomial<'a> {
    fn from_poly(mut num: Polynomial<'a>, mut den: Polynomial<'a>) -> RationalPolynomial<'a> {
        assert_eq!(
            &num.var_info.global_info as *const _,
            &den.var_info.global_info as *const _
        );

        polynomial::rationalpolynomial_normalize(num, den);

        // will also unify varmaps
        let gcd = num.gcd(&mut den);
        // FIXME: this looks horrible. done to avoid copying
        num.poly.poly = num.poly.poly.divmod(&gcd.poly.poly).0;
        den.poly.poly = den.poly.poly.divmod(&gcd.poly.poly).0;

        RationalPolynomial { num, den }
    }

    fn to_string(&self) -> String {
        format!("({})/({})", self.num.to_string(), self.den.to_string())
    }

    fn neg(&self) -> RationalPolynomial {
        RationalPolynomial {
            num: self.num.neg(),
            den: self.den.clone(),
        }
    }

    fn add(&self, rhs: &RationalPolynomial) -> RationalPolynomial<'a> {
        let mut l = self.clone();
        let mut r = rhs.clone();
        // TODO: unify?
        polynomial::rationalpolynomial_add(
            &mut l.num.poly,
            &mut l.den.poly,
            &mut r.num.poly,
            &mut r.den.poly,
        );
        l
    }

    fn sub(&self, rhs: &RationalPolynomial) -> RationalPolynomial<'a> {
        let mut l = self.clone();
        let mut r = rhs.clone();
        // TODO: unify?
        polynomial::rationalpolynomial_sub(
            &mut l.num.poly,
            &mut l.den.poly,
            &mut r.num.poly,
            &mut r.den.poly,
        );
        l
    }

    fn mul(&self, rhs: &RationalPolynomial) -> RationalPolynomial<'a> {
        let mut l = self.clone();
        let mut r = rhs.clone();
        // TODO: unify?
        polynomial::rationalpolynomial_mul(
            &mut l.num.poly,
            &mut l.den.poly,
            &mut r.num.poly,
            &mut r.den.poly,
        );
        l
    }

    fn div(&self, rhs: &RationalPolynomial) -> RationalPolynomial<'a> {
        let mut l = self.clone();
        let mut r = rhs.clone();
        // TODO: unify?
        polynomial::rationalpolynomial_div(
            &mut l.num.poly,
            &mut l.den.poly,
            &mut r.num.poly,
            &mut r.den.poly,
        );
        l
    }
}

impl<'a> Polynomial<'a> {
    fn new(expr: &str, var_info: &'a mut VarInfo) -> Polynomial<'a> {
        let mut e = Element::<String>::from_str(expr).unwrap();
        let mut ne = e.to_element(var_info);
        ne.normalize_inplace(&var_info.global_info);

        let poly = polynomial::Polynomial::from(&ne).unwrap();
        Polynomial { poly, var_info }
    }

    fn add(&self, rhs: &Polynomial) -> Polynomial<'a> {
        let r = self.poly.clone().add(rhs.poly.clone());

        Polynomial {
            poly: r,
            var_info: self.var_info,
        }
    }

    fn sub(&self, rhs: &Polynomial) -> Polynomial<'a> {
        let r = self.poly.clone().sub(rhs.poly.clone());

        Polynomial {
            poly: r,
            var_info: self.var_info,
        }
    }

    fn div(&self, rhs: &Polynomial) -> Polynomial<'a> {
        let r = self.poly.clone().div(rhs.poly.clone());

        Polynomial {
            poly: r,
            var_info: self.var_info,
        }
    }

    fn mul(&self, rhs: &Polynomial) -> Polynomial<'a> {
        let r = self.poly.clone().mul(rhs.poly.clone());

        Polynomial {
            poly: r,
            var_info: self.var_info,
        }
    }

    fn gcd(&self, rhs: &Polynomial) -> Polynomial<'a> {
        let r = self.poly.clone().gcd(&mut rhs.poly.clone());
        Polynomial {
            poly: r,
            var_info: self.var_info,
        }
    }

    fn neg(&self) -> Polynomial {
        Polynomial {
            poly: self.poly.clone().neg(),
            var_info: self.var_info,
        }
    }

    fn to_string(&self) -> String {
        format!(
            "{}",
            PolyPrinter {
                poly: &self.poly,
                var_info: &self.var_info.global_info
            }
        )
    }
}

#[no_mangle]
pub extern "C" fn polynomial_varinfo() -> *mut VarInfo {
    Box::into_raw(Box::new(VarInfo::new()))
}

#[no_mangle]
pub extern "C" fn polynomial_varinfo_free(ptr: *mut VarInfo) {
    if ptr.is_null() {
        return;
    }
    unsafe {
        Box::from_raw(ptr);
    }
}

#[no_mangle]
pub extern "C" fn polynomial_new<'a>(
    cexpr: *const c_char,
    cvar_info: *mut VarInfo,
) -> *mut Polynomial<'a> {
    let expr = unsafe {
        assert!(!cexpr.is_null());
        CStr::from_ptr(cexpr)
    };
    let expr = expr.to_str().unwrap();

    let var_info = unsafe {
        assert!(!cvar_info.is_null());
        &mut *cvar_info
    };

    Box::into_raw(Box::new(Polynomial::new(expr, var_info)))
}

#[no_mangle]
pub extern "C" fn polynomial_free(ptr: *mut Polynomial) {
    if ptr.is_null() {
        return;
    }
    unsafe {
        Box::from_raw(ptr);
    }
}

#[no_mangle]
pub extern "C" fn polynomial_to_string(ptr: *const Polynomial) -> *mut c_char {
    let poly = unsafe {
        assert!(!ptr.is_null());
        &*ptr
    };

    let c_str_poly = CString::new(poly.to_string()).unwrap();
    c_str_poly.into_raw()
}

#[no_mangle]
pub extern "C" fn polynomial_string_free(s: *mut c_char) {
    unsafe {
        if s.is_null() {
            return;
        }
        CString::from_raw(s)
    };
}

#[no_mangle]
pub extern "C" fn polynomial_clone<'a>(poly: *const Polynomial<'a>) -> *const Polynomial<'a> {
    let polyp = unsafe {
        assert!(!poly.is_null());
        &*poly
    };

    Box::into_raw(Box::new(polyp.clone()))
}

#[no_mangle]
pub extern "C" fn polynomial_add<'a>(
    lhs: *const Polynomial<'a>,
    rhs: *const Polynomial<'a>,
) -> *mut Polynomial<'a> {
    let lhsp = unsafe {
        assert!(!lhs.is_null());
        &*lhs
    };

    let rhsp = unsafe {
        assert!(!rhs.is_null());
        &*rhs
    };

    Box::into_raw(Box::new(lhsp.add(rhsp)))
}

#[no_mangle]
pub extern "C" fn polynomial_sub<'a>(
    lhs: *const Polynomial<'a>,
    rhs: *const Polynomial<'a>,
) -> *const Polynomial<'a> {
    let lhsp = unsafe {
        assert!(!lhs.is_null());
        &*lhs
    };

    let rhsp = unsafe {
        assert!(!rhs.is_null());
        &*rhs
    };

    Box::into_raw(Box::new(lhsp.sub(rhsp)))
}

#[no_mangle]
pub extern "C" fn polynomial_div<'a>(
    lhs: *const Polynomial<'a>,
    rhs: *const Polynomial<'a>,
) -> *mut Polynomial<'a> {
    let lhsp = unsafe {
        assert!(!lhs.is_null());
        &*lhs
    };

    let rhsp = unsafe {
        assert!(!rhs.is_null());
        &*rhs
    };

    Box::into_raw(Box::new(lhsp.div(rhsp)))
}

#[no_mangle]
pub extern "C" fn polynomial_mul<'a>(
    lhs: *const Polynomial<'a>,
    rhs: *const Polynomial<'a>,
) -> *const Polynomial<'a> {
    let lhsp = unsafe {
        assert!(!lhs.is_null());
        &*lhs
    };

    let rhsp = unsafe {
        assert!(!rhs.is_null());
        &*rhs
    };

    Box::into_raw(Box::new(lhsp.mul(rhsp)))
}

#[no_mangle]
pub extern "C" fn polynomial_neg<'a>(lhs: *const Polynomial<'a>) -> *const Polynomial<'a> {
    let lhsp = unsafe {
        assert!(!lhs.is_null());
        &*lhs
    };

    Box::into_raw(Box::new(lhsp.neg()))
}

#[no_mangle]
pub extern "C" fn polynomial_gcd<'a>(
    lhs: *const Polynomial<'a>,
    rhs: *const Polynomial<'a>,
) -> *const Polynomial<'a> {
    let lhsp = unsafe {
        assert!(!lhs.is_null());
        &*lhs
    };

    let rhsp = unsafe {
        assert!(!rhs.is_null());
        &*rhs
    };

    Box::into_raw(Box::new(lhsp.gcd(rhsp)))
}

#[no_mangle]
pub extern "C" fn rationalpolynomial_new<'a>(
    num: *const Polynomial<'a>,
    den: *const Polynomial<'a>,
) -> *mut RationalPolynomial<'a> {
    let nump = unsafe {
        assert!(!num.is_null());
        &*num
    };

    let denp = unsafe {
        assert!(!den.is_null());
        &*den
    };

    Box::into_raw(Box::new(RationalPolynomial::from_poly(
        nump.clone(),
        denp.clone(),
    )))
}

#[no_mangle]
pub extern "C" fn rationalpolynomial_free(ptr: *mut RationalPolynomial) {
    if ptr.is_null() {
        return;
    }
    unsafe {
        Box::from_raw(ptr);
    }
}

#[no_mangle]
pub extern "C" fn rationalpolynomial_clone<'a>(
    poly: *const RationalPolynomial<'a>,
) -> *const RationalPolynomial<'a> {
    let polyp = unsafe {
        assert!(!poly.is_null());
        &*poly
    };

    Box::into_raw(Box::new(polyp.clone()))
}

#[no_mangle]
pub extern "C" fn rationalpolynomial_to_string(ptr: *const RationalPolynomial) -> *mut c_char {
    let poly = unsafe {
        assert!(!ptr.is_null());
        &*ptr
    };

    let c_str_poly = CString::new(poly.to_string()).unwrap();
    c_str_poly.into_raw()
}

#[no_mangle]
pub extern "C" fn rationalpolynomial_neg<'a>(
    lhs: *const RationalPolynomial<'a>,
) -> *const RationalPolynomial<'a> {
    let lhsp = unsafe {
        assert!(!lhs.is_null());
        &*lhs
    };

    Box::into_raw(Box::new(lhsp.neg()))
}

#[no_mangle]
pub extern "C" fn rationalpolynomial_add<'a>(
    lhs: *const RationalPolynomial<'a>,
    rhs: *const RationalPolynomial<'a>,
) -> *const RationalPolynomial<'a> {
    let lhsp = unsafe {
        assert!(!lhs.is_null());
        &*lhs
    };

    let rhsp = unsafe {
        assert!(!rhs.is_null());
        &*rhs
    };

    Box::into_raw(Box::new(lhsp.add(rhsp)))
}

#[no_mangle]
pub extern "C" fn rationalpolynomial_sub<'a>(
    lhs: *const RationalPolynomial<'a>,
    rhs: *const RationalPolynomial<'a>,
) -> *const RationalPolynomial<'a> {
    let lhsp = unsafe {
        assert!(!lhs.is_null());
        &*lhs
    };

    let rhsp = unsafe {
        assert!(!rhs.is_null());
        &*rhs
    };

    Box::into_raw(Box::new(lhsp.sub(rhsp)))
}

#[no_mangle]
pub extern "C" fn rationalpolynomial_mul<'a>(
    lhs: *const RationalPolynomial<'a>,
    rhs: *const RationalPolynomial<'a>,
) -> *const RationalPolynomial<'a> {
    let lhsp = unsafe {
        assert!(!lhs.is_null());
        &*lhs
    };

    let rhsp = unsafe {
        assert!(!rhs.is_null());
        &*rhs
    };

    Box::into_raw(Box::new(lhsp.mul(rhsp)))
}

#[no_mangle]
pub extern "C" fn rationalpolynomial_div<'a>(
    lhs: *const RationalPolynomial<'a>,
    rhs: *const RationalPolynomial<'a>,
) -> *const RationalPolynomial<'a> {
    let lhsp = unsafe {
        assert!(!lhs.is_null());
        &*lhs
    };

    let rhsp = unsafe {
        assert!(!rhs.is_null());
        &*rhs
    };

    Box::into_raw(Box::new(lhsp.div(rhsp)))
}
