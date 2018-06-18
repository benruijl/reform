use libc::c_char;
use poly::polynomial;
use poly::polynomial::PolyPrinter;
use std::ffi::{CStr, CString};
use std::ops::{Add, Div, Mul, Neg, Sub};
use std::str;
use std::str::FromStr;
use structure::{Element, VarInfo};

pub struct Polynomial<'a> {
    poly: polynomial::Polynomial,
    var_info: &'a VarInfo,
}

impl<'a> Polynomial<'a> {
    fn new(expr: &str, var_info: &'a mut VarInfo) -> Polynomial<'a> {
        let mut e = Element::<String>::from_str(expr).unwrap();
        let mut ne = e.to_element(var_info);
        ne.normalize_inplace(&var_info.global_info);

        let poly = polynomial::Polynomial::from(&ne).unwrap();
        Polynomial { poly, var_info }
    }

    fn add(&mut self, rhs: &mut Polynomial) -> Polynomial<'a> {
        // unify the variable names first
        self.poly.unify_varmaps(&mut rhs.poly);
        let r = self.poly.clone().add(rhs.poly.clone());

        Polynomial {
            poly: r,
            var_info: self.var_info,
        }
    }

    fn sub(&mut self, rhs: &mut Polynomial) -> Polynomial<'a> {
        // unify the variable names first
        self.poly.unify_varmaps(&mut rhs.poly);
        let r = self.poly.clone().sub(rhs.poly.clone());

        Polynomial {
            poly: r,
            var_info: self.var_info,
        }
    }

    fn div(&mut self, rhs: &mut Polynomial) -> Polynomial<'a> {
        // unify the variable names first
        self.poly.unify_varmaps(&mut rhs.poly);
        let r = self.poly.clone().div(rhs.poly.clone());

        Polynomial {
            poly: r,
            var_info: self.var_info,
        }
    }

    fn mul(&mut self, rhs: &mut Polynomial) -> Polynomial<'a> {
        // unify the variable names first
        self.poly.unify_varmaps(&mut rhs.poly);
        let r = self.poly.clone().mul(rhs.poly.clone());

        Polynomial {
            poly: r,
            var_info: self.var_info,
        }
    }

    fn gcd(&mut self, rhs: &mut Polynomial) -> Polynomial<'a> {
        let r = self.poly.gcd(&mut rhs.poly);
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
pub extern "C" fn polynomial_to_string(ptr: *mut Polynomial) -> *mut c_char {
    let poly = unsafe {
        assert!(!ptr.is_null());
        &mut *ptr
    };

    // TODO: this string must be freed too
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
pub extern "C" fn polynomial_add<'a>(
    lhs: *mut Polynomial<'a>,
    rhs: *mut Polynomial<'a>,
) -> *mut Polynomial<'a> {
    let lhsp = unsafe {
        assert!(!lhs.is_null());
        &mut *lhs
    };

    let rhsp = unsafe {
        assert!(!rhs.is_null());
        &mut *rhs
    };

    Box::into_raw(Box::new(lhsp.add(rhsp)))
}

#[no_mangle]
pub extern "C" fn polynomial_sub<'a>(
    lhs: *mut Polynomial<'a>,
    rhs: *mut Polynomial<'a>,
) -> *mut Polynomial<'a> {
    let lhsp = unsafe {
        assert!(!lhs.is_null());
        &mut *lhs
    };

    let rhsp = unsafe {
        assert!(!rhs.is_null());
        &mut *rhs
    };

    Box::into_raw(Box::new(lhsp.sub(rhsp)))
}

#[no_mangle]
pub extern "C" fn polynomial_div<'a>(
    lhs: *mut Polynomial<'a>,
    rhs: *mut Polynomial<'a>,
) -> *mut Polynomial<'a> {
    let lhsp = unsafe {
        assert!(!lhs.is_null());
        &mut *lhs
    };

    let rhsp = unsafe {
        assert!(!rhs.is_null());
        &mut *rhs
    };

    Box::into_raw(Box::new(lhsp.div(rhsp)))
}

#[no_mangle]
pub extern "C" fn polynomial_mul<'a>(
    lhs: *mut Polynomial<'a>,
    rhs: *mut Polynomial<'a>,
) -> *mut Polynomial<'a> {
    let lhsp = unsafe {
        assert!(!lhs.is_null());
        &mut *lhs
    };

    let rhsp = unsafe {
        assert!(!rhs.is_null());
        &mut *rhs
    };

    Box::into_raw(Box::new(lhsp.mul(rhsp)))
}

#[no_mangle]
pub extern "C" fn polynomial_neg<'a>(lhs: *mut Polynomial<'a>) -> *mut Polynomial<'a> {
    let lhsp = unsafe {
        assert!(!lhs.is_null());
        &mut *lhs
    };

    Box::into_raw(Box::new(lhsp.neg()))
}

#[no_mangle]
pub extern "C" fn polynomial_gcd<'a>(
    lhs: *mut Polynomial<'a>,
    rhs: *mut Polynomial<'a>,
) -> *mut Polynomial<'a> {
    let lhsp = unsafe {
        assert!(!lhs.is_null());
        &mut *lhs
    };

    let rhsp = unsafe {
        assert!(!rhs.is_null());
        &mut *rhs
    };

    Box::into_raw(Box::new(lhsp.gcd(rhsp)))
}
