use libc::c_char;
use poly::polynomial;
use poly::polynomial::PolyPrinter;
use std::ffi::{CStr, CString};
use std::ops::{Add, Mul};
use std::str;
use std::str::FromStr;
use structure::{Element, GlobalVarInfo, VarInfo};

pub struct Polynomial {
    poly: polynomial::Polynomial,
    var_info: GlobalVarInfo,
}

impl Polynomial {
    fn new(expr: &str) -> Polynomial {
        let mut e = Element::<String>::from_str(expr).unwrap();
        let mut vi = VarInfo::new();
        let mut ne = e.to_element(&mut vi);
        ne.normalize_inplace(&vi.global_info);

        let poly = polynomial::Polynomial::from(&ne).unwrap();
        Polynomial {
            poly,
            var_info: vi.global_info,
        }
    }

    fn add(&mut self, rhs: &mut Polynomial) -> Polynomial {
        // unify the variable names first
        self.poly.unify_varmaps(&mut rhs.poly);
        let r = self.poly.clone().add(rhs.poly.clone());

        Polynomial {
            poly: r,
            var_info: self.var_info.clone(),
        }
    }

    fn mul(&mut self, rhs: &mut Polynomial) -> Polynomial {
        // unify the variable names first
        self.poly.unify_varmaps(&mut rhs.poly);
        let r = self.poly.clone().mul(rhs.poly.clone());

        Polynomial {
            poly: r,
            var_info: self.var_info.clone(),
        }
    }

    fn gcd(&mut self, rhs: &mut Polynomial) -> Polynomial {
        let r = self.poly.gcd(&mut rhs.poly);
        Polynomial {
            poly: r,
            var_info: self.var_info.clone(),
        }
    }

    fn to_string(&self) -> String {
        format!(
            "{}",
            PolyPrinter {
                poly: &self.poly,
                var_info: &self.var_info
            }
        )
    }
}

#[no_mangle]
pub extern "C" fn polynomial_new(cexpr: *const c_char) -> *mut Polynomial {
    let expr = unsafe {
        assert!(!cexpr.is_null());
        CStr::from_ptr(cexpr)
    };
    let expr = expr.to_str().unwrap();

    Box::into_raw(Box::new(Polynomial::new(expr)))
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
pub extern "C" fn polynomial_add(lhs: *mut Polynomial, rhs: *mut Polynomial) -> *mut Polynomial {
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
pub extern "C" fn polynomial_mul(lhs: *mut Polynomial, rhs: *mut Polynomial) -> *mut Polynomial {
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
pub extern "C" fn polynomial_gcd(lhs: *mut Polynomial, rhs: *mut Polynomial) -> *mut Polynomial {
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
