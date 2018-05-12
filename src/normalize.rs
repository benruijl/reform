use num_traits::{One, Pow, Zero};
use number::Number;
use poly::polynomial::Polynomial;
use std::cmp::Ordering;
use std::mem;
use std::ptr;
use structure::{Element, FunctionAttributes, GlobalVarInfo, FUNCTION_DELTA, FUNCTION_GCD,
                FUNCTION_MUL, FUNCTION_NARGS, FUNCTION_RAT, FUNCTION_SUM};
use tools::add_num_poly;

impl Element {
    // TODO: return iterator over Elements for ground level?
    /// Apply builtin-functions, such as `delta_` and `nargs_`.
    /// This function should be called during normalization.
    pub fn apply_builtin_functions(
        &mut self,
        var_info: &GlobalVarInfo,
        _ground_level: bool,
    ) -> bool {
        *self = match *self {
            Element::Fn(_, ref mut n, ref mut a) => {
                match *n {
                    FUNCTION_DELTA => {
                        if a.len() == 1 {
                            match a[0] {
                                Element::Num(_, Number::SmallInt(0)) => {
                                    Element::Num(false, Number::one())
                                }
                                _ => Element::Num(false, Number::zero()),
                            }
                        } else {
                            return false;
                        }
                    }
                    FUNCTION_NARGS => {
                        // get the number of arguments
                        Element::Num(false, Number::SmallInt(a.len() as isize))
                    }
                    FUNCTION_SUM | FUNCTION_MUL => {
                        if a.len() == 4 {
                            match (&a[1], &a[2]) {
                                (
                                    &Element::Num(_, Number::SmallInt(n1)),
                                    &Element::Num(_, Number::SmallInt(n2)),
                                ) => {
                                    let mut terms = vec![];
                                    for i in n1..n2 {
                                        let mut ne = a[3].clone();
                                        ne.replace(
                                            &a[0],
                                            &Element::Num(false, Number::SmallInt(i)),
                                        );
                                        terms.push(ne);
                                    }
                                    if *n == FUNCTION_SUM {
                                        Element::SubExpr(true, terms)
                                    } else {
                                        Element::Term(true, terms)
                                    }
                                }
                                _ => return false,
                            }
                        } else {
                            return false;
                        }
                    }
                    FUNCTION_RAT => {
                        if a.len() > 2 {
                            return false;
                        }

                        // convert to polyratfun if possible
                        // TODO: what to do with variable mappings?
                        // we don't want an enormous array
                        if a.len() == 1 {
                            if let Ok(mut prf) = Polynomial::from(&a[0]) {
                                let mut one = prf.cloned_one();
                                prf.unify_varmaps(&mut one); // make sure the variables are shared
                                Element::RationalPolynomialCoefficient(false, Box::new((prf, one)))
                            } else {
                                return false;
                            }
                        } else {
                            match Polynomial::from(&a[0]) {
                                Ok(mut num) => match Polynomial::from(&a[1]) {
                                    Ok(mut den) => {
                                        num.unify_varmaps(&mut den); // make sure the variables are shared
                                        Element::RationalPolynomialCoefficient(
                                            false,
                                            Box::new((num, den)),
                                        )
                                    }
                                    _ => return false,
                                },
                                _ => return false,
                            }
                        }
                    }
                    FUNCTION_GCD => {
                        if a.len() != 2 {
                            return false;
                        }

                        let mut ar = Polynomial::from(&a[0]);
                        let mut br = Polynomial::from(&a[1]);

                        if let (Ok(mut a1), Ok(mut a2)) = (ar, br) {
                            let gcd = a1.gcd(&mut a2);

                            // TODO: convert back to a subexpression
                            let mut res = gcd.to_expression();
                            res.normalize_inplace(var_info);
                            res
                        } else {
                            return false;
                        }
                    }
                    _ => {
                        return false;
                    }
                }
            }
            _ => unreachable!(),
        };
        true
    }

    /// Normalize an element in-place. Returns true if element changed.
    pub fn normalize_inplace(&mut self, var_info: &GlobalVarInfo) -> bool {
        let mut changed = false;
        match *self {
            Element::Num(ref mut dirty, ref mut num) => {
                if *dirty {
                    *dirty = false;
                    changed |= num.normalize_inplace()
                }
            }
            Element::Wildcard(_, ref mut restriction) => for x in restriction {
                changed |= x.normalize_inplace(var_info);
            },
            Element::NumberRange(ref mut n1, ..) => {
                changed |= n1.normalize_inplace();
            }
            Element::Pow(dirty, ..) => {
                if !dirty {
                    return false;
                }

                *self = if let Element::Pow(ref mut dirty, ref mut be) = *self {
                    let (ref mut b, ref mut e) = *&mut **be;
                    changed |= b.normalize_inplace(var_info);
                    changed |= e.normalize_inplace(var_info);
                    *dirty = false;

                    // TODO: Clippy doesn't like loops that never actually loop #[warn(never_loop)]
                    // though imho it looks the best way to make "goto" or "early-exit in match"
                    // for now. (See also rust-lang/rfcs#2046.)
                    loop {
                        match *e {
                            Element::Num(_, Number::SmallInt(0)) => {
                                // x^0 = 1
                                break Element::Num(false, Number::one());
                            }
                            Element::Num(_, Number::SmallInt(1)) => {
                                // x^1 = x
                                break mem::replace(b, DUMMY_ELEM!());
                            }
                            Element::Num(_, Number::SmallInt(ref mut n)) if *n > 0 => {
                                // exponent is a positive integer
                                // check if some simplification can be made

                                if let Element::Num(_, ref mut num) = *b {
                                    // base is a rational number: (p/q)^n = p^n/q^n
                                    break Element::Num(false, num.clone().pow(*n as u32));
                                }

                                // simplify x^a^b = x^(a*b) where x is a variable
                                // and a and b are positive integers
                                // In general, this may be mathematically wrong, e.g.,
                                //   for x = (-1+i), a = 2, b = 3/2,
                                //   (x^a)^b = - x^(a*b).
                                // We need to add more detailed conditions for such a reduction.
                                let mut newbase = DUMMY_ELEM!();
                                if let Element::Pow(_, ref mut be1) = *b {
                                    if let Element::Var(_) = be1.0 {
                                        if let Element::Num(_, Number::SmallInt(n1)) = be1.1 {
                                            newbase = be1.0.clone();
                                            *n *= n1;
                                            changed = true;
                                        }
                                    }
                                }

                                if newbase != DUMMY_ELEM!() {
                                    *b = newbase;
                                }
                            }
                            Element::Num(_, Number::SmallInt(ref n)) if *n < 0 => {
                                if let Element::Num(_, ref mut num) = *b {
                                    // base is a rational number: (p/q)^(-n) = q^n/p^n
                                    break Element::Num(
                                        false,
                                        Number::one() / num.clone().pow(-n as u32),
                                    );
                                }
                            }
                            _ => {}
                        };
                        return changed;
                    }
                } else {
                    unreachable!();
                };
                return changed;
            }
            Element::Fn(mut dirty, name, ..) => {
                if let Some(_) = var_info.func_attribs.get(&name) {
                    dirty = true; // for now, always set the dirty flag if a function has attributes
                }

                if dirty {
                    let mut newvalue = None;

                    if let Element::Fn(ref mut dirty, ref name, ref mut args) = *self {
                        for x in args.iter_mut() {
                            changed |= x.normalize_inplace(var_info);
                        }

                        newvalue = loop {
                            if let Some(attribs) = var_info.func_attribs.get(&name) {
                                if attribs.contains(&FunctionAttributes::Linear) {
                                    // split the function if any of its arguments is a subexpr
                                    let mut subv = vec![];
                                    let mut replace_index = 0;
                                    for (i, x) in args.iter_mut().enumerate() {
                                        if let Element::SubExpr(_, ref mut args1) = *x {
                                            mem::swap(args1, &mut subv);
                                            replace_index = i;
                                            break;
                                        }
                                    }

                                    if !subv.is_empty() {
                                        changed = true;

                                        // create a subexpr of functions
                                        let mut subexprs = Vec::with_capacity(subv.len());
                                        for a in &mut subv {
                                            let mut rest = Vec::with_capacity(args.len());

                                            for (ii, xx) in args.iter().enumerate() {
                                                if ii != replace_index {
                                                    rest.push(xx.clone());
                                                } else {
                                                    rest.push(mem::replace(a, DUMMY_ELEM!()));
                                                }
                                            }

                                            subexprs.push(Element::Fn(true, name.clone(), rest));
                                        }

                                        let mut e = Element::SubExpr(true, subexprs);
                                        e.normalize_inplace(var_info);
                                        break Some(e);
                                    }
                                }

                                if attribs.contains(&FunctionAttributes::Symmetric) {
                                    args.sort_unstable_by(|l, r| {
                                        l.partial_cmp(r, var_info, false).unwrap()
                                    });
                                }
                            }

                            *dirty = false;
                            break None; // the function remains a function
                        }
                    }

                    if let Some(x) = newvalue {
                        *self = x;
                        return true;
                    }
                }

                // TODO: only call when the function does not contain wildcards
                changed |= self.apply_builtin_functions(var_info, false);
            }
            Element::Term(dirty, _) => {
                if !dirty {
                    return false;
                }

                *self = if let Element::Term(ref mut dirty, ref mut ts) = *self {
                    *dirty = false;

                    // normalize factors and flatten
                    // TODO: check for 0 here
                    let mut restructure = false;
                    let mut newlen = ts.len();
                    for x in ts.iter_mut() {
                        changed |= x.normalize_inplace(var_info);
                        if let Element::Term(_, ref a) = *x {
                            newlen += a.len();
                            restructure = true;
                            changed = true;
                        }
                    }

                    // flatten the term
                    if restructure {
                        let mut tmp = Vec::with_capacity(newlen);
                        for x in ts.drain(..) {
                            match x {
                                Element::Term(_, tss) => tmp.extend(tss),
                                _ => tmp.push(x),
                            }
                        }
                        *ts = tmp;
                    }

                    // sort and merge the terms at the same time
                    if false {
                        if ts.len() > 1 {
                            changed |= expr_sort(ts, merge_factors, var_info, true);
                        }
                    } else {
                        // TODO: this is faster than expr_sort. presumable because there are fewer
                        // merge_factor calls
                        ts.sort_unstable_by(|l, r| l.partial_cmp(r, var_info, true).unwrap());

                        // now merge pows: x^a*x^b = x^(a*b)
                        // x*x^a and x*x, all should be side by side now
                        let mut lastindex = 0;

                        for i in 1..ts.len() {
                            let (a, b) = ts.split_at_mut(i);
                            if !merge_factors(&mut a[lastindex], &mut b[0], var_info) {
                                if lastindex + 1 < i {
                                    a[lastindex + 1] = mem::replace(&mut b[0], DUMMY_ELEM!());
                                }
                                lastindex += 1;
                            }
                        }
                        ts.truncate(lastindex + 1);

                        if let Some(Element::Num(..)) = ts.last() {
                            if let Some(Element::Num(_, num)) = ts.last().cloned() {
                                match num {
                                    Number::SmallInt(0) => ts.clear(),
                                    Number::SmallInt(1) if ts.len() > 1 => {
                                        ts.pop();
                                    } // don't add a factor
                                    _ => {}
                                }
                            }
                        }
                    }

                    //ts.shrink_to_fit(); // make sure we keep memory in check

                    match ts.len() {
                        0 => Element::Num(false, Number::zero()),
                        1 => ts.swap_remove(0), // downgrade
                        _ => return changed,
                    }
                } else {
                    unreachable!()
                }
            }
            Element::SubExpr(dirty, _) => {
                if !dirty {
                    return false;
                }
                *self = if let Element::SubExpr(ref mut dirty, ref mut ts) = *self {
                    *dirty = false;

                    // normalize factors and flatten
                    let mut restructure = false;
                    let mut newlen = ts.len();
                    for x in ts.iter_mut() {
                        changed |= x.normalize_inplace(var_info);
                        if let Element::SubExpr(_, ref a) = *x {
                            newlen += a.len();
                            restructure = true;
                            changed = true;
                        }
                    }

                    // flatten the expression
                    if restructure {
                        let mut tmp = Vec::with_capacity(newlen);
                        for x in ts.drain(..) {
                            match x {
                                Element::SubExpr(_, tss) => tmp.extend(tss),
                                _ => tmp.push(x),
                            }
                        }
                        *ts = tmp;
                    }

                    // sort and merge the terms at the same time
                    if false {
                        changed |= expr_sort(ts, merge_terms, var_info, true);
                    } else {
                        changed = true; // TODO: tell if changed?
                        ts.sort_unstable_by(|l, r| l.partial_cmp(r, var_info, true).unwrap()); // TODO: slow!
                                                                                               // merge coefficients of similar terms
                        let mut lastindex = 0;

                        for i in 1..ts.len() {
                            let (a, b) = ts.split_at_mut(i);
                            if !merge_terms(&mut a[lastindex], &mut b[0], var_info) {
                                if lastindex + 1 < i {
                                    a[lastindex + 1] = mem::replace(&mut b[0], DUMMY_ELEM!());
                                }
                                lastindex += 1;
                            }
                        }
                        ts.truncate(lastindex + 1);
                    }

                    match ts.len() {
                        0 => Element::Num(false, Number::zero()),
                        1 => ts.swap_remove(0),
                        _ => return changed,
                    }
                } else {
                    unreachable!();
                }
            }
            _ => {}
        };
        changed
    }
}

/// Merge factor `sec` into `first` if possible. Returns true if merged.
pub fn merge_factors(first: &mut Element, sec: &mut Element, var_info: &GlobalVarInfo) -> bool {
    let mut changed = false;

    if let Element::Num(_, ref mut num) = *first {
        if let Element::Num(_, ref mut num1) = *sec {
            *num *= mem::replace(num1, DUMMY_NUM!());
            return true;
        }

        if !var_info.polyratfun {
            return false;
        }
    }

    if !var_info.polyratfun {
        if let Element::Num(..) = *sec {
            return false;
        }
    }

    // swap the number and polyratfun to make merging easier
    if let Element::Num(..) = *first {
        if let Element::RationalPolynomialCoefficient(..) = *sec {
            mem::swap(first, sec);
        }
    }

    if let Element::RationalPolynomialCoefficient(ref mut _dirty, ref mut p) = *first {
        // multiply polyratfun and number
        if let Element::Num(ref _dirty, ref mut n) = *sec {
            let (ref mut num, ref mut den) = &mut **p;
            match n {
                Number::SmallInt(_) => *num = mem::replace(num, Polynomial::new()) * n.clone(), // TODO: improve
                Number::BigInt(_) => *num = mem::replace(num, Polynomial::new()) * n.clone(),
                Number::SmallRat(ref num1, ref den1) => {
                    *num = mem::replace(num, Polynomial::new()) * Number::SmallInt(num1.clone());
                    *den = mem::replace(den, Polynomial::new()) * Number::SmallInt(den1.clone());
                }
                Number::BigRat(ref nd) => {
                    *num =
                        mem::replace(num, Polynomial::new()) * Number::BigInt(nd.numer().clone());
                    *den =
                        mem::replace(den, Polynomial::new()) * Number::BigInt(nd.denom().clone());
                }
            }

            return true;
        }

        // multiply two polyratfuns
        if let Element::RationalPolynomialCoefficient(ref mut _dirty1, ref mut p1) = *sec {
            let (ref mut num, ref mut den) = &mut **p;
            let (ref mut num1, ref mut den1) = &mut **p1;

            let mut g1 = num.gcd(den1);
            let mut g2 = num1.gcd(den);

            let numnew = num.long_division(&mut g1).0;
            let num1new = num1.long_division(&mut g2).0;
            let dennew = den.long_division(&mut g2).0;
            let den1new = den1.long_division(&mut g1).0;

            *num = numnew * num1new;
            *den = dennew * den1new;

            let mut g = num.gcd(den);

            *num = num.long_division(&mut g).0;
            *den = den.long_division(&mut g).0;

            return true;
        }
    }

    // x*x => x^2
    if first == sec {
        *first = Element::Pow(
            true,
            Box::new((
                mem::replace(first, DUMMY_ELEM!()),
                Element::Num(false, Number::SmallInt(2)),
            )),
        );
        first.normalize_inplace(var_info);
        return true;
    }

    // x^a*x^b = x^(a+b)
    if let &mut Element::Pow(ref mut dirty, ref mut be2) = first {
        let (ref mut b2, ref mut e2) = *&mut **be2;
        if let &mut Element::Pow(_, ref mut be1) = sec {
            let (ref b1, ref mut e1) = *&mut **be1;
            if b1 == b2 {
                match (e1, e2) {
                    // TODO: can we remove many "&mut"?
                    (
                        &mut Element::SubExpr(_, ref mut a1),
                        &mut Element::SubExpr(ref mut d2, ref mut a2),
                    ) => {
                        *d2 = true;
                        a2.append(a1)
                    }
                    (ref mut a1, &mut Element::SubExpr(ref mut d2, ref mut a2)) => {
                        *d2 = true;
                        a2.push(mem::replace(a1, DUMMY_ELEM!()))
                    }
                    (a, b) => {
                        *b = Element::SubExpr(
                            true,
                            vec![
                                mem::replace(a, DUMMY_ELEM!()),
                                mem::replace(b, DUMMY_ELEM!()),
                            ],
                        )
                    }
                }
                *dirty = true;
                changed = true;
            }
        } else if sec == b2 {
            // e2 should become e2 + 1
            // avoid borrow checker error
            let mut addone = true;
            if let Element::Num(_, ref mut num) = *e2 {
                *num += Number::one();
                addone = false;
            }
            if addone {
                *e2 = Element::SubExpr(
                    true,
                    vec![
                        mem::replace(e2, DUMMY_ELEM!()),
                        Element::Num(false, Number::one()),
                    ],
                );
            }

            *dirty = true;
            changed = true;
        }
    };
    first.normalize_inplace(var_info);
    changed
}

// returns true if merged
pub fn merge_terms(mut first: &mut Element, sec: &mut Element, _var_info: &GlobalVarInfo) -> bool {
    // filter +0
    if let Element::Num(_, Number::SmallInt(0)) = *sec {
        return true;
    }

    if let Element::Num(_, Number::SmallInt(0)) = *first {
        mem::swap(first, sec);
        return true;
    }

    // make sure a term is always first
    if let Element::Term(..) = first {
    } else {
        if let Element::Term(..) = sec {
            mem::swap(first, sec);
        }
    }

    let mut is_zero = false;

    match (sec, &mut first) {
        (&mut Element::Term(_, ref mut t1), &mut &mut Element::Term(_, ref mut t2)) => {
            assert!(!t1.is_empty() && !t2.is_empty());

            // perform a quick check
            if t1[0] != t2[0] {
                return false;
            }

            let mut num1 = Element::Num(false, Number::SmallInt(1));
            let mut num2 = Element::Num(false, Number::SmallInt(1));
            let mut add_coeff = true;

            // check if the two terms should be merged
            {
                let len1 = t1.len();
                let len2 = t2.len();
                let (mut l1, mut l11) = t1.split_at_mut(len1 - 1);
                let (mut l2, mut l22) = t2.split_at_mut(len2 - 1);

                let same = match l11[0] {
                    Element::Num(..) | Element::RationalPolynomialCoefficient(..) => match l22[0] {
                        Element::Num(..) | Element::RationalPolynomialCoefficient(..) => l1 == l2,
                        _ => l1[..len1 - 2] == *l2 && l1[len1 - 2..] == *l22,
                    },
                    _ => match l22[0] {
                        Element::Num(..) | Element::RationalPolynomialCoefficient(..) => {
                            *l1 == l2[..len2 - 2] && *l11 == l2[len2 - 2..]
                        }
                        _ => l1 == l2 && l11 == l22,
                    },
                };

                // extract the coefficients
                if same {
                    match l11[0] {
                        Element::Num(..) | Element::RationalPolynomialCoefficient(..) => {
                            mem::swap(&mut l11[0], &mut num1)
                        }
                        _ => {}
                    }
                    match l22[0] {
                        Element::Num(..) | Element::RationalPolynomialCoefficient(..) => {
                            add_coeff = false;
                            mem::swap(&mut l22[0], &mut num2)
                        }
                        _ => {}
                    }
                } else {
                    return false;
                }
            }

            if let Element::Num(..) = num2 {
                // make sure that the RationalPolynomialCoefficient is in num2 if it is there
                mem::swap(&mut num1, &mut num2);
            }

            // now we merge the coefficient into num2
            match (&mut num1, &mut num2) {
                (
                    Element::RationalPolynomialCoefficient(ref mut _dirty, ref mut p),
                    Element::RationalPolynomialCoefficient(ref mut _dirty1, ref mut p1),
                ) => {
                    let (ref mut num, ref mut den) = &mut **p1; // note the switch
                    let (ref mut num1, ref mut den1) = &mut **p;

                    // TODO: improve!
                    let mut newnum = num.clone() * den1.clone() + num1.clone() * den.clone();
                    let mut newden = den.clone() * den1.clone();
                    let mut g1 = newnum.gcd(&mut newden);

                    *num = newnum.long_division(&mut g1).0;
                    *den = newden.long_division(&mut g1).0;

                    if num.is_zero() {
                        is_zero = true;
                    }
                }
                (
                    Element::Num(_, ref mut n),
                    Element::RationalPolynomialCoefficient(ref mut _dirty, ref mut p),
                ) => {
                    let (ref mut num, ref mut den) = &mut **p;
                    add_num_poly(n, num, den);

                    if num.is_zero() {
                        is_zero = true;
                    }
                }
                (Element::Num(_, ref mut n1), Element::Num(_, ref mut n)) => {
                    *n += mem::replace(n1, Number::SmallInt(1));
                    if n.is_zero() {
                        is_zero = true;
                    }
                }
                _ => unreachable!(),
            }

            if !is_zero {
                // write num2 into t2
                if add_coeff {
                    t2.push(num2);
                } else {
                    *t2.last_mut().unwrap() = num2;
                }
                return true;
            }
        }
        // x + x/2
        // (1+x) + (1+x)/2
        (ref a, &mut &mut Element::Term(_, ref mut t2)) => {
            assert!(!t2.is_empty());

            if **a == t2[0] && t2.len() == 2 {
                match t2[1] {
                    Element::Num(_, ref mut num) => {
                        *num += Number::one();
                        if num.is_zero() {
                            is_zero = true;
                        }
                    }
                    Element::RationalPolynomialCoefficient(_, ref mut num) => {
                        let (ref mut num, ref mut den) = &mut **num;
                        add_num_poly(&mut Number::SmallInt(1), num, den);
                        if num.is_zero() {
                            is_zero = true;
                        }
                    }
                    _ => return false,
                }
            } else {
                return false;
            }
        }
        (&mut Element::Num(_, ref mut num1), &mut &mut Element::Num(_, ref mut num)) => {
            *num += mem::replace(num1, DUMMY_NUM!());
            if num.is_zero() {
                is_zero = true;
            }
        }
        (
            &mut Element::Num(_, ref mut n),
            &mut &mut Element::RationalPolynomialCoefficient(ref mut dirty1, ref mut p1),
        ) => {
            let (ref mut num, ref mut den) = &mut **p1;
            add_num_poly(n, num, den);

            // TODO: check 0
            *dirty1 = true;
            return true;
        }
        (
            &mut Element::RationalPolynomialCoefficient(ref mut _dirty, ref mut p),
            &mut &mut Element::RationalPolynomialCoefficient(ref mut _dirty1, ref mut p1),
        ) => {
            let (ref mut num, ref mut den) = &mut **p1;
            let (ref mut num1, ref mut den1) = &mut **p;

            // TODO: improve!
            let mut newnum = num.clone() * den1.clone() + num1.clone() * den.clone();
            let mut newden = den.clone() * den1.clone();
            let mut g1 = newnum.gcd(&mut newden);

            *num = newnum.long_division(&mut g1).0;
            *den = newden.long_division(&mut g1).0;

            if num.is_zero() {
                is_zero = true;
            }
        }
        (ref a1, ref mut a2) if a1 == *a2 => {
            ***a2 = Element::Term(
                false,
                vec![
                    mem::replace(a2, DUMMY_ELEM!()),
                    Element::Num(false, Number::SmallInt(2)),
                ],
            )
        }
        _ => return false,
    }

    if is_zero {
        *first = Element::Num(false, Number::zero());
    }

    true
}

/// Sorts a vector `a`, using the `merger` function to merge identical terms.
/// This function can be used to sort subexpressions and terms.
/// Returns true if the vector has been changed.
pub fn expr_sort<F>(
    a: &mut Vec<Element>,
    merger: F,
    var_info: &GlobalVarInfo,
    ground_level: bool,
) -> bool
where
    F: Fn(&mut Element, &mut Element, &GlobalVarInfo) -> bool,
{
    if a.is_empty() {
        return false;
    }

    // count descending runs and merge adjacent terms if possible
    // also count ascending runs and reverse them
    // this is safe for non-commutative functions, since they will
    // always be treated as in-order
    let mut changed = false;
    let mut grouplen = vec![];
    let mut groupcount = 1;
    let mut writepos = 1;
    let mut ascenddescendmode = 0; // 0: no direction, 1: desc, 2: asc
    for x in 1..a.len() {
        {
            let (old, new) = a.split_at_mut(x);
            if merger(&mut old[writepos - 1], &mut new[0], var_info) {
                changed = true;
                continue;
            }
        }

        a.swap(writepos, x);
        writepos += 1;

        match a[writepos - 2].partial_cmp(&a[writepos - 1], var_info, ground_level) {
            Some(Ordering::Greater) => {
                if ascenddescendmode == 1 {
                    grouplen.push(groupcount);
                    ascenddescendmode = 0;
                    groupcount = 1;
                } else {
                    if ascenddescendmode == 0 {
                        ascenddescendmode = 2;
                    }
                    groupcount += 1;
                }
            }
            _ => {
                if ascenddescendmode == 2 {
                    // TODO: first check if the reversed array can join the last group?
                    grouplen.push(groupcount);
                    // change direction of last group, problem: writepos not included in this array
                    // yet..
                    a[writepos - groupcount - 1..writepos - 1].reverse();
                    ascenddescendmode = 0;
                    groupcount = 1;
                } else {
                    if ascenddescendmode == 0 {
                        ascenddescendmode = 1;
                    }
                    groupcount += 1;
                }
            }
        }
    }

    if !changed && groupcount == 1 && ascenddescendmode == 1 {
        return false;
    }

    // reverse last group if ascending
    if ascenddescendmode == 2 {
        a[writepos - groupcount..writepos].reverse();
    }

    a.truncate(writepos);

    // allocate buffer, TODO: could be half the size
    let mut b: Vec<Element> = Vec::with_capacity(a.len());
    grouplen.push(groupcount);

    //a.shrink_to_fit(); // slow!
    //b.shrink_to_fit();

    // Make successively longer sorted runs until whole array is sorted.
    while grouplen.len() > 1 {
        let mut newlen = 0;
        let mut groupindex = 0;
        let mut startpos = 0;
        let mut writepos = a.as_mut_ptr();
        while groupindex * 2 < grouplen.len() {
            let newsize;
            unsafe {
                if groupindex * 2 + 1 == grouplen.len() {
                    // only one group left, so just copy to writepos
                    newsize = sub_merge_sort(
                        a,
                        startpos,
                        startpos + grouplen[groupindex * 2],
                        startpos + grouplen[groupindex * 2],
                        &mut b,
                        writepos,
                        &merger,
                        var_info,
                        ground_level,
                    );
                } else {
                    newsize = sub_merge_sort(
                        a,
                        startpos,
                        startpos + grouplen[groupindex * 2],
                        startpos + grouplen[groupindex * 2] + grouplen[groupindex * 2 + 1],
                        &mut b,
                        writepos,
                        &merger,
                        var_info,
                        ground_level,
                    );
                    startpos += grouplen[groupindex * 2] + grouplen[groupindex * 2 + 1];
                }

                writepos = writepos.offset(newsize as isize);
            }
            grouplen[groupindex] = newsize;
            newlen += newsize;
            groupindex += 1;
        }

        grouplen.truncate(groupindex);
        unsafe {
            // resize without dropping
            a.set_len(newlen);
        }
    }
    true
}

unsafe fn sub_merge_sort<F>(
    a: &mut [Element],
    left: usize,
    right: usize,
    end: usize,
    buf: &mut [Element],
    mut writepos: *mut Element,
    merger: &F,
    var_info: &GlobalVarInfo,
    ground_level: bool,
) -> usize
where
    F: Fn(&mut Element, &mut Element, &GlobalVarInfo) -> bool,
{
    let mut i = left;
    let mut j = right;
    let mut lastsource = 0; // 0: none, 1: left, 2: right
    let origwritepos = writepos;

    // copy left part to array
    let mut leftp = buf.as_mut_ptr();
    let mut rightp = a.get_unchecked_mut(right) as *mut Element;

    ptr::copy_nonoverlapping(&a[left], buf.as_mut_ptr(), right - left);

    while i < right || j < end {
        if i < right && j < end {
            match (*leftp).partial_cmp(&*rightp, var_info, ground_level) {
                Some(Ordering::Greater) => {
                    if lastsource != 1 || !merger(&mut *writepos.offset(-1), &mut *rightp, var_info)
                    {
                        // FIXME: it should drop at writep! does this cause leaks?
                        assert!(writepos != rightp);
                        ptr::copy_nonoverlapping(rightp, writepos, 1);
                        writepos = writepos.offset(1);
                        lastsource = 2;
                    }
                    j += 1;
                    rightp = rightp.offset(1);
                }
                // TODO: special case if they are equal/mergeable
                _ => {
                    if lastsource != 2 || !merger(&mut *writepos.offset(-1), &mut *leftp, var_info)
                    {
                        ptr::copy_nonoverlapping(leftp, writepos, 1);
                        writepos = writepos.offset(1);
                        lastsource = 1;
                    }
                    i += 1;
                    leftp = leftp.offset(1);
                }
            }
        } else {
            if i < right {
                if lastsource != 2 || !merger(&mut *writepos.offset(-1), &mut *leftp, var_info) {
                    ptr::copy_nonoverlapping(leftp, writepos, 1);
                    writepos = writepos.offset(1);
                    lastsource = 1;
                }
                i += 1;
                leftp = leftp.offset(1);
            } else {
                if lastsource != 1 || !merger(&mut *writepos.offset(-1), &mut *rightp, var_info) {
                    assert!(writepos != rightp);
                    ptr::copy_nonoverlapping(rightp, writepos, 1);
                    writepos = writepos.offset(1);
                    lastsource = 2;
                }
                j += 1;
                rightp = rightp.offset(1);
            }
        }
    }

    (writepos as usize - origwritepos as usize) / mem::size_of::<Element>()
}
