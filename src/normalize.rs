use num_traits::{One, Pow, Zero};
use number::Number;
use poly::polynomial::{
    rationalpolynomial_add, rationalpolynomial_mul, rationalpolynomial_normalize, Polynomial,
};
use sort::split_merge;
use std::collections::HashMap;
use std::mem;
use structure::{
    Element, FunctionAttributes, GlobalVarInfo, Ordering, FUNCTION_DELTA, FUNCTION_GCD,
    FUNCTION_IFELSE, FUNCTION_LIST, FUNCTION_NARGS, FUNCTION_PROD, FUNCTION_RAT, FUNCTION_SUM,
    FUNCTION_TAKEARG, FUNCTION_TERM,
};
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
                    FUNCTION_TERM => {
                        // the term_() should be substituted at an earlier stage
                        unreachable!("term_() should have been substituted at an earlier stage.")
                    }
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
                    FUNCTION_TAKEARG => {
                        // take the nth argument, starting from 1
                        if a.len() > 2 {
                            if let Element::Num(_, Number::SmallInt(n1)) = a[0] {
                                if n1 > 0 && (n1 as usize) < a.len() {
                                    a.swap_remove(n1 as usize)
                                } else {
                                    return false;
                                }
                            } else {
                                return false;
                            }
                        } else {
                            return false;
                        }
                    }
                    FUNCTION_IFELSE => {
                        if a.len() != 3 {
                            return false;
                        }

                        let mut truebranch = false;
                        if let Element::Comparison(_, ref es, ref c) = a[0] {
                            // allow == on all elements and <,>, etc on numbers
                            let mut fullcompare = false;
                            if let Element::Num(..) = es.0 {
                                if let Element::Num(..) = es.1 {
                                    fullcompare = true;
                                }
                            }

                            if fullcompare {
                                if c.cmp_rel(es.0.partial_cmp(&es.1, var_info, false).unwrap()) {
                                    truebranch = true;
                                }
                            } else {
                                if c == &Ordering::Equal {
                                    if c.cmp_rel(es.0.partial_cmp(&es.1, var_info, false).unwrap())
                                    {
                                        truebranch = true;
                                    }
                                } else {
                                    return false;
                                }
                            }
                        } else {
                            return false;
                        }

                        // Select and normalize the correct branch.
                        // The branches are not normalized by default in the normalization function,
                        // since this may cause infinite loops for custom functions.
                        if truebranch {
                            let mut ee = a.swap_remove(1);
                            ee.normalize_inplace(var_info);
                            ee
                        } else {
                            let mut ee = a.swap_remove(2);
                            ee.normalize_inplace(var_info);
                            ee
                        }
                    }
                    FUNCTION_SUM | FUNCTION_PROD => {
                        if a.len() == 4 {
                            match (&a[1], &a[2]) {
                                (
                                    &Element::Num(_, Number::SmallInt(n1)),
                                    &Element::Num(_, Number::SmallInt(n2)),
                                ) => {
                                    let mut terms = vec![];
                                    for i in n1..n2 + 1 {
                                        let mut ne = a[3].clone();
                                        ne.replace(
                                            &a[0],
                                            &Element::Num(false, Number::SmallInt(i)),
                                        );
                                        terms.push(ne);
                                    }
                                    if *n == FUNCTION_SUM {
                                        let mut newe = Element::SubExpr(true, terms);
                                        newe.normalize_inplace(&var_info);
                                        newe
                                    } else {
                                        let mut newe = Element::Term(true, terms);
                                        newe.normalize_inplace(&var_info);
                                        newe
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
                        if a.len() == 1 {
                            if let Ok(mut prf) = Polynomial::from(&a[0]) {
                                let mut one = prf.cloned_one();

                                rationalpolynomial_normalize(&mut prf, &mut one);
                                Element::RationalPolynomialCoefficient(false, Box::new((prf, one)))
                            } else {
                                return false;
                            }
                        } else {
                            match Polynomial::from(&a[0]) {
                                Ok(mut num) => match Polynomial::from(&a[1]) {
                                    Ok(mut den) => {
                                        rationalpolynomial_normalize(&mut num, &mut den);
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
                            // check if the polynomials have integer coefficients
                            for x in a1.poly.coefficients.iter().chain(&a2.poly.coefficients) {
                                match x {
                                    Number::SmallRat(..) | Number::BigRat(..) => return false,
                                    _ => {}
                                }
                            }

                            let gcd = a1.gcd(&mut a2);

                            // TODO: convert back to a subexpression
                            let mut res = gcd.to_expression();
                            res.normalize_inplace(var_info);
                            res
                        } else {
                            return false;
                        }
                    }
                    nn => {
                        // process custom functions
                        if let Some((argvar, e)) = var_info.user_functions.get(&nn) {
                            if argvar.len() != a.len() {
                                return false;
                            }

                            let mut replace_map = HashMap::new();

                            for (av, aa) in argvar.iter().zip(a) {
                                replace_map.insert(*av, aa.clone());
                            }

                            let mut newe = e.clone();
                            if newe.replace_elements(&replace_map) {
                                newe.normalize_inplace(&var_info);
                            }

                            newe
                        } else {
                            return false;
                        }
                    }
                }
            }
            _ => unreachable!(),
        };
        true
    }

    #[inline]
    pub fn should_normalize(&self) -> bool {
        match *self {
            Element::Var(_, ref e) => e.is_zero(),
            Element::Num(dirty, ..)
            | Element::Comparison(dirty, ..)
            | Element::Pow(dirty, ..)
            | Element::Fn(dirty, ..)
            | Element::SubExpr(dirty, ..)
            | Element::Term(dirty, ..) => dirty,
            _ => true,
        }
    }

    /// Normalize an element in-place. Returns true if element changed.
    pub fn normalize_inplace(&mut self, var_info: &GlobalVarInfo) -> bool {
        let mut changed = false;
        match *self {
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
                        if x.should_normalize() {
                            changed |= x.normalize_inplace(var_info);
                        }
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

                    ts.sort_unstable_by(|l, r| l.partial_cmp_factor(r, var_info).unwrap());

                    // now merge pows: x^a*x^b = x^(a*b)
                    // x*x^a and x*x, all should be side by side now
                    let mut lastindex = 0;

                    for i in 1..ts.len() {
                        let (a, b) = ts.split_at_mut(i);
                        if !merge_factors(&mut a[lastindex], &mut b[0], var_info) {
                            if lastindex + 1 < i {
                                mem::swap(&mut a[lastindex + 1], &mut b[0]);
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
            Element::Expression(name) => {
                // replace an expression by its contents
                if let Some(x) = var_info.expressions.get(&name) {
                    let mut it = x.into_iter();
                    let mut terms = Vec::with_capacity(x.term_count());
                    while let Some(e) = it.next() {
                        terms.push(e.clone());
                    }
                    let mut e = Element::SubExpr(true, terms);
                    e.normalize_inplace(var_info);
                    *self = e;
                    changed = true;
                }
            }
            Element::Num(ref mut dirty, ref mut num) => {
                if *dirty {
                    *dirty = false;
                    changed |= num.normalize_inplace()
                }
            }
            Element::Comparison(ref mut dirty, ref mut e, _) => {
                if *dirty {
                    *dirty = false;
                    changed |= e.0.normalize_inplace(var_info);
                    changed |= e.1.normalize_inplace(var_info);
                }
            }
            Element::Var(..) => {
                // x^0 = 1
                if let Element::Var(_, Number::SmallInt(0)) = self {
                    *self = Element::Num(false, Number::one());
                    return true;
                }
            }
            Element::Dollar(ref _d, ref mut inds) => {
                // note that the dollar variable cannot be applied here, since
                // we only have global information
                for i in inds.iter_mut() {
                    i.normalize_inplace(var_info);
                }
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
                                break mem::replace(b, Element::default());
                            }
                            Element::Num(_, Number::SmallInt(ref mut n)) if *n > 0 => {
                                // exponent is a positive integer
                                // check if some simplification can be made

                                if let Element::Num(_, ref mut num) = *b {
                                    // base is a rational number: (p/q)^n = p^n/q^n
                                    break Element::Num(false, num.clone().pow(*n as u32));
                                }

                                // downgrade to variable with power
                                let mut downgrade = false;
                                if let Element::Var(_, ref mut mutexp) = b {
                                    downgrade = true;
                                    *mutexp *= Number::SmallInt(*n);
                                }
                                if downgrade {
                                    break mem::replace(b, Element::default());
                                }

                                // simplify x^a^b = x^(a*b) where x is a variable
                                // and a and b are positive integers
                                // In general, this may be mathematically wrong, e.g.,
                                //   for x = (-1+i), a = 2, b = 3/2,
                                //   (x^a)^b = - x^(a*b).
                                // We need to add more detailed conditions for such a reduction.
                                let mut newbase = Element::default();
                                if let Element::Pow(_, ref mut be1) = *b {
                                    if let Element::Var(_, Number::SmallInt(ee1)) = be1.0 {
                                        if let Element::Num(_, Number::SmallInt(n1)) = be1.1 {
                                            newbase = be1.0.clone();
                                            *n *= n1 * ee1;
                                            changed = true;
                                        }
                                    }
                                }

                                if newbase != Element::default() {
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

                                // downgrade to variable with power
                                let mut downgrade = false;
                                if let Element::Var(_, ref mut mutexp) = b {
                                    downgrade = true;
                                    *mutexp *= Number::SmallInt(*n);
                                }
                                if downgrade {
                                    break mem::replace(b, Element::default());
                                }
                            }
                            Element::Num(_, ref mut n) => {
                                // downgrade to variable with power
                                let mut downgrade = false;
                                if let Element::Var(_, ref mut mutexp) = b {
                                    downgrade = true;
                                    *mutexp *= mem::replace(n, Number::zero());
                                }
                                if downgrade {
                                    break mem::replace(b, Element::default());
                                }
                            }
                            _ => {}
                        };
                        return changed;
                    }
                } else {
                    unreachable!();
                };
                return true;
            }
            Element::Fn(mut dirty, name, ..) => {
                if let Some(_) = var_info.func_attribs.get(&name) {
                    dirty = true; // for now, always set the dirty flag if a function has attributes
                }

                if dirty {
                    let mut newvalue = None;

                    if let Element::Fn(ref mut dirty, ref name, ref mut args) = *self {
                        // the ifelse_ function should not normalize its two branches,
                        // since only one of them will be executed. This saves time and
                        // prevents infinite loops

                        let mut has_list_arg = false;
                        if *name == FUNCTION_IFELSE && args.len() == 3 {
                            if args[0].should_normalize() {
                                changed |= args[0].normalize_inplace(var_info);
                            }
                        } else {
                            for x in args.iter_mut() {
                                if x.should_normalize() {
                                    changed |= x.normalize_inplace(var_info);
                                }

                                if let Element::Fn(false, FUNCTION_LIST, args1) = x {
                                    if args1.len() == 4 {
                                        has_list_arg = true;
                                    }
                                }
                            }
                        }

                        if has_list_arg {
                            let mut new_args = Vec::with_capacity(args.len());

                            for x in mem::replace(args, vec![]) {
                                let mut replaced = false;
                                if let Element::Fn(false, FUNCTION_LIST, ref a) = x {
                                    if a.len() == 4 {
                                        if let (
                                            &Element::Num(_, Number::SmallInt(n1)),
                                            &Element::Num(_, Number::SmallInt(n2)),
                                        ) = (&a[1], &a[2])
                                        {
                                            for i in n1..n2 + 1 {
                                                let mut ne = a[3].clone();
                                                ne.replace(
                                                    &a[0],
                                                    &Element::Num(false, Number::SmallInt(i)),
                                                );
                                                ne.normalize_inplace(&var_info);
                                                new_args.push(ne);
                                                replaced = true;
                                            }
                                        }
                                    }
                                }

                                if !replaced {
                                    new_args.push(x);
                                }
                            }

                            *args = new_args;

                            changed = true;
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
                                                    rest.push(mem::replace(a, Element::default()));
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
                        if x.should_normalize() {
                            changed |= x.normalize_inplace(var_info);
                        }
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
                    if true {
                        let map = split_merge(
                            ts,
                            &|a: &Element, b: &Element| a.partial_cmp(b, var_info, true).unwrap(),
                            &|a: &mut Element, b: &mut Element| merge_terms(a, b, var_info),
                        );
                        let mut res = vec![Element::default(); map.len()];

                        if map.len() != ts.len() {
                            changed = true;
                        }

                        for i in 0..map.len() {
                            if i != map[i] {
                                changed = true;
                            }

                            mem::swap(&mut res[i], &mut ts[map[i]]);
                        }
                        mem::swap(&mut res, ts);
                    } else {
                        changed = true; // TODO: tell if changed?
                        ts.sort_unstable_by(|l, r| l.partial_cmp(r, var_info, true).unwrap()); // TODO: slow!
                                                                                               // merge coefficients of similar terms
                        let mut lastindex = 0;

                        for i in 1..ts.len() {
                            let (a, b) = ts.split_at_mut(i);
                            if !merge_terms(&mut a[lastindex], &mut b[0], var_info) {
                                if lastindex + 1 < i {
                                    a[lastindex + 1] = mem::replace(&mut b[0], Element::default());
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
            Element::Wildcard(_, ref mut restriction) => {
                for x in restriction {
                    changed |= x.normalize_inplace(var_info);
                }
            }
            Element::FnWildcard(_, ref mut b) => {
                let (restriction, args) = &mut **b;
                for x in restriction {
                    changed |= x.normalize_inplace(var_info);
                }
                for x in args {
                    changed |= x.normalize_inplace(var_info);
                }
            }
            Element::NumberRange(ref mut n1, ..) => {
                changed |= n1.normalize_inplace();
            }
            _ => {}
        };
        changed
    }
}

/// Merge factor `sec` into `first` if possible. Returns true if merged.
pub fn merge_factors(first: &mut Element, sec: &mut Element, var_info: &GlobalVarInfo) -> bool {
    let mut changed = false;

    // x^n1*x^n2 => x^(n1+n2)
    let mut iszero = false;
    if let Element::Var(n1, p1) = first {
        if let Element::Var(n2, p2) = sec {
            if n1 == n2 {
                *p1 = mem::replace(p1, Number::one()) + mem::replace(p2, Number::one());

                if p1.is_zero() {
                    iszero = true;
                } else {
                    return true;
                }
            } else {
                return false;
            }
        }
    }

    if let Element::Var(..) = first {
        if iszero {
            *first = Element::Num(false, Number::SmallInt(1));
            return true;
        }

        // TODO: merge x^n with x^(...) ?
        return false;
    }

    let mut swap = false;
    if let Element::Num(_, ref mut num) = *first {
        if let Element::Num(_, ref mut num1) = *sec {
            *num *= mem::replace(num1, DUMMY_NUM!());
            return true;
        }

        if let Element::RationalPolynomialCoefficient(..) = *sec {
            swap = true;
        }
    }

    // swap the number and polyratfun to make merging easier
    if swap {
        mem::swap(first, sec);
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

            rationalpolynomial_mul(num, den, num1, den1);
            return true;
        }
    }

    // x*x => x^2
    if first == sec {
        *first = Element::Pow(
            true,
            Box::new((
                mem::replace(first, Element::default()),
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
                        a2.push(mem::replace(a1, Element::default()))
                    }
                    (a, b) => {
                        *b = Element::SubExpr(
                            true,
                            vec![
                                mem::replace(a, Element::default()),
                                mem::replace(b, Element::default()),
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
                        mem::replace(e2, Element::default()),
                        Element::Num(false, Number::one()),
                    ],
                );
            }

            *dirty = true;
            changed = true;
        }
    };

    if first.should_normalize() {
        first.normalize_inplace(var_info);
    }
    changed
}

/// Merge `sec` into `first`. Returns `true` if the resulting term is 0.
pub fn merge_terms(mut first: &mut Element, sec: &mut Element, _var_info: &GlobalVarInfo) -> bool {
    // make sure a term is always first
    if let Element::Term(..) = first {
    } else {
        if let Element::Term(..) = sec {
            mem::swap(first, sec);
        }
    }

    match (sec, &mut first) {
        (&mut Element::Term(_, ref mut t1), &mut &mut Element::Term(_, ref mut t2)) => {
            let mut num1 = Element::Num(false, Number::SmallInt(1));
            let mut num2 = Element::Num(false, Number::SmallInt(1));
            let mut add_coeff = true;

            // extract the coefficients
            match t1.last_mut().unwrap() {
                x @ Element::Num(..) | x @ Element::RationalPolynomialCoefficient(..) => {
                    mem::swap(x, &mut num1)
                }
                _ => {}
            }
            match t2.last_mut().unwrap() {
                x @ Element::Num(..) | x @ Element::RationalPolynomialCoefficient(..) => {
                    add_coeff = false;
                    mem::swap(x, &mut num2)
                }
                _ => {}
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

                    if rationalpolynomial_add(num, den, num1, den1) {
                        return true;
                    }
                }
                (
                    Element::Num(_, ref mut n),
                    Element::RationalPolynomialCoefficient(ref mut _dirty, ref mut p),
                ) => {
                    let (ref mut num, ref mut den) = &mut **p;
                    add_num_poly(n, num, den);

                    if num.is_zero() {
                        return true;
                    }
                }
                (Element::Num(_, ref mut n1), Element::Num(_, ref mut n)) => {
                    *n += mem::replace(n1, Number::SmallInt(1));
                    if n.is_zero() {
                        return true;
                    }
                }
                _ => unreachable!(),
            }

            // write num2 into t2
            if add_coeff {
                t2.push(num2);
            } else {
                *t2.last_mut().unwrap() = num2;
            }
            return false;
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
                            return true;
                        }
                    }
                    Element::RationalPolynomialCoefficient(_, ref mut num) => {
                        let (ref mut num, ref mut den) = &mut **num;
                        add_num_poly(&mut Number::SmallInt(1), num, den);
                        if num.is_zero() {
                            return true;
                        }
                    }
                    _ => unreachable!(),
                }
            } else {
                unreachable!();
            }
        }
        (&mut Element::Num(_, ref mut num1), &mut &mut Element::Num(_, ref mut num)) => {
            *num += mem::replace(num1, DUMMY_NUM!());
            if num.is_zero() {
                return true;
            }
        }
        (
            &mut Element::Num(_, ref mut n),
            &mut &mut Element::RationalPolynomialCoefficient(_, ref mut p1),
        ) => {
            let (ref mut num, ref mut den) = &mut **p1;
            add_num_poly(n, num, den);

            if num.is_zero() {
                return true;
            }
        }
        (
            &mut Element::RationalPolynomialCoefficient(ref mut _dirty, ref mut p),
            &mut &mut Element::RationalPolynomialCoefficient(ref mut _dirty1, ref mut p1),
        ) => {
            let (ref mut num, ref mut den) = &mut **p1;
            let (ref mut num1, ref mut den1) = &mut **p;

            if rationalpolynomial_add(num, den, num1, den1) {
                return true;
            }
        }
        (ref a1, ref mut a2) if a1 == *a2 => {
            ***a2 = Element::Term(
                false,
                vec![
                    mem::replace(a2, Element::default()),
                    Element::Num(false, Number::SmallInt(2)),
                ],
            )
        }
        _ => unreachable!(),
    }

    false
}
