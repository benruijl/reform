use num_traits::{One, Pow, Zero};
use std::mem;

use poly::exponent::Exponent;
use poly::ring::Ring;

use number;
use number::Number;
use poly::raw::finitefield::FiniteField;
use poly::raw::zp;
use poly::raw::zp::ufield;
use poly::raw::MultivariatePolynomial;
use poly::ring::MulModNum;
use poly::ring::ToFiniteField;
use rand;
use rand::distributions::{Range, Sample};
use tools::GCD;

use ndarray::{arr1, Array};
use poly::raw::zp_solve::{solve, LinearSolverError};

// 100 large u32 primes starting from the 203213901st prime number
pub const LARGE_U32_PRIMES: [ufield; 100] = [
    4293490987, 4293491603, 4293492277, 4293492857, 4293491017, 4293491621, 4293492283, 4293492881,
    4293491023, 4293491639, 4293492293, 4293492893, 4293491051, 4293491659, 4293492331, 4293492941,
    4293491149, 4293491701, 4293492349, 4293492977, 4293491171, 4293491711, 4293492383, 4293493037,
    4293491221, 4293491747, 4293492403, 4293493049, 4293491261, 4293491779, 4293492421, 4293493069,
    4293491269, 4293491791, 4293492431, 4293493081, 4293491273, 4293491819, 4293492487, 4293493091,
    4293491281, 4293491849, 4293492499, 4293493117, 4293491299, 4293491863, 4293492523, 4293493121,
    4293491303, 4293491887, 4293492583, 4293493159, 4293491311, 4293491897, 4293492587, 4293493163,
    4293491327, 4293491911, 4293492649, 4293493207, 4293491329, 4293491953, 4293492661, 4293493229,
    4293491399, 4293491957, 4293492673, 4293493241, 4293491431, 4293492017, 4293492701, 4293493261,
    4293491467, 4293492023, 4293492739, 4293493319, 4293491509, 4293492097, 4293492751, 4293493363,
    4293491539, 4293492101, 4293492769, 4293493367, 4293491551, 4293492107, 4293492779, 4293493409,
    4293491561, 4293492113, 4293492781, 4293493423, 4293491567, 4293492139, 4293492811, 4293493433,
    4293491591, 4293492169, 4293492821, 4293493487,
];

// The maximum power of a variable that is cached
pub const POW_CACHE_SIZE: usize = 20;

enum GCDError {
    BadOriginalImage,
    BadCurrentImage,
}

fn newton_interpolation<E: Exponent>(
    a: &[FiniteField],
    u: &[MultivariatePolynomial<FiniteField, E>],
    p: ufield,
    x: usize, // the variable indexs to extend the polynomial by
) -> MultivariatePolynomial<FiniteField, E> {
    // compute inverses
    let mut gammas = vec![];
    for k in 1..a.len() {
        let mut pr = a[k] - a[0];
        for i in 1..k {
            pr = pr * (a[k] - a[i]);
        }
        gammas.push(FiniteField::new(FiniteField::inverse(pr.n, p), p));
    }

    // compute Newton coefficients
    let mut v = vec![u[0].clone()];
    for k in 1..a.len() {
        let mut tmp = v[k - 1].clone();
        for j in (0..k - 1).rev() {
            tmp = tmp * (a[k] - a[j]) + v[j].clone();
        }
        v.push((u[k].clone() - tmp) * gammas[k - 1]);
    }

    // convert to standard form
    let mut e = vec![E::zero(); u[0].nvars];
    e[x] = E::one();
    let xp = MultivariatePolynomial::from_monomial(FiniteField::new(1, p), e);
    let mut u = v[v.len() - 1].clone();
    for k in (0..v.len() - 1).rev() {
        u = u * (xp.clone() - MultivariatePolynomial::from_constant_with_nvars(a[k], xp.nvars))
            + v[k].clone();
    }
    u
}

fn construct_new_image<E: Exponent>(
    ap: &MultivariatePolynomial<FiniteField, E>,
    bp: &MultivariatePolynomial<FiniteField, E>,
    aldegree: E,
    bldegree: E,
    bounds: &mut [u32],
    single_scale: Option<usize>,
    nx: usize,
    vars: &[usize],
    var: usize,
    gfu: &[(MultivariatePolynomial<FiniteField, E>, u32)],
) -> Result<MultivariatePolynomial<FiniteField, E>, GCDError> {
    let p = ap.coefficients[0].p;
    let mut rng = rand::thread_rng();
    let mut range = Range::new(1, p);

    let mut system = vec![]; // coefficients for the linear system
    let mut ni = 0;
    let mut failure_count = 0;

    let mut rank_failure_count = 0;
    let mut last_rank = (0, 0);

    'newimage: loop {
        // generate random numbers for all non-leading variables
        // TODO: apply a Horner scheme to speed up the substitution?
        let (r, a1, b1) = loop {
            // store a table for variables raised to a certain power
            let mut cache = vec![[FiniteField::zero(); POW_CACHE_SIZE]; ap.nvars];

            let r: Vec<(usize, FiniteField)> = vars.iter()
                .map(|i| (i.clone(), FiniteField::new(range.sample(&mut rng), p)))
                .collect();

            /*for &(n, ref vv) in &r {
                cache[n].insert(1, vv.clone());
                for i in 2..12 {
                    let k = cache[n][&(i - 1)].clone();
                    cache[n].insert(i, k * vv.clone());
                }
            }*/

            let a1 = ap.replace_all_except(var, &r, &mut cache);
            let b1 = bp.replace_all_except(var, &r, &mut cache);

            if a1.ldegree(var) == aldegree && b1.ldegree(var) == bldegree {
                break (r, a1, b1);
            }
        };

        let g1 = MultivariatePolynomial::univariate_gcd(&a1, &b1);
        trace!("GCD of sample at point {:?}: {}", r, g1);

        if g1.ldegree(var).as_() < bounds[var] {
            // original image and form and degree bounds are unlucky
            // change the bound and try a new prime
            bounds[0] = g1.ldegree(var).as_();
            return Err(GCDError::BadOriginalImage);
        }

        if g1.ldegree(var).as_() > bounds[var] {
            failure_count += 1;
            if failure_count > 2 || failure_count > ni {
                // p is likely unlucky
                return Err(GCDError::BadCurrentImage);
            }
            continue;
        }

        // check if the single scaling is there, if we had a single scale
        let mut scale_factor = FiniteField::new(1, p);
        if let Some(scaling_index) = single_scale {
            // construct the scaling coefficient
            let mut coeff = FiniteField::new(1, p);
            let (ref c, ref d) = gfu[scaling_index];
            for &(n, v) in r.iter() {
                coeff = coeff * v.clone().pow(c.exponents(0)[n].as_());
            }

            let mut found = false;
            for t in 0..g1.nterms {
                if g1.exponents(t)[var].as_() == *d {
                    scale_factor = coeff / g1.coefficients[t];
                    found = true;
                    break;
                }
            }

            if !found {
                // the scaling term is missing, so the assumed form is wrong
                return Err(GCDError::BadOriginalImage);
            }
        }

        system.push((r, g1, scale_factor));
        ni += 1;

        // make sure we have at least nx images
        if ni < nx {
            continue 'newimage;
        }

        // construct the linear system
        let mut gfm = vec![];
        let mut rhs = vec![0; gfu.len() * system.len()];
        for (i, &(ref c, ref _e)) in gfu.iter().enumerate() {
            for (j, &(ref r, ref g, ref scale_factor)) in system.iter().enumerate() {
                let mut row = vec![];

                assert_eq!(g.nterms, gfu.len());

                // the first elements in the row come from the shape
                for ii in 0..gfu.len() {
                    if i == ii {
                        // note that we ignore the coefficient of the shape
                        for t in 0..c.nterms {
                            let mut coeff = FiniteField::new(1, p);
                            for &(n, v) in r.iter() {
                                coeff = coeff * v.clone().pow(c.exponents(t)[n].as_());
                            }
                            row.push(coeff.n);
                        }
                    } else {
                        for _ in 0..gfu[ii].0.nterms {
                            row.push(0);
                        }
                    }
                }

                // add the coefficient from the image
                // for single scaling, we move them to the rhs
                if single_scale.is_some() {
                    let currow = i * system.len() + j;
                    rhs[currow] =
                        zp::sub(rhs[currow], (g.coefficients[i] * scale_factor.clone()).n, p);
                    gfm.extend(row);
                    continue;
                }

                // the scaling of the first image is fixed to 1
                if j == 0 {
                    let currow = i * system.len();
                    rhs[currow] = zp::sub(rhs[currow], g.coefficients[i].n, p);
                }

                for ii in 1..system.len() {
                    if ii == j {
                        row.push((g.coefficients[i] * scale_factor.clone()).n);
                    } else {
                        row.push(0);
                    }
                }

                gfm.extend(row);
            }
        }

        let rows = gfu.len() * system.len();
        let cols = gfm.len() / rows;
        let m = Array::from_shape_vec((rows, cols), gfm).unwrap();

        match solve(&m, &arr1(&rhs), p) {
            Ok(x) => {
                debug!("Solution: {:?}", x);
                // construct the gcd
                let mut gp = MultivariatePolynomial::with_nvars(ap.nvars);

                // for every power of the main variable
                let mut i = 0; // index in the result x
                for &(ref c, ref ex) in gfu.iter() {
                    for mv in c.into_iter() {
                        let mut ee = mv.exponents.to_vec();
                        ee[var] = E::from_u32(ex.clone()).unwrap();

                        gp.append_monomial(FiniteField::new(x[i].clone(), p), ee);
                        i += 1;
                    }
                }

                debug!("Reconstructed {}", gp);
                return Ok(gp);
            }
            Err(LinearSolverError::Underdetermined { min_rank, max_rank }) => {
                debug!("Underdetermined system");

                if last_rank == (min_rank, max_rank) {
                    rank_failure_count += 1;

                    if rank_failure_count == 3 {
                        debug!("Same degrees of freedom encountered 3 times: assuming bad prime/evaluation point");
                        return Err(GCDError::BadCurrentImage);
                    }
                } else {
                    // update the rank and get new images
                    rank_failure_count = 0;
                    last_rank = (min_rank, max_rank);
                }
            }
            Err(LinearSolverError::Inconsistent) => {
                debug!("Inconsistent system");
                return Err(GCDError::BadOriginalImage);
            }
        }
    }
}

impl<E: Exponent> MultivariatePolynomial<FiniteField, E> {
    /// Compute the univariate GCD using Euclid's algorithm. The result is normalized to 1.
    fn univariate_gcd(
        a: &MultivariatePolynomial<FiniteField, E>,
        b: &MultivariatePolynomial<FiniteField, E>,
    ) -> MultivariatePolynomial<FiniteField, E> {
        assert!(!a.is_zero() && !b.is_zero());

        let mut c = a.clone();
        let mut d = b.clone();
        if a.ldegree_max() < b.ldegree_max() {
            mem::swap(&mut c, &mut d);
        }

        let mut r = c.long_division(&d).1;
        while !r.is_zero() {
            c = d;
            d = r;
            r = c.long_division(&d).1;
        }

        // normalize the gcd
        let l = d.coefficients.last().unwrap().clone();
        for x in &mut d.coefficients {
            *x = x.clone() / l.clone();
        }

        d
    }

    /// Compute the gcd shape of two polynomials in a finite field by filling in random
    /// numbers.
    fn gcd_shape_modular(
        a: &MultivariatePolynomial<FiniteField, E>,
        b: &MultivariatePolynomial<FiniteField, E>,
        vars: &[usize], // variables
        dx: &mut [u32], // degree bounds
    ) -> Option<MultivariatePolynomial<FiniteField, E>> {
        let lastvar = vars.last().unwrap().clone();

        // if we are in the univariate case, return the univariate gcd
        // TODO: this is a modification of the algorithm!
        if vars.len() == 1 {
            return Some(MultivariatePolynomial::univariate_gcd(&a, &b));
        }

        // the gcd of the content in the last variable should be 1
        let c = MultivariatePolynomial::multivariate_content_gcd(a, b, lastvar);
        if !c.is_one() {
            debug!("Content in last variable is not 1, but {}!", c);
            return None;
        }

        let gamma = MultivariatePolynomial::univariate_gcd(&a.lcoeff_last(), &b.lcoeff_last());

        let p = a.coefficients[0].p;
        let mut rng = rand::thread_rng();
        let mut range = Range::new(1, p);

        'newfirstnum: loop {
            let v = loop {
                let a = FiniteField::new(range.sample(&mut rng), p);
                if !gamma.replace(lastvar, a).is_zero() {
                    break a;
                }
            };

            let av = a.replace(lastvar, v);
            let bv = b.replace(lastvar, v);

            // performance dense reconstruction
            let mut gv = if vars.len() > 2 {
                match MultivariatePolynomial::gcd_shape_modular(
                    &av,
                    &bv,
                    &vars[..vars.len() - 1],
                    dx,
                ) {
                    Some(x) => x,
                    None => return None,
                }
            } else {
                let gg = MultivariatePolynomial::univariate_gcd(&av, &bv);
                if gg.ldegree(vars[0]).as_() > dx[vars[0]] {
                    return None;
                }
                dx[vars[0]] = gg.ldegree(vars[0]).as_(); // update degree bound
                gg
            };

            debug!(
                "GCD shape suggestion for sample point {} and gamma {}: {}",
                v, gamma, gv
            );

            // construct a new assumed form
            let gfu = gv.to_univariate_polynomial(vars[0]);

            // find a coefficient of x1 in gg that is a monomial (single scaling)
            let mut single_scale = None;
            let mut nx = 0; // count the minimal number of samples needed
            for (i, &(ref c, ref _e)) in gfu.iter().enumerate() {
                if c.nterms > nx {
                    nx = c.nterms;
                }
                if c.nterms == 1 {
                    single_scale = Some(i);
                }
            }

            // In the case of multiple scaling, each sample adds an
            // additional unknown, except for the first
            if single_scale == None {
                nx = (gv.nterms() - 1) / (gfu.len() - 1);
            }

            let mut lc = gv.lcoeff();
            let mut gseq = vec![gv * (gamma.replace(lastvar, v).coefficients[0].clone() / lc)];
            let mut vseq = vec![v];

            // sparse reconstruction
            'newnum: loop {
                let v = loop {
                    let v = FiniteField::new(range.sample(&mut rng), a.coefficients[0].p);
                    if !gamma.replace(lastvar, v).is_zero() {
                        break v;
                    }
                };

                let av = a.replace(lastvar, v);
                let bv = b.replace(lastvar, v);

                match construct_new_image(
                    &av,
                    &bv,
                    a.ldegree(vars[0]),
                    b.ldegree(vars[0]),
                    dx,
                    single_scale,
                    nx,
                    &vars[1..vars.len() - 1],
                    vars[0],
                    &gfu,
                ) {
                    Ok(r) => {
                        gv = r;
                    }
                    Err(GCDError::BadOriginalImage) => continue 'newfirstnum,
                    Err(GCDError::BadCurrentImage) => continue 'newnum,
                }

                lc = gv.lcoeff();
                gseq.push(gv * (gamma.replace(lastvar, v).coefficients[0].clone() / lc));
                vseq.push(v);

                if gseq.len() == (dx[lastvar] + gamma.ldegree_max().as_() + 1) as usize {
                    break;
                }
            }

            // use interpolation to construct x_n dependence
            let mut gc = newton_interpolation(&vseq, &gseq, p, lastvar);
            debug!("Interpolated: {}", gc);

            // remove content in x_n
            let cont = gc.univariate_content(lastvar);
            let cc = gc.long_division(&cont);
            assert!(cc.1.is_zero());
            gc = cc.0;

            // do a probabilistic division test
            let (g1, a1, b1) = loop {
                // store a table for variables raised to a certain power
                let mut cache = vec![[FiniteField::zero(); POW_CACHE_SIZE]; a.nvars];

                let r: Vec<(usize, FiniteField)> = vars.iter()
                    .skip(1)
                    .map(|i| (*i, FiniteField::new(range.sample(&mut rng), p)))
                    .collect();

                let g1 = gc.replace_all_except(vars[0], &r, &mut cache);

                if g1.ldegree(vars[0]) == gc.ldegree(vars[0]) {
                    let a1 = a.replace_all_except(vars[0], &r, &mut cache);
                    let b1 = b.replace_all_except(vars[0], &r, &mut cache);
                    break (g1, a1, b1);
                }
            };

            if a1.long_division(&g1).1.is_zero() && b1.long_division(&g1).1.is_zero() {
                return Some(gc);
            }

            // if the gcd is bad, we had a bad number
        }
    }
}

impl<R: Ring, E: Exponent> MultivariatePolynomial<R, E>
where
    MultivariatePolynomial<R, E>: PolynomialGCD,
{
    /// Get the content of a multivariate polynomial viewed as a
    /// univariate polynomial in `x`.
    pub fn univariate_content(&self, x: usize) -> MultivariatePolynomial<R, E> {
        let a = self.to_univariate_polynomial(x);

        let mut f = vec![];
        for &(ref c, _) in a.iter() {
            f.push(c.clone());
        }

        MultivariatePolynomial::gcd_multiple(f)
    }

    /// Compute the gcd of multiple polynomials efficiently.
    /// `gcd(f0,f1,f2,...)=gcd(f0,f1+k2*f(2)+k3*f(3))`
    /// with high likelihood.
    pub fn gcd_multiple(mut f: Vec<MultivariatePolynomial<R, E>>) -> MultivariatePolynomial<R, E>
    where
        MultivariatePolynomial<R, E>: PolynomialGCD,
    {
        assert!(f.len() > 0);

        if f.len() == 1 {
            return f.swap_remove(0);
        }

        if f.len() == 2 {
            return MultivariatePolynomial::gcd(&f[0], &f[1]);
        }

        let mut k = 1; // counter for scalar multiple
        let mut gcd;

        loop {
            let a = f.swap_remove(0); // TODO: take the smallest?
            let mut b = MultivariatePolynomial::with_nvars(a.nvars);

            for p in f.iter() {
                for v in p.into_iter() {
                    b.append_monomial(v.coefficient.mul_num(k), v.exponents.to_vec());
                }
                k += 1;
            }

            gcd = MultivariatePolynomial::gcd(&a, &b);

            let mut newf: Vec<MultivariatePolynomial<R, E>> = Vec::with_capacity(f.len());
            for x in f.drain(..) {
                if !x.long_division(&gcd).1.is_zero() {
                    newf.push(x);
                }
            }

            if newf.len() == 0 {
                return gcd;
            }

            newf.push(gcd); // should the gcd be cleared after the next round?
            mem::swap(&mut newf, &mut f);
        }
    }

    /// Compute the gcd of the univariate content in `x`.
    pub fn univariate_content_gcd(
        a: &MultivariatePolynomial<R, E>,
        b: &MultivariatePolynomial<R, E>,
        x: usize,
    ) -> MultivariatePolynomial<R, E> {
        let af = a.to_univariate_polynomial(x);
        let bf = b.to_univariate_polynomial(x);

        let mut f = vec![];
        for &(ref c, _) in af.iter().chain(bf.iter()) {
            f.push(c.clone());
        }

        MultivariatePolynomial::gcd_multiple(f)
    }

    /// Get the content of a multivariate polynomial viewed as a
    /// multivariate polynomial in all variables except `x`.
    pub fn multivariate_content_gcd(
        a: &MultivariatePolynomial<R, E>,
        b: &MultivariatePolynomial<R, E>,
        x: usize,
    ) -> MultivariatePolynomial<R, E> {
        let af = a.to_multivariate_polynomial(&[x], false);
        let bf = b.to_multivariate_polynomial(&[x], false);

        // TODO: drain?
        let f = af.values().cloned().chain(bf.values().cloned()).collect();

        MultivariatePolynomial::gcd_multiple(f)
    }

    /// Compute the gcd of two multivariate polynomials.
    pub fn gcd(
        a: &MultivariatePolynomial<R, E>,
        b: &MultivariatePolynomial<R, E>,
    ) -> MultivariatePolynomial<R, E> {
        assert_eq!(a.nvars, b.nvars);

        debug!("Compute gcd({}, {})", a, b);

        // if we have two numbers, use the integer gcd
        if a.nterms == 1 && a.exponents.iter().all(|c| c.is_zero()) {
            if b.nterms == 1 && b.exponents.iter().all(|c| c.is_zero()) {
                return MultivariatePolynomial::from_constant_with_nvars(
                    GCD::gcd(a.coefficients[0].clone(), b.coefficients[0].clone()),
                    a.nvars,
                );
            }
        }

        // compute the gcd efficiently if some variables do not occur in both
        // polynomials
        let mut scratch = vec![0i32; a.nvars];
        for (p, inc) in vec![(a, 1), (b, 2)] {
            for t in 0..p.nterms {
                for (e, ee) in scratch.iter_mut().zip(p.exponents(t)) {
                    if !ee.is_zero() {
                        *e |= inc;
                    }
                }
            }
        }

        if scratch.iter().any(|x| *x > 0 && *x < 3) {
            let inca: Vec<_> = scratch
                .iter()
                .enumerate()
                .filter_map(|(i, v)| if *v == 1 || *v == 3 { Some(i) } else { None })
                .collect();

            let incb: Vec<_> = scratch
                .iter()
                .enumerate()
                .filter_map(|(i, v)| if *v == 2 || *v == 3 { Some(i) } else { None })
                .collect();

            // extract the variables of b in the coefficient of a and vice versa
            let a1 = a.to_multivariate_polynomial(&incb, false);
            let b1 = b.to_multivariate_polynomial(&inca, false);

            let f = a1.values().cloned().chain(b1.values().cloned()).collect();
            return MultivariatePolynomial::gcd_multiple(f);
        }

        let vars: Vec<_> = scratch
            .iter()
            .enumerate()
            .filter_map(|(i, v)| if *v == 3 { Some(i) } else { None })
            .collect();

        // remove the gcd of the content in the first variable
        // TODO: don't do for univariate poly
        let c = MultivariatePolynomial::univariate_content_gcd(a, b, vars[0]);
        debug!("GCD of content: {}", c);

        if !c.is_one() {
            let x1 = a.long_division(&c);
            let x2 = b.long_division(&c);

            assert!(x1.1.is_zero());
            assert!(x2.1.is_zero());

            return c * MultivariatePolynomial::gcd(&x1.0, &x2.0);
        }

        // TODO: get proper degree bounds on gcd. how?
        // for now: take the lowest degree for each variable
        let mut bounds: Vec<u32> = (0..a.nvars)
            .map(|i| {
                let da = a.degree(i).as_();
                let db = b.degree(i).as_();
                if da < db {
                    da
                } else {
                    db
                }
            })
            .collect();

        // TODO: can the performance be improved by selecting a different lead
        // variable?
        PolynomialGCD::gcd(a, b, &vars, &mut bounds)
    }
}

impl<E: Exponent> MultivariatePolynomial<Number, E> {
    /// Compute the gcd of two multivariate polynomials using Zippel's algorithm.
    /// TODO: provide a parallel implementation?
    fn gcd_zippel(
        a: &MultivariatePolynomial<Number, E>,
        b: &MultivariatePolynomial<Number, E>,
        vars: &[usize], // variables
        bounds: &mut [u32],
    ) -> MultivariatePolynomial<Number, E> {
        debug!("Compute modular gcd({},{})", a, b);

        // compute scaling factor in Z
        let gamma = GCD::gcd(a.lcoeff(), b.lcoeff());
        debug!("gamma {}", gamma);

        let mut pi = 0;

        'newfirstprime: loop {
            pi += 1;
            for _ in pi..LARGE_U32_PRIMES.len() {
                if !(gamma.mod_num(LARGE_U32_PRIMES[pi])).is_zero() {
                    break;
                }
                pi += 1;
            }

            if pi == LARGE_U32_PRIMES.len() {
                panic!("Ran out of primes for gcd reconstruction");
            }

            let mut p = LARGE_U32_PRIMES[pi];

            let mut gammap = gamma.to_finite_field(p);
            let ap = a.to_finite_field(p);
            let bp = b.to_finite_field(p);

            debug!("New first image: gcd({},{}) mod {}", ap, bp, p);

            // calculate modular gcd image
            let mut gp = loop {
                if let Some(x) = MultivariatePolynomial::gcd_shape_modular(&ap, &bp, vars, bounds) {
                    break x;
                }
            };

            debug!("GCD suggestion: {}", gp);

            bounds[vars[0]] = gp.last_exponents()[vars[0]].as_();

            // construct a new assumed form
            // we have to find the proper normalization
            let gfu = gp.to_univariate_polynomial(vars[0]);

            // find a coefficient of x1 in gf that is a monomial (single scaling)
            let mut single_scale = None;
            let mut nx = 0; // count the minimal number of samples needed
            for (i, &(ref c, ref _e)) in gfu.iter().enumerate() {
                if c.nterms > nx {
                    nx = c.nterms;
                }
                if c.nterms == 1 {
                    single_scale = Some(i);
                }
            }

            // In the case of multiple scaling, each sample adds an
            // additional unknown, except for the first
            if single_scale == None {
                nx = (gp.nterms() - 1) / (gfu.len() - 1);
            }

            let gpc = gp.lcoeff();

            // construct the gcd suggestion in Z
            let mut gm = MultivariatePolynomial::with_nvars(gp.nvars);
            gm.nterms = gp.nterms;
            gm.exponents = gp.exponents.clone();
            gm.coefficients = gp.coefficients
                .iter()
                .map(|x| Number::from_finite_field(&(x.clone() * gammap / gpc)))
                .collect();

            let mut m = Number::SmallInt(p as isize); // used for CRT

            debug!("GCD suggestion with gamma: {}", gm);

            let mut old_gm = MultivariatePolynomial::with_nvars(a.nvars);

            // add new primes until we can reconstruct the full gcd
            'newprime: loop {
                if gm == old_gm {
                    // divide by integer content
                    let gmc = gm.content();
                    let mut gc = gm.clone();
                    gc.coefficients = gc.coefficients
                        .iter()
                        .map(|x| x.clone() / gmc.clone())
                        .collect();

                    debug!("Final suggested gcd: {}", gc);
                    if a.long_division(&gc).1.is_zero() && b.long_division(&gc).1.is_zero() {
                        return gc;
                    }

                    // if it does not divide, we need more primes
                }

                old_gm = gm.clone();

                pi += 1;
                for _ in pi..LARGE_U32_PRIMES.len() {
                    if !(gamma.mod_num(LARGE_U32_PRIMES[pi])).is_zero() {
                        break;
                    }
                    pi += 1;
                }

                if pi == LARGE_U32_PRIMES.len() {
                    panic!("Ran out of primes for gcd images");
                }

                p = LARGE_U32_PRIMES[pi];

                gammap = gamma.to_finite_field(p);
                let ap = a.to_finite_field(p);
                let bp = b.to_finite_field(p);
                debug!("New image: gcd({},{}) mod {}", ap, bp, p);

                // for the univariate case, we don't need to construct an image
                if vars.len() == 1 {
                    gp = MultivariatePolynomial::univariate_gcd(&ap, &bp);
                } else {
                    match construct_new_image(
                        &ap,
                        &bp,
                        a.ldegree(vars[0]),
                        b.ldegree(vars[0]),
                        bounds,
                        single_scale,
                        nx,
                        &vars[1..],
                        vars[0],
                        &gfu,
                    ) {
                        Ok(r) => {
                            gp = r;
                        }
                        Err(GCDError::BadOriginalImage) => continue 'newfirstprime,
                        Err(GCDError::BadCurrentImage) => continue 'newprime,
                    }
                }

                // scale the new image
                let gpc = gp.lcoeff();
                gp = gp * (gammap / gpc);
                debug!("gp: {} mod {}", gp, gpc.p);

                // use chinese remainder theorem to merge coefficients and map back to Z
                for (gmc, gpc) in gm.coefficients.iter_mut().zip(gp.coefficients) {
                    let mut coeff = if *gmc < Number::SmallInt(0) {
                        gmc.clone() + m.clone()
                    } else {
                        gmc.clone()
                    };

                    *gmc = number::chinese_remainder(
                        coeff,
                        Number::SmallInt(gpc.n as isize),
                        m.clone(),
                        Number::SmallInt(gpc.p as isize),
                    );
                }

                m *= Number::SmallInt(p as isize);
                debug!("gm: {} from ring {}", gm, m);
            }
        }
    }
}

pub trait PolynomialGCD: Sized {
    fn gcd(a: &Self, b: &Self, vars: &[usize], dx: &mut [u32]) -> Self;
}

impl<E: Exponent> PolynomialGCD for MultivariatePolynomial<Number, E> {
    fn gcd(
        a: &MultivariatePolynomial<Number, E>,
        b: &MultivariatePolynomial<Number, E>,
        vars: &[usize],
        dx: &mut [u32],
    ) -> MultivariatePolynomial<Number, E> {
        MultivariatePolynomial::gcd_zippel(&a, &b, vars, dx)
    }
}

impl<E: Exponent> PolynomialGCD for MultivariatePolynomial<FiniteField, E> {
    fn gcd(
        a: &MultivariatePolynomial<FiniteField, E>,
        b: &MultivariatePolynomial<FiniteField, E>,
        vars: &[usize],
        dx: &mut [u32],
    ) -> MultivariatePolynomial<FiniteField, E> {
        MultivariatePolynomial::gcd_shape_modular(&a, &b, vars, dx).unwrap()
    }
}
