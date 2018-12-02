use num_traits::{One, Zero};
use std::mem;

use poly::exponent::Exponent;
use poly::ring::Ring;

use fnv::FnvHashMap;
use number;
use number::Number;
use poly::raw::finitefield::FiniteField;
use poly::raw::zp;
use poly::raw::zp::{ufield, FastModulus};
use poly::raw::zp_mod::Modulus;
use poly::raw::MultivariatePolynomial;
use poly::ring::MulModNum;
use poly::ring::ToFiniteField;
use rand;
use rand::distributions::{Distribution, Uniform};
use rand::Rng;
use std::cmp::{max, min};
use std::collections::hash_map::Entry;
use tools::GCD;

use ndarray::{arr1, Array};
use poly::raw::zp_solve::{solve, solve_subsystem, LinearSolverError};

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

/// The maximum power of a variable that is cached
pub const POW_CACHE_SIZE: usize = 1000;
pub const INITIAL_POW_MAP_SIZE: usize = 1000;

/// The upper bound of the range to be sampled during the computation of multiple gcds
pub const MAX_RNG_PREFACTOR: u32 = 5000;

enum GCDError {
    BadOriginalImage,
    BadCurrentImage,
}

fn newton_interpolation<E: Exponent>(
    a: &[FiniteField],
    u: &[MultivariatePolynomial<FiniteField, E>],
    p: &FastModulus,
    x: usize, // the variable indexs to extend the polynomial by
) -> MultivariatePolynomial<FiniteField, E> {
    // compute inverses
    let mut gammas = vec![];
    for k in 1..a.len() {
        let mut pr = a[k] - a[0];
        for i in 1..k {
            pr = pr * (a[k] - a[i]);
        }
        gammas.push(FiniteField::new(zp::inv(pr.n, p), p.value()));
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
    let xp = MultivariatePolynomial::from_monomial(FiniteField::new(1, p.value()), e);
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
    p: &FastModulus,
) -> Result<MultivariatePolynomial<FiniteField, E>, GCDError> {
    let mut rng = rand::thread_rng();
    let range = Uniform::new(1, p.value());

    let mut system = vec![]; // coefficients for the linear system
    let mut ni = 0;
    let mut failure_count = 0;

    let mut rank_failure_count = 0;
    let mut last_rank = (0, 0);

    // store a table for variables raised to a certain power
    let mut cache = (0..ap.nvars)
        .map(|i| {
            vec![
                0;
                min(
                    max(ap.degree(i), bp.degree(i)).as_() as usize + 1,
                    POW_CACHE_SIZE
                )
            ]
        })
        .collect::<Vec<_>>();

    let var_bound = max(ap.degree(var).as_(), bp.degree(var).as_()) as usize + 1;
    let has_small_exp = var_bound < POW_CACHE_SIZE;

    // store a power map for the univariate polynomials that will be sampled
    // the sampling_polynomial routine will set the power to 0 after use.
    // If the exponent is small enough, we use a vec, otherwise we use a hashmap.
    let (mut tm, mut tm_fixed) = if has_small_exp {
        (
            FnvHashMap::with_hasher(Default::default()),
            vec![0; var_bound],
        )
    } else {
        (
            FnvHashMap::with_capacity_and_hasher(INITIAL_POW_MAP_SIZE, Default::default()),
            vec![],
        )
    };

    'newimage: loop {
        // generate random numbers for all non-leading variables
        // TODO: apply a Horner scheme to speed up the substitution?
        let mut failcount = 0;
        let (r, a1, b1) = loop {
            for v in &mut cache {
                for vi in v {
                    *vi = 0;
                }
            }

            let r: Vec<(usize, ufield)> = vars
                .iter()
                .map(|i| (i.clone(), range.sample(&mut rng)))
                .collect();

            let a1 = if has_small_exp {
                ap.sample_polynomial_small_exponent(var, p, &r, &mut cache, &mut tm_fixed)
            } else {
                ap.sample_polynomial(var, p, &r, &mut cache, &mut tm)
            };
            let b1 = if has_small_exp {
                bp.sample_polynomial_small_exponent(var, p, &r, &mut cache, &mut tm_fixed)
            } else {
                bp.sample_polynomial(var, p, &r, &mut cache, &mut tm)
            };

            if a1.ldegree(var) == aldegree && b1.ldegree(var) == bldegree {
                break (r, a1, b1);
            }

            failcount += 1;
            if failcount > 10 {
                panic!(
                "Cannot find samples with the right bounds after 10 tries: {} {} {} {}\nap={}\nbp={}\na1={}\nb1={}",
                a1.ldegree(var),
                aldegree,
                b1.ldegree(var),
                bldegree,
                ap,
                bp,
                a1,
                b1
            )
            }
        };

        let g1 = MultivariatePolynomial::univariate_gcd(&a1, &b1);
        trace!("GCD of sample at point {:?}: {}", r, g1);

        if g1.ldegree(var).as_() < bounds[var] {
            // original image and form and degree bounds are unlucky
            // change the bound and try a new prime
            bounds[var] = g1.ldegree(var).as_();
            debug!("Unlucky degree bound");
            return Err(GCDError::BadOriginalImage);
        }

        if g1.ldegree(var).as_() > bounds[var] {
            failure_count += 1;
            if failure_count > 2 || failure_count > ni {
                // p is likely unlucky
                debug!(
                    "Bad current image: gcd({},{}) mod {} under {:?} = {}",
                    ap,
                    bp,
                    p.value(),
                    r,
                    g1
                );
                return Err(GCDError::BadCurrentImage);
            }
            debug!("Degree too high");
            continue;
        }

        // check if the single scaling is there, if we had a single scale
        let mut scale_factor = FiniteField::new(1, p.value());
        if let Some(scaling_index) = single_scale {
            // construct the scaling coefficient
            let mut coeff = FiniteField::new(1, p.value());
            let (ref c, ref d) = gfu[scaling_index];
            for &(n, v) in r.iter() {
                coeff = coeff * zp::pow(v, c.exponents(0)[n].as_(), p);
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
                debug!("Bad original image");
                return Err(GCDError::BadOriginalImage);
            }
        }

        // check if all the monomials of the image appear in the shape
        // if not, the original shape is bad
        for m in g1.into_iter() {
            if gfu.iter().all(|(_, pow)| *pow != m.exponents[var].as_()) {
                debug!("Bad shape: terms missing");
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
        // for single scaling, we split the matrix into (potentially overdetermined) block-submatrices
        if let Some(..) = single_scale {
            // construct the gcd
            let mut gp = MultivariatePolynomial::with_nvars(ap.nvars);

            for (i, &(ref c, ref ex)) in gfu.iter().enumerate() {
                let mut gfm = vec![];
                let mut rhs = vec![0; system.len()];

                for (j, &(ref r, ref g, ref scale_factor)) in system.iter().enumerate() {
                    let mut row = vec![];

                    // note that we ignore the coefficient of the shape
                    for t in 0..c.nterms {
                        let mut coeff = FiniteField::new(1, p.value());
                        for &(n, v) in r.iter() {
                            coeff = coeff * zp::pow(v, c.exponents(t)[n].as_(), p);
                        }
                        row.push(coeff.n);
                    }

                    // move the coefficients of the image to the rhs
                    if i < g.nterms && g.exponents(i)[var].as_() == *ex {
                        rhs[j] =
                            zp::sub(rhs[j], zp::mul(g.coefficients[i].n, scale_factor.n, p), p);
                    } else {
                        // find the matching term if it exists
                        for m in g.into_iter() {
                            if m.exponents[var].as_() == *ex {
                                rhs[j] =
                                    zp::sub(rhs[j], zp::mul(m.coefficient.n, scale_factor.n, p), p);
                                break;
                            }
                        }
                    }

                    gfm.extend(row);
                }

                let m = Array::from_shape_vec((system.len(), c.nterms), gfm).unwrap();

                match solve(&m, &arr1(&rhs), p) {
                    Ok(x) => {
                        debug!("Solution: {:?}", x);

                        let mut i = 0; // index in the result x
                        for mv in c.into_iter() {
                            let mut ee = mv.exponents.to_vec();
                            ee[var] = E::from_u32(ex.clone()).unwrap();

                            gp.append_monomial(FiniteField::new(x[i].clone(), p.value()), &ee);
                            i += 1;
                        }
                    }
                    Err(LinearSolverError::Underdetermined { min_rank, max_rank }) => {
                        debug!("Underdetermined system 1");

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
                            gp = MultivariatePolynomial::zero();
                            break;
                        }
                    }
                    Err(LinearSolverError::Inconsistent) => {
                        debug!("Inconsistent system");
                        return Err(GCDError::BadOriginalImage);
                    }
                }
            }

            if !gp.is_zero() {
                debug!("Reconstructed {}", gp);
                return Ok(gp);
            }
        } else {
            // multiple scaling case: construct subsystems with augmented
            // columns for the scaling factors
            let mut subsystems = Vec::with_capacity(gfu.len());
            for (i, &(ref c, ref ex)) in gfu.iter().enumerate() {
                let mut gfm = vec![];

                for (j, &(ref r, ref g, ref _scale_factor)) in system.iter().enumerate() {
                    let mut row = Vec::with_capacity(c.nterms + system.len());

                    for t in 0..c.nterms {
                        let mut coeff = FiniteField::new(1, p.value());
                        for &(n, v) in r.iter() {
                            coeff = coeff * zp::pow(v, c.exponents(t)[n].as_(), p);
                        }
                        row.push(coeff.n);
                    }

                    // it could be that some coefficients of g are
                    // 0, so we have to be careful to find the matching monomial
                    for ii in 1..system.len() {
                        if ii == j {
                            if i < g.nterms && g.exponents(i)[var].as_() == *ex {
                                row.push(g.coefficients[i].n);
                            } else {
                                // find the matching term or otherwise, push 0
                                let mut found = false;
                                for m in g.into_iter() {
                                    if m.exponents[var].as_() == *ex {
                                        row.push(m.coefficient.n);
                                        found = true;
                                        break;
                                    }
                                }
                                if !found {
                                    row.push(0);
                                }
                            }
                        } else {
                            row.push(0);
                        }
                    }

                    // the scaling of the first image is fixed to 1
                    // we add it as a last column, since that is the rhs
                    if j == 0 {
                        if i < g.nterms && g.exponents(i)[var].as_() == *ex {
                            row.push(g.coefficients[i].n);
                        } else {
                            // find the matching term or otherwise, push 0
                            let mut found = false;
                            for m in g.into_iter() {
                                if m.exponents[var].as_() == *ex {
                                    row.push(m.coefficient.n);
                                    found = true;
                                    break;
                                }
                            }
                            if !found {
                                row.push(0);
                            }
                        }
                    } else {
                        row.push(0);
                    }

                    gfm.extend(row);
                }

                // bring each subsystem to upper triangular form
                let mut m =
                    Array::from_shape_vec((system.len(), c.nterms + system.len()), gfm).unwrap();

                match solve_subsystem(&mut m, c.nterms, p) {
                    Ok(..) => {
                        subsystems.push(m);
                    }
                    Err(LinearSolverError::Underdetermined { min_rank, max_rank }) => {
                        debug!("Underdetermined system 2");

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
                            break;
                        }
                    }
                    Err(LinearSolverError::Inconsistent) => {
                        debug!("Inconsistent system");
                        return Err(GCDError::BadOriginalImage);
                    }
                }
            }

            if subsystems.len() == gfu.len() {
                // construct a system for the scaling constants
                let mut sys = vec![];
                let mut rhs = vec![];
                for s in &subsystems {
                    for r in s.genrows() {
                        // only include rows that only depend on scaling constants
                        if r.iter().take(s.cols() - system.len()).any(|&x| x != 0) {
                            continue;
                        }

                        // note the last column is the rhs, so we skip it
                        sys.extend(
                            r.iter()
                                .skip(s.cols() - system.len())
                                .take(system.len() - 1)
                                .cloned(),
                        );

                        rhs.push(zp::neg(r.iter().last().unwrap().clone(), p));
                    }
                }

                let m = Array::from_shape_vec((rhs.len(), system.len() - 1), sys).unwrap();
                match solve(&m, &arr1(&rhs), p) {
                    Ok(x) => {
                        debug!("Solved scaling constants: {:?}", x);

                        let mut gp = MultivariatePolynomial::with_nvars(ap.nvars);

                        // now we fill in the constants in the subsystems and solve it
                        let mut si = 0;
                        for s in &mut subsystems {
                            // convert to arrays
                            let mut m = Vec::with_capacity(s.rows() * s.rows());
                            let mut rhs = Vec::with_capacity(s.rows());
                            let k = s.cols() - system.len();
                            for r in s.genrows() {
                                if r.iter().take(s.cols() - system.len()).all(|&x| x == 0) {
                                    continue;
                                }

                                let mut coeff = 0;
                                for (i, &xx) in r.iter().enumerate() {
                                    if i < k {
                                        m.push(xx);
                                    } else {
                                        if i == r.len() - 1 {
                                            coeff = zp::sub(coeff, xx, p);
                                        } else {
                                            coeff = zp::sub(coeff, zp::mul(xx, x[i - k], p), p);
                                        }
                                    }
                                }
                                rhs.push(coeff);
                            }

                            // solve the system and plug in the scaling constants
                            let mm = Array::from_shape_vec((rhs.len(), k), m).unwrap();
                            match solve(&mm, &arr1(&rhs), p) {
                                Ok(x) => {
                                    // for every power of the main variable
                                    let mut i = 0; // index in the result x
                                    let (ref c, ref ex) = gfu[si];
                                    for mv in c.into_iter() {
                                        let mut ee = mv.exponents.to_vec();
                                        ee[var] = E::from_u32(ex.clone()).unwrap();

                                        gp.append_monomial(
                                            FiniteField::new(x[i].clone(), p.value()),
                                            &ee,
                                        );
                                        i += 1;
                                    }
                                }
                                Err(LinearSolverError::Underdetermined { min_rank, max_rank }) => {
                                    debug!("Underdetermined system 3: {}/{}", ni, nx);

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
                                        gp = MultivariatePolynomial::with_nvars(ap.nvars);
                                        break;
                                    }
                                }
                                Err(LinearSolverError::Inconsistent) => {
                                    debug!("Inconsistent system");
                                    return Err(GCDError::BadOriginalImage);
                                }
                            }

                            si += 1;
                        }

                        if !gp.is_zero() {
                            debug!("Reconstructed {}", gp);
                            return Ok(gp);
                        }
                    }
                    Err(LinearSolverError::Underdetermined { min_rank, max_rank }) => {
                        debug!(
                            "Underdetermined system 4: {}/{}, rank: {}/{}",
                            ni, nx, min_rank, max_rank
                        );

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
    }
}

impl<E: Exponent> MultivariatePolynomial<FiniteField, E> {
    /// Optimized division routine for the univariate case in a finite field.
    fn divmod_finite(
        &self,
        div: &mut MultivariatePolynomial<FiniteField, E>,
        p: &FastModulus,
    ) -> (
        MultivariatePolynomial<FiniteField, E>,
        MultivariatePolynomial<FiniteField, E>,
    ) {
        if div.nterms == 1 {
            // calculate inverse once
            let inv = zp::inv(div.coefficients[0].n, p);

            if div.is_constant() {
                let mut q = self.clone();
                for c in &mut q.coefficients {
                    c.n = zp::mul(c.n, inv, p);
                }

                return (q, MultivariatePolynomial::with_nvars(self.nvars));
            }

            let mut q = MultivariatePolynomial::with_nvars_and_capacity(self.nvars, self.nterms);
            let mut r = MultivariatePolynomial::with_nvars(self.nvars);
            let dive = div.exponents(0);

            for m in self.into_iter() {
                if m.exponents.iter().zip(dive).all(|(a, b)| a >= b) {
                    q.coefficients.push(FiniteField::new(
                        zp::mul(m.coefficient.n, inv, p),
                        p.value(),
                    ));

                    for (ee, ed) in m.exponents.iter().zip(dive) {
                        q.exponents.push(*ee - *ed);
                    }
                    q.nterms += 1;
                } else {
                    r.coefficients.push(m.coefficient.clone());
                    r.exponents.extend(m.exponents);
                    r.nterms += 1;
                }
            }
            return (q, r);
        }

        // normalize the lcoeff to 1 to prevent a costly inversion
        if !div.lcoeff().is_one() {
            let o = div.lcoeff().n;
            let inv = zp::inv(div.lcoeff().n, p);

            for c in &mut div.coefficients {
                c.n = zp::mul(c.n, inv, p);
            }

            let mut res = self.synthetic_division(div);

            for c in &mut res.0.coefficients {
                c.n = zp::mul(c.n, o, p);
            }

            for c in &mut div.coefficients {
                c.n = zp::mul(c.n, o, p);
            }
            return res;
        }

        // fall back to generic case
        self.synthetic_division(div)
    }

    /// Compute the univariate GCD using Euclid's algorithm. The result is normalized to 1.
    fn univariate_gcd(
        a: &MultivariatePolynomial<FiniteField, E>,
        b: &MultivariatePolynomial<FiniteField, E>,
    ) -> MultivariatePolynomial<FiniteField, E> {
        if a.is_zero() {
            return b.clone();
        }
        if b.is_zero() {
            return a.clone();
        }

        let mut c = a.clone();
        let mut d = b.clone();
        if a.ldegree_max() < b.ldegree_max() {
            mem::swap(&mut c, &mut d);
        }

        let p = FastModulus::from(a.coefficients[0].p);

        // TODO: there exists an efficient algorithm for univariate poly
        // division in a finite field using FFT
        let mut r = c.divmod_finite(&mut d, &p).1;
        while !r.is_zero() {
            c = d;
            d = r;
            r = c.divmod_finite(&mut d, &p).1;
        }

        // normalize the gcd
        let l = d.coefficients.last().unwrap().clone();
        for x in &mut d.coefficients {
            *x = x.clone() / l.clone();
        }

        d
    }

    /// Replace all variables except `v` in the polynomial by elements from
    /// a finite field of size `p`.
    pub fn sample_polynomial(
        &self,
        v: usize,
        p: &FastModulus,
        r: &[(usize, ufield)],
        cache: &mut [Vec<ufield>],
        tm: &mut FnvHashMap<E, ufield>,
    ) -> MultivariatePolynomial<FiniteField, E> {
        for mv in self.into_iter() {
            let mut c = mv.coefficient.n;
            for &(n, vv) in r {
                let exp = mv.exponents[n].as_() as usize;
                if exp > 0 {
                    if n < cache[n].len() {
                        if cache[n][exp].is_zero() {
                            cache[n][exp] = zp::pow(vv, exp as u32, p);
                        }

                        c = zp::mul(c, cache[n][exp], p)
                    } else {
                        c = zp::mul(c, zp::pow(vv, exp as u32, p), p);
                    }
                }
            }

            match tm.entry(mv.exponents[v]) {
                Entry::Occupied(mut e) => {
                    *e.get_mut() = zp::add(*e.get(), c, p);
                }
                Entry::Vacant(mut e) => {
                    e.insert(c);
                }
            }
        }

        let mut res = MultivariatePolynomial::with_nvars(self.nvars);
        let mut e = vec![E::zero(); self.nvars];
        for (k, c) in tm {
            if *c > 0 {
                e[v] = *k;
                res.append_monomial(FiniteField::new(mem::replace(c, 0), p.value()), &e);
                e[v] = E::zero();
            }
        }

        res
    }

    /// Replace all variables except `v` in the polynomial by elements from
    /// a finite field of size `p`. The exponent of `v` should be small.
    pub fn sample_polynomial_small_exponent(
        &self,
        v: usize,
        p: &FastModulus,
        r: &[(usize, ufield)],
        cache: &mut [Vec<ufield>],
        tm: &mut [ufield],
    ) -> MultivariatePolynomial<FiniteField, E> {
        for mv in self.into_iter() {
            let mut c = mv.coefficient.n;
            for &(n, vv) in r {
                let exp = mv.exponents[n].as_() as usize;
                if exp > 0 {
                    if n < cache[n].len() {
                        if cache[n][exp].is_zero() {
                            cache[n][exp] = zp::pow(vv, exp as u32, p);
                        }

                        c = zp::mul(c, cache[n][exp], p)
                    } else {
                        c = zp::mul(c, zp::pow(vv, exp as u32, p), p);
                    }
                }
            }

            let expv = mv.exponents[v].as_() as usize;
            tm[expv] = zp::add(tm[expv], c, p);
        }

        // TODO: add bounds estimate
        let mut res = MultivariatePolynomial::with_nvars(self.nvars);
        let mut e = vec![E::zero(); self.nvars];
        for (k, c) in tm.iter_mut().enumerate() {
            if *c > 0 {
                e[v] = E::from_usize(k).unwrap();
                res.append_monomial_back(FiniteField::new(mem::replace(c, 0), p.value()), &e);
                e[v] = E::zero();
            }
        }

        res
    }

    /// Compute the gcd shape of two polynomials in a finite field by filling in random
    /// numbers.
    fn gcd_shape_modular(
        a: &MultivariatePolynomial<FiniteField, E>,
        b: &MultivariatePolynomial<FiniteField, E>,
        vars: &[usize],           // variables
        bounds: &mut [u32],       // degree bounds
        tight_bounds: &mut [u32], // tighter degree bounds
        p: &FastModulus,
    ) -> Option<MultivariatePolynomial<FiniteField, E>> {
        let lastvar = vars.last().unwrap().clone();

        // if we are in the univariate case, return the univariate gcd
        // TODO: this is a modification of the algorithm!
        if vars.len() == 1 {
            let gg = MultivariatePolynomial::univariate_gcd(&a, &b);
            if gg.degree(vars[0]).as_() > bounds[vars[0]] {
                return None;
            }
            bounds[vars[0]] = gg.degree(vars[0]).as_(); // update degree bound
            return Some(gg);
        }

        // the gcd of the content in the last variable should be 1
        let c = MultivariatePolynomial::multivariate_content_gcd(a, b, lastvar);
        if !c.is_one() {
            debug!("Content in last variable is not 1, but {}!", c);
            return None;
        }

        let gamma = MultivariatePolynomial::univariate_gcd(
            &a.lcoeff_last_varorder(vars),
            &b.lcoeff_last_varorder(vars),
        );

        let mut rng = rand::thread_rng();
        let range = Uniform::new(1, p.value());

        let mut failure_count = 0;

        'newfirstnum: loop {
            // if we had two failures, it may be that the tight degree bound
            // was too tight due to an unfortunate prime/evaluation, so we relax it
            if failure_count == 2 {
                debug!(
                    "Changing tight bound for x{} from {} to {}",
                    lastvar, tight_bounds[lastvar], bounds[lastvar]
                );
                tight_bounds[lastvar] = bounds[lastvar];
            }
            failure_count += 1;

            let v = loop {
                let a = FiniteField::new(range.sample(&mut rng), p.value());
                if !gamma.replace(lastvar, a).is_zero() {
                    break a;
                }
            };

            debug!("Chosen variable: {}", v);
            let av = a.replace(lastvar, v);
            let bv = b.replace(lastvar, v);

            // performance dense reconstruction
            let mut gv = if vars.len() > 2 {
                match MultivariatePolynomial::gcd_shape_modular(
                    &av,
                    &bv,
                    &vars[..vars.len() - 1],
                    bounds,
                    tight_bounds,
                    p,
                ) {
                    Some(x) => x,
                    None => return None,
                }
            } else {
                let gg = MultivariatePolynomial::univariate_gcd(&av, &bv);
                if gg.degree(vars[0]).as_() > bounds[vars[0]] {
                    return None;
                }
                bounds[vars[0]] = gg.degree(vars[0]).as_(); // update degree bound
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
                let mut nx1 = (gv.nterms() - 1) / (gfu.len() - 1);
                if (gv.nterms() - 1) % (gfu.len() - 1) != 0 {
                    nx1 += 1;
                }
                if nx < nx1 {
                    nx = nx1;
                }
                debug!("Multiple scaling case: sample {} times", nx);
            }

            // we need one extra sample to detect inconsistencies, such
            // as missing terms in the shape.
            // NOTE: not in paper
            nx += 1;

            let mut lc = gv.lcoeff_varorder(vars);
            let mut gseq = vec![gv * (gamma.replace(lastvar, v).coefficients[0].clone() / lc)];
            let mut vseq = vec![v];

            // sparse reconstruction
            'newnum: loop {
                if gseq.len() == (tight_bounds[lastvar] + gamma.ldegree_max().as_() + 1) as usize {
                    break;
                }

                let v = loop {
                    let v = FiniteField::new(range.sample(&mut rng), p.value());
                    if !gamma.replace(lastvar, v).is_zero() {
                        // we need unique sampling points
                        if !vseq.contains(&v) {
                            break v;
                        }
                    }
                };

                let av = a.replace(lastvar, v);
                let bv = b.replace(lastvar, v);

                match construct_new_image(
                    &av,
                    &bv,
                    // NOTE: different from paper where they use a.degree(..)
                    // it could be that the degree in av is lower than that of a
                    // which means the sampling will never terminate
                    av.degree(vars[0]),
                    bv.degree(vars[0]),
                    bounds,
                    single_scale,
                    nx,
                    &vars[1..vars.len() - 1],
                    vars[0],
                    &gfu,
                    p,
                ) {
                    Ok(r) => {
                        gv = r;
                    }
                    Err(GCDError::BadOriginalImage) => {
                        debug!("Bad original image");
                        continue 'newfirstnum;
                    }
                    Err(GCDError::BadCurrentImage) => {
                        debug!("Bad current image");
                        continue 'newnum;
                    }
                }

                lc = gv.lcoeff_varorder(vars);
                gseq.push(gv * (gamma.replace(lastvar, v).coefficients[0].clone() / lc));
                vseq.push(v);
            }

            // use interpolation to construct x_n dependence
            let mut gc = newton_interpolation(&vseq, &gseq, p, lastvar);
            debug!("Interpolated: {}", gc);

            // remove content in x_n (wrt all other variables)
            let cont = gc.multivariate_content(lastvar);
            if !cont.is_one() {
                debug!("Removing content in x{}: {}", lastvar, cont);
                let cc = gc.divmod(&cont);
                debug_assert!(cc.1.is_zero());
                gc = cc.0;
            }

            // do a probabilistic division test
            let (g1, a1, b1) = loop {
                // store a table for variables raised to a certain power
                let mut cache = (0..a.nvars)
                    .map(|i| {
                        vec![
                            FiniteField::zero();
                            min(
                                max(a.degree(i), b.degree(i)).as_() as usize + 1,
                                POW_CACHE_SIZE
                            )
                        ]
                    })
                    .collect::<Vec<_>>();

                let r: Vec<(usize, FiniteField)> = vars
                    .iter()
                    .skip(1)
                    .map(|i| (*i, FiniteField::new(range.sample(&mut rng), p.value())))
                    .collect();

                let g1 = gc.replace_all_except(vars[0], &r, &mut cache);

                if g1.ldegree(vars[0]) == gc.degree(vars[0]) {
                    let a1 = a.replace_all_except(vars[0], &r, &mut cache);
                    let b1 = b.replace_all_except(vars[0], &r, &mut cache);
                    break (g1, a1, b1);
                }
            };

            if g1.is_one() || (a1.divmod(&g1).1.is_zero() && b1.divmod(&g1).1.is_zero()) {
                return Some(gc);
            }

            // if the gcd is bad, we had a bad number
            debug!(
                "Division test failed: gcd may be bad or probabilistic division test is unlucky: a1 {} b1 {} g1 {}", a1, b1, g1
            );
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

    /// Get the content of a multivariate polynomial viewed as a
    /// multivariate polynomial in all variables except `x`.
    pub fn multivariate_content(&self, x: usize) -> MultivariatePolynomial<R, E> {
        let af = self.to_multivariate_polynomial(&[x], false);
        MultivariatePolynomial::gcd_multiple(af.values().cloned().collect())
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

        // check if all entries are numbers
        // in this case summing them may give bad gcds often
        if f.iter().all(|x| x.is_constant()) {
            let mut gcd = f.swap_remove(0);
            for x in f.iter() {
                gcd = MultivariatePolynomial::gcd(&gcd, x);
            }
            return gcd;
        }

        // TODO: extract gcd of content first, since that may easily cause a miss!
        let mut rng = rand::thread_rng();
        let mut k = 1; // counter for scalar multiple
        let mut gcd;

        // take the smallest element
        let mut index_smallest = f
            .iter()
            .enumerate()
            .min_by_key(|(_, v)| v.nterms)
            .unwrap()
            .0;

        loop {
            let a = f.swap_remove(index_smallest);

            let term_bound = f.iter().map(|x| x.nterms).sum();
            let mut b = MultivariatePolynomial::with_nvars_and_capacity(a.nvars, term_bound);

            // Add all the monomials to a vector, sort them and build a new polynomial.
            // The last step will merge equal monomials.
            {
                let mut c = Vec::with_capacity(f.iter().map(|x| x.nterms).sum());

                for p in f.iter() {
                    for v in p.into_iter() {
                        c.push((v.coefficient.mul_num(k), v.exponents));
                    }
                    k = rng.gen_range(2, MAX_RNG_PREFACTOR);
                }

                c.sort_unstable_by(|a, b| a.1.cmp(b.1));
                for m in c {
                    b.append_monomial_back(m.0, m.1);
                }
            }

            gcd = MultivariatePolynomial::gcd(&a, &b);

            if gcd.is_one() {
                return gcd;
            }

            let mut newf: Vec<MultivariatePolynomial<R, E>> = Vec::with_capacity(f.len());
            for x in f.drain(..) {
                if !x.divmod(&gcd).1.is_zero() {
                    newf.push(x);
                }
            }

            if newf.len() == 0 {
                return gcd;
            }

            debug!(
                "Multiple-gcd was not found instantly. GCD guess: {}; Terms left: {}",
                gcd,
                newf.len()
            );

            newf.push(gcd);
            index_smallest = newf.len() - 1; // the gcd is the smallest element
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

    /// Find the upper bound of a variable `var` in the gcd.
    /// This is done by computing the univariate gcd by
    /// substituting all variables except `var`. This
    /// upper bound could be too tight due to an unfortunate
    /// sample point, but this is rare.
    pub fn get_gcd_var_bound(
        ap: &MultivariatePolynomial<FiniteField, E>,
        bp: &MultivariatePolynomial<FiniteField, E>,
        vars: &[usize],
        var: usize,
    ) -> E {
        let p = ap.coefficients[0].p;
        let fastp = FastModulus::from(p);
        let mut rng = rand::thread_rng();
        let range = Uniform::new(1, p);

        // store a table for variables raised to a certain power
        let mut cache = (0..ap.nvars)
            .map(|i| {
                vec![
                    0;
                    min(
                        max(ap.degree(i), bp.degree(i)).as_() as usize + 1,
                        POW_CACHE_SIZE
                    )
                ]
            })
            .collect::<Vec<_>>();

        // store a power map for the univariate polynomials that will be sampled
        // the sampling_polynomial routine will set the power to 0 after use
        let mut tm = FnvHashMap::with_capacity_and_hasher(INITIAL_POW_MAP_SIZE, Default::default());

        // generate random numbers for all non-leading variables
        // TODO: apply a Horner scheme to speed up the substitution?
        let (_, a1, b1) = loop {
            for v in &mut cache {
                for vi in v {
                    *vi = 0;
                }
            }

            let r: Vec<(usize, ufield)> = vars
                .iter()
                .map(|i| (i.clone(), range.sample(&mut rng)))
                .collect();

            let a1 = ap.sample_polynomial(var, &fastp, &r, &mut cache, &mut tm);
            let b1 = bp.sample_polynomial(var, &fastp, &r, &mut cache, &mut tm);

            if a1.ldegree(var) == ap.degree(var) && b1.ldegree(var) == bp.degree(var) {
                break (r, a1, b1);
            }

            debug!(
                "Degree error during sampling: trying again: a={}, a1=={}, bp={}, b1={}",
                ap, a1, bp, b1
            );
        };

        let g1 = MultivariatePolynomial::univariate_gcd(&a1, &b1);
        return g1.ldegree_max();
    }

    /// Compute the gcd of two multivariate polynomials.
    pub fn gcd(
        a: &MultivariatePolynomial<R, E>,
        b: &MultivariatePolynomial<R, E>,
    ) -> MultivariatePolynomial<R, E> {
        debug_assert_eq!(a.nvars, b.nvars);

        if a.is_zero() {
            return b.clone();
        }
        if b.is_zero() {
            return a.clone();
        }

        // if we have two numbers, use the integer gcd
        if a.is_constant() && b.is_constant() {
            return MultivariatePolynomial::from_constant_with_nvars(
                GCD::gcd(a.coefficients[0].clone(), b.coefficients[0].clone()),
                a.nvars,
            );
        }

        debug!("Compute gcd({}, {})", a, b);

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

        let mut vars: Vec<_> = scratch
            .iter()
            .enumerate()
            .filter_map(|(i, v)| if *v == 3 { Some(i) } else { None })
            .collect();

        // remove the gcd of the content wrt the first variable
        // TODO: don't do for univariate poly
        debug!("Starting content computation");
        let c = MultivariatePolynomial::univariate_content_gcd(a, b, vars[0]);
        debug!("GCD of content: {}", c);

        if !c.is_one() {
            let x1 = a.divmod(&c);
            let x2 = b.divmod(&c);

            assert!(x1.1.is_zero());
            assert!(x2.1.is_zero());

            return c * MultivariatePolynomial::gcd(&x1.0, &x2.0);
        }

        // determine safe bounds for variables in the gcd
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

        // find better upper bounds for all variables
        // these bounds could actually be wrong due to an unfortunate prime or sampling points
        let mut tight_bounds = bounds.clone();
        let mut i = 0;
        loop {
            let ap = a.to_finite_field(LARGE_U32_PRIMES[i]);
            let bp = b.to_finite_field(LARGE_U32_PRIMES[i]);
            if ap.nterms > 0
                && bp.nterms > 0
                && ap.last_exponents() == a.last_exponents()
                && bp.last_exponents() == b.last_exponents()
            {
                for var in vars.iter() {
                    let mut vvars = vars
                        .iter()
                        .filter(|i| *i != var)
                        .cloned()
                        .collect::<Vec<_>>();
                    tight_bounds[*var] = MultivariatePolynomial::<Number, E>::get_gcd_var_bound(
                        &ap, &bp, &vvars, *var,
                    )
                    .as_();
                }
                break;
            } else {
                debug!("Variable bounds failed due to unlucky prime");
                i += 1;
            }
        }

        // Determine a good variable ordering based on the estimated degree (decreasing) in the gcd.
        // If it is different from the input, make a copy and rearrange so that the
        // polynomials do not have to be sorted after filling in variables.
        // TODO: understand better why copying is so much faster (about 10%) than using a map
        vars.sort_by(|&i, &j| tight_bounds[j].cmp(&tight_bounds[i]));

        if vars.len() == 1 || vars.windows(2).all(|s| s[0] < s[1]) {
            debug!("Computing gcd without map");
            PolynomialGCD::gcd(&a, &b, &vars, &mut bounds, &mut tight_bounds)
        } else {
            debug!("Rearranging variables with map: {:?}", vars);
            let aa = a.rearrange(&vars, false);
            let bb = b.rearrange(&vars, false);

            let mut newbounds = vec![0; bounds.len()];
            for x in 0..vars.len() {
                newbounds[x] = bounds[vars[x]];
            }

            let mut newtight_bounds = vec![0; bounds.len()];
            for x in 0..vars.len() {
                newtight_bounds[x] = tight_bounds[vars[x]];
            }

            // we need to extract the content if the first variable changed
            if vars[1..].iter().any(|&c| c < vars[0]) {
                debug!("Starting new content computation after mapping {:?}", vars);
                let c = MultivariatePolynomial::univariate_content_gcd(&aa, &bb, 0);
                debug!("New content: {}", c);
                if !c.is_one() {
                    let x1 = aa.divmod(&c);
                    let x2 = bb.divmod(&c);

                    assert!(x1.1.is_zero());
                    assert!(x2.1.is_zero());

                    let gcd = c * PolynomialGCD::gcd(
                        &x1.0,
                        &x2.0,
                        &(0..vars.len()).collect::<Vec<_>>(),
                        &mut newbounds,
                        &mut newtight_bounds,
                    );
                    return gcd.rearrange(&vars, true);
                }
            }

            let gcd = PolynomialGCD::gcd(
                &aa,
                &bb,
                &(0..vars.len()).collect::<Vec<_>>(),
                &mut newbounds,
                &mut newtight_bounds,
            );

            gcd.rearrange(&vars, true)
        }
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
        tight_bounds: &mut [u32],
    ) -> MultivariatePolynomial<Number, E> {
        debug!("Compute modular gcd({},{})", a, b);

        #[cfg(debug_assertions)]
        {
            a.check_consistency();
            b.check_consistency();
        }

        // compute scaling factor in Z
        let gamma = GCD::gcd(a.lcoeff_varorder(vars), b.lcoeff_varorder(vars));
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
                a.check_consistency();
                b.check_consistency();
                panic!(
                    "Ran out of primes for gcd reconstruction.\ngcd({},{})",
                    a, b
                );
            }

            let mut p = LARGE_U32_PRIMES[pi];
            let mut fastp = FastModulus::from(p);

            let mut gammap = gamma.to_finite_field(p);
            let ap = a.to_finite_field(p);
            let bp = b.to_finite_field(p);

            debug!("New first image: gcd({},{}) mod {}", ap, bp, p);

            // calculate modular gcd image
            let mut gp = match MultivariatePolynomial::gcd_shape_modular(
                &ap,
                &bp,
                vars,
                bounds,
                tight_bounds,
                &fastp,
            ) {
                Some(x) => x,
                None => {
                    debug!("Modular GCD failed: getting new prime");
                    continue 'newfirstprime;
                }
            };

            debug!("GCD suggestion: {}", gp);

            bounds[vars[0]] = gp.degree(vars[0]).as_();

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
                let mut nx1 = (gp.nterms() - 1) / (gfu.len() - 1);
                if (gp.nterms() - 1) % (gfu.len() - 1) != 0 {
                    nx1 += 1;
                }
                if nx < nx1 {
                    nx = nx1;
                }
                debug!("Multiple scaling case: sample {} times", nx);
            }

            // we need one extra sample to detect inconsistencies, such
            // as missing terms in the shape.
            // NOTE: not in paper
            nx += 1;

            let gpc = gp.lcoeff_varorder(vars);

            // construct the gcd suggestion in Z
            let mut gm = MultivariatePolynomial::with_nvars(gp.nvars);
            gm.nterms = gp.nterms;
            gm.exponents = gp.exponents.clone();
            gm.coefficients = gp
                .coefficients
                .iter()
                .map(|x| Number::from_finite_field(&(x.clone() * gammap / gpc)))
                .collect();

            let mut m = Number::SmallInt(p as isize); // used for CRT

            debug!("GCD suggestion with gamma: {} mod {} ", gm, p);

            let mut old_gm = MultivariatePolynomial::with_nvars(a.nvars);

            // add new primes until we can reconstruct the full gcd
            'newprime: loop {
                if gm == old_gm {
                    // divide by integer content
                    let gmc = gm.content();
                    let mut gc = gm.clone();
                    gc.coefficients = gc
                        .coefficients
                        .iter()
                        .map(|x| x.clone() / gmc.clone())
                        .collect();

                    debug!("Final suggested gcd: {}", gc);
                    if gc.is_one() || (a.divmod(&gc).1.is_zero() && b.divmod(&gc).1.is_zero()) {
                        return gc;
                    }

                    // if it does not divide, we need more primes
                    debug!("Does not divide: more primes needed");
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
                    a.check_consistency();
                    b.check_consistency();
                    panic!(format!(
                        "Ran out of primes for gcd images.\ngcd({},{})\nAttempt: {}\n vars: {:?}, bounds: {:?}; {:?}",
                        a, b, gm, vars, bounds, tight_bounds
                    ));
                }

                p = LARGE_U32_PRIMES[pi];
                fastp = FastModulus::from(p);

                gammap = gamma.to_finite_field(p);
                let ap = a.to_finite_field(p);
                let bp = b.to_finite_field(p);
                debug!("New image: gcd({},{}) mod {}", ap, bp, p);

                // for the univariate case, we don't need to construct an image
                if vars.len() == 1 {
                    gp = MultivariatePolynomial::univariate_gcd(&ap, &bp);
                    if gp.degree(vars[0]).as_() < bounds[vars[0]] {
                        // original image and variable bound unlucky: restart
                        debug!("Unlucky original image: restart");
                        continue 'newfirstprime;
                    }

                    if gp.degree(vars[0]).as_() > bounds[vars[0]] {
                        // prime is probably unlucky
                        debug!("Unlucky current image: try new one");
                        continue 'newprime;
                    }

                    for m in gp.into_iter() {
                        if gfu
                            .iter()
                            .all(|(_, pow)| *pow != m.exponents[vars[0]].as_())
                        {
                            debug!("Bad shape: terms missing");
                            continue 'newfirstprime;
                        }
                    }
                } else {
                    match construct_new_image(
                        &ap,
                        &bp,
                        // NOTE: different from paper where they use a.degree(..)
                        // it could be that the degree in ap is lower than that of a
                        // which means the sampling will never terminate
                        ap.degree(vars[0]),
                        bp.degree(vars[0]),
                        bounds,
                        single_scale,
                        nx,
                        &vars[1..],
                        vars[0],
                        &gfu,
                        &fastp,
                    ) {
                        Ok(r) => {
                            gp = r;
                        }
                        Err(GCDError::BadOriginalImage) => continue 'newfirstprime,
                        Err(GCDError::BadCurrentImage) => continue 'newprime,
                    }
                }

                // scale the new image
                let gpc = gp.lcoeff_varorder(vars);
                gp = gp * (gammap / gpc);
                debug!("gp: {} mod {}", gp, gpc.p);

                // use chinese remainder theorem to merge coefficients and map back to Z
                // terms could be missing in gp, but not in gm (TODO: check this?)
                let mut gpi = 0;
                for t in 0..gm.nterms {
                    let gpc = if gm.exponents(t) == gp.exponents(gpi) {
                        gpi += 1;
                        gp.coefficients[gpi - 1].n
                    } else {
                        0
                    };

                    let mut gmc = &mut gm.coefficients[t];
                    let mut coeff = if *gmc < Number::SmallInt(0) {
                        gmc.clone() + m.clone()
                    } else {
                        gmc.clone()
                    };

                    *gmc = number::chinese_remainder(
                        coeff,
                        Number::SmallInt(gpc as isize),
                        m.clone(),
                        Number::SmallInt(p as isize),
                    );
                }

                m *= Number::SmallInt(p as isize);
                debug!("gm: {} from ring {}", gm, m);
            }
        }
    }
}

pub trait PolynomialGCD: Sized {
    fn gcd(
        a: &Self,
        b: &Self,
        vars: &[usize],
        bounds: &mut [u32],
        tight_bounds: &mut [u32],
    ) -> Self;
}

impl<E: Exponent> PolynomialGCD for MultivariatePolynomial<Number, E> {
    fn gcd(
        a: &MultivariatePolynomial<Number, E>,
        b: &MultivariatePolynomial<Number, E>,
        vars: &[usize],
        bounds: &mut [u32],
        tight_bounds: &mut [u32],
    ) -> MultivariatePolynomial<Number, E> {
        MultivariatePolynomial::gcd_zippel(&a, &b, vars, bounds, tight_bounds)
    }
}

impl<E: Exponent> PolynomialGCD for MultivariatePolynomial<FiniteField, E> {
    fn gcd(
        a: &MultivariatePolynomial<FiniteField, E>,
        b: &MultivariatePolynomial<FiniteField, E>,
        vars: &[usize],
        bounds: &mut [u32],
        tight_bounds: &mut [u32],
    ) -> MultivariatePolynomial<FiniteField, E> {
        assert!(!a.is_zero() || !b.is_zero());
        MultivariatePolynomial::gcd_shape_modular(
            &a,
            &b,
            vars,
            bounds,
            tight_bounds,
            &FastModulus::from(if a.is_zero() {
                b.coefficients[0].p
            } else {
                a.coefficients[0].p
            }),
        )
        .unwrap()
    }
}
