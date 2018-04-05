use num_traits::{One, Pow, Zero};
use std::mem;

use poly::exponent::Exponent;
use poly::ring::Ring;

use poly::raw::MultivariatePolynomial;
use poly::raw::finitefield::FiniteField;
use poly::ring::MulModNum;
use poly::ring::ToFiniteField;
use rand;
use rand::distributions::{Range, Sample};
use tools::GCD;

use ndarray::{Array, arr1};
use poly::raw::zp_solve::{solve, LinearSolverError};

enum GCDError {
    BadOriginalImage,
    BadCurrentImage,
}

fn newton_interpolation<E: Exponent>(
    a: &[FiniteField],
    u: &[MultivariatePolynomial<FiniteField, E>],
    p: usize,
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
    bounds: &mut [usize],
    single_scale: Option<usize>,
    nx: usize,
    vars: &[usize],
    var: usize,
    gfu: &[(MultivariatePolynomial<FiniteField, E>, usize)],
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
        let (r, a1, b1) = loop {
            let r: Vec<(usize, FiniteField)> = vars.iter()
                .map(|i| (i.clone(), FiniteField::new(range.sample(&mut rng), p)))
                .collect();

            let a1 = ap.replace_multiple(&r);
            let b1 = bp.replace_multiple(&r);

            if a1.ldegree() == aldegree && b1.ldegree() == bldegree {
                break (r, a1, b1);
            }
        };

        let g1 = MultivariatePolynomial::univariate_gcd(&a1, &b1);
        println!("GCD of sample at point {:?}: {}", r, g1);

        if g1.ldegree().as_() < bounds[0] {
            // original image and form and degree bounds are unlucky
            // change the bound and try a new prime
            bounds[0] = g1.ldegree().as_();
            return Err(GCDError::BadOriginalImage);
        }

        if g1.ldegree().as_() > bounds[0] {
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
                // g1 is univariate, so we can compare the maximum degree
                if g1.exponents(t).iter().max().unwrap().as_() == *d {
                    scale_factor = coeff / g1.coefficients[0];
                    println!("Single scale factor: {}", scale_factor);
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

        println!("GFU {:?}", gfu);

        // construct the linear system
        let mut gfm = vec![];

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
                for ii in 0..system.len() {
                    if ii == j {
                        // TODO: is i always the correct coefficient index?

                        // for the single scaling case, we scale the images in the matrix
                        // we also add rows (later) to the matrix that force all scaling constants
                        // to 1.
                        row.push((g.coefficients[i] * scale_factor.clone()).n);
                    } else {
                        row.push(0);
                    }
                }

                println!("{:?} {}", row, c);
                gfm.extend(row);
            }
        }

        let rows = gfu.len() * system.len();
        let cols = gfm.len() / rows;
        let mut newrows = rows;

        // add constraint row to set the first scaling coefficient to 1
        // or all of them, in case of single scaling
        let onecount = if single_scale == None {
            newrows += 1;
            1
        } else {
            newrows += system.len();
            system.len()
        };

        println!("gfm {:?} {:?} {} {}", gfm, system, rows, cols);

        let mut rhs = vec![0; newrows];
        for i in 0..onecount {
            let mut con = vec![0; cols];
            con[cols - system.len() + i] = 1;

            rhs[rows + i] = 1;
            gfm.extend(con);
        }

        let m = Array::from_shape_vec((newrows, cols), gfm).unwrap();

        println!("Solve matrix {:?}={:?}", m, rhs);

        match solve(&m, &arr1(&rhs), p) {
            Ok(x) => {
                println!("Solution: {:?}", x);
                // construct the gcd
                let mut gp = MultivariatePolynomial::with_nvars(ap.nvars);

                // for every power of the main variable
                let mut i = 0; // index in the result x
                for &(ref c, ref ex) in gfu.iter() {
                    for mv in c.into_iter() {
                        let mut ee = mv.exponents.to_vec();
                        ee[var] = E::from_usize(ex.clone()).unwrap();

                        gp.append_monomial(FiniteField::new(x[i].clone(), p), ee);
                        i += 1;
                    }
                }

                println!("Reconstructed {}", gp);
                return Ok(gp);
            }
            Err(LinearSolverError::Underdetermined { min_rank, max_rank }) => {
                println!("Underdetermined system");

                if last_rank == (min_rank, max_rank) {
                    rank_failure_count += 1;

                    if rank_failure_count == 3 {
                        println!("Same degrees of freedom encountered 3 times: assuming bad prime/evaluation point");
                        return Err(GCDError::BadCurrentImage);
                    }
                } else {
                    // update the rank and get new images
                    rank_failure_count = 0;
                    last_rank = (min_rank, max_rank);
                }
            }
            Err(LinearSolverError::Inconsistent) => {
                println!("Inconsistent system");
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
        vars: &[usize],   // variables
        dx: &mut [usize], // degree bounds
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
            println!("Content in last variable is not 1, but {}!", c);
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
                if gg.ldegree().as_() > dx[vars[0]] {
                    return None;
                }
                dx[vars[0]] = gg.ldegree().as_(); // update degree bound
                gg
            };

            println!(
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

            // In the case of multiple scaling, we need an additional sample
            // TODO: is this correct?
            if single_scale == None {
                nx += 1;
            }

            let mut lc = gv.lcoeff();
            let mut gseq = vec![
                gv * (gamma.replace(lastvar, v).coefficients[0].clone() / lc),
            ];
            let mut vseq = vec![v];

            // sparse reconstruction
            'newnum: loop {
                let v = loop {
                    let v = FiniteField::new(range.sample(&mut rng), a.coefficients[0].p);
                    if !gamma.replace(lastvar, v).is_zero() {
                        break v;
                    }
                };

                println!("Choose sample point {}", v);

                let av = a.replace(lastvar, v);
                let bv = b.replace(lastvar, v);

                match construct_new_image(
                    &av,
                    &bv,
                    a.ldegree(),
                    b.ldegree(),
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

                if gseq.len() == dx[lastvar] + gamma.ldegree_max().as_() + 1 {
                    break;
                }
            }

            // use interpolation to construct x_n dependence
            let mut gc = newton_interpolation(&vseq, &gseq, p, lastvar);
            println!("Interpolated: {} from {:?} -- {:?}", gc, vseq, gseq);

            // remove content in x_n
            let cont = gc.univariate_content(lastvar);
            let cc = gc.long_division(&cont);
            assert!(cc.1.is_zero());
            gc = cc.0;

            // do a probabilistic division test
            let (g1, a1, b1) = loop {
                let r: Vec<(usize, FiniteField)> = (1..a.nvars)
                    .map(|i| (i, FiniteField::new(range.sample(&mut rng), p)))
                    .collect();

                let g1 = gc.replace_multiple(&r);

                if g1.ldegree() == gc.ldegree() {
                    let a1 = a.replace_multiple(&r);
                    let b1 = b.replace_multiple(&r);
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
        println!("Multiple gcds of {:?}", f);

        if f.len() == 1 {
            return f[0].clone();
        }

        let mut k = 1; // counter for scalar multiple
        let mut gcd;

        loop {
            let a = f[0].clone(); // TODO: take the smallest?
            let mut b = MultivariatePolynomial::with_nvars(a.nvars);

            for p in f.iter().skip(1) {
                for v in p.into_iter() {
                    b.append_monomial(v.coefficient.mul_num(k), v.exponents.to_vec());
                }
                k += 1;
            }

            gcd = MultivariatePolynomial::gcd(&a, &b);

            let mut newf: Vec<MultivariatePolynomial<R, E>> = vec![];
            for x in &f {
                if !x.long_division(&gcd).1.is_zero() {
                    newf.push(x.clone());
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

        println!("Compute gcd({}, {})", a, b);

        // if we have two numbers, use the integer gcd
        if a.nterms == 1 && a.exponents.iter().all(|c| c.is_zero()) {
            if b.nterms == 1 && b.exponents.iter().all(|c| c.is_zero()) {
                return MultivariatePolynomial::from_constant_with_nvars(
                    GCD::gcd(a.coefficients[0], b.coefficients[0]),
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
        let c = MultivariatePolynomial::univariate_content_gcd(a, b, vars[0]);
        println!("GCD of content: {}", c);

        if !c.is_one() {
            let x1 = a.long_division(&c);
            let x2 = b.long_division(&c);

            assert!(x1.1.is_zero());
            assert!(x2.1.is_zero());

            return c * MultivariatePolynomial::gcd(&x1.0, &x2.0);
        }

        // TODO: get proper degree bounds on gcd. how?
        // for now: take the lowest degree for each variable
        let mut bounds: Vec<usize> = (0..a.nvars)
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

impl<E: Exponent> MultivariatePolynomial<i64, E> {
    /// Compute the gcd of two multivariate polynomials using Zippel's algorithm.
    /// TODO: provide a parallel implementation?
    fn gcd_zippel(
        a: &MultivariatePolynomial<i64, E>,
        b: &MultivariatePolynomial<i64, E>,
        vars: &[usize], // variables
        bounds: &mut [usize],
    ) -> MultivariatePolynomial<i64, E> {
        println!("Compute modular gcd({},{})", a, b);

        // compute scaling factor in Z
        println!("gamma comp {} {}", a.lcoeff(), b.lcoeff());
        let gamma = GCD::gcd(a.lcoeff(), b.lcoeff());
        println!("gamma {}", gamma);

        let primes = [
            4254797, 4255213, 4255609, 4256009, 4254799, 4255249, 4255619, 4256029, 4254821,
            4255301, 4255637, 4256051, 4254853, 4255313, 4255673, 4256089, 4254869, 4255351,
            4255679, 4256101, 4254883, 4255369, 4255697, 4256117, 4254911, 4255387, 4255739,
            4256141, 4254949, 4255399, 4255747, 4256159, 4254961, 4255403, 4255751, 4256167,
            4254983, 4255429, 4255781, 4256191, 4255039, 4255439, 4255789, 4256227, 4255057,
            4255451, 4255807, 4256233,
        ];

        let mut pi = 0;

        'newfirstprime: loop {
            pi += 1;
            for _ in pi..primes.len() {
                if !(gamma.mod_num(primes[pi])).is_zero() {
                    break;
                }
                pi += 1;
            }

            if pi == primes.len() {
                panic!("Ran out of primes for gcd reconstruction");
            }

            let mut p = primes[pi];

            let mut gammap = gamma.to_finite_field(p);
            let ap = a.to_finite_field(p);
            let bp = b.to_finite_field(p);

            println!("New first image: gcd({},{}) mod {}", ap, bp, p);

            // calculate modular gcd image
            let mut gp = loop {
                if let Some(x) = MultivariatePolynomial::gcd_shape_modular(&ap, &bp, vars, bounds) {
                    break x;
                }
            };

            println!("GCD suggestion: {}", gp);

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

            // In the case of multiple scaling, we need an additional sample
            // TODO: is this correct?
            if single_scale == None {
                nx += 1;
            }

            let gpc = gp.lcoeff();
            let mut gm = gp * (gammap / gpc);
            let mut m = p; // used for CRT

            println!("GCD suggestion with gamma: {}", gm);

            let mut old_gm = MultivariatePolynomial::<FiniteField, E>::with_nvars(a.nvars);

            // add new primes until we can reconstruct the full gcd
            'newprime: loop {
                if gm == old_gm.to_finite_field(m) {
                    // divide by lcoeff and convert from finite field
                    let gmc = gm.lcoeff();
                    let mut gc = MultivariatePolynomial::with_nvars(gm.nvars);
                    gc.nterms = gm.nterms;
                    gc.exponents = gm.exponents.clone();
                    gc.coefficients = gm.coefficients
                        .iter()
                        .map(|x| i64::from_finite_field(&(x.clone() / gmc.clone())))
                        .collect();

                    println!("Final suggested gcd: {}", gc);
                    if a.long_division(&gc).1.is_zero() && b.long_division(&gc).1.is_zero() {
                        return gc;
                    }

                    // if it does not divide, we need more primes
                }

                old_gm = gm.clone();

                pi += 1;
                for _ in pi..primes.len() {
                    if !(gamma.mod_num(primes[pi])).is_zero() {
                        break;
                    }
                    pi += 1;
                }

                if pi == primes.len() {
                    panic!("Ran out of primes for gcd images");
                }

                p = primes[pi];

                gammap = gamma.to_finite_field(p);
                let ap = a.to_finite_field(p);
                let bp = b.to_finite_field(p);
                println!("New image: gcd({},{}) mod {}", ap, bp, p);

                // for the univariate case, we don't need to construct an image
                if vars.len() == 1 {
                    gp = MultivariatePolynomial::univariate_gcd(&ap, &bp);
                } else {
                    match construct_new_image(
                        &ap,
                        &bp,
                        a.ldegree(),
                        b.ldegree(),
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
                println!("gp: {}", gp);

                // use chinese remainder theorem to merge coefficients
                for (gmc, gpc) in gm.coefficients.iter_mut().zip(gp.coefficients) {
                    *gmc = FiniteField::new(
                        FiniteField::chinese_remainder(gmc.n, gpc.n, gmc.p, gpc.p),
                        m * p,
                    );
                }

                m = m * p;
                println!("gm: {} mod {}", gm, m);
            }
        }
    }
}

pub trait PolynomialGCD: Sized {
    fn gcd(a: &Self, b: &Self, vars: &[usize], dx: &mut [usize]) -> Self;
}

impl<E: Exponent> PolynomialGCD for MultivariatePolynomial<i64, E> {
    fn gcd(
        a: &MultivariatePolynomial<i64, E>,
        b: &MultivariatePolynomial<i64, E>,
        vars: &[usize],
        dx: &mut [usize],
    ) -> MultivariatePolynomial<i64, E> {
        MultivariatePolynomial::gcd_zippel(&a, &b, vars, dx)
    }
}

impl<E: Exponent> PolynomialGCD for MultivariatePolynomial<FiniteField, E> {
    fn gcd(
        a: &MultivariatePolynomial<FiniteField, E>,
        b: &MultivariatePolynomial<FiniteField, E>,
        vars: &[usize],
        dx: &mut [usize],
    ) -> MultivariatePolynomial<FiniteField, E> {
        MultivariatePolynomial::gcd_shape_modular(&a, &b, vars, dx).unwrap()
    }
}
