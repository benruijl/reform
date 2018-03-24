use num_traits::{pow, One, Zero};

use poly::exponent::Exponent;
use poly::ring::Ring;

use poly::raw::finitefield::FiniteField;
use rand;
use rand::distributions::{Range, Sample};
use poly::raw::MultivariatePolynomial;
use tools;

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
    for k in (0..v.len()).rev() {
        u = u * (xp.clone() - MultivariatePolynomial::from_constant_with_nvars(a[k], xp.nvars))
            + v[k].clone();
    }
    u
}

fn construct_new_image<R: Ring, E: Exponent>(
    ap: &MultivariatePolynomial<FiniteField, E>,
    bp: &MultivariatePolynomial<FiniteField, E>,
    aldegree: E,
    bldegree: E,
    bounds: &mut [usize],
    single_scale: Option<usize>,
    nx: usize,
    gfu: &[(MultivariatePolynomial<R, E>, usize)],
) -> Result<MultivariatePolynomial<FiniteField, E>, GCDError> {
    let p = ap.coefficients[0].p;
    let mut rng = rand::thread_rng();
    let mut range = Range::new(1, p);

    let mut S = vec![]; // coefficients for the linear system
    let mut ni = 0;
    let mut failure_count = 0;
    'newimage: loop {
        // generate random numbers for all non-leading variables
        let (r, a1, b1) = loop {
            let r: Vec<(usize, FiniteField)> = (1..ap.nvars)
                .map(|i| (i, FiniteField::new(range.sample(&mut rng), p)))
                .collect();

            let a1 = ap.replace_multiple(&r);
            let b1 = bp.replace_multiple(&r);

            if a1.ldegree() == aldegree && b1.ldegree() == bldegree {
                break (r, a1, b1);
            }
        };

        let g1 = MultivariatePolynomial::univariate_gcd(&a1, &b1);

        if g1.ldegree().as_() < bounds[0] {
            // original image and form and degree bounds are unlucky
            // change the bound and try a new prime
            bounds[0] = g1.ldegree().as_();
            return Err(GCDError::BadOriginalImage);
            //continue 'newfirstprime;
        }

        if g1.ldegree().as_() > bounds[0] {
            failure_count += 1;

            if failure_count > 2 || failure_count > ni {
                // p is likely unlucky
                return Err(GCDError::BadCurrentImage);
                //continue 'newprime;
            }
            continue;
        }

        // check if the single scaling is there, if we had a single scale
        if let Some(d) = single_scale {
            if !(0..g1.nterms).any(|i| g1.exponents(i)[0].as_() == d) {
                // the scaling term is missing, so the assumed form is wrong
                return Err(GCDError::BadOriginalImage);
            }
        }

        S.push((r, g1));
        ni += 1;

        // make sure we have at least nx images
        if ni < nx {
            continue 'newimage;
        }

        // construct the linear system
        let mut gfm = vec![];

        for (i, &(ref c, ref e)) in gfu.iter().enumerate() {
            for (j, &(ref r, ref g)) in S.iter().enumerate() {
                let mut row = vec![];

                assert_eq!(g.nterms, gfu.len());

                // the first elements in the row come from the shape
                for ii in 0..gfu.len() {
                    if i == ii {
                        // note that we ignore the coefficient of the shape
                        for t in 0..c.nterms {
                            let mut coeff = FiniteField::new(1, p);
                            for &(n, v) in r.iter() {
                                coeff = coeff * pow(v.clone(), c.exponents(t)[n].as_());
                            }
                            row.push(coeff.n);
                        }
                    } else {
                        for t in 0..c.nterms {
                            row.push(0);
                        }
                    }
                }

                // add the coefficient from the image
                for ii in 0..g.nterms {
                    if ii == i {
                        row.push(g.coefficients[i].n);
                    } else {
                        row.push(0);
                    }
                }

                gfm.push(row);
            }
        }

        // solve for S and call the result gp
        let gp = MultivariatePolynomial::new();

        // if inconsistent: return Err(GCDError::BadOriginalImage);
        // underdetermined and same degree 3 times? bad prime: return Err(GCDError::BadCurrentImage);
        // else: more images: continue 'newimage

        return Ok(gp);
    }
}

impl<E: Exponent> MultivariatePolynomial<FiniteField, E> {
    /// Compute the gcd shape of two polynomials in a finite field by filling in random
    /// numbers.
    fn gcd_shape_modular(
        a: &MultivariatePolynomial<FiniteField, E>,
        b: &MultivariatePolynomial<FiniteField, E>,
        n: usize,         // number of active vars
        dx: &mut [usize], // degree bounds
    ) -> Option<MultivariatePolynomial<FiniteField, E>> {
        // TODO: "If the gcd of the inputs has content in x n return Fail.""
        // what do they mean? we don't know this gcd yet...

        let gamma = MultivariatePolynomial::univariate_gcd(&a.lcoeff_last(), &b.lcoeff_last());

        let p = a.coefficients[0].p;
        let mut rng = rand::thread_rng();
        let mut range = Range::new(1, p);

        'newfirstnum: loop {
            let v = loop {
                let a = FiniteField::new(range.sample(&mut rng), p);
                if gamma.replace(n - 1, a).nterms() != 0 {
                    break a;
                }
            };

            let av = a.replace(n - 1, v);
            let bv = b.replace(n - 1, v);

            // performance dense reconstruction
            let mut gv = if n > 2 {
                match MultivariatePolynomial::gcd_shape_modular(&av, &bv, n - 1, dx) {
                    Some(x) => x,
                    None => return None,
                }
            } else {
                let gg = MultivariatePolynomial::univariate_gcd(&av, &bv);
                if gg.ldegree().as_() > dx[0] {
                    return None;
                }
                dx[0] = gg.ldegree().as_(); // update degree bound
                gg
            };

            // construct a new assumed form
            // we have to find the proper normalization
            let mut gf = gv.clone();

            // construct the univariate polynomial
            let gfu = gf.to_univariate_polynomial(0);

            // find a coefficient of x1 in gg that is a monomial (single scaling)
            let mut single_scale = None;
            let mut nx = 0; // count the minimal number of samples needed
            for &(ref c, ref e) in &gfu {
                if c.nterms > nx {
                    nx = c.nterms;
                }
                if c.nterms == 1 {
                    single_scale = Some(e.clone());
                }
            }

            // In the case of multiple scaling, we need an additional sample
            // TODO: is this correct?
            if single_scale == None {
                nx += 1;
            }

            let mut lc = gv.lcoeff();
            let mut gseq = vec![gv * (gamma.replace(0, v).coefficients[0].clone() / lc)];
            let mut vseq = vec![v];

            // sparse reconstruction
            'newnum: loop {
                let v = loop {
                    let v = FiniteField::new(range.sample(&mut rng), a.coefficients[0].p);
                    if gamma.replace(n - 1, v).nterms() != 0 {
                        break v;
                    }
                };
                let av = a.replace(n - 1, v);
                let bv = b.replace(n - 1, v);

                match construct_new_image(
                    &av,
                    &bv,
                    a.ldegree(),
                    b.ldegree(),
                    dx,
                    single_scale,
                    nx,
                    &gfu,
                ) {
                    Ok(r) => {
                        gv = r;
                    }
                    Err(GCDError::BadOriginalImage) => continue 'newfirstnum,
                    Err(GCDError::BadCurrentImage) => continue 'newnum,
                }

                lc = gv.lcoeff();
                gseq.push(gv * (gamma.replace(0, v).coefficients[0].clone() / lc));
                vseq.push(v);

                if gseq.len() == dx[n - 1] + gamma.ldegree_max().as_() + 1 {
                    break;
                }
            }

            // use interpolation to construct x_n dependence
            let mut gc = newton_interpolation(&vseq, &gseq, p, n - 1);

            // remove content in x_n
            let cont = gc.univariate_content(n - 1);
            let cc = gc.long_division(&cont);
            assert_eq!(cc.1, MultivariatePolynomial::zero());
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

            if a.long_division(&gc).1 == MultivariatePolynomial::new()
                && b.long_division(&gc).1 == MultivariatePolynomial::new()
            {
                return Some(gc);
            }

            // if the gcd is bad, we had a bad number
        }
    }
}

impl<R: Ring, E: Exponent> MultivariatePolynomial<R, E> {
    /// Compute the gcd of two multivariate polynomials using Zippel's algorithm.
    pub fn gcd(
        a: &MultivariatePolynomial<R, E>,
        b: &MultivariatePolynomial<R, E>,
    ) -> MultivariatePolynomial<R, E> {
        // TODO: check if a and b are monic

        assert_eq!(a.nvars, b.nvars);

        let mut rng = rand::thread_rng();

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

        // compute scaling factor
        let gamma = tools::gcd(a.ldegree().as_(), b.ldegree().as_());

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
            for _ in pi..primes.len() {
                if gamma % primes[pi] != 0 {
                    break;
                }
                pi += 1;
            }

            let p = primes[pi];

            let gammap = FiniteField::new(gamma, p);
            let ap = a.to_finite_field(p);
            let bp = b.to_finite_field(p);

            println!("{:?} {:?} {}", ap, bp, p);

            // calculate modular gcd image
            let mut gp = loop {
                if let Some(x) =
                    MultivariatePolynomial::gcd_shape_modular(&ap, &bp, ap.nvars, &mut bounds)
                {
                    break x;
                }
            };

            bounds[0] = gp.last_exponents()[0].as_();

            // construct a new assumed form
            // we have to find the proper normalization
            let mut gf = gp.clone();

            // construct the univariate polynomial
            let gfu = gf.to_univariate_polynomial(0);

            // find a coefficient of x1 in gf that is a monomial (single scaling)
            let mut single_scale = None;
            let mut nx = 0; // count the minimal number of samples needed
            for &(ref c, ref e) in &gfu {
                if c.nterms > nx {
                    nx = c.nterms;
                }
                if c.nterms == 1 {
                    single_scale = Some(e.clone());
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

            let mut old_gm = MultivariatePolynomial::new();

            // add new primes until we can reconstruct the full gcd
            'newprime: loop {
                if gm == old_gm {
                    // divide by lcoeff and convert from finite field
                    let gmc = gm.lcoeff();
                    let mut gc = MultivariatePolynomial::new();
                    gc.nterms = gm.nterms;
                    gc.nvars = gm.nvars;
                    gc.exponents = gm.exponents.clone();
                    gc.coefficients = gm.coefficients
                        .iter()
                        .map(|x| R::from_finite_field(&(x.clone() / gmc.clone())))
                        .collect();

                    if a.long_division(&gc).1 == MultivariatePolynomial::new()
                        && b.long_division(&gc).1 == MultivariatePolynomial::new()
                    {
                        return gc;
                    }

                    // if it does not divide, we need more primes
                }

                old_gm = gm.clone();

                for _ in pi..primes.len() {
                    if gamma % primes[pi] != 0 {
                        break;
                    }
                    pi += 1;
                }

                let p = primes[pi];

                let gammap = FiniteField::new(gamma, p);
                let ap = a.to_finite_field(p);
                let bp = b.to_finite_field(p);

                match construct_new_image(
                    &ap,
                    &bp,
                    a.ldegree(),
                    b.ldegree(),
                    &mut bounds,
                    single_scale,
                    nx,
                    &gfu,
                ) {
                    Ok(r) => {
                        gp = r;
                        break;
                    }
                    Err(GCDError::BadOriginalImage) => continue 'newfirstprime,
                    Err(GCDError::BadCurrentImage) => continue 'newprime,
                }
            }

            // scale the new image
            let gpc = gp.content();
            gp = gp * (gammap / gpc);

            // use chinese remainder theorem to merge coefficients
            for (gmc, gpc) in gm.coefficients.iter_mut().zip(gp.coefficients) {
                *gmc = FiniteField::new(
                    FiniteField::chinese_remainder(gmc.n, gpc.n, gmc.p, gpc.p),
                    m * p,
                );
            }

            m = m * p;
        }
    }
}
