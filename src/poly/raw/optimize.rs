use fnv::FnvHashMap;
use fnv::FnvHasher;
use num_traits::{One, Zero};
use poly::exponent::Exponent;
use poly::raw::finitefield::FiniteField;
use poly::raw::zp;
use poly::raw::zp::{ufield, FastModulus};
use poly::raw::zp_mod::Modulus;
use poly::raw::MultivariatePolynomial;
use poly::ring::Ring;
use std::hash::{Hash, Hasher};
use std::mem;
use tools;

pub const POW_CACHE_SIZE: usize = 1000;

/// You can register polynomials and they will be sampled at
/// the same time. Common subexpressions will be recylced.
pub struct PolynomialSampler<R: Ring, E: Exponent> {
    polys: Vec<(usize, usize, Vec<(u32, usize)>)>, // list of polys: (nvars, var, (power, index to instr))
    prime: Option<FastModulus>,
    instructions: Vec<Instructions<R, E>>,
    sample_points: Vec<ufield>,
    result: Vec<R>,                             // the cached results
    cse: FnvHashMap<HornerScheme<R, E>, usize>, // cached cse
    pow_cache: Vec<Vec<ufield>>,
}

impl<R: Ring, E: Exponent> PolynomialSampler<R, E> {
    pub fn new(num_vars: usize) -> PolynomialSampler<R, E> {
        PolynomialSampler {
            polys: vec![],
            prime: None,
            instructions: vec![],
            result: vec![],
            cse: FnvHashMap::with_hasher(Default::default()),
            sample_points: vec![0; num_vars],
            pow_cache: vec![vec![]; num_vars],
        }
    }

    /// Add a polynomial bracketed in `var`.
    pub fn add(&mut self, poly: &MultivariatePolynomial<R, E>, var: usize, order: &[usize]) {
        // adjust the cache size
        for i in 0..poly.nvars {
            let bound = poly.degree(i).as_() as usize + 1;
            if self.pow_cache[i].len() < bound && bound < POW_CACHE_SIZE {
                self.pow_cache[i].resize(bound, 0);
            }
        }

        // construct an occurrence order scheme for the entire polynomial
        let mut occ_order = poly.occurrence_order();
        occ_order = occ_order
            .iter()
            .cloned()
            .filter(|x| order.contains(x))
            .collect();

        // TODO: for now, evaluating the instructions is sometimes slower than
        // evaluating a polynomial straight away. Until this is changed,
        // we do not include the last variable in the Horner scheme
        occ_order.pop();

        let apf = poly.to_univariate_polynomial(var);
        trace!("poly {}", poly);
        trace!("apf {:?}", apf);

        let evalap = apf.iter()
            .map(|(p, x)| {
                let mut h = p.horner(&occ_order, true);
                trace!("h {:?}", h);
                HornerScheme::hash(&mut h); // hash is required for csee
                let pos = h.linearize_subexpr_rec(&mut self.instructions, &mut self.cse);
                (*x, pos)
            })
            .collect::<Vec<_>>();

        /*for (i, x) in self.instructions.iter().enumerate() {
            print!("Z{} = ", i);
            x.print();
            println!(";");
        }*/
        debug!("{:?}", evalap);

        self.polys.push((poly.nvars(), var, evalap));
    }

    /// Change the polynomial sampler into a sampler over prime fields.
    pub fn set_prime(&self, p: ufield) -> PolynomialSampler<FiniteField, E> {
        // apply the prime to the instructions
        let prime = FastModulus::from(p);

        let mut ins = Vec::with_capacity(self.instructions.len());
        for x in &self.instructions {
            ins.push(x.set_prime(p));
        }

        // TODO: also migrate the common subexpression tree
        PolynomialSampler {
            polys: self.polys.clone(),
            prime: Some(prime),
            instructions: ins,
            result: vec![],
            cse: FnvHashMap::with_hasher(Default::default()),
            sample_points: self.sample_points.clone(),
            pow_cache: self.pow_cache.clone(),
        }
    }

    #[inline]
    pub fn get_prime(&self) -> Option<ufield> {
        self.prime.as_ref().map(|p| p.value())
    }
}

impl<E: Exponent> PolynomialSampler<FiniteField, E> {
    pub fn evaluate(&mut self) {
        let p = self.prime.as_ref().unwrap();
        let pp = p.value();

        self.result = vec![FiniteField::new_safe(0, pp); self.instructions.len()];
        let mut resfield = vec![0; self.instructions.len()];

        // clear cache
        for v in &mut self.pow_cache {
            for vi in v {
                *vi = 0;
            }
        }

        for (i, ins) in self.instructions.iter().enumerate() {
            resfield[i] = ins.evaluate(&mut resfield, &self.sample_points, p, &mut self.pow_cache);
            self.result[i] = FiniteField::new_safe(resfield[i], pp);
        }
    }

    /// Get an evaluated polynomial
    pub fn get_polynomial(&self, p: usize) -> MultivariatePolynomial<FiniteField, E> {
        let pfrag = &self.polys[p];
        let mut poly = MultivariatePolynomial::with_nvars(pfrag.0);

        for (p, i) in &pfrag.2 {
            let mut exp = vec![E::zero(); pfrag.0];
            exp[pfrag.1] = E::from_u32(*p).unwrap();
            poly.append_monomial(self.result[*i], &exp);
        }

        poly
    }

    pub fn set_sample(&mut self, var: usize, v: ufield) {
        self.sample_points[var] = v;
    }
}

#[derive(Debug, Clone)]
pub enum Instructions<R: Ring, E: Exponent> {
    Add(Box<(Instructions<R, E>, Instructions<R, E>)>),
    Mul(Vec<Instructions<R, E>>),
    VarPow(usize, E),
    Number(R),
    InstructionNumber(usize),
    Poly(MultivariatePolynomial<R, E>),
}

/// Specialized routines for finite field evaluation
impl<E: Exponent> Instructions<FiniteField, E> {
    #[inline]
    pub fn evaluate_basic(
        &self,
        res: &mut [ufield],
        vals: &[ufield],
        p: &FastModulus,
        pow_cache: &mut Vec<Vec<ufield>>,
    ) -> ufield {
        match self {
            Instructions::Number(x) => x.n,
            Instructions::VarPow(v, pow) => {
                debug_assert!(vals[*v] != 0);

                if pow.is_one() {
                    vals[*v]
                } else {
                    // TODO: use binary exponentiation and cache result?
                    pow_cache[*v][pow.as_() as usize] = zp::pow(vals[*v], pow.as_(), p);
                    pow_cache[*v][pow.as_() as usize]
                }
            }
            Instructions::InstructionNumber(i) => res[*i].clone(),
            Instructions::Poly(poly) => poly.sample_polynomial_to_number(p, &vals, pow_cache).n,
            _ => unreachable!(),
        }
    }

    #[inline]
    pub fn evaluate_norec(
        &self,
        res: &mut [ufield],
        vals: &[ufield],
        p: &FastModulus,
        pow_cache: &mut Vec<Vec<ufield>>,
    ) -> ufield {
        match self {
            Instructions::Mul(v) => {
                let mut r = v[0].evaluate_basic(res, vals, p, pow_cache);
                for x in v.iter().skip(1) {
                    r = zp::mul(r, x.evaluate_basic(res, vals, p, pow_cache), p);
                }
                r
            }
            _ => self.evaluate_basic(res, vals, p, pow_cache),
        }
    }

    /// Evaluate an instruction and return the result.
    /// `res` is a list of previous results that can
    /// be accessed with the `InstructionNumber` variant.
    #[inline]
    pub fn evaluate(
        &self,
        res: &mut [ufield],
        vals: &[ufield],
        p: &FastModulus,
        pow_cache: &mut Vec<Vec<ufield>>,
    ) -> ufield {
        match self {
            Instructions::Add(b) => {
                let (a1, a2) = &**b;
                zp::add(
                    a1.evaluate_norec(res, vals, p, pow_cache),
                    a2.evaluate_norec(res, vals, p, pow_cache),
                    p,
                )
            }
            _ => self.evaluate_norec(res, vals, p, pow_cache),
        }
    }

    /// Evaluate a list of instructions and return the last evaluation.
    pub fn evaluate_list(
        instructions: &[Instructions<FiniteField, u32>],
        vals: &[ufield],
        p: &FastModulus,
        pow_cache: &mut Vec<Vec<ufield>>,
    ) -> ufield {
        let mut res = vec![0; instructions.len()];

        for (i, ins) in instructions.iter().enumerate() {
            res[i] = ins.evaluate(&mut res, vals, p, pow_cache);
        }

        res.last().unwrap().clone()
    }
}

impl<R: Ring, E: Exponent> Instructions<R, E> {
    pub fn set_prime(&self, p: ufield) -> Instructions<FiniteField, E> {
        match self {
            Instructions::Poly(poly) => Instructions::Poly(poly.to_finite_field(p)),
            Instructions::Mul(iv) => {
                let mut v = Vec::with_capacity(iv.len());
                for x in iv.iter() {
                    v.push(x.set_prime(p));
                }
                Instructions::Mul(v)
            }
            Instructions::Number(n) => Instructions::Number(n.to_finite_field(p)),
            Instructions::Add(b) => {
                let (a1, a2) = &**b;
                Instructions::Add(Box::new((a1.set_prime(p), a2.set_prime(p))))
            }
            Instructions::VarPow(v, pow) => Instructions::VarPow(*v, *pow),
            Instructions::InstructionNumber(i) => Instructions::InstructionNumber(*i),
        }
    }

    /// Print an instruction.
    pub fn print(&self) {
        match self {
            Instructions::Poly(p) => print!("{}", p),
            Instructions::InstructionNumber(n) => print!("Z{}", n),
            Instructions::Mul(iv) => {
                iv.first().unwrap().print();
                for x in iv.iter().skip(1) {
                    print!("*");
                    x.print();
                }
            }
            Instructions::VarPow(v, p) => {
                if p.is_one() {
                    print!("x{}", v)
                } else {
                    print!("x{}^{}", v, p)
                }
            }
            Instructions::Number(n) => {
                print!("{}", n);
            }
            Instructions::Add(b) => {
                let (a1, a2) = &**b;
                a1.print();
                print!("+");
                a2.print();
            }
        }
    }
}

/// A representation of a Horner scheme.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HornerScheme<R: Ring, E: Exponent> {
    Node(
        u64,
        usize,
        E,
        R,
        R,
        Box<(HornerScheme<R, E>, HornerScheme<R, E>)>,
    ), // hash, variable, power, gcd_sub, gcd_rest, child
    Leaf(u64, MultivariatePolynomial<R, E>), // hash, poly
}

impl<R: Ring, E: Exponent> Hash for HornerScheme<R, E> {
    /// A custom hash function for the HornerScheme that caches
    /// the hash-values for the branches.
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            HornerScheme::Node(h, ..) | HornerScheme::Leaf(h, ..) => {
                assert!(*h != 0);
                state.write_u64(*h);
            }
        }
    }
}

impl<R: Ring, E: Exponent> HornerScheme<R, E> {
    /// Extract the content at a certain level of the Horner scheme.
    pub fn get_content(&self) -> R {
        match self {
            HornerScheme::Node(_, _, _, gcd1, gcd2, _) => {
                tools::GCD::gcd(gcd1.clone(), gcd2.clone())
            }
            HornerScheme::Leaf(_, p) => p.content(),
        }
    }

    /// Divide out the content `g`.
    pub fn div_content(&mut self, g: R) {
        match self {
            HornerScheme::Node(_, _, _, gcd1, gcd2, _) => {
                *gcd1 = mem::replace(gcd1, R::zero()) / g.clone();
                *gcd2 = mem::replace(gcd2, R::zero()) / g;
            }
            HornerScheme::Leaf(_, p) => *p = mem::replace(p, MultivariatePolynomial::new()) / g,
        }
    }

    /// Generate a hash for each element of the horner scheme.
    pub fn hash(&mut self) -> u64 {
        match self {
            HornerScheme::Node(h, v, p, gcd1, gcd2, children) => {
                let (c1, c2) = &mut **children;
                let h1 = c1.hash();
                let h2 = c2.hash();

                // create the node hash
                let mut hasher = FnvHasher::default();
                hasher.write_usize(*v);
                p.hash(&mut hasher);
                gcd1.hash(&mut hasher);
                gcd2.hash(&mut hasher);
                hasher.write_u64(h1);
                hasher.write_u64(h2);
                *h = hasher.finish();

                *h
            }
            HornerScheme::Leaf(h, p) => {
                let mut hasher = FnvHasher::default();
                p.hash(&mut hasher);
                *h = hasher.finish();

                *h
            }
        }
    }

    /// Linearize a Horner scheme into a set of evaluation instructions.
    /// Common subexpressions are removed at this stage.
    pub fn linearize_subexpr(&mut self, instructions: &mut Vec<Instructions<R, E>>) -> usize {
        let mut hm: FnvHashMap<HornerScheme<R, E>, usize> =
            FnvHashMap::with_hasher(Default::default());

        self.hash(); // hash the Horner scheme, such that we can find common subexpressions

        self.linearize_subexpr_rec(instructions, &mut hm)
    }

    fn linearize_subexpr_rec(
        &mut self,
        instructions: &mut Vec<Instructions<R, E>>,
        m: &mut FnvHashMap<HornerScheme<R, E>, usize>,
    ) -> usize {
        // have we seen the subexpression before?
        if let Some(x) = m.get(self) {
            return *x;
        }

        // for now, we print the linearized form of a complete
        // horner scheme
        match self {
            HornerScheme::Node(_, v, p, gcd_sub, gcd_rest, children) => {
                let (c1, c2) = &mut **children;

                let mut is = vec![];

                is.push(Instructions::VarPow(*v, *p));

                if !gcd_sub.is_one() {
                    is.push(Instructions::Number(gcd_sub.clone()));
                }

                let mut is_constant = None;
                let is_one = if let HornerScheme::Leaf(_, x) = c1 {
                    if !x.is_zero() && x.is_constant() {
                        is_constant = Some(x.coefficients[0].clone());
                    }
                    x.is_one()
                } else {
                    false
                };

                if !is_one {
                    if let Some(n) = is_constant {
                        is.push(Instructions::Number(n));
                    } else {
                        let num1 = c1.linearize_subexpr_rec(instructions, m);
                        is.push(Instructions::InstructionNumber(num1));
                    }
                }

                let subins = if is.len() == 1 {
                    is.swap_remove(0)
                } else {
                    Instructions::Mul(is)
                };

                is_constant = None;
                let is_zero = if let HornerScheme::Leaf(_, x) = c2 {
                    if !x.is_zero() && x.is_constant() {
                        is_constant = x.get_constant();
                    }
                    x.is_zero()
                } else {
                    false
                };

                let ins = if !is_zero {
                    // if c2 is a constant, do not create an instruction
                    if let Some(n) = is_constant {
                        Instructions::Add(Box::new((
                            subins,
                            Instructions::Number(n * gcd_rest.clone()),
                        )))
                    } else {
                        let num2 = c2.linearize_subexpr_rec(instructions, m);

                        if !gcd_rest.is_one() {
                            Instructions::Add(Box::new((
                                subins,
                                Instructions::Mul(vec![
                                    Instructions::Number(gcd_rest.clone()),
                                    Instructions::InstructionNumber(num2),
                                ]),
                            )))
                        } else {
                            Instructions::Add(Box::new((
                                subins,
                                Instructions::InstructionNumber(num2),
                            )))
                        }
                    }
                } else {
                    subins
                };

                instructions.push(ins);
            }
            HornerScheme::Leaf(_, p) => {
                if p.is_constant() {
                    instructions.push(Instructions::Number(p.get_constant().unwrap()));
                } else {
                    instructions.push(Instructions::Poly(p.clone()));
                }
            }
        }

        m.insert(self.clone(), instructions.len() - 1);
        instructions.len() - 1
    }
}

impl<R: Ring, E: Exponent> MultivariatePolynomial<R, E> {
    /// Get the occurence order of the variables in the polynomial.
    pub fn occurrence_order(&self) -> Vec<usize> {
        let mut count = vec![0; self.nvars];
        let mut indices = (0..self.nvars).collect::<Vec<usize>>();

        for m in self.into_iter() {
            for v in 0..self.nvars {
                if m.exponents[v].as_() > 0 {
                    count[v] += 1;
                }
            }
        }

        indices.sort_by(|&i, &j| count[i].cmp(&count[j]));
        indices
    }

    /// Construct a horner scheme form the polynomial.
    pub fn horner(&self, indices: &[usize], extract_gcd: bool) -> HornerScheme<R, E> {
        if indices.len() == 0 {
            return HornerScheme::Leaf(0, self.clone());
        }

        let v = *indices.first().unwrap();

        // get the lowest non-zero power of the variable
        let mut pow = E::zero();
        for t in 0..self.nterms {
            if self.exponents(t)[v].as_() > 0 && (pow.is_zero() || pow > self.exponents(t)[v]) {
                pow = self.exponents(t)[v];
            }
        }

        if pow.is_zero() {
            return self.horner(&indices[1..], extract_gcd);
        }

        // split-up into two: contains v and does not contain v
        let mut sub = MultivariatePolynomial::<R, E>::with_nvars(self.nvars);
        let mut rest = MultivariatePolynomial::<R, E>::with_nvars(self.nvars);

        for m in self.into_iter() {
            if m.exponents[v].is_zero() {
                rest.append_monomial(m.coefficient.clone(), &m.exponents);
            } else {
                let mut ex = m.exponents.to_vec();
                ex[v] = ex[v] - pow;
                sub.append_monomial(m.coefficient.clone(), &ex);
            }
        }

        // now get the gcd
        if extract_gcd {
            let mut subh = sub.horner(indices, extract_gcd);
            let mut resth = rest.horner(&indices[1..], extract_gcd);

            let gcd_sub = subh.get_content();
            subh.div_content(gcd_sub.clone());

            let is_zero = if let HornerScheme::Leaf(_, x) = &resth {
                x.is_zero()
            } else {
                false
            };

            let gcd_rest = if is_zero {
                R::one()
            } else {
                let gcd_rest = resth.get_content();
                resth.div_content(gcd_rest.clone());
                gcd_rest
            };

            HornerScheme::Node(0, v, pow, gcd_sub, gcd_rest, Box::new((subh, resth)))
        } else {
            HornerScheme::Node(
                0,
                v,
                pow,
                R::one(), // FIXME: if prime field, this could cause issues with a wrong prime!
                R::one(),
                Box::new((
                    sub.horner(indices, extract_gcd),
                    rest.horner(&indices[1..], extract_gcd),
                )),
            )
        }
    }
}
