use fnv::FnvHashMap;
use fnv::FnvHasher;
use num_traits::{One, Zero};
use poly::exponent::Exponent;
use poly::raw::MultivariatePolynomial;
use poly::ring::Ring;
use std::hash::{Hash, Hasher};
use std::mem;

#[derive(Debug, Clone)]
pub enum Instructions<R: Ring, E: Exponent> {
    Add(Box<(Instructions<R, E>, Instructions<R, E>)>),
    Mul(Vec<Instructions<R, E>>),
    VarPow(usize, E),
    Number(R),
    InstructionNumber(usize),
    Poly(MultivariatePolynomial<R, E>),
}

impl<R: Ring, E: Exponent> Instructions<R, E> {
    /// Evaluate an instruction and return the result.
    /// `res` is a list of previous results that can
    /// be accessed with the `InstructionNumber` variant.
    pub fn evaluate(&self, res: &mut [R], vals: &[R]) -> R {
        match self {
            Instructions::Number(x) => x.clone(),
            Instructions::VarPow(v, p) => vals[*v].clone().pow(p.clone().as_()),
            Instructions::InstructionNumber(i) => res[*i].clone(),
            Instructions::Add(b) => {
                let (a1, a2) = &**b;
                a1.evaluate(res, vals) + a2.evaluate(res, vals)
            }
            Instructions::Mul(v) => {
                let mut r = v[0].evaluate(res, vals);
                for x in v.iter().skip(1) {
                    r *= x.evaluate(res, vals);
                }
                r
            }
            Instructions::Poly(p) => {
                let mut rv = vals.iter().cloned().enumerate().collect::<Vec<_>>();
                let pp = p.replace_multiple(&rv);

                debug_assert!(pp.is_constant());
                if pp.is_zero() {
                    R::zero()
                } else {
                    pp.coefficients[0].clone()
                }
            }
        }
    }

    /// Evaluate a list of instructions and return the last evaluation.
    pub fn evaluate_list(instructions: &[Instructions<R, E>], vals: &[R]) -> R {
        let mut res = vec![R::zero(); instructions.len()];

        for (i, ins) in instructions.iter().enumerate() {
            res[i] = ins.evaluate(&mut res, vals);
        }

        res.last().unwrap().clone()
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
        Box<(HornerScheme<R, E>, HornerScheme<R, E>)>,
    ), // hash, variable, power, gcd, child
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
            HornerScheme::Node(_, _, _, gcd, _) => gcd.clone(),
            HornerScheme::Leaf(_, p) => p.content(),
        }
    }

    /// Divide out the content `g`.
    pub fn div_content(&mut self, g: R) {
        match self {
            HornerScheme::Node(_, _, _, gcd, _) => *gcd = mem::replace(gcd, R::zero()) / g,
            HornerScheme::Leaf(_, p) => *p = mem::replace(p, MultivariatePolynomial::new()) / g,
        }
    }

    /// Generate a hash for each element of the horner scheme.
    pub fn hash(&mut self) -> u64 {
        match self {
            HornerScheme::Node(h, v, p, gcd, children) => {
                let (c1, c2) = &mut **children;
                let h1 = c1.hash();
                let h2 = c2.hash();

                // create the node hash
                let mut hasher = FnvHasher::default();
                hasher.write_usize(*v);
                p.hash(&mut hasher);
                gcd.hash(&mut hasher);
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

        // for now, we print the linearized form
        match self {
            HornerScheme::Node(_, v, p, gcd, children) => {
                let (c1, c2) = &mut **children;
                let num1 = c1.linearize_subexpr_rec(instructions, m);

                let mut is = vec![];

                is.push(Instructions::VarPow(*v, *p));

                if !gcd.is_one() {
                    is.push(Instructions::Number(gcd.clone()));
                }

                let is_one = if let HornerScheme::Leaf(_, x) = c1 {
                    x.is_one()
                } else {
                    false
                };

                if !is_one {
                    is.push(Instructions::InstructionNumber(num1));
                }

                let subins = if is.len() == 1 {
                    is.swap_remove(0)
                } else {
                    Instructions::Mul(is)
                };

                let is_zero = if let HornerScheme::Leaf(_, x) = c2 {
                    x.is_zero()
                } else {
                    false
                };

                let ins = if !is_zero {
                    let num2 = c2.linearize_subexpr_rec(instructions, m);
                    Instructions::Add(Box::new((subins, Instructions::InstructionNumber(num2))))
                } else {
                    subins
                };

                instructions.push(ins);
            }
            HornerScheme::Leaf(_, p) => {
                instructions.push(Instructions::Poly(p.clone()));
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
            if pow.is_zero() || pow > self.exponents(t)[v] {
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
                rest.append_monomial(m.coefficient.clone(), m.exponents.to_vec());
            } else {
                let mut ex = m.exponents.to_vec();
                ex[v] = ex[v] - pow;
                sub.append_monomial(m.coefficient.clone(), ex);
            }
        }

        // now get the gcd
        if extract_gcd {
            let mut subh = sub.horner(indices, extract_gcd);
            let mut resth = rest.horner(&indices[1..], extract_gcd);

            let gcd = R::gcd(subh.get_content(), resth.get_content());
            subh.div_content(gcd.clone());
            resth.div_content(gcd.clone());

            HornerScheme::Node(0, v, pow, gcd, Box::new((subh, resth)))
        } else {
            HornerScheme::Node(
                0,
                v,
                pow,
                R::one(),
                Box::new((
                    sub.horner(indices, extract_gcd),
                    rest.horner(&indices[1..], extract_gcd),
                )),
            )
        }
    }
}
