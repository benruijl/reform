use id::MatchOpt;
use number::Number;
use std::cmp::Ordering;
use std::mem;
use structure::*;
use tools::{ncr, CombinationsWithReplacement};

#[derive(Debug)]
pub struct ExpandIterator<'a> {
    subiter: ExpandSubIterator<'a>,
    ground_level: bool,
    done: bool,
}

#[derive(Debug)]
enum ExpandSubIterator<'a> {
    SubExpr(Vec<ExpandIterator<'a>>, usize, bool),
    Term(Vec<(ExpandIterator<'a>, MatchOpt<'a>)>),
    Exp(Box<CombinationsWithReplacement<Element>>, usize),
    Yield(Element),
    YieldMultiple(&'a [Element]),
}

enum ExpandIteratorOption<T> {
    Some(T),
    None,
    NotEnoughInformation,
}

impl<T> ExpandIteratorOption<T> {
    fn unwrap(self) -> T {
        match self {
            ExpandIteratorOption::Some(x) => x,
            ExpandIteratorOption::None => panic!("Cannot unwrap none"),
            ExpandIteratorOption::NotEnoughInformation => {
                panic!("Cannot unwrap enough information")
            }
        }
    }

    fn or_else<F: FnOnce() -> Option<T>>(self, f: F) -> Option<T> {
        match self {
            ExpandIteratorOption::Some(x) => Some(x),
            ExpandIteratorOption::None => None,
            ExpandIteratorOption::NotEnoughInformation => f(),
        }
    }
}

impl<'a> ExpandIterator<'a> {
    pub fn new(
        element: &'a mut Element,
        var_info: &'a GlobalVarInfo,
        ground_level: bool,
    ) -> ExpandIterator<'a> {
        let subiter =
        // modify the element so that all substructures are expanded
        match element {
            // this processing way is slow but we need it to handle
            // ((1+x)^5+..)*(...)
            Element::SubExpr(_, ref mut ts) => {
                let mut seqiter = Vec::with_capacity(ts.len());
                for x in ts {
                    seqiter.push(ExpandIterator::new(x, var_info, ground_level));
                }

                let inline = seqiter.iter().all(|x| match x.subiter {
                    ExpandSubIterator::Yield(..) | ExpandSubIterator::YieldMultiple(..) => true, _ => false });
                ExpandSubIterator::SubExpr(seqiter, 0, inline)
            }
            Element::Term(_, ref mut ts) => {
                // Sort the original term such that all factors that don't need further expansion are at the front.
                // We store a reference to these for further use, so that we avoid copying.
                // TODO: some pow may actually also be static: x^(1+e) for example
                ts.sort_by(|a, b| { match (a,b) {
                    (Element::SubExpr(..), Element::SubExpr(..)) => Ordering::Equal,
                    (Element::SubExpr(..), Element::Pow(..)) => Ordering::Equal,
                    (Element::Pow(..), Element::SubExpr(..)) => Ordering::Equal,
                    (Element::Pow(..), Element::Pow(..)) => Ordering::Equal,
                    (Element::SubExpr(..), _) => Ordering::Greater,
                    (Element::Pow(..), _) => Ordering::Greater,
                    (_, Element::SubExpr(..)) => Ordering::Less,
                    (_, Element::Pow(..)) => Ordering::Less,
                    _ => Ordering::Equal
                } } );

                let mut static_count = 0;
                for x in ts.iter_mut() {
                    match x {
                        Element::Fn(_dirty, _name, ref mut args) => {
                            for a in args {
                                *a = ExpandIterator::new(a, var_info, false).to_element(var_info);
                            }
                            // TODO: normalize function?
                            static_count += 1;
                        }
                        Element::SubExpr(..) | Element::Pow(..) => {},
                        _ => { static_count += 1; }
                    }
                }

                let (static_part, dyn_part) = ts.split_at_mut(static_count);

                let mut seqiter = vec![];
                for x in dyn_part.iter_mut() {
                    match x {
                        Element::SubExpr(..) => {seqiter.push((ExpandIterator::new(x, var_info, ground_level),
                         MatchOpt::SingleOwned(Element::default())));}
                        Element::Pow(..) => {seqiter.push((ExpandIterator::new(x, var_info, ground_level),
                         MatchOpt::SingleOwned(Element::default())));}
                        _ => unreachable!()
                    }
                }

                // completely static term
                if seqiter.is_empty() {
                    return ExpandIterator {
                            subiter: ExpandSubIterator::YieldMultiple(static_part),
                            ground_level,
                            done: false,
                            };
                }

                // push the static terms onto the back
                if static_count > 0 {
                    seqiter.push((
                        ExpandIterator {
                            subiter: ExpandSubIterator::YieldMultiple(static_part),
                            ground_level,
                            done: false,
                            },
                        MatchOpt::SingleOwned(Element::default()))
                    );
                }

                // disable all but the first iterator
                for x in seqiter.iter_mut().skip(1) {
                    x.0.done = true;
                }

                ExpandSubIterator::Term(seqiter)
            }
            Element::Fn(_dirty, ref name, ref mut args) => {
                // TODO: don't create new fn
                let newargs = args
                    .into_iter()
                    .map(|x| ExpandIterator::new(x, var_info, false).to_element(var_info))
                    .collect();

                let mut f = Element::Fn(true, *name, newargs);
                f.normalize_inplace(var_info);
                ExpandSubIterator::Yield(f)
            }
            Element::Pow(_, be) => {
                let (b, e) = &mut **be;

                // TODO: in principle expansions in the base and exponent could also be iterator over
                // instead of collected
                let (mut eb, ee) = (ExpandIterator::new(b, var_info, false).to_element(var_info),
                                ExpandIterator::new(e, var_info, false).to_element(var_info));

                if let Element::Num(_, Number::SmallInt(n)) = ee {
                    if n > 0 {
                        if let Element::SubExpr(_, ref mut t) = eb {
                            // compute the exponent of a list, without generating double entries
                            let it = CombinationsWithReplacement::new(mem::replace(t, vec![]), n as usize);
                            ExpandSubIterator::Exp(Box::new(it), n as usize)
                        }
                        else if let Element::Term(_, t) = eb {
                            //  (x*y)^z -> x^z*y^z
                            let mut e = Element::Term(
                                true,
                                t.iter()
                                    .map(|x| {
                                        Element::Pow(
                                            true,
                                            Box::new((
                                                x.clone(),
                                                Element::Num(false, Number::SmallInt(n)),
                                            )),
                                        )
                                    })
                                    .collect(),
                            );
                            e.normalize_inplace(var_info);
                            ExpandSubIterator::Yield(e)
                        }
                        else {
                            let mut a = Element::Pow(true, Box::new((eb, ee)));
                            a.normalize_inplace(var_info);
                            ExpandSubIterator::Yield(a)
                        }
                    } else {
                        let mut a = Element::Pow(true, Box::new((eb, ee)));
                        a.normalize_inplace(var_info);
                        ExpandSubIterator::Yield(a)
                    }
                } else {
                    let mut a = Element::Pow(true, Box::new((eb, ee)));
                    a.normalize_inplace(var_info);
                    ExpandSubIterator::Yield(a)
                }
            }
            e => ExpandSubIterator::Yield(mem::replace(e, Element::default()))
        };

        ExpandIterator {
            subiter,
            ground_level,
            done: false,
        }
    }

    fn reset(&mut self) {
        self.done = false;

        match self.subiter {
            ExpandSubIterator::SubExpr(ref mut i, ref mut pos, _) => {
                *pos = 0;
                for x in i {
                    x.reset();
                }
            }
            ExpandSubIterator::Term(ref mut i) => {
                // only reset the first iterator
                i[0].0.reset();
            }
            ExpandSubIterator::Exp(ref mut it, n) => {
                **it = CombinationsWithReplacement::new(mem::replace(it.get_inner(), vec![]), n);
            }
            _ => {}
        }
    }

    fn to_element(&mut self, var_info: &GlobalVarInfo) -> Element {
        let mut res = vec![];

        while let Some(x) = self.next(var_info) {
            res.push(match x {
                MatchOpt::Single(ee) => ee.clone(),
                MatchOpt::SingleOwned(ee) => ee,
                MatchOpt::Multiple(es) => Element::Term(false, es.to_vec()),
            });
        }

        let mut e = Element::SubExpr(true, res);
        e.normalize_inplace(var_info);
        e
    }
}

impl<'a> ExpandIterator<'a> {
    #[inline]
    fn next_inline(&mut self) -> ExpandIteratorOption<MatchOpt<'a>> {
        if self.done {
            return ExpandIteratorOption::None;
        }
        match &mut self.subiter {
            ExpandSubIterator::YieldMultiple(e) => {
                self.done = true;
                ExpandIteratorOption::Some(MatchOpt::Multiple(e))
            }
            ExpandSubIterator::Yield(e) => {
                self.done = true;
                ExpandIteratorOption::Some(MatchOpt::SingleOwned(e.clone())) // TODO: prevent clone
            }
            _ => ExpandIteratorOption::NotEnoughInformation,
        }
    }
}

impl<'a> ExpandIterator<'a> {
    #[inline]
    fn next_inline_subexpr(&mut self) -> ExpandIteratorOption<MatchOpt<'a>> {
        if self.done {
            return ExpandIteratorOption::None;
        }

        if let ExpandSubIterator::SubExpr(..) = self.subiter {
        } else {
            return self.next_inline();
        }

        match &mut self.subiter {
            ExpandSubIterator::SubExpr(seqiter, pos, inline) => {
                if !*inline {
                    return ExpandIteratorOption::NotEnoughInformation;
                }
                // for subexpressions, yield each iterator one by one
                while *pos < seqiter.len() {
                    if !seqiter[*pos].done {
                        return ExpandIteratorOption::Some(seqiter[*pos].next_inline().unwrap());
                    }
                    *pos += 1;
                }

                self.done = true;
                return ExpandIteratorOption::None;
            }
            _ => unreachable!(),
        }
    }
}

impl<'a> ExpandIterator<'a> {
    pub fn next(&mut self, var_info: &GlobalVarInfo) -> Option<MatchOpt<'a>> {
        if self.done {
            return None;
        }

        match &mut self.subiter {
            ExpandSubIterator::SubExpr(seqiter, ref mut pos, _) => {
                // for subexpressions, yield each iterator one by one
                while *pos < seqiter.len() {
                    if !seqiter[*pos].done {
                        if let Some(x) = seqiter[*pos]
                            .next_inline()
                            .or_else(|| seqiter[*pos].next(var_info))
                        {
                            return Some(x);
                        }
                    }
                    *pos += 1;
                }

                self.done = true;
                None
            }
            ExpandSubIterator::Term(seqiter_state) => {
                let mut i = seqiter_state.len() - 1;
                loop {
                    if !seqiter_state[i].0.done {
                        if let Some(x) = seqiter_state[i]
                            .0
                            .next_inline_subexpr()
                            .or_else(|| seqiter_state[i].0.next(var_info))
                        {
                            seqiter_state[i].1 = x;

                            if i + 1 == seqiter_state.len() {
                                let size = seqiter_state
                                    .iter()
                                    .map(|i| match i.1 {
                                        MatchOpt::Multiple(es) => es.len(),
                                        _ => 1,
                                    })
                                    .sum();
                                let mut v = Vec::with_capacity(size);
                                for x in seqiter_state {
                                    match x.1 {
                                        MatchOpt::Single(e) => {
                                            v.push(e.clone());
                                        }
                                        MatchOpt::SingleOwned(ref e) => {
                                            v.push(e.clone());
                                        }
                                        MatchOpt::Multiple(es) => {
                                            v.extend_from_slice(es);
                                        }
                                    }
                                }

                                let mut nt = Element::Term(true, v);
                                nt.normalize_inplace(var_info);
                                return Some(MatchOpt::SingleOwned(nt));
                            }

                            // reset the next iterator
                            i += 1;
                            seqiter_state[i].0.reset();
                            continue;
                        }
                    }

                    if i == 0 {
                        self.done = true;
                        return None;
                    }

                    i -= 1;
                }
            }
            ExpandSubIterator::Exp(ref mut it, ..) => match it.next() {
                Some((c, mut newt)) => {
                    newt.push(Element::Num(false, c));
                    let mut nt = Element::Term(true, newt);
                    nt.normalize_inplace(var_info);
                    Some(MatchOpt::SingleOwned(nt))
                }
                None => {
                    self.done = true;
                    None
                }
            },
            ExpandSubIterator::Yield(e) => {
                self.done = true;
                Some(MatchOpt::SingleOwned(e.clone()))
            }
            ExpandSubIterator::YieldMultiple(ee) => {
                self.done = true;
                Some(MatchOpt::Multiple(ee))
            }
        }
    }
}

impl Element {
    /// Expands products and positive powers in the element (non-iteratively).
    pub fn expand(self, var_info: &GlobalVarInfo) -> Element {
        match self {
            Element::Fn(_, name, args) => {
                let mut f = Element::Fn(
                    true,
                    name,
                    args.into_iter().map(|x| x.expand(var_info)).collect(),
                );
                f.normalize_inplace(var_info);
                f
            }
            Element::Term(_, fs) => {
                let mut r: Vec<Element> = vec![Element::Term(false, vec![])];

                for f in fs {
                    let fe = f.expand(var_info);
                    match fe {
                        Element::SubExpr(_, s) => {
                            let mut rnew = Vec::with_capacity(r.len() * s.len());

                            for x in r {
                                rnew.extend(s.iter().map(|y| x.clone().append_factors(y)));
                            }

                            r = rnew;
                        }
                        _ => {
                            for rr in &mut r {
                                *rr = mem::replace(rr, Element::default()).append_factors(&fe);
                            }
                        }
                    }
                }

                let mut e = Element::SubExpr(true, r);
                e.normalize_inplace(var_info);
                e
            }
            Element::SubExpr(_, f) => {
                let mut e =
                    Element::SubExpr(true, f.into_iter().map(|x| x.expand(var_info)).collect());
                e.normalize_inplace(var_info);
                e
            }
            Element::Pow(_, be) => {
                let (b, e) = { *be };

                let (mut eb, ee) = (b.expand(var_info), e.expand(var_info));

                if let Element::Num(_, Number::SmallInt(n)) = ee {
                    if n > 0 {
                        if let Element::SubExpr(_, ref mut t) = eb {
                            // compute the exponent of a list, without generating double entries
                            let it = CombinationsWithReplacement::new(
                                mem::replace(t, vec![]),
                                n as usize,
                            );

                            let mut terms_out = Vec::with_capacity(ncr(
                                t.len() as u64 + n as u64 - 1,
                                t.len() as u64 - 1,
                            )
                                as usize);

                            for (c, mut newt) in it {
                                newt.push(Element::Num(false, c));
                                let mut nt = Element::Term(true, newt);
                                nt.normalize_inplace(var_info);
                                terms_out.push(nt);
                            }

                            let mut e = Element::SubExpr(true, terms_out);
                            e.normalize_inplace(var_info);
                            return e.expand(var_info);
                        }

                        //  (x*y)^z -> x^z*y^z
                        if let Element::Term(_, t) = eb {
                            let mut e = Element::Term(
                                true,
                                t.iter()
                                    .map(|x| {
                                        Element::Pow(
                                            true,
                                            Box::new((
                                                x.clone(),
                                                Element::Num(false, Number::SmallInt(n)),
                                            )),
                                        )
                                    })
                                    .collect(),
                            );
                            e.normalize_inplace(var_info);
                            return e.expand(var_info);
                        }
                    }
                }

                let mut e = Element::Pow(true, Box::new((eb, ee)));
                e.normalize_inplace(var_info);
                e
            }
            _ => self,
        }
    }
}
