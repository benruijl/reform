use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use gmp_mpfr_sys::gmp;
use number::Number;
use poly::raw::MultivariatePolynomial;
use rug::{Integer, Rational};
use std::cmp::Ordering;
use std::io::Cursor;
use std::io::{Error, Read, Seek, SeekFrom, Write};
use std::os::raw::c_void;
use structure::*;

// TODO: replace by mem::discriminant when it stabilizes
const NUM_ID: u8 = 1;
const VAR_ID: u8 = 2;
const FN_ID: u8 = 3;
const TERM_ID: u8 = 4;
const EXPR_ID: u8 = 5;
const POW_ID: u8 = 6;
const PRF_ID: u8 = 7;

const NUM_SMALLINT_ID: u8 = 1;
const NUM_BIGINT_ID: u8 = 2;
const NUM_SMALLRAT_ID: u8 = 3;
const NUM_BIGRAT_ID: u8 = 4;

fn serialize_list(args: &[Element], buffer: &mut Write) -> usize {
    let mut len = 4;
    buffer.write_u32::<LittleEndian>(args.len() as u32).unwrap();
    for x in args {
        len += x.serialize(buffer);
    }
    len
}

fn deserialize_list(buffer: &mut Read) -> Vec<Element> {
    let len = buffer.read_u32::<LittleEndian>().unwrap() as usize;
    let mut list = Vec::with_capacity(len);
    for _ in 0..len {
        list.push(Element::deserialize(buffer).unwrap());
    }
    list
}

fn serialize_integer(i: &Integer, buffer: &mut Write) -> usize {
    unsafe {
        // TODO: can we overflow, since we use bytes?
        let mut count = (gmp::mpz_sizeinbase(i.as_raw(), 2) + 7) / 8;
        buffer.write_u8(gmp::mpz_sgn(i.as_raw()) as u8).unwrap();
        buffer.write_u64::<LittleEndian>(count as u64).unwrap();

        // TODO: directly write to buffer?
        let mut numbuffer = vec![0u8; count];
        gmp::mpz_export(
            &mut numbuffer[0] as *mut _ as *mut c_void,
            &mut count,
            1,
            1,
            -1,
            0,
            i.as_raw(),
        );
        buffer.write(&numbuffer).unwrap();
        9 + count
    }
}

fn deserialize_integer(buffer: &mut Read) -> Result<Integer, Error> {
    let sign = buffer.read_u8()?;
    let count = buffer.read_u64::<LittleEndian>()? as usize;

    let mut res = gmp::mpz_t {
        alloc: 0,
        size: 0,
        d: 0 as *mut u64,
    };

    let mut numbuffer = vec![0u8; count];
    buffer.read(&mut numbuffer)?;
    unsafe {
        gmp::mpz_import(
            &mut res,
            count,
            1,
            1,
            -1,
            0,
            &numbuffer[0] as *const _ as *const c_void,
        );

        if sign > 1 {
            Ok(-Integer::from_raw(res))
        } else {
            Ok(Integer::from_raw(res))
        }
    }
}

impl Number {
    pub fn serialize(&self, buffer: &mut Write) -> usize {
        match self {
            Number::SmallInt(i) => {
                buffer.write_u8(NUM_SMALLINT_ID).unwrap();
                buffer.write_i64::<LittleEndian>(*i as i64).unwrap();
                9
            }
            Number::SmallRat(n, d) => {
                buffer.write_u8(NUM_SMALLRAT_ID).unwrap();
                buffer.write_i64::<LittleEndian>(*n as i64).unwrap();
                buffer.write_i64::<LittleEndian>(*d as i64).unwrap();
                17
            }
            Number::BigInt(i) => {
                buffer.write_u8(NUM_BIGINT_ID).unwrap();
                1 + serialize_integer(i, buffer)
            }
            Number::BigRat(r) => {
                buffer.write_u8(NUM_BIGRAT_ID).unwrap();
                let n = serialize_integer(r.numer(), buffer);
                1 + n + serialize_integer(r.denom(), buffer)
            }
        }
    }

    pub fn deserialize(buffer: &mut Read) -> Result<Number, Error> {
        Ok(match buffer.read_u8()? {
            NUM_SMALLINT_ID => Number::SmallInt(buffer.read_i64::<LittleEndian>()? as isize),
            NUM_SMALLRAT_ID => Number::SmallRat(
                buffer.read_i64::<LittleEndian>()? as isize,
                buffer.read_i64::<LittleEndian>()? as isize,
            ),
            NUM_BIGINT_ID => Number::BigInt(deserialize_integer(buffer)?),
            NUM_BIGRAT_ID => {
                let num = deserialize_integer(buffer)?;
                let den = deserialize_integer(buffer)?;
                Number::BigRat(Box::new(Rational::from((num, den))))
            }
            _ => unreachable!(),
        })
    }

    pub fn compare_serialized(b1: &mut Cursor<&[u8]>, b2: &mut Cursor<&[u8]>) -> Ordering {
        // TODO: compare bytes?
        let num1 = Number::deserialize(b1).unwrap();
        let num2 = Number::deserialize(b2).unwrap();
        num1.partial_cmp(&num2).unwrap()
    }
}

impl MultivariatePolynomial<Number, u32> {
    pub fn serialize(&self, buffer: &mut Write) -> usize {
        buffer
            .write_u64::<LittleEndian>(self.nterms as u64)
            .unwrap();
        buffer.write_u32::<LittleEndian>(self.nvars as u32).unwrap();
        let mut len = 13;
        for t in 0..self.nterms {
            len += self.coefficients[t].serialize(buffer);

            for e in 0..self.nvars {
                buffer
                    .write_u32::<LittleEndian>(self.exponents(t)[e])
                    .unwrap();
            }
        }

        12 + len + self.nterms * self.nvars * 4
    }

    pub fn deserialize(buffer: &mut Read) -> Result<MultivariatePolynomial<Number, u32>, Error> {
        let nterms = buffer.read_u64::<LittleEndian>()? as usize;
        let nvars = buffer.read_u32::<LittleEndian>()? as usize;

        let mut coeffs = Vec::with_capacity(nterms);
        let mut exponents = Vec::with_capacity(nterms * nvars);

        for _ in 0..nterms {
            coeffs.push(Number::deserialize(buffer)?);

            for _ in 0..nvars {
                exponents.push(buffer.read_u32::<LittleEndian>()?);
            }
        }

        let mut p = MultivariatePolynomial::new();
        p.nterms = nterms;
        p.nvars = nvars;
        p.coefficients = coeffs;
        p.exponents = exponents;

        Ok(p)
    }
}

impl Element {
    // convert a normalized Element to a linear representation
    pub fn serialize(&self, buffer: &mut Write) -> usize {
        match *self {
            Element::Num(false, ref num) => {
                // TODO: use varint for compression?
                buffer.write_u8(NUM_ID).unwrap();
                1 + num.serialize(buffer)
            }
            Element::Fn(false, ref name, ref args) => {
                buffer.write_u8(FN_ID).unwrap();
                buffer.write_u32::<LittleEndian>(*name).unwrap();
                9 + serialize_list(args, buffer)
            }
            Element::Var(ref name) => {
                buffer.write_u8(VAR_ID).unwrap();
                buffer.write_u32::<LittleEndian>(*name).unwrap();
                9
            }
            Element::Term(false, ref args) => {
                buffer.write_u8(TERM_ID).unwrap();
                1 + serialize_list(args, buffer)
            }
            Element::SubExpr(false, ref args) => {
                buffer.write_u8(EXPR_ID).unwrap();
                1 + serialize_list(args, buffer)
            }
            Element::Pow(false, ref be) => {
                let (ref b, ref e) = **be;
                buffer.write_u8(POW_ID).unwrap();
                let len = b.serialize(buffer);
                1 + len + e.serialize(buffer)
            }
            Element::RationalPolynomialCoefficient(false, ref r) => {
                let (ref num, ref den) = **r;
                buffer.write_u8(PRF_ID).unwrap();
                let len = num.serialize(buffer);
                1 + len + den.serialize(buffer)
            }
            _ => unreachable!(),
        }
    }

    pub fn deserialize(buffer: &mut Read) -> Result<Element, Error> {
        Ok(match buffer.read_u8()? {
            NUM_ID => Element::Num(false, Number::deserialize(buffer)?),
            FN_ID => Element::Fn(
                false,
                buffer.read_u32::<LittleEndian>()?,
                deserialize_list(buffer),
            ),
            VAR_ID => Element::Var(buffer.read_u32::<LittleEndian>()?),
            TERM_ID => Element::Term(false, deserialize_list(buffer)),
            EXPR_ID => Element::SubExpr(false, deserialize_list(buffer)),
            POW_ID => {
                let b = Element::deserialize(buffer)?;
                let e = Element::deserialize(buffer)?;
                Element::Pow(false, Box::new((b, e)))
            }
            PRF_ID => {
                let num = MultivariatePolynomial::deserialize(buffer)?;
                let den = MultivariatePolynomial::deserialize(buffer)?;
                Element::RationalPolynomialCoefficient(false, Box::new((num, den)))
            }
            _ => unreachable!(),
        })
    }

    /// Compare normalized terms in serialized form.
    pub fn compare_term_serialized(
        b1: &mut Cursor<&[u8]>,
        b2: &mut Cursor<&[u8]>,
        ground_level: bool,
    ) -> Ordering {
        match (b1.read_u8().unwrap(), b2.read_u8().unwrap()) {
            (FN_ID, FN_ID) => {
                let name1 = b1.read_u32::<LittleEndian>().unwrap();
                let name2 = b2.read_u32::<LittleEndian>().unwrap();

                if name1 != name2 {
                    return name1.cmp(&name2);
                }

                let len1 = b1.read_u32::<LittleEndian>().unwrap();
                let len2 = b2.read_u32::<LittleEndian>().unwrap();

                if len1 != len2 {
                    return len1.cmp(&len2);
                }

                for _ in 0..len1 {
                    match Element::compare_term_serialized(b1, b2, false) {
                        Ordering::Equal => {}
                        x => return x,
                    }
                }

                Ordering::Equal
            }
            (NUM_ID, NUM_ID) => {
                if ground_level {
                    Ordering::Equal
                } else {
                    Number::compare_serialized(b1, b2)
                }
            }
            (_, NUM_ID) => Ordering::Less,
            (NUM_ID, _) => Ordering::Greater,
            // TODO: if we allow polyratfuns in functions, we should add a partial_cmp between them
            (PRF_ID, PRF_ID) => Ordering::Equal,
            (_, PRF_ID) => Ordering::Less,
            (PRF_ID, _) => Ordering::Greater,
            (POW_ID, POW_ID) => {
                // compare the base
                match Element::compare_term_serialized(b1, b2, false) {
                    // compare exponent
                    Ordering::Equal => Element::compare_term_serialized(b1, b2, false),
                    x => x,
                }
            }
            (POW_ID, _) => Ordering::Less, // TODO: check if this is correct
            (_, POW_ID) => Ordering::Greater,
            (TERM_ID, TERM_ID) => {
                let len1 = b1.read_u32::<LittleEndian>().unwrap();
                let len2 = b2.read_u32::<LittleEndian>().unwrap();

                // do a quick length check
                // TODO: check if the terms have coefficients
                if (!ground_level && len1 != len2)
                    || (ground_level && (len1 + 1 < len2 || len1 > len2 + 1))
                {
                    return len1.cmp(&len2);
                }

                let maxlen = if len1 > len2 { len1 } else { len2 };

                for i in 0..maxlen {
                    // ignore coefficients on ground level
                    if ground_level {
                        if i < len1 {
                            let e1 = b1.read_u8().unwrap();
                            b1.seek(SeekFrom::Current(-1)).unwrap();
                            if e1 == NUM_ID || e1 == PRF_ID {
                                continue;
                            }
                        }

                        if i < len2 {
                            let e2 = b2.read_u8().unwrap();
                            b2.seek(SeekFrom::Current(-1)).unwrap();
                            if e2 == NUM_ID || e2 == PRF_ID {
                                continue;
                            }
                        }
                    }
                    match Element::compare_term_serialized(b1, b2, false) {
                        Ordering::Equal => {}
                        x => return x,
                    }
                }

                Ordering::Equal
            }
            (_, TERM_ID) => {
                let len = b2.read_u32::<LittleEndian>().unwrap();
                if ground_level && len == 2 {
                    let e = b2.read_u8().unwrap();
                    if e == NUM_ID {
                        b2.seek(SeekFrom::Current(-1)).unwrap();
                        return Element::compare_term_serialized(b1, b2, ground_level);
                    }
                }

                Ordering::Less
            }
            (TERM_ID, _) => {
                let len = b1.read_u32::<LittleEndian>().unwrap();
                if ground_level && len == 2 {
                    let e = b1.read_u8().unwrap();
                    if e == NUM_ID {
                        b1.seek(SeekFrom::Current(-1)).unwrap();
                        return Element::compare_term_serialized(b1, b2, ground_level);
                    }
                }

                Ordering::Greater
            }
            (FN_ID, _) => Ordering::Less,
            (_, FN_ID) => Ordering::Greater,
            (EXPR_ID, EXPR_ID) => {
                let len1 = b1.read_u32::<LittleEndian>().unwrap();
                let len2 = b2.read_u32::<LittleEndian>().unwrap();
                if len1 != len2 {
                    return len1.cmp(&len2);
                }

                for _ in 0..len1 {
                    match Element::compare_term_serialized(b1, b2, false) {
                        Ordering::Equal => {}
                        x => return x,
                    }
                }

                Ordering::Equal
            }
            (EXPR_ID, _) => Ordering::Less,
            (VAR_ID, VAR_ID) => b1.read_u32::<LittleEndian>()
                .unwrap()
                .cmp(&b2.read_u32::<LittleEndian>().unwrap()),
            _ => Ordering::Less,
        }
    }
}
