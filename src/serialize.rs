use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use number::Number;
use poly::raw::MultivariatePolynomial;
use std::io::{Error, Read, Write};
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
            Number::BigInt(_i) => {
                // mpz_out_raw is not in the bindings yet
                unimplemented!()
            }
            Number::BigRat(_r) => unimplemented!(),
        }
    }

    pub fn deserialize(buffer: &mut Read) -> Result<Number, Error> {
        Ok(match buffer.read_u8()? {
            NUM_SMALLINT_ID => Number::SmallInt(buffer.read_i64::<LittleEndian>()? as isize),
            NUM_SMALLRAT_ID => Number::SmallRat(
                buffer.read_i64::<LittleEndian>()? as isize,
                buffer.read_i64::<LittleEndian>()? as isize,
            ),
            NUM_BIGINT_ID => unimplemented!(),
            NUM_BIGRAT_ID => unimplemented!(),
            _ => unreachable!(),
        })
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
}
