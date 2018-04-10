use structure::*;
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use std::io::{Error, Read, Write};

// TODO: replace by mem::discriminant when it stabilizes
const NUM_ID: u8 = 1;
const VAR_ID: u8 = 2;
const FN_ID: u8 = 3;
const TERM_ID: u8 = 4;
const EXPR_ID: u8 = 5;
const POW_ID: u8 = 6;

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

impl Element {
    // convert a normalized Element to a linear representation
    pub fn serialize(&self, buffer: &mut Write) -> usize {
        match *self {
            Element::Num(false, ref num) => {
                unimplemented!();
                // TODO: use varint for compression?
                /*buffer.write_u8(NUM_ID).unwrap();
                buffer.write_u8(pos as u8).unwrap();
                buffer.write_u64::<LittleEndian>(num).unwrap();
                buffer.write_u64::<LittleEndian>(den).unwrap();
                18*/
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
            _ => unreachable!(),
        }
    }

    pub fn deserialize(buffer: &mut Read) -> Result<Element, Error> {
        Ok(match buffer.read_u8()? {
            /*NUM_ID => Element::Num(
                false,
                buffer.read_u8().unwrap() != 0u8,
                buffer.read_u64::<LittleEndian>().unwrap(),
                buffer.read_u64::<LittleEndian>().unwrap(),
            ),*/
            FN_ID => Element::Fn(
                false,
                buffer.read_u32::<LittleEndian>().unwrap(),
                deserialize_list(buffer),
            ),
            VAR_ID => Element::Var(buffer.read_u32::<LittleEndian>().unwrap()),
            TERM_ID => Element::Term(false, deserialize_list(buffer)),
            EXPR_ID => Element::SubExpr(false, deserialize_list(buffer)),
            POW_ID => {
                let b = Element::deserialize(buffer).unwrap();
                let e = Element::deserialize(buffer).unwrap();
                Element::Pow(false, Box::new((b, e)))
            }
            _ => unreachable!(),
        })
    }
}
