use test::Bencher;

use structure::{NamedElement, VarInfo};

#[bench]
fn to_element(b: &mut Bencher) {
    let mut f = NamedElement::Fn(
        true,
        "g".to_string(),
        vec![
            NamedElement::Var("m1".to_string()),
            NamedElement::Var("m2".to_string()),
            NamedElement::Var("m3".to_string()),
            NamedElement::Var("m4".to_string()),
            NamedElement::Var("m5".to_string()),
            NamedElement::Var("m6".to_string()),
            NamedElement::Var("m7".to_string()),
            NamedElement::Var("m8".to_string()),
            NamedElement::Var("m9".to_string()),
            NamedElement::Var("m10".to_string()),
            NamedElement::Var("m11".to_string()),
            NamedElement::Var("m12".to_string()),
            NamedElement::Var("m13".to_string()),
            NamedElement::Var("m14".to_string()),
        ],
    );
    let mut var_info = VarInfo::new();
    b.iter(|| f.to_element(&mut var_info));
}

#[bench]
fn id_func_args(b: &mut Bencher) {
    let mut f = NamedElement::Fn(
        true,
        "g".to_string(),
        vec![
            NamedElement::Var("m1".to_string()),
            NamedElement::Var("m2".to_string()),
            NamedElement::Var("m3".to_string()),
            NamedElement::Var("m4".to_string()),
            NamedElement::Var("m5".to_string()),
            NamedElement::Var("m6".to_string()),
            NamedElement::Var("m7".to_string()),
            NamedElement::Var("m8".to_string()),
            NamedElement::Var("m9".to_string()),
            NamedElement::Var("m10".to_string()),
            NamedElement::Var("m11".to_string()),
            NamedElement::Var("m12".to_string()),
            NamedElement::Var("m13".to_string()),
            NamedElement::Var("m14".to_string()),
        ],
    );
    let mut var_info = VarInfo::new();
    let mut f = f.to_element(&mut var_info);
    f.normalize_inplace();
    b.iter(|| {
        // TODO: small part of the tracen problem
        f.clone()
    });
}
