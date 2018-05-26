use normalize;
use num_traits::{One, Zero};
use number::Number;
use std::cmp::Ordering::*;
use std::mem;
use std::ptr;
use structure::{Element, GlobalVarInfo};

///
/// Gets a vector elements of Element's, sorts them according to compare, adds
/// equal Element's according to add_Element and returns the number of elements
/// remaining.
/// We allocate the necessary vector once and use a separate
/// recursive routine after that. The output overwrites the input.
///
/// The function returns the new number of terms, but does not resize the vector.
///
pub fn split_merge(mut elements: &mut [Element], var_info: &GlobalVarInfo) -> usize {
    let n = elements.len();
    if n < 2 {
        return n;
    }

    let mut sbuf: Vec<Element> = Vec::with_capacity(n / 2);

    unsafe { split_merge_rec(&mut elements, &mut sbuf, n, var_info) }
}

unsafe fn split_merge_rec(
    elements: &mut [Element],
    mut sbuf: &mut [Element],
    n: usize,
    var_info: &GlobalVarInfo,
) -> usize {
    //==================================================================
    #[inline]
    unsafe fn add_one(
        elements: &mut [Element],
        one: usize,
        two: usize,
        var_info: &GlobalVarInfo,
    ) -> bool {
        let mut element = mem::replace(elements.get_unchecked_mut(two), DUMMY_ELEM!());

        let v = elements.get_unchecked_mut(one);

        normalize::merge_terms(v, &mut element, var_info);
        *v == Element::Num(false, Number::zero())
    }
    //==================================================================
    //
    //  When the buffers, cq. number of terms, become very large this method
    //  is rather cache unfriendly. The original purpose of this routine was
    //  to have a fast sorting method that would not allow swapping, due to
    //  its intensive use of the buffers (and the sorting by pointers).
    //  One sorted, the contents are supposed to be written as a sorted 'patch'
    //  to a larger buffer. There several patches can then be merged by a
    //  method that is much better protected against swapping, but that needs
    //  to move each term once during the complete merge.
    //
    //  The art is in choosing the sizes of the various buffers. This is
    //  very dependent on the parameters of the computer.
    //
    if n < 2 {
        return n;
    } else if n == 2 {
        match elements
            .get_unchecked(0)
            .partial_cmp(elements.get_unchecked(1), var_info, true)
            .unwrap()
        {
            Greater => {
                ptr::swap(elements.get_unchecked_mut(0), elements.get_unchecked_mut(1));
            }
            Less => (),
            Equal => {
                if add_one(elements, 0, 1, var_info) {
                    return 0;
                }
                return 1;
            }
        }
        return 2;
    }
    let split = n / 2;
    let mut len1 = split_merge_rec(&mut elements[0..split], &mut sbuf, split, var_info);
    let len2 = split_merge_rec(&mut elements[split..n], &mut sbuf, n - split, var_info);
    if len1 > 0 && len2 > 0 {
        //------------------------------------------------------------
        //
        //  We start by testing whether the second part comes after the
        //  first part in its entirety. This ensures that when there is
        //  a very high degree of order, things will go at top speed.
        //
        match elements
            .get_unchecked(len1 - 1)
            .partial_cmp(elements.get_unchecked(split), var_info, true)
            .unwrap()
        {
            Greater => (), // Out of order. Do it the hard way!
            Less => {
                // lucky
                if len1 < split {
                    ptr::copy(
                        elements.get_unchecked(split),
                        elements.get_unchecked_mut(len1),
                        len2,
                    );
                }
                return len1 + len2;
            }
            Equal => {
                // (lucky)^2
                if add_one(elements, len1 - 1, split, var_info) {
                    len1 -= 1;
                }
                ptr::copy(
                    elements.get_unchecked(split + 1),
                    elements.get_unchecked_mut(len1),
                    len2 - 1,
                );
                return len1 + len2 - 1;
            }
        }

        //------------------------------------------------------------
        //
        // Now we have to merge elements and elements+split. This cannot happen in
        // place and hence we need the sbuf.
        //
        let mut i1: usize = 0;
        let mut i2: usize = 0;
        let mut ifill: usize = 0;
        //------------------------------------------------------------
        //
        //  First a timsort-style improvement. We look by binary search for
        //  whether the second run comes after a reasonable number of terms
        //  in the first run. We choose the resolution not too small, because
        //  this earch is an investment, and we do not want to make it too big.
        //  It is very helpful when there is much partial ordering. It does
        //  cost a bit when there is none.
        //
        let mut size1 = len1;
        while size1 > 8 {
            let ins = size1 / 2;
            match elements
                .get_unchecked(i1 + ins - 1)
                .partial_cmp(elements.get_unchecked(split), var_info, true)
                .unwrap()
            {
                Greater => {
                    size1 = ins;
                }
                Less => {
                    i1 += ins;
                    size1 -= ins;
                    ifill = i1;
                }
                Equal => {
                    if add_one(elements, i1 + ins - 1, split, var_info) {
                        i1 += ins;
                        ifill = i1 - 1;
                    } else {
                        i1 += ins;
                        ifill = i1;
                    }
                    i2 += 1;
                    break;
                }
            }
        }
        //
        //  Now we continue with the split_merge proper.
        //  Note that we always do a forward merge. This can always be done
        //  inside an sbuf that is at most N/2 long because the split is
        //  always equal (at N/2).
        //
        ptr::copy_nonoverlapping(
            elements.get_unchecked(i1),
            sbuf.get_unchecked_mut(i1),
            len1 - i1,
        );
        //------------------------------------------------------------
        if i2 < len2 {
            loop {
                match sbuf.get_unchecked(i1)
                    .partial_cmp(elements.get_unchecked(i2 + split), var_info, true)
                    .unwrap()
                {
                    Greater => {
                        ptr::swap(
                            elements.get_unchecked_mut(ifill),
                            elements.get_unchecked_mut(i2 + split),
                        );
                        i2 += 1;
                        ifill += 1;
                        if i2 >= len2 {
                            break;
                        }
                    }
                    Less => {
                        ptr::swap(
                            elements.get_unchecked_mut(ifill),
                            sbuf.get_unchecked_mut(i1),
                        );
                        i1 += 1;
                        ifill += 1;
                        if i1 >= len1 {
                            break;
                        }
                    }
                    Equal => {
                        ptr::swap(
                            elements.get_unchecked_mut(ifill),
                            sbuf.get_unchecked_mut(i1),
                        );
                        if !add_one(elements, ifill, i2 + split, var_info) {
                            ifill += 1;
                        }
                        i1 += 1;
                        i2 += 1;
                        if i1 >= len1 || i2 >= len2 {
                            break;
                        }
                    }
                }
            }
        }
        if i1 < len1 {
            ptr::copy_nonoverlapping(
                sbuf.get_unchecked(i1),
                elements.get_unchecked_mut(ifill),
                len1 - i1,
            );
            ifill += len1 - i1;
        } else if i2 < len2 {
            ptr::copy(
                elements.get_unchecked(split + i2),
                elements.get_unchecked_mut(ifill),
                len2 - i2,
            );
            ifill += len2 - i2;
        }
        ifill
    } else if len1 > 0 {
        len1
    } else if len2 > 0 {
        ptr::copy(
            elements.get_unchecked(split),
            elements.get_unchecked_mut(0),
            len2,
        );
        len2
    } else {
        0
    }
}
