use std::cmp::Ordering;
use std::cmp::Ordering::*;
use std::mem;
use std::ptr;

/// Sorts a vector of `T` according to `cmp`, adds
/// equal elements according to `merger`, and returns an index map of
/// the (merged) elements in the proper
/// order. We allocate the necessary vectors once and use a separate
/// recursive routine after that. Reading the output properly is done with
/// ```
/// for i in ..row.len() {
///     ...
///     terms[row[i]]
///     ...
/// }```
pub fn split_merge<T: Default, F1, F2>(mut terms: &mut [T], cmp: &F1, merger: &F2) -> Vec<usize>
where
    F1: Fn(&T, &T) -> Ordering,
    F2: Fn(&mut T, &mut T) -> bool,
{
    let n = terms.len();
    let mut row: Vec<usize> = (0..n).collect();

    let mut sbuf = vec![0; n / 2];
    unsafe {
        let n_out = split_merge_rec(&mut terms, &mut row, &mut sbuf, n, cmp, merger);
        row.truncate(n_out);
    }
    row
}

unsafe fn split_merge_rec<T: Default, F1, F2>(
    mut terms: &mut [T],
    row: &mut [usize],
    mut sbuf: &mut [usize],
    n: usize,
    cmp: &F1,
    merger: &F2,
) -> usize
where
    F1: Fn(&T, &T) -> Ordering,
    F2: Fn(&mut T, &mut T) -> bool,
{
    //==================================================================
    #[inline]
    unsafe fn add_one<T: Default, F>(
        terms: &mut [T],
        row: &mut [usize],
        one: usize,
        two: usize,
        merger: &F,
    ) -> bool
    where
        F: Fn(&mut T, &mut T) -> bool,
    {
        let mut term = mem::replace(
            terms.get_unchecked_mut(*row.get_unchecked(two)),
            T::default(),
        );

        let v = terms.get_unchecked_mut(*row.get_unchecked(one));

        merger(v, &mut term)
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
        match cmp(
            terms.get_unchecked(*row.get_unchecked(0)),
            terms.get_unchecked(*row.get_unchecked(1)),
        ) {
            Greater => {
                ptr::swap_nonoverlapping(row.get_unchecked_mut(0), row.get_unchecked_mut(1), 1);
            }
            Less => (),
            Equal => {
                if add_one(terms, row, 0, 1, merger) {
                    return 0;
                }
                return 1;
            }
        }
        return 2;
    }
    let split = n / 2;
    let mut len1 = split_merge_rec(
        &mut terms,
        row.get_unchecked_mut(0..split),
        &mut sbuf,
        split,
        cmp,
        merger,
    );
    let len2 = split_merge_rec(
        &mut terms,
        row.get_unchecked_mut(split..n),
        &mut sbuf,
        n - split,
        cmp,
        merger,
    );
    if len1 > 0 && len2 > 0 {
        //------------------------------------------------------------
        //
        //  We start by testing whether the second part comes after the
        //  first part in its entirety. This ensures that when there is
        //  a very high degree of order, things will go at top speed.
        //
        match cmp(
            terms.get_unchecked(*row.get_unchecked(len1 - 1)),
            terms.get_unchecked(*row.get_unchecked(split)),
        ) {
            Greater => (), // Out of order. Do it the hard way!
            Less => {
                // lucky
                if len1 < split {
                    ptr::copy(row.get_unchecked(split), row.get_unchecked_mut(len1), len2);
                }
                return len1 + len2;
            }
            Equal => {
                // (lucky)^2
                if add_one(terms, row, len1 - 1, split, merger) {
                    len1 -= 1;
                }
                ptr::copy(
                    row.get_unchecked(split + 1),
                    row.get_unchecked_mut(len1),
                    len2 - 1,
                );
                return len1 + len2 - 1;
            }
        }

        //------------------------------------------------------------
        //
        // Now we have to merge row and row+split. This cannot happen in place
        // and hence we need the sbuf. We have to copy the pointers
        // in row to the sbuf, after which the merge should be easy.
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
            match cmp(
                terms.get_unchecked(*row.get_unchecked(i1 + ins - 1)),
                terms.get_unchecked(*row.get_unchecked(split)),
            ) {
                Greater => {
                    size1 = ins;
                }
                Less => {
                    i1 += ins;
                    size1 -= ins;
                    ifill = i1;
                }
                Equal => {
                    if add_one(terms, row, i1 + ins - 1, split, merger) {
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
        ptr::copy_nonoverlapping(row.get_unchecked(i1), sbuf.get_unchecked_mut(i1), len1 - i1);
        //------------------------------------------------------------
        if i2 < len2 {
            loop {
                match cmp(
                    terms.get_unchecked(*sbuf.get_unchecked(i1)),
                    terms.get_unchecked(*row.get_unchecked(i2 + split)),
                ) {
                    Greater => {
                        *row.get_unchecked_mut(ifill) = *row.get_unchecked(i2 + split);
                        i2 += 1;
                        ifill += 1;
                        if i2 >= len2 {
                            break;
                        }
                    }
                    Less => {
                        *row.get_unchecked_mut(ifill) = *sbuf.get_unchecked(i1);
                        i1 += 1;
                        ifill += 1;
                        if i1 >= len1 {
                            break;
                        }
                    }
                    Equal => {
                        *row.get_unchecked_mut(ifill) = *sbuf.get_unchecked(i1);
                        if !add_one(terms, row, ifill, i2 + split, merger) {
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
                row.get_unchecked_mut(ifill),
                len1 - i1,
            );
            ifill += len1 - i1;
        } else if i2 < len2 {
            ptr::copy(
                row.get_unchecked(split + i2),
                row.get_unchecked_mut(ifill),
                len2 - i2,
            );
            ifill += len2 - i2;
        }
        ifill
    } else if len1 > 0 {
        len1
    } else if len2 > 0 {
        ptr::copy(row.get_unchecked(split), row.get_unchecked_mut(0), len2);
        len2
    } else {
        0
    }
}
