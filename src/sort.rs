use std::fmt::Debug;
use std::mem;
use std::cmp::min;
use std::cmp::Ordering;

pub fn sort<T: PartialOrd + Debug>(input: &mut [T]) {
    let n = input.len();

    if n > 2 {
        heapify(input);

        let mut end = n - 1;
        while end > 0 {
            input.swap(end, 0);
            end -= 1;
            sift_down(input, 0, end);
        }
    }
}

fn node_parent_id(i: usize) -> usize {
    if i == 0 { 0 }
    else      { (i - 1) / 2 }
}

fn node_child_left(i: usize) -> usize {
    2 * i + 1
}

// fn node_child_right(i: usize) -> usize {
//     2 * i + 2
// }

fn heapify<T: PartialOrd + Debug>(input: &mut [T]) {
    let n = input.len();
    let end = n - 1;

    // Last element is at "n-1". Find its parent and start there:
    let mut start: usize = node_parent_id(n-1);

    loop {
        sift_down(input, start, end);
        if start == 0 { break; }
        start -= 1;
    }
}

fn sift_down<T: PartialOrd + Debug>(input: &mut [T], start: usize, end: usize) {
    let mut i = start;

    // Starting at the "start" element, loop "down" the vector and swap elements that are
    // not in max-heap order.
    while node_child_left(i) <= end {
        let child = node_child_left(i);
        let mut swap = i;

        //println!("cmp {:?} {:?}", input[swap], input[child]);
        if input[swap] < input[child] {
            //println!("other child");
            swap = child;
        }
        if child+1 <= end && input[swap] < input[child+1] {
            swap = child + 1;
            //println!("other child 2");
        }

        if swap == i {
            return;
        } else {
            input.swap(i, swap);
            i = swap;
        }
    }
}

pub fn merge_sort<'a,T: PartialOrd + Debug>(mut a: &'a mut [T], mut b: &'a mut [T]) -> usize {
    if a.len() == 0 { return 0; }

    let mut grouplen = vec![];

    println!("Orig:  {:?}", a);

    let mut groupcount = 1;
    let mut writepos = 1;
    for x in 1..a.len() {
        match a[writepos - 1].partial_cmp(&a[x]) {
            Some(Ordering::Equal) => {
                //groupcount += 1;
            }
            Some(Ordering::Greater) => {
                grouplen.push(groupcount);
                groupcount = 1;
                a.swap(writepos, x);
                writepos += 1
            },
            Some(Ordering::Less) => {
                groupcount += 1;
                a.swap(writepos, x);
                writepos += 1
            },
            _ => unreachable!()
        }
    }
    grouplen.push(groupcount);
    println!("Natural order: {:?}", grouplen);
    println!("Input: {:?}", a);

    // Make successively longer sorted runs of length 2, 4, 8, 16... until whole array is sorted.
    while grouplen.len() > 1 {
        let mut groupcount = 0;
        let mut newgroupcount = vec![];
        let mut startpos = 0;
        let mut writepos = 0;
        while groupcount < grouplen.len() { // what happens with odd number?
            let newsize;
            if groupcount + 1 == grouplen.len() { // odd number?
                newsize = sub_merge_sort(a, startpos, startpos + grouplen[groupcount],
                            startpos + grouplen[groupcount],
                            b, writepos);
            } else {
                newsize = sub_merge_sort(a, startpos, startpos + grouplen[groupcount],
                            startpos + grouplen[groupcount] + grouplen[groupcount + 1],
                            b, writepos);
                startpos += grouplen[groupcount] + grouplen[groupcount + 1];
            }
            
            writepos += newsize;
            newgroupcount.push(newsize);
            groupcount += 2;
        }

        println!("R {:?} {:?}", b, &newgroupcount);
        grouplen = newgroupcount;

        mem::swap(&mut a, &mut b);
    }
    grouplen[0]
}

fn sub_merge_sort<T: PartialOrd + Debug>(a: &mut [T], left: usize, right: usize,
        end: usize, b: &mut [T], writepos: usize) -> usize {
    let mut i = left;
    let mut j = right;
    let mut k = writepos;

    while i < right || j < end {
        /*if i < right && i > left && a[i - 1] > a[i] {
            i = right;
        }
        if j < end && j > right && a[j - 1] > a[j] {
            j = end;
        }*/

        if i < right && j < end {
            //println!("cmp {:?} {:?}", a[i], a[j]);
            match a[i].partial_cmp(&a[j]) { // we need to compare to last result we put in
                Some(Ordering::Equal) => {
                    mem::swap(&mut b[k], &mut a[i]);
                    i += 1; // consume both
                    j += 1;
                    k += 1;
                }
                Some(Ordering::Greater) => {
                    mem::swap(&mut b[k], &mut a[j]);
                    j += 1;
                    k += 1;
                }
                Some(Ordering::Less) => {
                    mem::swap(&mut b[k], &mut a[i]);
                    i += 1;
                    k += 1
                },
                _ => unreachable!("Element comparison failed")
            }
        } else {
            if i < right {
                mem::swap(&mut b[k], &mut a[i]);
                i += 1;
            } else {
                mem::swap(&mut b[k], &mut a[j]);
                j += 1;
            }
            k += 1
        }
    }
    k - writepos
}