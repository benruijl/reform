//! Linear solver in Zp.

use ndarray::{Array1, Array2, ArrayBase, Data, Ix1, Ix2};

use poly::raw::zp;
use poly::raw::zp::ufield;

/// Error from linear solver.
#[derive(Debug, Eq, PartialEq)]
pub enum LinearSolverError {
    Underdetermined { min_rank: usize, max_rank: usize },
    Inconsistent,
}

/// Solves `a * x = b` in Zp.
pub fn solve<S1: Data<Elem = ufield>, S2: Data<Elem = ufield>>(
    a: &ArrayBase<S1, Ix2>,
    b: &ArrayBase<S2, Ix1>,
    p: ufield,
) -> Result<Array1<ufield>, LinearSolverError> {
    assert!(a.shape()[0] == b.shape()[0]);

    let neqs = a.shape()[0];
    let nvars = a.shape()[1];

    // A fast check.
    if neqs < nvars {
        return Err(LinearSolverError::Underdetermined {
            min_rank: 0,
            max_rank: neqs,
        });
    }

    // Create the augmented matrix.
    let mut m = unsafe { Array2::<ufield>::uninitialized((neqs, nvars + 1)) };
    for (i, e) in a.indexed_iter() {
        m[i] = *e;
    }
    for (i, e) in b.indexed_iter() {
        m[(i, nvars)] = *e;
    }

    // by the Gaussian elimination

    // First, transform the augmented matrix into the row echelon form.
    let mut i = 0;
    for j in 0..nvars {
        if m[(i, j)] == 0 {
            // Select a non-zero pivot.
            for k in i + 1..neqs {
                if m[(k, j)] != 0 {
                    // Swap i-th row and k-th row.
                    for l in j..nvars + 1 {
                        m.swap((i, l), (k, l));
                    }
                    break;
                }
            }
            if m[(i, j)] == 0 {
                // NOTE: complete pivoting may give an increase of the rank.
                return Err(LinearSolverError::Underdetermined {
                    min_rank: i,
                    max_rank: nvars - 1,
                });
            }
        }
        let x = m[(i, j)];
        let inv_x = zp::inv(x, p);
        for k in i + 1..neqs {
            if m[(k, j)] != 0 {
                let s = zp::mul(m[(k, j)], inv_x, p);
                #[cfg(debug_assertions)]
                {
                    m[(k, j)] = 0;
                }
                for l in j + 1..nvars + 1 {
                    m[(k, l)] = zp::sub(m[(k, l)], zp::mul(m[(i, l)], s, p), p);
                }
            }
        }
        i += 1;
        if i >= neqs {
            break;
        }
    }

    let rank = i;

    // Check the consistency.
    for k in rank..neqs {
        if m[(k, nvars)] != 0 {
            return Err(LinearSolverError::Inconsistent);
        }
    }

    // Check the rank.
    if rank < nvars {
        return Err(LinearSolverError::Underdetermined {
            min_rank: rank,
            max_rank: rank,
        });
    }
    assert_eq!(rank, nvars);

    // Now, back substitution.
    i -= 1;
    for j in (0..nvars).rev() {
        if m[(i, j)] != 1 {
            let x = m[(i, j)];
            let inv_x = zp::inv(x, p);
            #[cfg(debug_assertions)]
            {
                m[(i, j)] = 1;
            }
            m[(i, nvars)] = zp::mul(m[(i, nvars)], inv_x, p);
        }
        for k in 0..i {
            if m[(k, j)] != 0 {
                m[(k, nvars)] = zp::sub(m[(k, nvars)], zp::mul(m[(i, nvars)], m[(k, j)], p), p);
                #[cfg(debug_assertions)]
                {
                    m[(k, j)] = 0;
                }
            }
        }
        if i == 0 {
            break;
        }
        i -= 1;
    }

    // Return the solution.
    Ok(Array1::<ufield>::from_iter(
        (0..nvars).map(|i| m[(i, nvars)]),
    ))
}

#[test]
fn test_solve() {
    use ndarray::{arr1, arr2};
    let a: Array2<ufield> = arr2(&[[1, 1, 2], [3, 4, 3], [16, 5, 5]]);
    let b: Array1<ufield> = arr1(&[3, 15, 8]);
    let p: ufield = 17;
    let r = solve(&a, &b, p).unwrap();
    assert_eq!(r, arr1(&[2, 3, 16]));
}

#[test]
#[should_panic]
fn test_solve_bad_shape() {
    use ndarray::{arr1, arr2};
    let a: Array2<ufield> = arr2(&[[1, 1, 2], [3, 4, 3], [16, 5, 5]]);
    let b: Array1<ufield> = arr1(&[3, 15, 8, 1]);
    let p: ufield = 17;
    let _ = solve(&a, &b, p);
}

#[test]
fn test_solve_underdetermined1() {
    use ndarray::{arr1, arr2};
    let a: Array2<ufield> = arr2(&[[1, 1, 2], [3, 4, 3]]);
    let b: Array1<ufield> = arr1(&[3, 15]);
    let p: ufield = 17;
    let r = solve(&a, &b, p);
    assert_eq!(
        r,
        Err(LinearSolverError::Underdetermined {
            min_rank: 0,
            max_rank: 2
        })
    );
}

#[test]
fn test_solve_underdetermined2() {
    use ndarray::{arr1, arr2};
    let a: Array2<ufield> = arr2(&[[1, 1, 1, 1], [0, 0, 1, 1], [0, 0, 0, 1], [0, 0, 0, 2]]);
    let b: Array1<ufield> = arr1(&[1, 15, 1, 2]);
    let p: ufield = 17;
    let r = solve(&a, &b, p);
    assert_eq!(
        r,
        Err(LinearSolverError::Underdetermined {
            min_rank: 1,
            max_rank: 3
        })
    );
}

#[test]
fn test_solve_underdetermined3() {
    use ndarray::{arr1, arr2};
    let a: Array2<ufield> = arr2(&[[1, 1, 2], [3, 4, 3], [10, 7, 12]]);
    let b: Array1<ufield> = arr1(&[3, 15, 12]);
    let p: ufield = 17;
    let r = solve(&a, &b, p);
    assert_eq!(
        r,
        Err(LinearSolverError::Underdetermined {
            min_rank: 2,
            max_rank: 2
        })
    );
}

#[test]
fn test_solve_overdetermined() {
    use ndarray::{arr1, arr2};
    let a: Array2<ufield> = arr2(&[[1, 1, 2], [3, 4, 3], [9, 0, 11], [1, 1, 7], [2, 3, 8]]);
    let b: Array1<ufield> = arr1(&[3, 15, 7, 6, 6]);
    let p: ufield = 17;
    let r = solve(&a, &b, p).unwrap();
    assert_eq!(r, arr1(&[11, 1, 4]));
}

#[test]
fn test_solve_inconsistent() {
    use ndarray::{arr1, arr2};
    let a: Array2<ufield> = arr2(&[[1, 1, 2], [3, 4, 3], [16, 5, 5], [14, 2, 4]]);
    let b: Array1<ufield> = arr1(&[3, 15, 8, 3]);
    let p: ufield = 17;
    let r = solve(&a, &b, p);
    assert_eq!(r, Err(LinearSolverError::Inconsistent));
}
