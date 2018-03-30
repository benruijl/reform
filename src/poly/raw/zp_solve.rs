//! Linear solver in Zp.

use ndarray::{Array1, Array2, ArrayBase, Data, Ix1, Ix2};

use poly::raw::zp;
use poly::raw::zp::UnsignedInteger;

/// Error from linear solver.
#[derive(Debug, Eq, PartialEq)]
pub enum LinearSolverError {
    Underdetermined,
    Inconsistent,
}

/// Solves `a * x = b` in Zp.
pub fn solve<T: UnsignedInteger, S1: Data<Elem = T>, S2: Data<Elem = T>>(
    a: &ArrayBase<S1, Ix2>,
    b: &ArrayBase<S2, Ix1>,
    p: T,
) -> Result<Array1<T>, LinearSolverError> {
    assert!(a.shape()[0] == b.shape()[0]);

    let neqs = a.shape()[0];
    let nvars = a.shape()[1];

    if neqs < nvars {
        return Err(LinearSolverError::Underdetermined);
    }

    // Create the augmented matrix.
    let mut m = Array2::<T>::zeros((neqs, nvars + 1));
    for (i, e) in a.indexed_iter() {
        m[i] = e.clone();
    }
    for (i, e) in b.indexed_iter() {
        m[(i, nvars)] = e.clone();
    }

    // by the Gaussian elimination

    // First, transform the augmented matrix into the row echelon form.
    let mut i = 0;
    for j in 0..nvars {
        if m[(i, j)].is_zero() {
            // Select a non-zero pivot.
            for k in i + 1..neqs {
                if !m[(k, j)].is_zero() {
                    // Swap i-th row and k-th row.
                    for l in j..nvars + 1 {
                        m.swap((i, l), (k, l));
                    }
                    break;
                }
            }
            if m[(i, j)].is_zero() {
                return Err(LinearSolverError::Underdetermined);
            }
        }
        let x = m[(i, j)].clone();
        let inv_x = zp::inv(x, p.clone());
        for k in i + 1..neqs {
            if !m[(k, j)].is_zero() {
                let s = zp::mul(m[(k, j)].clone(), inv_x.clone(), p.clone());
                m[(k, j)] = T::zero();
                for l in j + 1..nvars + 1 {
                    m[(k, l)] = zp::sub(
                        m[(k, l)].clone(),
                        zp::mul(m[(i, l)].clone(), s.clone(), p.clone()),
                        p.clone(),
                    );
                }
            }
        }
        i += 1;
        if i >= neqs {
            break;
        }
    }

    // Check the rank.
    let rank = i;
    if rank < nvars {
        return Err(LinearSolverError::Underdetermined);
    }

    // Check the consistency.
    for k in i..neqs {
        if !m[(k, nvars)].is_zero() {
            return Err(LinearSolverError::Inconsistent);
        }
    }

    // Now, back substitution.
    i -= 1;
    for j in (0..nvars).rev() {
        if m[(i, j)] != T::one() {
            let x = m[(i, j)].clone();
            let inv_x = zp::inv(x, p.clone());
            m[(i, j)] = T::one();
            m[(i, nvars)] = zp::mul(m[(i, nvars)].clone(), inv_x.clone(), p.clone());
        }
        for k in 0..i {
            if !m[(k, j)].is_zero() {
                let s = m[(k, j)].clone();
                m[(k, j)] = T::zero();
                for l in j + 1..nvars + 1 {
                    m[(k, l)] = zp::sub(
                        m[(k, l)].clone(),
                        zp::mul(m[(i, l)].clone(), s.clone(), p.clone()),
                        p.clone(),
                    );
                }
            }
        }
        if i == 0 {
            break;
        }
        i -= 1;
    }

    // Return the solution.
    Ok(Array1::<T>::from_iter(
        (0..nvars).map(|i| m[(i, nvars)].clone()),
    ))
}

#[test]
fn test_solve() {
    use ndarray::{arr1, arr2};
    let a: Array2<u8> = arr2(&[[1, 1, 2], [3, 4, 3], [16, 5, 5]]);
    let b: Array1<u8> = arr1(&[3, 15, 8]);
    let p: u8 = 17;
    let r = solve(&a, &b, p).unwrap();
    assert_eq!(r, arr1(&[2, 3, 16]));
}

#[test]
#[should_panic]
fn test_solve_bad_shape() {
    use ndarray::{arr1, arr2};
    let a: Array2<u8> = arr2(&[[1, 1, 2], [3, 4, 3], [16, 5, 5]]);
    let b: Array1<u8> = arr1(&[3, 15, 8, 1]);
    let p: u8 = 17;
    let _ = solve(&a, &b, p);
}

#[test]
fn test_solve_underdetermined() {
    use ndarray::{arr1, arr2};
    let a: Array2<u8> = arr2(&[[1, 1, 2], [3, 4, 3], [10, 7, 12]]);
    let b: Array1<u8> = arr1(&[3, 15, 12]);
    let p: u8 = 17;
    let r = solve(&a, &b, p);
    assert_eq!(r, Err(LinearSolverError::Underdetermined));
}

#[test]
fn test_solve_overdetermined() {
    use ndarray::{arr1, arr2};
    let a: Array2<u8> = arr2(&[[1, 1, 2], [3, 4, 3], [9, 0, 11], [1, 1, 7], [2, 3, 8]]);
    let b: Array1<u8> = arr1(&[3, 15, 7, 6, 6]);
    let p: u8 = 17;
    let r = solve(&a, &b, p).unwrap();
    assert_eq!(r, arr1(&[11, 1, 4]));
}

#[test]
fn test_solve_inconsistent() {
    use ndarray::{arr1, arr2};
    let a: Array2<u8> = arr2(&[[1, 1, 2], [3, 4, 3], [16, 5, 5], [14, 2, 4]]);
    let b: Array1<u8> = arr1(&[3, 15, 8, 3]);
    let p: u8 = 17;
    let r = solve(&a, &b, p);
    assert_eq!(r, Err(LinearSolverError::Inconsistent));
}
