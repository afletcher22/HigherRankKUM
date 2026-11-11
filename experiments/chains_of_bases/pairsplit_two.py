"""Two bases: the constrained symmetric exchange behind the pair split.

B_0 = unit vectors, B_1 = columns of an invertible r x r matrix A, x_0 = row 0, x_1 = column 0.
A split of size c of the other r - 1 elements closes iff there are c-subsets Q of rows 1..r-1 and
Q' of columns 1..r-1 with  det A[Q, Q'] != 0  and  det A[Q^c, Q'^c] != 0.

Identity: sum over Q' of A[Q, Q'] * Ainv[Q', Q] = 1 - sum_{i in Q} A[i, 0] * Ainv[0, i], so the
split closes unless A[i, 0] * Ainv[0, i] = 1 / c for every i >= 1 (impossible when the
characteristic divides c).  This script looks for failures by sampling sparse matrices over F_q.

Usage: python pairsplit_two.py q r c samples seed
"""
import itertools, sys
import numpy as np


def det_mod(M, q):
    """Determinants of a stack of square matrices (n, m, m) over F_q (q prime), by elimination."""
    M = M.copy() % q; n, m, _ = M.shape
    det = np.ones(n, dtype=np.int64)
    inv = np.array([0] + [pow(a, q - 2, q) for a in range(1, q)], dtype=np.int64)
    idx = np.arange(n)
    for c in range(m):
        piv = np.argmax(M[:, c:, c] != 0, axis=1) + c
        has = M[idx, piv, c] != 0
        det[~has] = 0
        swap = piv != c
        tmp = M[idx, piv].copy(); M[idx, piv] = M[:, c]; M[:, c] = tmp
        det = np.where(swap, -det, det) * M[:, c, c] % q
        f = M[:, c + 1:, c] * inv[M[:, c, c]][:, None] % q
        M[:, c + 1:] = (M[:, c + 1:] - f[:, :, None] * M[:, c][:, None, :]) % q
    return det % q


def main(q, r, c, samples, seed):
    rng = np.random.default_rng(seed)
    rows = list(itertools.combinations(range(1, r), c))
    tot = inv_n = valid = fail = fail_valid = 0
    example = None
    while tot < samples:
        n = 100_000; tot += n
        dens = rng.uniform(0.2, 0.8, size=(n, 1, 1))
        A = rng.integers(1, q, size=(n, r, r)); A[rng.random((n, r, r)) > dens] = 0
        A = A[det_mod(A, q) != 0]
        inv_n += len(A)
        ok = np.zeros(len(A), dtype=bool)
        for Q in rows:
            Qc = [i for i in range(r) if i not in Q]
            for Qp in rows:
                Qpc = [i for i in range(r) if i not in Qp]
                ok |= (det_mod(A[:, Q][:, :, Qp], q) != 0) & (det_mod(A[:, Qc][:, :, Qpc], q) != 0)
        rest = list(range(1, r))
        v = (A[:, 0, 0] != 0) & (det_mod(A[:, rest][:, :, rest], q) != 0)
        valid += v.sum(); fail += (~ok).sum(); fail_valid += (~ok & v).sum()
        if example is None and (~ok & v).any(): example = A[~ok & v][0]
    print("F_%d, rank %d, split (1, %d, %d): invertible %d, valid root split %d" % (q, r, c, r - 1 - c, inv_n, valid))
    print("  no split: %d, of which with a valid root split: %d" % (fail, fail_valid))
    if example is not None: print("  example:\n", example)


if __name__ == "__main__":
    main(*map(int, sys.argv[1:]))
