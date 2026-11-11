"""Two consecutive bases B, B' of a chain in rank 5 over F_2: which choices (a, b) give a slack
pair-split relation?

B = unit vectors, B' = columns of A in GL_5(2) (all 9,999,360 matrices).  A choice a in B, b in B'
is admissible if B - a + b is a basis (A[a][b] = 1).  Its relation on 2-subsets is
    T(Q, Q') = [det A[{a} + (W - Q), {b} + (W' - Q')] != 0],   W = B - a, W' = B' - b,
and it is slack if for every bijection pi : W -> W' some Q has T(Q, pi Q) = 1.

Prints the histogram of (admissible choices, slack choices) and describes the matrices with no
slack choice at all ("totally tight" pairs of bases).

Usage: python pairsplit_pairs.py
"""
import itertools, time
from collections import Counter
import numpy as np

R = 5
PAIRS5 = list(itertools.combinations(range(R), 2))
TRIPLES = list(itertools.combinations(range(R), 3))
PERMS4 = list(itertools.permutations(range(4)))


def main():
    t0 = time.time()
    hist = Counter(); tt = []
    chunk = 1 << 20
    for lo in range(0, 1 << 25, chunk):
        idx = np.arange(lo, lo + chunk, dtype=np.uint32)
        a = [[(idx >> np.uint32(5 * r + c) & np.uint32(1)).astype(bool) for c in range(R)] for r in range(R)]
        m2 = {(Rw, C): (a[Rw[0]][C[0]] & a[Rw[1]][C[1]]) ^ (a[Rw[0]][C[1]] & a[Rw[1]][C[0]])
              for Rw in PAIRS5 for C in PAIRS5}
        m3 = {}
        for Rw in TRIPLES:
            for C in TRIPLES:
                m3[(Rw, C)] = ((a[Rw[0]][C[0]] & m2[((Rw[1], Rw[2]), (C[1], C[2]))])
                               ^ (a[Rw[0]][C[1]] & m2[((Rw[1], Rw[2]), (C[0], C[2]))])
                               ^ (a[Rw[0]][C[2]] & m2[((Rw[1], Rw[2]), (C[0], C[1]))]))
        det = np.zeros(chunk, dtype=bool)
        for C in PAIRS5:
            Cc = tuple(i for i in range(R) if i not in C)
            det ^= m2[((0, 1), C)] & m3[((2, 3, 4), Cc)]
        nvalid = np.zeros(chunk, dtype=np.uint8); nslack = np.zeros(chunk, dtype=np.uint8)
        for ra in range(R):
            Wr = [i for i in range(R) if i != ra]
            for cb in range(R):
                Wc = [i for i in range(R) if i != cb]
                slack = np.ones(chunk, dtype=bool)
                for pi in PERMS4:
                    hit = np.zeros(chunk, dtype=bool)
                    for Q in itertools.combinations(range(4), 2):
                        rows = tuple(sorted([ra] + [Wr[i] for i in range(4) if i not in Q]))
                        cols = tuple(sorted([cb] + [Wc[pi[i]] for i in range(4) if i not in Q]))
                        hit |= m3[(rows, cols)]
                    slack &= hit
                v = a[ra][cb]
                nvalid += v; nslack += (v & slack)
        keys, counts = np.unique(nvalid[det].astype(np.int32) * 100 + nslack[det], return_counts=True)
        for k, c in zip(keys, counts): hist[(int(k) // 100, int(k) % 100)] += int(c)
        tt.extend(idx[det & (nslack == 0)].tolist())
        if (lo // chunk) % 8 == 7: print("  %d / 32 chunks  [%.0fs]" % (lo // chunk + 1, time.time() - t0), flush=True)
    total = sum(hist.values())
    print("invertible matrices: %d" % total)
    by_slack = Counter()
    for (v, s), c in hist.items(): by_slack[s] += c
    print("number of slack choices -> matrices:", dict(sorted(by_slack.items())))
    print("totally tight (no slack choice): %d" % len(tt))
    # describe the totally tight matrices by weight and by sorted row and column sums
    desc = Counter()
    for code in tt:
        M = [[code >> (5 * r + c) & 1 for c in range(R)] for r in range(R)]
        desc[(sum(map(sum, M)), tuple(sorted(map(sum, M))), tuple(sorted(sum(M[r][c] for r in range(R)) for c in range(R))))] += 1
    for k, c in sorted(desc.items()): print("  weight %d, row sums %s, column sums %s: %d" % (k[0], k[1], k[2], c))
    np.save("pairsplit_pairs_totally_tight.npy", np.array(tt, dtype=np.uint32))


if __name__ == "__main__":
    main()
