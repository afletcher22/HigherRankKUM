"""Local theory of (2, 2)-splits of 4-blocks in a twisted chain.

W, W' are bases of a rank-4 matroid N.  A split of W is a 2-subset Q (the trailing pair); the
transition relation is
    T(Q, Q') = 1  iff  Q u (W' - Q') is a basis of N.
A cyclic sequence of such relations closes iff the product has a nonzero diagonal entry.

For N represented by an invertible matrix A (columns of W' in the basis W) this is the support
of a 2-compound.  The script collects the relations coming from GL_4(F_q), classifies them up to
relabelling W and W' (S_4 x S_4), generates the semigroup of products and lists

  * the classes that meet every permutation of the six states ("Hall slack");
  * for each class the set of bijections pi : W -> W' met by T (Pi(T));
  * the classes that occur in some product with zero diagonal ("non-absorbing").

Usage: python pairsplit_local.py q [sample] [seed]      (q = 2 enumerates all of GL_4(2))
"""
import itertools, random, sys, time
import numpy as np

PAIRS = list(itertools.combinations(range(4), 2))
PIDX = {p: i for i, p in enumerate(PAIRS)}
S4 = list(itertools.permutations(range(4)))
IND = np.array([[PIDX[tuple(sorted((pi[a], pi[b])))] for (a, b) in PAIRS] for pi in S4])  # (24, 6)
S6 = np.array(list(itertools.permutations(range(6))))                                      # (720, 6)

# column permutation tables on 6-bit row masks: bit j of the mask moves to bit IND[p][j]
COLPERM = np.zeros((24, 64), dtype=np.uint8)
for p in range(24):
    for m in range(64):
        COLPERM[p, m] = sum(1 << int(IND[p][j]) for j in range(6) if m >> j & 1)
SHIFT = (np.arange(6, dtype=np.uint64) * np.uint64(6))


def pack(rows):                       # (..., 6) uint8 row masks -> uint64
    return (rows.astype(np.uint64) << SHIFT).sum(axis=-1, dtype=np.uint64)


def unpack(keys):                     # uint64 -> (n, 6) uint8
    keys = np.asarray(keys, dtype=np.uint64)
    return ((keys[:, None] >> SHIFT) & np.uint64(63)).astype(np.uint8)


def canon(keys):
    """Canonical representative under relabelling rows and columns by S_4."""
    rows = unpack(keys)
    best = np.full(len(rows), np.iinfo(np.uint64).max, dtype=np.uint64)
    for p1 in range(24):
        # row i of the new relation is old row with IND[p1][old] = i
        inv = np.argsort(IND[p1])
        r1 = rows[:, inv]
        for p2 in range(24):
            best = np.minimum(best, pack(COLPERM[p2][r1]))
    return best


def compose(rowsP, rowsG):
    """(n, 6) x (m, 6) row-mask relations -> (n, m, 6) row masks of P.G"""
    tab = np.zeros((len(rowsG), 64), dtype=np.uint8)
    for j in range(6):
        bit = (np.arange(64) >> j & 1).astype(bool)
        tab[:, bit] |= rowsG[:, j][:, None]
    return tab[:, rowsP].transpose(1, 0, 2)


def meets(rows, perms):
    """rows (n, 6) masks, perms (k, 6): matrix (n, k) of 'relation meets the permutation'."""
    out = np.zeros((len(rows), len(perms)), dtype=bool)
    for i in range(6):
        out |= (rows[:, i][:, None] >> perms[:, i][None, :].astype(np.uint8) & 1).astype(bool)
    return out


def det2(a, b, c, d, q):
    return (a * d - b * c) % q


def relation(A, q):
    """A: 4x4 list of lists over F_q (prime q), invertible.  Row masks of T."""
    rows = []
    for Q in PAIRS:
        rQ = [i for i in range(4) if i not in Q]
        m = 0
        for j, Qp in enumerate(PAIRS):
            cP = [i for i in range(4) if i not in Qp]
            if det2(A[rQ[0]][cP[0]], A[rQ[0]][cP[1]], A[rQ[1]][cP[0]], A[rQ[1]][cP[1]], q):
                m |= 1 << j
        rows.append(m)
    return rows


def det4(A, q):
    M = [r[:] for r in A]; d = 1
    for c in range(4):
        piv = next((r for r in range(c, 4) if M[r][c] % q), None)
        if piv is None: return 0
        if piv != c: M[c], M[piv] = M[piv], M[c]; d = -d
        d = d * M[c][c] % q
        inv = pow(M[c][c], q - 2, q)
        for r in range(c + 1, 4):
            f = M[r][c] * inv % q
            if f: M[r] = [(x - f * y) % q for x, y in zip(M[r], M[c])]
    return d % q


def generators(q, sample, rng):
    """All relations from GL_4(F_q): exhaustive for q <= 3, otherwise `sample` random matrices
    (entries zero with a random probability, so that sparse matrices are well represented)."""
    rp = PAIRS
    comp = {p: tuple(i for i in range(4) if i not in p) for p in PAIRS}
    seen = set()
    total = q ** 16
    exhaustive = total <= 50_000_000
    chunk = 400_000
    npr = np.random.default_rng(rng.randrange(1 << 30))
    done = 0
    while done < (total if exhaustive else sample):
        if exhaustive:
            idx = np.arange(done, min(done + chunk, total), dtype=np.int64)
            a = [(idx // q ** e % q).astype(np.int16) for e in range(16)]
        else:
            dens = npr.random((chunk, 1))
            vals = npr.integers(1, q, size=(chunk, 16))
            vals[npr.random((chunk, 16)) < dens] = 0
            a = [vals[:, e].astype(np.int16) for e in range(16)]
        done += chunk
        A = lambda r, c: a[4 * r + c]
        minor = {(R, C): (A(R[0], C[0]) * A(R[1], C[1]) - A(R[0], C[1]) * A(R[1], C[0])) % q
                 for R in rp for C in rp}
        det = sum((-1) ** (1 + C[0] + C[1]) * minor[((0, 1), C)].astype(np.int64) * minor[((2, 3), comp[C])]
                  for C in rp) % q
        key = np.zeros(len(a[0]), dtype=np.uint64)
        for i, Q in enumerate(PAIRS):
            for j, Qp in enumerate(PAIRS):
                key |= (minor[(comp[Q], comp[Qp])] != 0).astype(np.uint64) << np.uint64(6 * i + j)
        seen.update(np.unique(key[det != 0]).tolist())
    return np.array(sorted(seen), dtype=np.uint64)


def describe(key):
    rows = unpack([key])[0]
    return " ".join(format(int(r), "06b")[::-1] for r in rows)


def main():
    q = int(sys.argv[1]); sample = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    rng = random.Random(int(sys.argv[3]) if len(sys.argv) > 3 else 1)
    t0 = time.time()
    gens_all = generators(q, sample, rng)
    gens = np.unique(canon(gens_all))
    print("F_%d: %d distinct relations, %d classes up to S_4 x S_4  [%.0fs]" % (
        q, len(gens_all), len(gens), time.time() - t0), flush=True)
    grow = unpack(gens)
    hall = meets(grow, S6).all(axis=1)
    hasperm = np.array([any(all(r[i] >> s[i] & 1 for i in range(6)) for s in S6) for r in grow])
    pi_cnt = meets(grow, IND).sum(axis=1)
    ones = np.array([sum(bin(int(x)).count("1") for x in r) for r in grow])
    print("classes containing a permutation of the six states: %d of %d" % (hasperm.sum(), len(gens)))
    print("Hall-slack classes (meet every permutation of the six states): %d" % hall.sum())
    print("classes meeting all 24 bijections W -> W': %d" % (pi_cnt == 24).sum())

    # semigroup of products, canonical representatives
    S = set(int(x) for x in gens)
    frontier = gens
    # generators with a relabelling in the middle: P . pi . g
    gmid = np.concatenate([grow[:, np.argsort(IND[p])] for p in range(24)])
    rnd = 0
    while len(frontier):
        rnd += 1
        new = set()
        for lo in range(0, len(frontier), 256):
            prod = compose(unpack(frontier[lo:lo + 256]), gmid).reshape(-1, 6)
            keys = np.unique(pack(prod))
            for c in np.unique(canon(keys)):
                c = int(c)
                if c not in S: new.add(c)
        S |= new
        frontier = np.array(sorted(new), dtype=np.uint64)
        print("round %d: semigroup has %d classes (+%d)  [%.0fs]" % (rnd, len(S), len(new), time.time() - t0),
              flush=True)
    Sarr = np.array(sorted(S), dtype=np.uint64)
    Srow = unpack(Sarr)
    bad = ~meets(Srow, IND).all(axis=1)
    print("product classes with a zero-diagonal labelling: %d of %d" % (bad.sum(), len(Sarr)))

    # non-absorbing generators: g . pi . P misses some bijection, for some product P (or P empty)
    nonabs = (pi_cnt < 24).copy()
    Smid = np.concatenate([Srow[:, np.argsort(IND[p])] for p in range(24)])
    for gi in range(len(gens)):
        if nonabs[gi]: continue
        for lo in range(0, len(Smid), 4096):
            prod = compose(grow[gi:gi + 1], Smid[lo:lo + 4096]).reshape(-1, 6)
            if not meets(prod, IND).all():
                nonabs[gi] = True; break
    print("non-absorbing generator classes: %d of %d  [%.0fs]" % (nonabs.sum(), len(gens), time.time() - t0))
    print("\nclass  ones  Pi  hall  absorbing   rows (pairs 01 02 03 12 13 23)")
    for i in np.argsort(ones):
        print("%4d  %4d  %2d  %4s  %9s   %s" % (i, ones[i], pi_cnt[i], "yes" if hall[i] else "no",
                                               "no" if nonabs[i] else "yes", describe(gens[i])))
    print("Hall slack but non-absorbing: %d;  absorbing but not Hall slack: %d" % (
        (hall & nonabs).sum(), (~hall & ~nonabs).sum()))


if __name__ == "__main__":
    main()
