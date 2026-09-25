"""Local extension lemma by SAT, for all matroids (representation-free).

Claim(L): let M be a rank-4 matroid containing a basis S = {s0..s3} and a sequence
e_0..e_{L-1} of further elements whose 4-windows (e_i..e_{i+3}) are bases.  Then S can be
interleaved into the interior of the sequence (at least three e's before the first and after the
last S-element) so that every 4-window of the merged sequence is a basis.

Encoding: rank variables (order encoding, var = "r(X) >= v") for every subset X of every block
S + {e_i..e_{i+w-1}}; the matroid rank axioms (normalisation, monotonicity, unit increase, local
submodularity) are imposed inside each block.  This is a RELAXATION of "M is a matroid", so UNSAT
proves Claim(L) for every matroid.  One clause per interior interleaving says that one of its new
windows is not a basis.

Usage: python local_sat.py L [w]
"""
import itertools, sys, time
from pysat.solvers import Cadical153


def build(L, w=6, extra=None):
    ids = {}

    def var(X, v):
        key = (X, v)
        if key not in ids:
            ids[key] = len(ids) + 1
        return ids[key]

    Sm = 0b1111
    E = [4 + i for i in range(L)]
    cls = set()
    pc = lambda X: bin(X).count("1")
    blocks = []
    for i in range(L - w + 1):
        blocks.append([0, 1, 2, 3] + E[i:i + w])
    done = set()
    for B in blocks:
        B = sorted(B)
        subsets = []
        for r in range(len(B) + 1):
            for c in itertools.combinations(B, r):
                subsets.append(sum(1 << x for x in c))
        for X in subsets:
            if X in done:
                continue
            done.add(X)
            for v in range(1, 4):
                cls.add((-var(X, v + 1), var(X, v)))
            for v in range(pc(X) + 1, 5):
                cls.add((-var(X, v),))
        for X in subsets:
            out = [x for x in B if not X >> x & 1]
            for a in out:
                T = X | 1 << a
                for v in range(1, 5):
                    cls.add((-var(X, v), var(T, v)))
                    if v < 4:
                        cls.add((-var(T, v + 1), var(X, v)))
                for b in out:
                    if b <= a:
                        continue
                    U, Xb = T | 1 << b, X | 1 << b
                    for v in range(1, 5):
                        c = [-var(U, v), var(T, v), var(Xb, v), var(X, v)]
                        if v >= 2:
                            c.append(-var(X, v - 1))
                        cls.add(tuple(c))
    cls.add((var(Sm, 4),))
    for i in range(L - 3):
        cls.add((var(sum(1 << e for e in E[i:i + 4]), 4),))
    if extra:
        for c in extra(var, E):
            cls.add(tuple(c))
    # interleavings
    gaps = list(range(3, L - 2))
    nint = 0
    for perm in itertools.permutations(range(4)):
        for gs in itertools.combinations_with_replacement(gaps, 4):
            seq = []
            gi = 0
            for pos in range(L + 1):
                while gi < 4 and gs[gi] == pos:
                    seq.append(perm[gi]); gi += 1
                if pos < L:
                    seq.append(E[pos])
            wins = set()
            for j in range(len(seq) - 3):
                W = seq[j:j + 4]
                if any(x < 4 for x in W):
                    wins.add(sum(1 << x for x in W))
            cls.add(tuple(sorted(-var(W, 4) for W in wins)))
            nint += 1
    return [list(c) for c in cls], ids, nint


def solve(L, w=6, extra=None, verbose=True):
    t = time.time()
    cls, ids, nint = build(L, w, extra)
    if verbose:
        print(f"L={L} w={w}: {len(ids)} vars, {len(cls)} clauses, {nint} interleavings "
              f"(built {time.time()-t:.0f}s)", flush=True)
    s = Cadical153(bootstrap_with=cls)
    res = s.solve()
    if verbose:
        print(f"L={L} w={w}: {'SAT (a relaxed counter-model exists)' if res else 'UNSAT: Claim(L) holds for all matroids'} "
              f"({time.time()-t:.0f}s)", flush=True)
    model = set(l for l in s.get_model() if l > 0) if res else None
    return res, model, ids


if __name__ == "__main__":
    L = int(sys.argv[1])
    w = int(sys.argv[2]) if len(sys.argv) > 2 else 6
    solve(L, w)
