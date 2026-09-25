"""Discriminating control for the hitting-lemma SAT encoding (hit_sat14.py), at n=4k+2 with
k=2 (n=10), where deletable bases are known to fail (five doubled points).  Same construction
as hit_sat14.build, parametrised by k: rank axioms, no loops, strict t=0 caps (k, 2k, 3k), and one
clause per 4-set B saying B is not a basis or M-B violates density (a k-set of rank 1, a 2k-set
of rank <= 2, or a (3k-1)-set of rank <= 3 inside E-B).  The answer must be SAT, and the model is
re-verified independently: full submodularity, uniform density, strictness, and a direct scan of
all 4-sets for a deletable basis."""
import itertools, time
from pysat.solvers import Cadical153
from cyclic_sat import axioms_on

def build(k):
    N = 4 * k + 2
    ids = {}
    def var(X, v):
        if (X, v) not in ids:
            ids[(X, v)] = len(ids) + 1
        return ids[(X, v)]
    cls, done = set(), set()
    axioms_on(list(range(N)), var, cls, done)
    cls.add((var((1 << N) - 1, 4),))
    for x in range(N):
        cls.add((var(1 << x, 1),))
    for j, cap in enumerate((k, 2 * k, 3 * k), start=1):
        for c in itertools.combinations(range(N), cap + 1):
            cls.add((var(sum(1 << x for x in c), j + 1),))
    m = lambda c: sum(1 << x for x in c)
    for B in itertools.combinations(range(N), 4):
        rest = [x for x in range(N) if x not in B]
        c = [-var(m(B), 4)]
        c += [-var(m(X), 2) for X in itertools.combinations(rest, k)]
        c += [-var(m(X), 3) for X in itertools.combinations(rest, 2 * k)]
        c += [-var(m(X), 4) for X in itertools.combinations(rest, 3 * k - 1)]
        cls.add(tuple(c))
    return [list(c) for c in cls], ids, N

if __name__ == "__main__":
    k = 2
    t = time.time()
    cls, ids, N = build(k)
    s = Cadical153(bootstrap_with=cls)
    res = s.solve()
    print(f"k={k} n={N}: {'SAT' if res else 'UNSAT'} ({time.time()-t:.0f}s)", flush=True)
    if res:
        mdl = set(l for l in s.get_model() if l > 0)
        R = [sum(1 for v in range(1, 5) if ids[(X, v)] in mdl) for X in range(1 << N)]
        pc = lambda X: bin(X).count("1")
        sub = all(R[X] + R[Y] >= R[X | Y] + R[X & Y] for X in range(1 << N) for Y in range(1 << N))
        dense = all(4 * pc(X) <= N * R[X] for X in range(1 << N))
        full = (1 << N) - 1
        strict = all(4 * pc(X) < N * R[X] for X in range(1, full))
        dele = 0
        for B in itertools.combinations(range(N), 4):
            Bm = sum(1 << b for b in B)
            if R[Bm] == 4 and all(4 * pc(X) <= (N - 4) * R[X] for X in range(1 << N) if X & Bm == 0):
                dele += 1
        pts = sorted({frozenset(y for y in range(N) if R[(1 << x) | (1 << y)] == 1) for x in range(N)}, key=len)
        print("full submodularity:", sub, "| uniformly dense:", dense, "| strict:", strict,
              "| deletable bases:", dele, "| point sizes:", sorted(len(p) for p in pts), flush=True)
