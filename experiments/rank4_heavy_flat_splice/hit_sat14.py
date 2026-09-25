"""SAT check of the unified hitting lemma at n=14 (k=3), representation-free.

Claim: every strict t=0 rank-4 matroid on 14 elements (points <= 3, lines <= 6, planes <= 9) has a
basis B with M-B uniformly dense (10 elements at ratio 5/2: points <= 2, lines <= 5, planes <= 7).
Encoding: full rank function on all 2^14 subsets with the rank axioms and the caps; for every 4-set
B one clause "B is not a basis, or some 3-set of E-B has rank 1, or some 6-set of E-B has rank
<= 2, or some 8-set of E-B has rank <= 3".  UNSAT proves the claim.

Options: 'nostrict' drops the t=0 caps down to plain uniform density (points <= 3, lines <= 7,
planes <= 10) as a control (the t>0 / tight cases may then fail).
"""
import itertools, sys, time
from pysat.solvers import Cadical153
from cyclic_sat import axioms_on

N = 14


def build(caps=(3, 6, 9)):
    ids = {}

    def var(X, v):
        key = (X, v)
        if key not in ids:
            ids[key] = len(ids) + 1
        return ids[key]

    cls, done = set(), set()
    axioms_on(list(range(N)), var, cls, done)
    cls.add((var((1 << N) - 1, 4),))
    for x in range(N):
        cls.add((var(1 << x, 1),))                  # no loops (uniform density)
    for j, cap in enumerate(caps, start=1):
        for c in itertools.combinations(range(N), cap + 1):
            cls.add((var(sum(1 << x for x in c), j + 1),))
    m = lambda c: sum(1 << x for x in c)
    for B in itertools.combinations(range(N), 4):
        rest = [x for x in range(N) if x not in B]
        c = [-var(m(B), 4)]
        c += [-var(m(X), 2) for X in itertools.combinations(rest, 3)]
        c += [-var(m(X), 3) for X in itertools.combinations(rest, 6)]
        c += [-var(m(X), 4) for X in itertools.combinations(rest, 8)]
        cls.add(tuple(c))
    return [list(c) for c in cls], ids


if __name__ == "__main__":
    caps = (3, 7, 10) if "nostrict" in sys.argv else (3, 6, 9)
    t = time.time()
    cls, ids = build(caps)
    print(f"caps={caps}: {len(ids)} vars, {len(cls)} clauses (built {time.time()-t:.0f}s)", flush=True)
    s = Cadical153(bootstrap_with=cls)
    res = s.solve()
    print(f"   -> {'SAT: a matroid with NO deletable basis exists' if res else 'UNSAT: every such matroid has a deletable basis'} "
          f"({time.time()-t:.0f}s)", flush=True)
    if res:
        mdl = set(l for l in s.get_model() if l > 0)
        r = lambda c: sum(1 for v in range(1, 5) if ids.get((sum(1 << x for x in c), v)) in mdl)
        for j, name in ((1, "points"), (2, "lines"), (3, "planes")):
            fl = {}
            for size in range(2, 11):
                for c in itertools.combinations(range(N), size):
                    if r(c) == j:
                        cl = frozenset(x for x in range(N) if r(c + (x,)) == j) if True else None
                        fl[cl] = 1
            big = sorted((len(F), sorted(F)) for F in fl)[-6:]
            print(name, big)
