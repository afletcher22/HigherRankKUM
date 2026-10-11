"""The deletion step at n = 14 (k = 3) without strictness.

Uniform density only (points <= 3, lines <= 7, planes <= 10), split by the non-strict flat present:
  dangerous : elements 0..9 form a 10-plane (rank 3);
  tight     : elements 0..6 form a 7-line (rank 2), and there is no 10-plane.
With the strict t=0 case (Lemma H and Rank4/HitThree.lean) this covers every uniformly dense
rank-4 matroid on 14 elements. UNSAT in a case means: every such matroid has a basis S with
M - S uniformly dense (points <= 2, lines <= 5, planes <= 7 outside S).
Usage: python hit_sat14_nonstrict.py dangerous|tight
"""
import itertools, sys, time
from pysat.solvers import Cadical195
from hit_sat14 import build, N


def run(case):
    t = time.time()
    cls, ids = build((3, 7, 10))
    v = lambda X, r: ids[(X, r)]
    if case == "dangerous":
        X = (1 << 10) - 1
        cls += [[v(X, 3)], [-v(X, 4)]]
    elif case == "tight":
        X = (1 << 7) - 1
        cls += [[v(X, 2)], [-v(X, 3)]]
        for c in itertools.combinations(range(N), 10):
            cls.append([v(sum(1 << x for x in c), 4)])
    else:
        raise SystemExit("case must be dangerous or tight")
    print(f"{case}: {len(ids)} vars, {len(cls)} clauses (built {time.time()-t:.0f}s)", flush=True)
    s = Cadical195(bootstrap_with=cls)
    res = s.solve()
    print(case, "SAT: a matroid with no deletable basis" if res else
          "UNSAT: a deletable basis always exists", f"({time.time()-t:.0f}s)", flush=True)
    if res:
        mdl = set(l for l in s.get_model() if l > 0)
        r = lambda X: sum(1 for w in range(1, 5) if ids.get((X, w)) in mdl)
        for j, name in ((1, "points"), (2, "lines"), (3, "planes")):
            fl = set()
            for size in range(1, 11):
                for c in itertools.combinations(range(N), size):
                    X = sum(1 << x for x in c)
                    if r(X) == j:
                        fl.add(sum(1 << x for x in range(N) if r(X | 1 << x) == j))
            big = sorted(((bin(F).count("1"), [x for x in range(N) if F >> x & 1]) for F in fl),
                         reverse=True)[:8]
            print(name, big, flush=True)
    return res


if __name__ == "__main__":
    run(sys.argv[1])
