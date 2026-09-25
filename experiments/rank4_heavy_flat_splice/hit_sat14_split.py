"""hit_sat14 split by the heavy flat that Lemma H does not cover (k=3, n=14):
  plane : elements 0..8 form a 9-plane (rank 3);
  line  : elements 0..5 form a 6-line (rank 2), and no 9-plane.
Together with Lemma H (no 9-plane, no 6-line) this covers every strict t=0 matroid on 14
elements.  UNSAT in both cases proves the hitting lemma at n=14."""
import sys, time, itertools
from pysat.solvers import Cadical153, Glucose4
from hit_sat14 import build

def run(case, solver="cadical"):
    t = time.time()
    cls, ids = build((3, 6, 9))
    v = lambda X, r: ids[(X, r)]
    if case == "plane":
        X = (1 << 9) - 1
        cls += [[v(X, 3)], [-v(X, 4)]]
    else:
        X = (1 << 6) - 1
        cls += [[v(X, 2)], [-v(X, 3)]]
        for c in itertools.combinations(range(14), 9):
            cls.append([v(sum(1 << x for x in c), 4)])
    S = Cadical153 if solver == "cadical" else Glucose4
    s = S(bootstrap_with=cls)
    res = s.solve()
    print(case, solver, "SAT (no deletable basis)" if res else "UNSAT (hitting holds)", f"{time.time()-t:.0f}s", flush=True)
    return res, s, ids

if __name__ == "__main__":
    run(sys.argv[1], sys.argv[2] if len(sys.argv) > 2 else "cadical")
