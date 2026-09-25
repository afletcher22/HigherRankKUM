"""Run hit_sat14's formula with an alternative solver (argv[1] in glucose, maple, lingeling)."""
import sys, time
from pysat.solvers import Glucose4, MapleChrono, Lingeling
from hit_sat14 import build
S = {"glucose": Glucose4, "maple": MapleChrono, "lingeling": Lingeling}[sys.argv[1]]
t = time.time()
cls, ids = build((3, 6, 9))
s = S(bootstrap_with=cls)
res = s.solve()
print(sys.argv[1], "SAT (no deletable basis exists)" if res else "UNSAT (hitting lemma holds at n=14)", f"{time.time()-t:.0f}s", flush=True)
