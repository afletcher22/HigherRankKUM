"""Extra certification runs for cyclic_sat.py: N=10 with the full rank function; N=12 block with
Glucose4 and MapleChrono."""
import time
from pysat.solvers import Glucose4, MapleChrono
from cyclic_sat import build, solve
cls, ids, _ = build(12, "block", 6)
for name, Sv in (("Glucose4", Glucose4), ("MapleChrono", MapleChrono)):
    t = time.time()
    print(f"N=12 block {name}: {'SAT' if Sv(bootstrap_with=cls).solve() else 'UNSAT'} ({time.time()-t:.0f}s)", flush=True)
solve(10, "full")
