"""Is X'(6) true when M (10 elements, rank 4) is strict with t = 0?

xcyc6 (plain X' on 6 elements) is SAT. Here the local formula of ext_rank_r.py (r = 4, N = 6,
w = 6: the blocks cover all 10 elements, so the rank function is complete) gets extra lower bounds:

  M uniformly dense on 10 elements, M - S uniformly dense on 6 elements, and
  strict t=0 caps: points <= 2, lines <= 4, planes <= 6 (every 5-set has rank >= 3, every
  7-set rank 4);
  'light' adds no 6-plane and no 4-line (every 6-set rank 4, every 4-set rank >= 3).

Usage: python xcyc6_restricted.py [light]
"""
import sys, time
from pysat.solvers import Cadical195
import ext_rank_r as E

light = len(sys.argv) > 1 and sys.argv[1] == "light"
t = time.time()
cls, n = E.build(4, 6, 6, dense=True)
var = lambda X, v: 5 * X + v
pc = lambda X: bin(X).count("1")
low = {5: 3, 7: 4} if not light else {4: 3, 5: 3, 6: 4, 7: 4}
for X in range(1 << 10):
    need = max([v for s, v in low.items() if pc(X) >= s], default=0)
    if need:
        cls.append([var(X, need)])
s = Cadical195(bootstrap_with=cls)
res = s.solve()
print(f"X'(6) with {'light' if light else 'strict t=0'} caps: "
      f"{'SAT (still fails)' if res else 'UNSAT (holds)'} ({time.time() - t:.0f}s)")
if res:
    m = set(l for l in s.get_model() if l > 0)
    r = lambda X: sum(1 for v in range(1, 5) if var(X, v) in m)
    import itertools
    print("non-bases:", [B for B in itertools.combinations(range(10), 4) if r(sum(1 << x for x in B)) < 4])
