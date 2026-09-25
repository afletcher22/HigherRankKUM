"""Controls for local_sat.py.
1. Threshold: Claim(L) for L = 11..14 (L=13 must be SAT: binary survivors exist).
2. Second solver (Glucose4, MapleChrono) on L=14.
3. Real-matroid consistency: plug the rank function of a binary length-13 survivor (and of random
   binary length-14 sequences) into the L=13 / L=14 encodings as assumptions.  The survivor must
   be SAT (a genuine counter-model); every length-14 real sequence must be UNSAT under its ranks
   only because of an interleaving clause, i.e. the axiom part alone must be SAT under them."""
import sys, random, itertools, time
sys.path.insert(0, "bsi")
from pysat.solvers import Cadical153, Glucose4, MapleChrono
from local_sat import build, solve
from block_bin import rank, PTS
from ext_local_bin import survivors

for L in (11, 12, 13):
    solve(L, 6)
cls, ids, nint = build(14, 6)
for name, Sv in (("Glucose4", Glucose4), ("MapleChrono", MapleChrono)):
    t = time.time()
    s = Sv(bootstrap_with=cls)
    print(f"L=14 {name}: {'SAT' if s.solve() else 'UNSAT'} ({time.time()-t:.0f}s)", flush=True)

def assumptions(ids, vals):
    """vals: list of GF(2)^4 values for elements 0..(4+L-1)."""
    asm = []
    for (X, v), vid in ids.items():
        els = [i for i in range(len(vals)) if X >> i & 1]
        r = rank(tuple(sorted(vals[i] for i in els)))
        asm.append(vid if r >= v else -vid)
    return asm

cnt, level = survivors(13)
Y13 = list(level[0][0])
cls13, ids13, _ = build(13, 6)
s = Cadical153(bootstrap_with=cls13)
print("survivor", Y13, "consistent with L=13 encoding (must be True):",
      s.solve(assumptions=assumptions(ids13, [1, 2, 4, 8] + Y13)), flush=True)
# axiom part only, for L=14, with real binary sequences
ax_cls = [c for c in cls if not all(l < 0 for l in c) or len(c) == 1]
rng = random.Random(2)
okc = 0
for _ in range(20):
    Y = [rng.choice(PTS)]
    while len(Y) < 14:
        c = [v for v in PTS if rank(tuple(sorted(Y[-3:] + [v]))) == len(Y[-3:]) + 1]
        Y.append(rng.choice(c))
    s2 = Cadical153(bootstrap_with=[c for c in cls if len(c) <= 5 and any(l > 0 for l in c)] + [c for c in cls if len(c) == 1])
    okc += s2.solve(assumptions=assumptions(ids, [1, 2, 4, 8] + Y))
print("real length-14 binary sequences satisfying the axiom+window clauses (must be 20):", okc)
