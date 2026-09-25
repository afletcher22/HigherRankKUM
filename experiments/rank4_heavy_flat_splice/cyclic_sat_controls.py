"""Controls for cyclic_sat.py.
1. N=7 block; N=8 with the FULL rank function (independent, stronger encoding).
2. Solver cross-check (Glucose4, MapleChrono) for N=8..10 block.
3. Real-matroid consistency: the binary t=3 non-extendable n=10 examples must satisfy the N=6
   encoding under their true ranks; random GF(3)/GF(5)/sparse-paving matroids with a CBO of M-S
   must satisfy the axiom+window clauses of the N=8 block encoding under their true ranks."""
import sys, random, itertools, time
sys.path.insert(0, "bsi")
from pysat.solvers import Cadical153, Glucose4, MapleChrono
from cyclic_sat import build, solve
from kum import binary, gfp, sparse_paving, find_cbo, Timeout
from gen import proj_points

solve(7, "block", 6)
solve(8, "full")
for N in (8, 9, 10):
    cls, ids, _ = build(N, "block", 6)
    for name, Sv in (("Glucose4", Glucose4), ("MapleChrono", MapleChrono)):
        t = time.time()
        print(f"N={N} block {name}: {'SAT' if Sv(bootstrap_with=cls).solve() else 'UNSAT'} ({time.time()-t:.0f}s)", flush=True)

def assumptions(ids, rk, elems):
    asm = []
    for (X, v), vid in ids.items():
        r = rk([elems[i] for i in range(len(elems)) if X >> i & 1])
        asm.append(vid if r >= v else -vid)
    return asm

# (a) binary t=3 examples at N=6: full formula must be SAT under true ranks
cls6, ids6, _ = build(6, "block", 6)
s = Cadical153(bootstrap_with=cls6)
for Y in ([1, 6, 8, 3, 4, 10], [3, 8, 6, 1, 10, 4]):
    M = binary([1, 2, 4, 8] + Y)
    print("t=3 example", Y, "consistent with N=6 encoding (must be True):",
          s.solve(assumptions=assumptions(ids6, M.rk, list(range(10)))), flush=True)
# (b) random non-binary: axiom+window part of N=8 must be SAT under true ranks
cls8, ids8, _ = build(8, "block", 6)
ax8 = [c for c in cls8 if not (len(c) > 1 and all(l < 0 for l in c))]
s8 = Cadical153(bootstrap_with=ax8)
rng = random.Random(3)
okc = tot = 0
while tot < 40:
    kind = rng.choice(["gf3", "gf5", "sp"])
    if kind == "sp":
        chs = [tuple(sorted(rng.sample(range(12), 4))) for _ in range(rng.randint(3, 12))]
        # keep a valid sparse paving family: pairwise |C1 & C2| <= 2
        fam = []
        for c in chs:
            if all(len(set(c) & set(d)) <= 2 for d in fam):
                fam.append(c)
        M = sparse_paving(12, fam)
    else:
        p = 3 if kind == "gf3" else 5
        pts = proj_points(p, 4)
        vecs = [rng.choice(pts) for _ in range(12)]
        M = gfp(vecs, p)
    Sb = [B for B in itertools.combinations(range(12), 4) if M.rk(B) == 4]
    if not Sb:
        continue
    S = list(rng.choice(Sb))
    Y = [x for x in range(12) if x not in S]
    try:
        o = find_cbo(M, elems=Y, limit=10 ** 5, rng=rng)
    except Timeout:
        continue
    if not o:
        continue
    tot += 1
    okc += s8.solve(assumptions=assumptions(ids8, M.rk, S + list(o)))
print(f"random matroids with CBO of M-S consistent with N=8 axioms+windows (must be {tot}): {okc}")
