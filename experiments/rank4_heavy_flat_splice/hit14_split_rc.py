"""hit14plane split by r(C), C = {9..13} the complement of the 9-plane {0..8}: writes
certs/hit14plane_rC.cnf for rC in 2, 3, 4 (density forces r(C) >= 2), for lrat_native.py."""
import os, sys
from cert_measure import OUT
from hit_sat14 import build

for rC in map(int, sys.argv[1:]):
    cls, ids = build((3, 6, 9))
    v = lambda X, r: ids[(X, r)]
    K, C = (1 << 9) - 1, ((1 << 14) - 1) ^ ((1 << 9) - 1)
    cls += [[v(K, 3)], [-v(K, 4)], [v(C, rC)]]
    if rC < 4:
        cls.append([-v(C, rC + 1)])
    nv = max(abs(l) for c in cls for l in c)
    with open(os.path.join(OUT, f"hit14plane_r{rC}.cnf"), "w", newline="\n") as f:
        f.write(f"p cnf {nv} {len(cls)}\n")
        for c in cls:
            f.write(" ".join(map(str, c)) + " 0\n")
    print("wrote", rC, len(cls), flush=True)
