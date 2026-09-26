"""The choice lemma of Theorem G at k=3 as a SAT claim (representation-free).

Claim: let M be strict t=0 of rank 4 on 14 elements (points <= 3, lines <= 6, planes <= 9) whose
elements 0..8 form a 9-point plane K, partitioned into the bases D1 = {0,1,2}, D2 = {3,4,5},
D3 = {6,7,8} of M|K, and let C = {9..13}. Then some candidate B = Dc + z (c in 1..3, z in C) is a
basis of M with M - B uniformly dense (10 elements at ratio 10/4).

Encoding: rank function on all 2^14 subsets (variable 4X+v for r(X) >= v) with the rank axioms,
no loops, the caps, r(K) = 3 and r(Di) = 3; for each of the 15 candidates one clause "B is not a
basis, or E-B contains a 3-set of rank <= 1, a 6-set of rank <= 2, or an 8-set of rank <= 3".
UNSAT proves the claim. Writes certs/hit14g.cnf.
"""
import itertools, os
from cert_measure import OUT
from lean_witness_h import rank_axioms, var, mask, N

LOWG = [0, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4, 4, 4, 4, 4]          # no loops, points <= 3, lines <= 6, planes <= 9


def build():
    cls = [c for c, _ in rank_axioms(LOWG)]
    K = mask(range(9))
    cls += [[var(K, 3)], [-var(K, 4)]]
    D = [list(range(3 * i, 3 * i + 3)) for i in range(3)]
    for Di in D:
        cls.append([var(mask(Di), 3)])
    for Di in D:
        for z in range(9, 14):
            B = mask(Di + [z])
            rest = [x for x in range(N) if not B >> x & 1]
            c = [-var(B, 4)]
            c += [-var(mask(Y), 2) for Y in itertools.combinations(rest, 3)]
            c += [-var(mask(Y), 3) for Y in itertools.combinations(rest, 6)]
            c += [-var(mask(Y), 4) for Y in itertools.combinations(rest, 8)]
            cls.append(c)
    return cls


if __name__ == "__main__":
    cls = build()
    nv = max(abs(l) for c in cls for l in c)
    with open(os.path.join(OUT, "hit14g.cnf"), "w", newline="\n") as f:
        f.write(f"p cnf {nv} {len(cls)}\n")
        for c in cls:
            f.write(" ".join(map(str, c)) + " 0\n")
    print("hit14g", len(cls), "clauses")
