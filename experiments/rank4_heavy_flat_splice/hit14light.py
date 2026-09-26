"""The hitting lemma at k=3 in Lemma H's case, as a SAT claim: every strict t=0 rank-4 matroid on
14 elements with no 9-point plane and no 6-point line (points <= 3, lines <= 5, planes <= 8) has a
deletable basis. One clause per 4-set, as in hit_sat14.py. Writes certs/hit14light.cnf."""
import itertools, os
from cert_measure import OUT
from lean_witness_h import rank_axioms, var, mask, N

LOWL = [0, 1, 1, 1, 2, 2, 3, 3, 3, 4, 4, 4, 4, 4, 4]


def build():
    cls = [c for c, _ in rank_axioms(LOWL)]
    for Bt in itertools.combinations(range(N), 4):
        B = mask(Bt)
        rest = [x for x in range(N) if not B >> x & 1]
        c = [-var(B, 4)]
        c += [-var(mask(Y), 2) for Y in itertools.combinations(rest, 3)]
        c += [-var(mask(Y), 3) for Y in itertools.combinations(rest, 6)]
        c += [-var(mask(Y), 4) for Y in itertools.combinations(rest, 8)]
        cls.append(c)
    return cls


if __name__ == "__main__":
    cls = build()
    with open(os.path.join(OUT, "hit14light.cnf"), "w", newline="\n") as f:
        f.write(f"p cnf {4 * ((1 << N) - 1) + 4} {len(cls)}\n")
        for c in cls:
            f.write(" ".join(map(str, c)) + " 0\n")
    print("hit14light", len(cls), "clauses")
