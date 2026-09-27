"""Controls for check_lemmas.py: the base hypotheses are satisfiable, and single cover splits
do not suffice (so the checks are not vacuous)."""
import check_lemmas as C
from pysat.solvers import Cadical195
s = Cadical195(bootstrap_with=C.cls + C.base)
print("base hypotheses satisfiable:", s.solve())
u, v, w, z, a, ab, b, bb = range(8)
for P, Q in (((u, w), (v, z)), ((u, z), (v, w))):
    g = C.new()
    extra = C.crossed_clauses(P, Q, g) + [[-C.basis(C.A0 + P), -C.basis(Q + C.A1), g]]
    print(f"split {P}|{Q} alone can be bad (SAT expected):", Cadical195(bootstrap_with=C.cls + C.base + extra).solve())
# each of the three 'bad' disjuncts of C1 is realizable
for lab, ex in (("w in H", [[C.H(w)]]), ("b in cl(v,z)", [[C.incl(b, (v, z))]]),
                ("w in Hbar and bb in cl(u,z)", [[C.Hb(w)], [C.incl(bb, (u, z))]])):
    print(f"  realizable: {lab}:", Cadical195(bootstrap_with=C.cls + C.base + ex).solve())
