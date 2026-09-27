"""SAT check of the transported cover theorem (Q-only side), 8 elements.
S = {p1, p2, q1, q2}; A0 = {a, ab}, A1 = {b, bb} with A0 + A1 a basis.
Mirror-crossed split (P, Q): Q = {q, q'} with q in cl(A1 + ab), q' in cl(A1 + a),
a in cl(P + q), ab in cl(P + q').
Hypothesis: ({p1,p2},{q1,q2}) valid and mirror-crossed with (q, q') = (q1, q2).
Claim: ({q2,p2},{q1,p1}) or ({q2,p1},{q1,p2}) is valid and not mirror-crossed."""
import check_lemmas as C
from pysat.solvers import Cadical195
p1, p2, q1, q2, a, ab, b, bb = range(8)
A0, A1 = (a, ab), (b, bb)
Bs, incl, new = C.basis, C.incl, C.new
base = [[Bs((p1, p2, q1, q2))], [Bs(A0 + A1)], [Bs(A0 + (p1, p2))], [Bs((q1, q2) + A1)],
        [incl(q1, A1 + (ab,))], [incl(q2, A1 + (a,))], [incl(a, (p1, p2, q1))], [incl(ab, (p1, p2, q2))]]


def mcross(P, Q, g):
    out, opts = [], []
    for q, qq in (Q, Q[::-1]):
        h = new()
        conds = [incl(q, A1 + (ab,)), incl(qq, A1 + (a,)), incl(a, P + (q,)), incl(ab, P + (qq,))]
        out += [[-h, c] for c in conds] + [[h] + [-c for c in conds]]
        opts.append(h)
    return out + [[-g] + opts] + [[g, -h] for h in opts]


print("base satisfiable:", Cadical195(bootstrap_with=C.cls[:0] + C.cls + base).solve() if False else Cadical195(bootstrap_with=C.cls + base).solve())
bad = []
for P, Q in (((q2, p2), (q1, p1)), ((q2, p1), (q1, p2))):
    g = new()
    bad += mcross(P, Q, g) + [[-Bs(A0 + P), -Bs(Q + A1), g]]
print("mirror cover theorem:", "UNSAT (holds)" if not Cadical195(bootstrap_with=C.cls + base + bad).solve() else "SAT (fails)")
