"""SAT sanity checks of the intermediate claims of PROOF.md, Part B (8 elements).

Standing hypotheses (Step 8): B = {a,ab,b,bb} basis, S = {u,v,w,z} basis, (P,Q) = ({u,v},{w,z})
valid and P-crossed with u||b, v||bb in M/A0 and u||bb, v||b in M/Q.
Every claim is checked by asserting its negation together with the hypotheses (UNSAT = claim holds
in every rank-4 matroid on these 8 elements). Controls check that the situations are not vacuous.
"""
from m8 import *
u, v, w, z = s0, s1, s2, s3
f = F()


def cl_in(e, T):
    """literal for: e in cl(T)"""
    T = tuple(T)
    return f.AND([f.OR([-var(mask(T + (e,)), k), var(mask(T), k)]) for k in range(1, 5)])


f.cls += [[Bs(S)], [Bs(A0 + A1)]]
L = {sp: preds(f, *sp) for sp in splits()}
base = ((u, v), (w, z))
f.cls.append([L[base]["valid"]])
f.cls += [[par(A0, u, b)], [par(A0, v, bb)], [par((w, z), u, bb)], [par((w, z), v, b)]]
print("standing hypotheses consistent:", f.solve()[0])
Xw, Xz = ((u, w), (v, z)), ((u, z), (v, w))
Xvw, Xvz = ((v, w), (u, z)), ((v, z), (u, w))
Hb, Hbb = (a, ab, b), (a, ab, bb)


def unsat(name, extra):
    r = f.solve([list(c) for c in extra])[0]
    print(f"  {name}: {'holds (UNSAT)' if not r else 'FAILS (SAT)'}")


Kw = f.AND([L[Xw]["valid"], L[Xw]["Pcross"]])
Kz = f.AND([L[Xz]["valid"], L[Xz]["Pcross"]])
Gw = f.AND([L[Xw]["valid"], -L[Xw]["Pcross"]])
Gz = f.AND([L[Xz]["valid"], -L[Xz]["Pcross"]])
print("Step 9 claims:")
unsat("9.0 Xw valid <-> (w not in Hb and v not in cl(z,b,bb))",
      [[-f.XOR(L[Xw]["valid"], f.OR([cl_in(w, Hb), cl_in(v, (z, b, bb))]))]])
unsat("9.1 not (w in Hb and z in Hb)", [[cl_in(w, Hb)], [cl_in(z, Hb)]])
unsat("9.2 v in cl(w,b,bb) -> v in cl(w,b)", [[cl_in(v, (w, b, bb))], [-cl_in(v, (w, b))]])
unsat("9.2 v in cl(w,b,bb) -> w not in Hb", [[cl_in(v, (w, b, bb))], [cl_in(w, Hb)]])
unsat("9.2 v in cl(w,b,bb) -> w not in Hbb", [[cl_in(v, (w, b, bb))], [cl_in(w, Hbb)]])
unsat("9.2' (twin) v in cl(z,b,bb) -> v in cl(z,b), z not in Hb u Hbb",
      [[cl_in(v, (z, b, bb))], [f.OR([-cl_in(v, (z, b)), cl_in(z, Hb), cl_in(z, Hbb)])]])
unsat("9.3 not (v in cl(w,b,bb) and v in cl(z,b,bb))", [[cl_in(v, (w, b, bb))], [cl_in(v, (z, b, bb))]])
unsat("9.4 Xw or Xz valid", [[-L[Xw]["valid"]], [-L[Xz]["valid"]]])
unsat("9.5 Kw -> w in Hbb", [[Kw], [-cl_in(w, Hbb)]])
unsat("9.5 Kw -> u in cl(z,bb)", [[Kw], [-cl_in(u, (z, bb))]])
unsat("9.5' (twin) Kz -> z in Hbb and u in cl(w,bb)", [[Kz], [f.OR([-cl_in(z, Hbb), -cl_in(u, (w, bb))])]])
unsat("9.6 not (Kw and Kz)", [[Kw], [Kz]])
unsat("9.7 Kw -> Xz valid", [[Kw], [-L[Xz]["valid"]]])
unsat("9.7' (twin) Kz -> Xw valid", [[Kz], [-L[Xw]["valid"]]])
print("Lemma F1 (Xw or Xz is valid and not P-crossed):")
unsat("F1", [[-Gw], [-Gz]])
print("Lemma F2 (a valid one-swap split is not Q-crossed; all four one-swaps):")
for X in (Xw, Xz, Xvw, Xvz):
    unsat(f"F2 {fmt(X)}", [[L[X]["valid"]], [L[X]["Qcross"]]])
print("Main lemma (Step 11; no standing hypotheses): every valid split P- or Q-crossed")
g = F()
g.cls += [[Bs(S)], [Bs(A0 + A1)]]
for sp in splits():
    d = preds(g, *sp)
    g.cls.append([-d["valid"], d["evenbad"]])
print("  ", "impossible (UNSAT)" if not g.solve()[0] else "possible (SAT) - FAILS")
print("Controls (should be SAT: the situations occur):")
for name, ex in [("Xw valid and P-crossed", [[Kw]]), ("Xw invalid", [[-L[Xw]["valid"]]]),
                 ("Xz invalid", [[-L[Xz]["valid"]]]), ("base split also Q-crossed", [[L[base]["Qcross"]]]),
                 ("both Xw, Xz valid", [[L[Xw]["valid"]], [L[Xz]["valid"]]])]:
    print(f"  {name}: {'SAT' if f.solve(ex)[0] else 'UNSAT'}")
