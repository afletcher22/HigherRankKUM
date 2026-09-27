"""Base split (P,Q)=((u,v),(w,z)) = ((s0,s1),(s2,s3)) valid; extra base conditions given as
parallelism facts. Report forced 4-sets (basis / non-basis) and per-split forced predicates."""
import sys, itertools
from m8 import *
u, v, w, z = s0, s1, s2, s3
nm = ["u", "v", "w", "z", "a", "ab", "b", "bb"]
def fm(sp):
    return "{" + "".join(nm[x] for x in sp[0]) + "|" + "".join(nm[x] for x in sp[1]) + "}"
f = F()
f.cls += [[Bs(S)], [Bs(A0 + A1)]]
L = {sp: preds(f, *sp) for sp in splits()}
base = ((u, v), (w, z))
f.cls.append([L[base]["valid"]])
mode = sys.argv[1]
if mode in ("Pcross", "oddP"):
    # u||b, v||bb in M/A0 ; u||bb, v||b in M/Q
    f.cls += [[par(A0, u, b)], [par(A0, v, bb)], [par((w, z), u, bb)], [par((w, z), v, b)]]
if mode == "oddP":
    # Q straight-matched: w||a, z||ab in M/P and w||a, z||ab in M/A1
    f.cls += [[par((u, v), w, a)], [par((u, v), z, ab)], [par(A1, w, a)], [par(A1, z, ab)]]
if mode == "Qcross":
    # w||a, z||ab in M/P ; w||ab, z||a in M/A1
    f.cls += [[par((u, v), w, a)], [par((u, v), z, ab)], [par(A1, w, ab)], [par(A1, z, a)]]
extra = [list(map(int, c.split(":"))) for c in sys.argv[2:]]
f.cls += extra
print("consistent:", f.solve()[0])
s = Cadical195(bootstrap_with=f.cls)
fb, fd, free = [], [], []
for q in itertools.combinations(range(8), 4):
    lit = Bs(q)
    if not s.solve(assumptions=[-lit]):
        fb.append(q)
    elif not s.solve(assumptions=[lit]):
        fd.append(q)
    else:
        free.append(q)
g = lambda q: "".join(nm[x] + "." for x in q)[:-1]
print("forced bases:", " ".join(g(q) for q in fb))
print("forced dependent:", " ".join(g(q) for q in fd))
print("free:", " ".join(g(q) for q in free))
for sp in splits():
    d = L[sp]
    out = []
    for key in ["valid", "alpha", "gamma", "beta", "delta", "Pcross", "Qcross", "evenbad", "oddbad"]:
        lit = d[key]
        t = s.solve(assumptions=[d["valid"], lit]) if key != "valid" else s.solve(assumptions=[lit])
        fl = s.solve(assumptions=[d["valid"], -lit]) if key != "valid" else s.solve(assumptions=[-lit])
        out.append(key + ("=?" if t and fl else "=T" if t else "=F" if fl else "=X"))
    print(fm(sp), " ".join(out))
