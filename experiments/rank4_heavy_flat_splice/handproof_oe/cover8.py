import sys, itertools
from m8 import *
kind = sys.argv[1]      # evenbad / oddbad
basecond = sys.argv[2]  # a predicate name required at base, e.g. Pcross, Qcross
f = F()
f.cls += [[Bs(S)], [Bs(A0 + A1)]]
L = {sp: preds(f, *sp) for sp in splits()}
base = ((s0, s1), (s2, s3))
f.cls.append([L[base]["valid"]])
for c in basecond.split(","):
    neg = c.startswith("-")
    c = c.lstrip("-")
    f.cls.append([-L[base][c] if neg else L[base][c]])
print("base consistent:", f.solve()[0])
others = [sp for sp in splits() if sp != base]
for k in range(1, len(others) + 1):
    found = []
    for sub in itertools.combinations(others, k):
        extra = [[-L[sp]["valid"], L[sp][kind]] for sp in sub]
        if not f.solve(extra)[0]:
            found.append(sub)
    if found:
        print(f"minimal covers of size {k}:")
        for sub in found:
            print("  ", [fmt(sp) for sp in sub])
        break
