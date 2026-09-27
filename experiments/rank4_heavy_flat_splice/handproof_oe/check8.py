import sys, time
from m8 import *
for kind in ["Pcross", "Qcross", "evenbad", "oddbad"]:
    f = F()
    f.cls += [[Bs(S)], [Bs(A0 + A1)]]
    for sp in splits():
        d = preds(f, *sp)
        f.cls.append([-d["valid"], d[kind]])
    t = time.time()
    res, m = f.solve()
    print(kind, "every valid split bad:", "SAT" if res else "UNSAT", f"{time.time()-t:.1f}s")
