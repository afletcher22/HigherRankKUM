"""Exact GL(4,2) orbit classification of binary multisets via invariants + orbit-stabilizer."""
import itertools, json, time, sys
import numpy as np
from bin_class import PTS, LINES, PLANES, multisets
from kum import gf2_rank

def gl_perms():
    perms=[]
    for cols in itertools.permutations(PTS,4):
        if gf2_rank(list(cols))!=4: continue
        img=[]
        for v in PTS:
            out=0
            for i in range(4):
                if (v>>i)&1: out^=cols[i]
            img.append(out)
        perms.append([PTS.index(x) for x in img])
    return np.array(perms,dtype=np.int8)

GLP=None
def invariant(cnt):
    c=[cnt.get(p,0) for p in PTS]
    ls=tuple(sorted(tuple(sorted(c[PTS.index(x)] for x in L)) for L in LINES))
    ps=tuple(sorted(tuple(sorted(c[PTS.index(x)] for x in P)) for P in PLANES))
    return (tuple(sorted(c)),ls,ps)

def classify(n,k,t0=True):
    global GLP
    if GLP is None: GLP=gl_perms()
    ms=multisets(n,k,t0)
    buckets={}
    for cnt in ms:
        buckets.setdefault(invariant(cnt),[]).append(cnt)
    reps=[]
    ok=True
    for key,lst in buckets.items():
        cnt=lst[0]
        c=np.array([cnt.get(p,0) for p in PTS],dtype=np.int8)
        imgs=c[GLP]            # images under all group elements (as count vectors permuted)
        orbit={tuple(r) for r in imgs}
        if len(orbit)!=len(lst):
            ok=False
        reps.append(dict(counts=[int(x) for x in c],orbit=len(orbit),bucket=len(lst)))
    return ms,reps,ok

if __name__=="__main__":
    n,k=int(sys.argv[1]),int(sys.argv[2])
    t=time.time()
    ms,reps,ok=classify(n,k)
    print(f"n={n}: patterns={len(ms)} buckets={len(reps)} buckets==orbits:{ok} ({time.time()-t:.1f}s)")
    json.dump(reps,open(f"orbits_n{n}_t0.json","w"))
    for r in reps: print(r)
