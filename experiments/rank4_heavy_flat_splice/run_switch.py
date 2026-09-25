import json, random, time
from collections import Counter
from kum import *
from bin_class import PTS
from gen import instance_with_plane
def rc(M,K): return M.rk([x for x in range(M.n) if not (K>>x)&1])
tot=Counter()
reps=json.load(open("orbits_n10_t0.json"))
for r in reps:
    cols=[]
    for p,c in zip(PTS,r["counts"]): cols+=[p]*c
    M=binary(cols); info=classify(M)
    ranks=[rc(M,K) for K in info["planes3k"]]
    if not ranks: tot["n10 no 3k-plane"]+=1; continue
    tot[("n10", "has r2" if 2 in ranks else "no r2", "has r>=3" if max(ranks)>=3 else "ONLY r2")]+=1
print(dict(tot))
rng=random.Random(11)
for k in (3,4,5):
  for p in (2,3,5):
    c=Counter(); T=time.time()
    for it in range(60 if k<5 else 25):
        inst=instance_with_plane(p,k,rng,mode="line")
        if inst is None: continue
        M,K,info=inst
        ranks=[rc(M,K2) for K2 in info["planes3k"]]
        c[("has r2" if 2 in ranks else "no r2","has r>=3" if max(ranks)>=3 else "ONLY r2")]+=1
        if max(ranks)<3 and c[("has r2","ONLY r2")]<=2: print("   only-r2 example",k,p,M.data,"profile",info["profile"],"#3kplanes",len(ranks))
    print(k,p,dict(c),f"{time.time()-T:.0f}s",flush=True)
