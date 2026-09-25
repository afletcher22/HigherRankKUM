import json, sys, random, time
from collections import Counter
from kum import *
from gtest import rank3_cbos, extend_tau_any
from bin_class import PTS
from gen import instance_with_plane
def study(M,K,tau_cap=None,rng=None):
    Kl=bits(K); C=[x for x in range(M.n) if not (K>>x)&1]
    rC=M.rk(C)
    taus=rank3_cbos(M,Kl,cap=tau_cap,rng=rng)
    ok=0; to=0
    for t in taus:
        try:
            if extend_tau_any(M,list(t),C,limit=3*10**6) is not None: ok+=1
        except Timeout: to+=1
    return rC,len(taus),ok,to
tot=Counter()
reps=json.load(open("orbits_n10_t0.json"))
for i,r in enumerate(reps):
    cols=[]
    for p,c in zip(PTS,r["counts"]): cols+=[p]*c
    M=binary(cols); info=classify(M)
    for K in info["planes3k"]:
        rC,nt,ok,to=study(M,K)
        tot[("n10",rC,"some" if ok else "NONE","all" if ok==nt else "notall")]+=1
print(dict(tot))
rng=random.Random(7)
for k in (3,4):
  for p in (2,3,5):
    T=time.time(); c=Counter()
    for it in range(25 if k==3 else 12):
        inst=instance_with_plane(p,k,rng)
        if inst is None: continue
        M,K,info=inst
        rC,nt,ok,to=study(M,K,tau_cap=(None if k==3 else 40),rng=rng)
        c[(rC,"some" if ok else ("TO" if to else "NONE"),"all" if ok==nt else "notall")]+=1
        if ok==0 and not to: print("  NONE-EXT",k,p,M.data,"rC",rC)
    print(k,p,dict(c),f"{time.time()-T:.0f}s",flush=True)
