"""n=10 base: for r(C)>=3, does EVERY perfect rank-3 order tau of K extend to a CBO with a K-site
whose induced K-order is tau?  (r(C)=2 recorded separately.)"""
import json, random, sys, time
from collections import Counter
from kum import *
from dp import has_site
from gtest import rank3_cbos
from bin_class import PTS
from gen import instance_with_plane

def site_extensions(M,tau,C,K):
    """all placements of C into cyclic tau (tau[0] first) giving a CBO; return (any, any_with_site)."""
    n=len(tau)+len(C); order=[tau[0]]; st={"ti":1,"used":set()}; res=[False,False]
    def ok():
        w=order[-4:] if len(order)>=4 else order
        return M.rk(w)==len(w) and len(set(w))==len(w)
    def dfs():
        if res[1]: return
        if len(order)==n:
            if all(M.rk([order[(i+j)%n] for j in range(4)])==4 for i in range(n-3,n)):
                res[0]=True
                if has_site(order,K) is not None: res[1]=True
            return
        if st["ti"]<len(tau):
            order.append(tau[st["ti"]]); st["ti"]+=1
            if ok(): dfs()
            st["ti"]-=1; order.pop()
        for c in C:
            if c in st["used"]: continue
            order.append(c); st["used"].add(c)
            if ok(): dfs()
            st["used"].discard(c); order.pop()
    dfs(); return tuple(res)

rng=random.Random(5); c=Counter(); T=time.time()
def study(tag,M,K):
    C=[x for x in range(M.n) if not (K>>x)&1]; rC=M.rk(C)
    taus=rank3_cbos(M,bits(K))
    for t in taus:
        a,s=site_extensions(M,list(t),C,K)
        c[(tag,"r%d"%rC,"site" if s else ("ext-no-site" if a else "no-ext"))]+=1
reps=json.load(open("orbits_n10_t0.json"))
for r in reps:
    cols=[]
    for p,cn in zip(PTS,r["counts"]): cols+=[p]*cn
    M=binary(cols); info=classify(M)
    for K in info["planes3k"]: study("bin",M,K)
for p in (3,5):
    for it in range(80):
        inst=instance_with_plane(p,2,rng,mode=rng.choice(["mixed","mixed","line"]))
        if inst: study("gf%d"%p,inst[0],inst[1])
for k,v in sorted(c.items()): print(k,v)
print(f"{time.time()-T:.0f}s")
