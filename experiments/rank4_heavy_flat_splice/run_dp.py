"""Base lemma + end-to-end DP construction for 3k-planes."""
import itertools, json, random, sys, time
from collections import Counter
from kum import *
from dp import *
from bin_class import PTS
from gen import instance_with_plane

def val(M,x):
    d=M.data; return d[x] if d is not None else x

def base_search(M,K,rng,maxtries=None):
    k=pc(K)//3
    Kl=bits(K); C=[x for x in range(M.n) if not (K>>x)&1]
    seen=set(); tries=0
    K0s=list(itertools.combinations(Kl,6)); rng.shuffle(K0s)
    C0s=list(itertools.combinations(C,4))
    for K0 in K0s:
        key0=tuple(sorted(map(str,(val(M,x) for x in K0))))
        S=K&~sum(1<<x for x in K0)
        if k>2 and not rank3_dense(M,S,k-2): continue
        for C0 in C0s:
            key=(key0,tuple(sorted(map(str,(val(M,x) for x in C0)))))
            if key in seen: continue
            seen.add(key); tries+=1
            if maxtries and tries>maxtries: return "gaveup",tries
            s=site_cbo(M,list(K0)+list(C0),K)
            if isinstance(s,list): return (K0,C0,s),tries
    return None,tries

def run_case(tag,M,K,rng,c):
    r,tries=base_search(M,K,rng)
    if r is None: c[(tag,"BASE FAILS")]+=1; print("  BASE FAILS",tag,M.data,bits(K),"tries",tries,flush=True); return
    if r=="gaveup": c[(tag,"gaveup")]+=1; return
    K0,C0,s0=r
    sig=dp_construct(M,K,K0,C0,s0) if pc(K)>6 else s0
    ok=is_cbo(M,sig) and sorted(sig)==list(range(M.n))
    c[(tag,"CBO built" if ok else "BROKEN")]+=1
    if not ok: print("  BROKEN",tag,M.data,flush=True)

rng=random.Random(int(sys.argv[1]) if len(sys.argv)>1 else 1)
c=Counter(); T=time.time()
# exact n=10 class, every 6-plane
reps=json.load(open("orbits_n10_t0.json"))
for r in reps:
    cols=[]
    for p,cn in zip(PTS,r["counts"]): cols+=[p]*cn
    M=binary(cols); info=classify(M)
    for K in info["planes3k"]: run_case("n10",M,K,rng,c)
print({k:v for k,v in c.items() if k[0]=="n10"},f"{time.time()-T:.0f}s",flush=True)
# completion counterexamples and growing witnesses
special=[("cx-bin-k3",binary((4,1,3,6,6,3,2,5,7,13,9,13,9,13))),
 ("cx-gf3-k3",gfp([(1,1,2,0),(1,2,1,0),(1,0,2,0),(1,1,0,0),(1,0,2,0),(1,1,0,0),(1,2,0,0),(1,2,0,0),(1,2,2,0),(1,1,1,1),(0,1,1,2),(0,1,1,2),(0,1,1,2),(1,1,1,1)],3)),
 ("cx-k4a",binary((1,7,6,2,6,5,4,2,4,4,5,2,11,11,11,11,14,14))),
 ("cx-k4b",binary((2,5,4,7,1,3,6,7,3,1,1,4,14,14,14,14,10,10))),
 ("wit-k3",binary((10,3,11,1,3,3,15,15,7,6,1,14,11,7))),
 ("wit-k4",binary((10,3,11,1,3,3,15,15,7,6,1,14,11,7,3,7,8,1))),
 ("wit-k5",binary((10,3,11,1,3,3,15,15,7,6,1,14,11,7,3,7,8,1,15,3,8,9)))]
for tag,M in special:
    info=classify(M)
    for K in info["planes3k"]: run_case(tag,M,K,rng,c)
    print(tag,"profile",info["profile"],"#3k-planes",len(info["planes3k"]),{k:v for k,v in c.items() if k[0]==tag},f"{time.time()-T:.0f}s",flush=True)
for k in (3,4,5):
    for p in (2,3,5):
        for mode in ("mixed","line"):
            for it in range(6 if k<5 else 3):
                inst=instance_with_plane(p,k,rng,mode=mode)
                if inst is None: continue
                M,K,info=inst
                run_case(f"k{k}",M,K,rng,c)
    print(k,{kk:v for kk,v in c.items() if kk[0]==f"k{k}"},f"{time.time()-T:.0f}s",flush=True)
