import json, random, time, sys
from collections import Counter
from kum import *
from bsl import *
from bin_class import PTS
from gen import instance_with_plane
rng=random.Random(int(sys.argv[1]) if len(sys.argv)>1 else 3)
def test(M,K,nsig,tag,c):
    H=hitting_sets(M,K)
    c[(tag,"hit" if H else "NOHIT")]+=1
    if not H:
        return False
    T,cc=H[rng.randrange(len(H))]
    D=sum(1<<x for x in T)|(1<<cc)
    els=[x for x in range(M.n) if not (D>>x)&1]
    for s in range(nsig):
        try:
            sig=find_cbo(M,elems=els,first=els[0],rng=rng,limit=5*10**5)
        except Timeout:
            c[(tag,"timeout")]+=1; continue
        if sig is None:
            c[(tag,"M' has no CBO?!")]+=1; continue
        new=splice(M,K,list(T),cc,list(sig))
        if new is None:
            c[(tag,"no usable run")]+=1
        else:
            ok=is_cbo(M,new) and sorted(new)==list(range(M.n))
            c[(tag,"spliced OK" if ok else "SPLICE BROKEN")]+=1
    return True
c=Counter()
reps=json.load(open("orbits_n10_t0.json"))
for r in reps:
    cols=[]
    for p,cn in zip(PTS,r["counts"]): cols+=[p]*cn
    M=binary(cols); info=classify(M)
    for K in info["planes3k"]:
        test(M,K,5,"n10",c)
print(dict(c),flush=True)
for k in (3,4,5,6):
    for p in (2,3,5):
        T0=time.time()
        for it in range(20 if k<6 else 8):
            inst=instance_with_plane(p,k,rng,mode="mixed")
            if inst is None: continue
            M,K,info=inst
            test(M,K,4,f"k{k}",c)
        print(k,p,{kk:v for kk,v in c.items() if kk[0]==f"k{k}"},f"{time.time()-T0:.0f}s",flush=True)
