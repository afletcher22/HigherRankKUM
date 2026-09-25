"""k=2 base lemma (no freedom): every strict t=0 n=10 M with a 6-plane K has a CBO with a K-site."""
import random, sys, time
from collections import Counter
from kum import *
from dp import site_cbo
from gen import instance_with_plane
rng=random.Random(int(sys.argv[1]) if len(sys.argv)>1 else 3)
c=Counter(); T=time.time(); seen=set()
for p in (3,5,7):
    for it in range(int(sys.argv[2]) if len(sys.argv)>2 else 150):
        inst=instance_with_plane(p,2,rng,mode=rng.choice(["mixed","line","mixed"]))
        if inst is None: continue
        M,K,info=inst
        key=tuple(sorted(M.data)); 
        if key in seen: continue
        seen.add(key)
        C=[x for x in range(10) if not (K>>x)&1]
        s=site_cbo(M,list(range(10)),K)
        rC=M.rk(C)
        if isinstance(s,list): c[(p,"site",rC)]+=1
        elif s is None:
            anyc=find_cbo(M)
            c[(p,"NO SITE",rC,"anyCBO" if anyc else "noCBO")]+=1
            print("NO SITE",p,M.data,"rC",rC,"anyCBO",anyc,flush=True)
        else: c[(p,"timeout")]+=1
    print(p,dict((k,v) for k,v in c.items() if k[0]==p),f"{time.time()-T:.0f}s",flush=True)
