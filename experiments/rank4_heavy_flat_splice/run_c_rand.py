import sys, time, random
from collections import Counter
from kum import *
from ctest import *
from gen import instance_with_plane
seed=int(sys.argv[1]); k=int(sys.argv[2]); ninst=int(sys.argv[3]); nsig=int(sys.argv[4])
rng=random.Random(seed)
T=time.time(); tot=Counter()
for p in (2,3,5):
    for it in range(ninst):
        inst=instance_with_plane(p,k,rng)
        if inst is None: continue
        M,K,info=inst
        tot[("inst",p)]+=1
        for e in range(M.n):
            if (K>>e)&1: continue
            try:
                sig=deletion_cbos(M,e,sample=nsig,rng=rng,limit=2*10**5)
            except Timeout:
                continue
            for s in sig:
                tot["cases"]+=1
                try:
                    ok=completes(M,K,s,limit=2*10**6)
                except Timeout:
                    tot["timeout"]+=1; continue
                if ok is None:
                    tot["FAIL"]+=1
                    print("FAIL p=%d"%p, M.data, bits(K), e, s, "type",gap_type(s,K),"bad",bad_triples(M,inherited(s,K)),flush=True)
    print(p, dict(tot), f"{time.time()-T:.0f}s", flush=True)
