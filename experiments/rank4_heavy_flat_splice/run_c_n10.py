import json, time
from collections import Counter
from kum import *
from ctest import *
from bin_class import PTS
reps=json.load(open("orbits_n10_t0.json"))
T=time.time()
tot=Counter()
for i,r in enumerate(reps):
    cols=[]
    for p,c in zip(PTS,r["counts"]): cols+=[p]*c
    M=binary(cols)
    info=classify(M)
    for K in info["planes3k"]:
        for e in range(M.n):
            if (K>>e)&1: continue
            sig=deletion_cbos(M,e)
            for s in sig:
                tot["cases"]+=1
                gt=gap_type(s,K); nb=len(bad_triples(M,inherited(s,K)))
                tot[("type",gt,nb)]+=1
                if completes(M,K,s) is None:
                    tot["FAIL"]+=1
                    if tot["FAIL"]<=5: print("FAIL",i,cols,bits(K),e,s)
    print(f"orbit {i} done; cumulative cases={tot['cases']} fails={tot['FAIL']} ({time.time()-T:.0f}s)",flush=True)
print(dict(tot))
