import json, random, sys, time
from collections import Counter
from kum import *
from theorem_g import theorem_g
from bin_class import PTS
from gen import instance_with_plane
rng=random.Random(int(sys.argv[1]) if len(sys.argv)>1 else 11)
c=Counter(); T=time.time()
def go(tag,M,K):
    info=classify(M)
    if not (info["strict"] and info["t"]==0): c[(tag,"skip-nonstrict")]+=1; return
    try:
        sig,case=theorem_g(M,K); c[(tag,"CBO",case)]+=1
    except AssertionError as ex:
        c[(tag,"FAIL",str(ex)[:40])]+=1; print("FAIL",tag,M.data,bits(K),ex,flush=True)
reps=json.load(open("orbits_n10_t0.json"))
for r in reps:
    cols=[]
    for p,cn in zip(PTS,r["counts"]): cols+=[p]*cn
    M=binary(cols)
    for K in classify(M)["planes3k"]: go("n10",M,K)
for tag,cols in (("cx-bin-k3",(4,1,3,6,6,3,2,5,7,13,9,13,9,13)),("cx-k4a",(1,7,6,2,6,5,4,2,4,4,5,2,11,11,11,11,14,14)),
                 ("wit-k4",(10,3,11,1,3,3,15,15,7,6,1,14,11,7,3,7,8,1)),("wit-k5",(10,3,11,1,3,3,15,15,7,6,1,14,11,7,3,7,8,1,15,3,8,9))):
    M=binary(cols)
    for K in classify(M)["planes3k"]: go(tag,M,K)
for k in (3,4,5,6,7):
    for p in (2,3,5):
        for mode in ("mixed","line","mixed"):
            for it in range(4 if k<6 else 2):
                inst=instance_with_plane(p,k,rng,mode=mode)
                if inst: go(f"k{k}",inst[0],inst[1])
    print(k,{kk:v for kk,v in c.items() if kk[0]==f"k{k}"},f"{time.time()-T:.0f}s",flush=True)
print({kk:v for kk,v in c.items() if not kk[0].startswith("k")})
