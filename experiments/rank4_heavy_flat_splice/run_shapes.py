import json, random, time
from collections import Counter
from kum import *
from gtest import rank3_cbos
from bin_class import PTS
from gen import instance_with_plane
from base_shapes import shapes_working
rng=random.Random(8); c=Counter(); T=time.time()
def study(tag,M,K):
    C=[x for x in range(M.n) if not (K>>x)&1]; rC=M.rk(C)
    if rC<3: return
    for t in rank3_cbos(M,bits(K)):
        w=shapes_working(M,list(t),C,is_cbo)
        key=(f"r{rC}","S1" in w,"S2/S3" in w or "S2" in w or "S3" in w)
        c[key]+=1
        if not w: print("NONE",tag,M.data,t,flush=True)
reps=json.load(open("orbits_n10_t0.json"))
for r in reps:
    cols=[]
    for p,cn in zip(PTS,r["counts"]): cols+=[p]*cn
    M=binary(cols); info=classify(M)
    for K in info["planes3k"]: study("bin",M,K)
for p in (3,5,7):
    for it in range(60):
        inst=instance_with_plane(p,2,rng,mode="mixed")
        if inst: study(f"gf{p}",inst[0],inst[1])
print("(rank C, S1 works, S2|S3 works) -> #perfect taus")
for k,v in sorted(c.items()): print(" ",k,v)
print(f"{time.time()-T:.0f}s")
