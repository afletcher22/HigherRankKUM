import random, time
from collections import Counter
from kum import *
from ctest import *
from bsl import uniformly_dense_rank4
rng=random.Random(2)
plane=[1,2,3,4,5,6,7]           # x3=0 in GF(2)^4 (bit 3 clear)
found=0; tried=Counter(); T=time.time()
for trial in range(400):
    k=4
    Kv=rng.choices(plane,k=12)
    # complement: 4 copies of a, 2 of b, a,b outside plane, line {a,b,a^b} meets plane at a^b
    a,b=rng.sample([8,9,10,11,12,13,14,15],2)
    cols=tuple(Kv+[a]*4+[b]*2)
    M=binary(cols); info=classify(M)
    if not (info["strict"] and info["t"]==0): tried["notstrict"]+=1; continue
    K=(1<<12)-1
    if K not in info["planes3k"]: tried["noK"]+=1; continue
    tried["inst"]+=1
    for e in (12,16):              # a copy / b copy
        try: sig=deletion_cbos(M,e,sample=6,rng=rng,limit=2*10**5)
        except Timeout: continue
        for s in sig:
            tried["cases"]+=1
            try: ok=completes(M,K,s,limit=3*10**6)
            except Timeout: tried["to"]+=1; continue
            if ok is None:
                found+=1; tried["FAIL"]+=1
                if found<=3: print("FAIL k=4",cols,"e",e,"sigma",s,"type",gap_type(s,K),"bad",bad_triples(M,inherited(s,K)),flush=True)
    if found>=3: break
print(dict(tried),f"{time.time()-T:.0f}s")
