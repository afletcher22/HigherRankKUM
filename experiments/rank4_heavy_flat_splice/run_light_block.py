import random, sys, time, itertools
from collections import Counter
from kum import *
from gen import proj_points, mk
from light_block import blocked_orders
rng=random.Random(int(sys.argv[1]) if len(sys.argv)>1 else 5)
def light_inst(p,k,poolsize,maxmult):
    pts=proj_points(p,4)
    for _ in range(3000):
        pool=rng.sample(pts,poolsize); vecs=[]
        while len(vecs)<4*k+2:
            q=rng.choice(pool)
            if vecs.count(q)<maxmult: vecs.append(q)
        M=mk(p,vecs); info=classify(M); prof=info["profile"]
        if not (info["strict"] and info["t"]==0): continue
        if prof[0]<=k-1 and prof[1]<=2*k-2 and prof[2]<=3*k-2: return M,prof
    return None
def degenerate_bases(M,num):
    """bases ranked by degeneracy: #elements in planes spanned by 3-subsets of B (more = worse)"""
    cands=[]
    for _ in range(400):
        B=rng.sample(range(M.n),4)
        if M.rk(B)<4: continue
        score=0
        for T in itertools.combinations(B,3):
            score+=pc(M.cl(sum(1<<x for x in T)))
        for T in itertools.combinations(B,2):
            score+=2*pc(M.cl(sum(1<<x for x in T)))
        cands.append((score,sorted(B)))
    cands.sort(reverse=True)
    out=[];seen=set()
    for s,B in cands:
        if tuple(B) not in seen: seen.add(tuple(B)); out.append((s,B))
        if len(out)>=num: break
    return out
c=Counter(); T=time.time()
for k,p,pool,mm in ((4,3,9,3),(4,3,12,3),(4,5,10,3),(5,3,12,4),(5,3,14,4)):
    for it in range(4):
        r=light_inst(p,k,pool,mm)
        if r is None: c[(k,"noinst")]+=1; continue
        M,prof=r
        for score,B in degenerate_bases(M,3):
            found,st=blocked_orders(M,B,limit=3*10**5,rng=rng)
            key=(k,"BLOCKED" if found else ("none-exhaustive" if st=="exhausted" else "none-timeout"))
            c[key]+=1
            if found: print("BLOCKED",k,p,"profile",prof,"B",B,"vals",[M.data[x] for x in B],"sigma",found[0],flush=True)
    print(k,p,pool,dict((kk,v) for kk,v in c.items() if kk[0]==k),f"{time.time()-T:.0f}s",flush=True)
