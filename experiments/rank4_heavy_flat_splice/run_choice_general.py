"""Stress the choice + DP pipeline for (3k-1)-planes, (2k-1)-lines, k-points, 2k-lines."""
import random, sys, time
from collections import Counter
from kum import *
from gen import proj_points, mk
from choice_general import dp_general
rng=random.Random(int(sys.argv[1]) if len(sys.argv)>1 else 21)
def norm(v,p):
    for x in v:
        if x%p: inv=pow(x,p-2,p); return tuple((y*inv)%p for y in v)
def inst(p,k,kind):
    pts=proj_points(p,4)
    for _ in range(6000):
        if kind=="pt":
            a=rng.choice(pts); vecs=[a]*k
        elif kind in ("ln","ln-1"):
            a,b=rng.sample(pts,2)
            line=sorted({norm(tuple((x*s+y*t)%p for x,y in zip(a,b)),p) for s in range(p) for t in range(p) if (s,t)!=(0,0)})
            target=2*k if kind=="ln" else 2*k-1; vecs=[]
            while len(vecs)<target:
                q=rng.choice(line)
                if vecs.count(q)<k-1: vecs.append(q)
        else:  # plane of size 3k-1
            plane=[v for v in pts if v[3]==0]; vecs=[]
            while len(vecs)<3*k-1:
                q=rng.choice(plane)
                if vecs.count(q)<k-1: vecs.append(q)
        while len(vecs)<4*k+2: vecs.append(rng.choice(pts))
        M=mk(p,vecs); info=classify(M)
        if not (info["strict"] and info["t"]==0) or info["planes3k"]: continue   # exclude Theorem G cases
        if kind=="pt": F=M.cl(1); want=(1,k)
        elif kind in ("ln","ln-1"):
            j=next((j for j in range(1,len(vecs)) if M.rk([0,j])==2),None)
            if j is None: continue
            F=M.cl(1|1<<j); want=(2,2*k if kind=="ln" else 2*k-1)
        else:
            F=M.cl(sum(1<<x for x in range(3*k-1))); want=(3,3*k-1)
        if (M.r(F),pc(F))!=want: continue
        return M,F
    return None
opts={"pt":(False,False),"ln":(False,False),"ln-1":(True,False),"pl-1":(True,True)}
c=Counter(); T=time.time()
for k in (3,4,5):
    for kind in ("pt","ln","ln-1","pl-1"):
        for p in (2,3,5):
            for it in range(5 if k<5 else 3):
                r=inst(p,k,kind)
                if r is None: c[(k,kind,"noinst")]+=1; continue
                M,F=r
                sig,msg=dp_general(M,F,rng,*opts[kind])
                c[(k,kind,msg if isinstance(msg,str) else msg[0])]+=1
                if msg!="ok": print(k,kind,p,msg,M.data,flush=True)
        print(k,kind,{kk[2]:v for kk,v in c.items() if kk[:2]==(k,kind)},f"{time.time()-T:.0f}s",flush=True)
