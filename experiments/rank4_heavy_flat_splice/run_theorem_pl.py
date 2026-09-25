import random, sys, time
from collections import Counter
from kum import *
from gen import proj_points, mk
from theorem_pl import dp_point, dp_line
rng=random.Random(int(sys.argv[1]) if len(sys.argv)>1 else 4)
def norm(v,p):
    for x in v:
        if x%p: inv=pow(x,p-2,p); return tuple((y*inv)%p for y in v)
def inst(p,k,kind):
    pts=proj_points(p,4)
    for _ in range(4000):
        if kind=="point":
            a=rng.choice(pts); vecs=[a]*k
        else:
            a,b=rng.sample(pts,2)
            line=sorted({norm(tuple((x*s+y*t)%p for x,y in zip(a,b)),p) for s in range(p) for t in range(p) if (s,t)!=(0,0)})
            vecs=[]
            while len(vecs)<2*k:
                q=rng.choice(line)
                if vecs.count(q)<k: vecs.append(q)
        while len(vecs)<4*k+2: vecs.append(rng.choice(pts))
        M=mk(p,vecs); info=classify(M)
        if not (info["strict"] and info["t"]==0): continue
        F=M.cl(1) if kind=="point" else M.cl(M.cl(1)|(1<<(bits(M.full)[-1] if False else 0)))
        if kind=="point":
            if pc(F)==k: return M,F
        else:
            # the forced line: closure of the first two non-parallel forced elements
            first=[i for i in range(2*k)]
            for j in first[1:]:
                if M.rk([0,j])==2: F=M.cl(1|1<<j); break
            if pc(F)==2*k and M.r(F)==2: return M,F
    return None
c=Counter(); T=time.time()
for k in (3,4,5,6):
    for kind in ("point","line"):
        for p in (2,3,5):
            for it in range(5 if k<6 else 2):
                r=inst(p,k,kind)
                if r is None: c[(k,kind,"noinst")]+=1; continue
                M,F=r
                sig,msg=(dp_point if kind=="point" else dp_line)(M,F,rng)
                c[(k,kind,msg)]+=1
                if msg!="ok": print(k,kind,p,msg,M.data,flush=True)
        print(k,kind,{kk:v for kk,v in c.items() if kk[:2]==(k,kind)},f"{time.time()-T:.0f}s",flush=True)
