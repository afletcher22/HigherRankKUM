import itertools, random, time, sys
from collections import Counter
from kum import *
from gen import proj_points, mk
from bsl import uniformly_dense_rank4
from hfs import splice_hfs
rng=random.Random(int(sys.argv[1]) if len(sys.argv)>1 else 5)

def norm(v,p):
    for x in v:
        if x%p:
            inv=pow(x,p-2,p); return tuple((y*inv)%p for y in v)
def rand_instance(p,k,kind,tries=4000):
    pts=proj_points(p,4); n=4*k+2
    for _ in range(tries):
        vecs=[]
        if kind=="point":
            a=rng.choice(pts); s=rng.choice([k,k,k-1]); vecs=[a]*s
        else:
            a,b=rng.sample(pts,2)
            line=sorted({norm(tuple((x*s+y*t)%p for x,y in zip(a,b)),p) for s in range(p) for t in range(p) if (s,t)!=(0,0)})
            target=rng.choice([2*k,2*k,2*k-1])
            while len(vecs)<target: vecs.append(rng.choice(line))
        while len(vecs)<n: vecs.append(rng.choice(pts))
        M=mk(p,vecs)
        if M.rank()!=4: continue
        if not uniformly_dense_rank4(M,M.full): continue
        # find the heavy flat
        if kind=="point":
            F=M.cl(1); 
        else:
            F=M.cl(0b11) if M.r(0b11)==2 else None
            if F is None: continue
        return M,F
    return None

def candidate_B(M,F):
    rho=M.r(F); Fl=bits(F); X=[x for x in range(M.n) if not (F>>x)&1]
    out=[]
    for TF in itertools.combinations(Fl,rho):
        if M.rk(TF)!=rho: continue
        for TX in itertools.combinations(X,4-rho):
            if M.rk(list(TF)+list(TX))!=4: continue
            out.append((TF,TX))
    rng.shuffle(out)
    return out

c=Counter()
for k in (3,4,5,6):
  for kind in ("point","line"):
    for p in (2,3,5):
      T0=time.time()
      for it in range(6):
        inst=rand_instance(p,k,kind)
        if inst is None: c[(k,kind,"noinst")]+=1; continue
        M,F=inst
        found=None
        for TF,TX in candidate_B(M,F)[:400]:
            D=sum(1<<x for x in TF+TX)
            if uniformly_dense_rank4(M,M.full&~D): found=(TF,TX); break
        if not found: c[(k,kind,"no hitting B in sample")]+=1; continue
        TF,TX=found; D=sum(1<<x for x in TF+TX)
        els=[x for x in range(M.n) if not (D>>x)&1]
        for s in range(4):
            try: sig=find_cbo(M,elems=els,first=els[0],rng=rng,limit=4*10**5)
            except Timeout: c[(k,kind,"timeout")]+=1; continue
            if sig is None: c[(k,kind,"M-B no CBO?!")]+=1; continue
            new,info=splice_hfs(M,F,TF,TX,list(sig))
            if new is None: c[(k,kind,"no regular stretch")]+=1
            elif is_cbo(M,new) and sorted(new)==list(range(M.n)): c[(k,kind,"OK",info[0])]+=1
            else: c[(k,kind,"BROKEN")]+=1; print("BROKEN",k,kind,M.data,F,TF,TX,sig,new)
      print(k,kind,p,{kk:v for kk,v in c.items() if kk[0]==k and kk[1]==kind},f"{time.time()-T0:.0f}s",flush=True)
