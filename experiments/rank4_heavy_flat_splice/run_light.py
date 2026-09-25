import itertools, random, time, sys
from collections import Counter
from kum import *
from gen import proj_points, mk
from bsl import uniformly_dense_rank4
rng=random.Random(int(sys.argv[1]) if len(sys.argv)>1 else 9)

def contiguous_splice(M,B,sig):
    n=len(sig); res=[]
    for g in range(n):
        L=[sig[(g-3+j)%n] for j in range(3)]; R=[sig[(g+j)%n] for j in range(3)]
        for pi in itertools.permutations(B):
            seq=L+list(pi)+R
            if all(M.rk(seq[i:i+4])==4 for i in range(len(seq)-3)):
                return (g,pi)
    return None

def slacks(M,k):
    info=classify(M); prof=info["profile"]
    return prof, (k+0.5-prof[0], 2*k+1-prof[1], 3*k+1.5-prof[2])

WIT={6:(10,3,11,1,3,3,15,15,7,6,1,14,11,7,3,7,8,1,15,3,8,9,1,11,6,3),
     7:(10,3,11,1,3,3,15,15,7,6,1,14,11,7,3,7,8,1,15,3,8,9,1,11,6,3,4,12,11,1)}
def rand_light(p,k,tries=200):
    pts=proj_points(p,4)
    for _ in range(tries):
        vecs=[rng.choice(pts) for _ in range(4*k+2)]
        M=mk(p,vecs)
        if M.rank()==4 and uniformly_dense_rank4(M,M.full): return M
c=Counter()
insts=[("wit6",binary(WIT[6]),6),("wit7",binary(WIT[7]),7)]
for k in (5,6):
    for p in (3,5):
        for i in range(3):
            M=rand_light(p,k)
            if M: insts.append((f"rnd{p}k{k}",M,k))
for name,M,k in insts:
    prof,sl=slacks(M,k)
    T0=time.time(); cc=Counter()
    for trial in range(6):
        while True:
            B=rng.sample(range(M.n),4)
            if M.rk(B)==4: break
        D=sum(1<<x for x in B)
        if not uniformly_dense_rank4(M,M.full&~D): cc["B not dense"]+=1; continue
        els=[x for x in range(M.n) if not (D>>x)&1]
        for s in range(3):
            try: sig=find_cbo(M,elems=els,first=els[0],rng=rng,limit=3*10**5)
            except Timeout: cc["timeout"]+=1; continue
            if sig is None: cc["noCBO"]+=1; continue
            r=contiguous_splice(M,B,list(sig))
            cc["splice ok" if r else "BLOCKED"]+=1
            if not r: print("   BLOCKED",name,M.data,B,sig)
    print(name,"profile",prof,"slacks",tuple(round(x,2) for x in sl),dict(cc),f"{time.time()-T0:.0f}s",flush=True)
