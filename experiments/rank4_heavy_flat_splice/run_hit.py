import random, sys, time
from collections import Counter
from kum import *
from gen import proj_points, mk
from hitting import *
from bsl import uniformly_dense_rank4
rng=random.Random(int(sys.argv[1]))
def rand_inst(p,k,style):
    pts=proj_points(p,4)
    for _ in range(3000):
        if style=="biased":
            base=rng.sample(pts,rng.randint(5,min(len(pts),12)))
            w=[rng.random()**2 for _ in base]
            vecs=rng.choices(base,weights=w,k=4*k+2)
        elif style=="plane":
            pl=[v for v in pts if v[3]==0]
            vecs=rng.choices(pl,k=3*k)+rng.choices([v for v in pts if v[3]],k=k+2)
        else:
            vecs=[rng.choice(pts) for _ in range(4*k+2)]
        M=mk(p,vecs)
        if M.rank()==4 and uniformly_dense_rank4(M,M.full): return M
c=Counter(); T=time.time()
for k in (4,5,6,7,8,9,10):
    for p in (2,3):
        for style in ("biased","plane","uniform"):
            for it in range(8):
                M=rand_inst(p,k,style)
                if M is None: continue
                fl,NT=near_tight(M)
                H=heavy_flats(M,fl)
                if not H: c[(k,"light")]+=1; continue
                c[(k,"has heavy")]+=1
                ok=False
                for F in sorted(H,key=lambda F:-pc(F)):
                    r=find_hitting(M,F,NT)
                    if isinstance(r,list):
                        ok=True; c[(k,"hit",("pt","ln","pl")[M.r(F)-1])]+=1; break
                if not ok:
                    c[(k,"NO HIT for any heavy flat")]+=1
                    print("NOHIT",k,p,style,M.data,[ (M.r(F),pc(F)) for F in H],flush=True)
    print(k,{kk:v for kk,v in c.items() if kk[0]==k},f"{time.time()-T:.0f}s",flush=True)
