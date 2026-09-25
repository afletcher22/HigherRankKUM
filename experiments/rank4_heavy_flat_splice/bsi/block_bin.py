"""Fast binary search: cyclic sequence Y (length m, CBO of multiset Y) with every gap blocked
for D = {1,2,4,8}, subject to: M = Y + D strict t=0 on n=m+4=4k+2 (caps k,2k,3k),
and M\\D = Y uniformly dense at m/4.  DFS with incremental cap pruning."""
import sys, random, itertools
from functools import lru_cache
sys.setrecursionlimit(100000)

@lru_cache(maxsize=None)
def rank(t):
    piv = [0]*4; r = 0
    for v in t:
        x = v
        while x:
            i = x.bit_length()-1
            if piv[i]: x ^= piv[i]
            else: piv[i] = x; r += 1; break
    return r
def rk(*vs): return rank(tuple(sorted(vs)))

PTS = list(range(1,16))
LINES = sorted({frozenset(x for x in PTS if rk(a,b,x)<=2) for a,b in itertools.combinations(PTS,2)}, key=sorted)
PLANES = [frozenset(x for x in PTS if bin(nv & x).count('1')%2==0) for nv in PTS]
LINES_OF = {p:[i for i,L in enumerate(LINES) if p in L] for p in PTS}
PLANES_OF = {p:[i for i,H in enumerate(PLANES) if p in H] for p in PTS}
D = (1,2,4,8)
PERMS = list(itertools.permutations(D))

@lru_cache(maxsize=None)
def gap_works(a3,a2,a1,b1,b2,b3):
    for d in PERMS:
        if (rk(a3,a2,a1,d[0])==4 and rk(a2,a1,d[0],d[1])==4 and rk(a1,d[0],d[1],d[2])==4 and
            rk(d[1],d[2],d[3],b1)==4 and rk(d[2],d[3],b1,b2)==4 and rk(d[3],b1,b2,b3)==4):
            return True
    return False

def search(m, rng, node_limit, restarts):
    n = m+4; k = (n-2)//4
    capY = (m/4, m/2, 3*m/4)  # uniform density of Y
    found = []
    for r in range(restarts):
        cnt = {p:0 for p in PTS}
        lineM = [0]*len(LINES); planeM = [0]*len(PLANES)
        lineY = [0]*len(LINES); planeY = [0]*len(PLANES)
        for d in D:
            cnt[d] += 0  # D counted separately below
            for i in LINES_OF[d]: lineM[i]+=1
            for i in PLANES_OF[d]: planeM[i]+=1
        cntM = {p:(1 if p in D else 0) for p in PTS}
        Y = []; nodes=[0]
        def add(v, s):
            cnt[v]+=s; cntM[v]+=s
            for i in LINES_OF[v]: lineM[i]+=s; lineY[i]+=s
            for i in PLANES_OF[v]: planeM[i]+=s; planeY[i]+=s
        def ok_caps(v):
            if cntM[v] > k or cnt[v] > capY[0]: return False
            if any(lineM[i] > 2*k or lineY[i] > capY[1] for i in LINES_OF[v]): return False
            if any(planeM[i] > 3*k or planeY[i] > capY[2] for i in PLANES_OF[v]): return False
            return True
        def dfs():
            nodes[0]+=1
            if nodes[0]>node_limit: return False
            L=len(Y)
            if L==m:
                for i in range(m-3,m):
                    if rk(*[Y[(i+j)%m] for j in range(4)])!=4: return False
                for g in list(range(m-2,m))+[0,1,2]:
                    s=[Y[(g-3+t)%m] for t in range(6)]
                    if gap_works(*s): return False
                return True
            cands = PTS[:]; rng.shuffle(cands)
            for v in cands:
                if L>=3 and rk(Y[-3],Y[-2],Y[-1],v)!=4: continue
                if L<3 and rk(*(Y+[v]))!=L+1: continue
                add(v,1)
                good = ok_caps(v)
                if good:
                    Y.append(v)
                    if len(Y)>=6 and gap_works(*Y[-6:]): good=False
                    if good and dfs(): return True
                    Y.pop()
                add(v,-1)
            return False
        if dfs():
            found.append(list(Y))
    return found

if __name__=="__main__":
    rng=random.Random(int(sys.argv[1]) if len(sys.argv)>1 else 1)
    for m in [6,10,14]:
        f=search(m,rng,node_limit=300000,restarts=200)
        print(f"m={m} (n={m+4}): cyclic fully-blocked sequences with M strict t0 & Y dense: {len(f)}",flush=True)
        for Y in f[:5]: print("   ",Y)
