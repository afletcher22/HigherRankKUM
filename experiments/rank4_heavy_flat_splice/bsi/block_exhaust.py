"""EXHAUSTIVE binary classification: cyclic sequences Y of length m (CBO of multiset Y, labelled)
with every gap blocked for D = {1,2,4,8} (WLOG by GL(4,2) transitivity on bases),
subject to caps: M = Y+D has flat sizes <= (k,2k,3k) [strict t=0, n=4k+2] and optionally
Y uniformly dense.  Counts sequences with Y[0] fixed to the lexicographically... (no symmetry
reduction beyond nothing; counts ordered sequences)."""
import sys, itertools
from block_bin import rk, gap_works, PTS, LINES, PLANES, LINES_OF, PLANES_OF, D
sys.setrecursionlimit(100000)
def run(m, t0caps=True, ydense=True, max_report=5):
    n=m+4; k=(n-2)//4
    capM=(k,2*k,3*k) if t0caps else (k,2*k,3*k+1)
    capY=(m/4,m/2,3*m/4)
    cntM={p:(1 if p in D else 0) for p in PTS}; cntY={p:0 for p in PTS}
    lineM=[sum(1 for d in D if d in L) for L in LINES]; planeM=[sum(1 for d in D if d in H) for H in PLANES]
    lineY=[0]*len(LINES); planeY=[0]*len(PLANES)
    Y=[]; found=[]; nodes=[0]
    def add(v,s):
        cntM[v]+=s; cntY[v]+=s
        for i in LINES_OF[v]: lineM[i]+=s; lineY[i]+=s
        for i in PLANES_OF[v]: planeM[i]+=s; planeY[i]+=s
    def caps_ok(v):
        if cntM[v]>capM[0]: return False
        if ydense and cntY[v]>capY[0]: return False
        for i in LINES_OF[v]:
            if lineM[i]>capM[1] or (ydense and lineY[i]>capY[1]): return False
        for i in PLANES_OF[v]:
            if planeM[i]>capM[2] or (ydense and planeY[i]>capY[2]): return False
        return True
    def dfs():
        nodes[0]+=1
        L=len(Y)
        if L==m:
            for i in range(m-3,m):
                if rk(*[Y[(i+j)%m] for j in range(4)])!=4: return
            for g in list(range(m-2,m))+[0,1,2]:
                if gap_works(*[Y[(g-3+t)%m] for t in range(6)]): return
            found.append(list(Y)); return
        for v in PTS:
            if L>=3:
                if rk(Y[-3],Y[-2],Y[-1],v)!=4: continue
            elif rk(*(Y+[v]))!=L+1: continue
            add(v,1)
            if caps_ok(v):
                Y.append(v)
                if not (len(Y)>=6 and gap_works(*Y[-6:])):
                    dfs()
                Y.pop()
            add(v,-1)
    dfs()
    return found, nodes[0]
if __name__=="__main__":
    for m in [int(a) for a in sys.argv[1:]] or [6]:
        for t0 in [True, False]:
            f,nd=run(m,t0caps=t0)
            print(f"m={m} n={m+4} caps={'t0' if t0 else 'strict(t>0 allowed)'}: fully blocked cyclic sequences={len(f)} (DFS nodes {nd})",flush=True)
            for Y in f[:3]: print("   ",Y)
