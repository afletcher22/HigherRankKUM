#!/usr/bin/env python3
"""Explicit GF(3) n=18 counterexample to bounded one-step low-slack claims.

Witness properties:
  * rank 4 on n=18 = 4k+2 with k=4;
  * strict/two-deletion-robust density caps;
  * omitted element e belongs to a 4-element parallel class;
  * displayed deletion order is a CBO of M\e and is bad for insertion of e;
  * no single CBO-preserving permutation of four consecutive positions is favorable;
  * every rank-three flat of M\e has at most 9 elements;
  * exact fixed-e four-block repair distance is 2.

Thus one-step rigidity does NOT force a deletion hyperplane of size
3k-1=11 or 3k-2=10.  Its best rank-three slack is
3(4k+1)-4*9 = 15.

Finite exact computation; not Lean certification.
"""

from collections import Counter, deque
from itertools import combinations, permutations, product
import json

P=3
K=4
VECTORS=(
 (0,1,0,0),
 (0,1,1,1),
 (1,1,2,2),
 (0,1,0,1),
 (1,0,1,0),
 (0,1,1,0),
 (1,2,0,1),
 (1,0,0,2),
 (1,1,1,2),
 (1,2,1,1),
 (1,1,2,0),
 (1,1,1,1),
 (0,1,0,1),
 (0,1,0,1),
 (1,2,2,2),
 (1,2,0,0),
 (1,1,0,0),
 (0,1,0,1),
)
E=13
ORDER=(3,7,8,10,12,14,1,5,17,2,11,15,4,6,16,9,0)
ALL4=tuple(p for p in permutations(range(4)) if p!=(0,1,2,3))

def inv(a): return pow(a,P-2,P)

def rank(vs):
    A=[list(v) for v in vs]
    r=0
    for c in range(4):
        q=next((i for i in range(r,len(A)) if A[i][c]%P),None)
        if q is None: continue
        A[r],A[q]=A[q],A[r]
        z=inv(A[r][c]%P)
        A[r]=[(z*x)%P for x in A[r]]
        for i in range(len(A)):
            if i!=r and A[i][c]%P:
                f=A[i][c]%P
                A[i]=[(A[i][j]-f*A[r][j])%P for j in range(4)]
        r+=1
    return r

def canonv(v):
    for x in v:
        if x%P:
            z=inv(x%P)
            return tuple((z*y)%P for y in v)
    raise ValueError

PG=sorted({canonv(v) for v in product(range(P), repeat=4) if any(v)})
HYPERPLANES=tuple(
    frozenset(x for x,v in enumerate(PG)
              if sum(a*b for a,b in zip(n,v))%P==0)
    for n in PG
)
POINT_INDEX={v:i for i,v in enumerate(PG)}
COLS=tuple(POINT_INDEX[v] for v in VECTORS)

def profile(labels):
    cnt=Counter(COLS[i] for i in labels)
    support=list(cnt)
    max1=max(cnt.values(),default=0)
    max2=0
    for a,b in combinations(support,2):
        va,vb=PG[a],PG[b]
        if rank((va,vb))<2: continue
        occ=sum(c for x,c in cnt.items()
                if rank((va,vb,PG[x]))<=2)
        max2=max(max2,occ)
    max3=max(sum(cnt[x] for x in H) for H in HYPERPLANES)
    return (max1,max2,max3)

def isbase4(labels):
    return rank(tuple(VECTORS[i] for i in labels))==4

def cbo(order):
    n=len(order)
    return all(isbase4([order[(i+j)%n] for j in range(4)]) for i in range(n))

def blocker_word(order):
    n=len(order)
    out=[]
    for i in range(n):
        tri=[order[(i+j)%n] for j in range(3)]
        r=rank(tuple(VECTORS[x] for x in tri))
        out.append(int(rank(tuple(VECTORS[x] for x in tri)+(VECTORS[E],))==r))
    return tuple(out)

def favorable(order):
    b=blocker_word(order); n=len(b)
    return any(all(b[(i+j)%n]==0 for j in range(4)) for i in range(n))

def canonical(order):
    order=tuple(order); i=order.index(min(order))
    return order[i:]+order[:i]

def neighbors(order):
    n=len(order); out={}
    co=canonical(order)
    for st in range(n):
        inds=[(st+j)%n for j in range(4)]
        vals=[order[i] for i in inds]
        for p in ALL4:
            a=list(order)
            for dst,src in enumerate(p):
                a[inds[dst]]=vals[src]
            t=canonical(a)
            if t!=co and t not in out and cbo(t):
                out[t]=(st,p)
    return out

def one_step_favorable(order):
    return [t for t in neighbors(order) if favorable(t)]

def deletion_hyperplane_max():
    cnt=Counter(COLS[i] for i in range(18) if i!=E)
    return max(sum(cnt[x] for x in H) for H in HYPERPLANES)

def shortest_path():
    s=canonical(ORDER)
    q=deque([s]); prev={s:None}; edge={}
    while q:
        u=q.popleft()
        if favorable(u):
            path=[]; x=u
            while prev[x] is not None:
                path.append({
                    "move_start":edge[x][0],
                    "pattern":list(edge[x][1]),
                    "order":list(x),
                    "blocker_word":"".join(map(str,blocker_word(x))),
                })
                x=prev[x]
            path.reverse()
            return path
        for v,mv in neighbors(u).items():
            if v not in prev:
                prev[v]=u; edge[v]=mv; q.append(v)
    raise AssertionError("no favorable state in fixed-e component")

def main():
    assert rank(VECTORS)==4
    assert profile(range(18))==(4,7,10)

    # Every two-element deletion remains rank four and obeys the 16/4 caps.
    for D in combinations(range(18),2):
        keep=[i for i in range(18) if i not in D]
        assert rank(tuple(VECTORS[i] for i in keep))==4
        a,b,c=profile(keep)
        assert a<=4 and b<=8 and c<=12

    assert cbo(ORDER)
    assert not favorable(ORDER)
    assert len(one_step_favorable(ORDER))==0
    assert deletion_hyperplane_max()==9

    path=shortest_path()
    assert len(path)==2

    print(json.dumps({
        "field":"GF(3)",
        "k":K,
        "n":18,
        "vectors":[list(v) for v in VECTORS],
        "omitted_label":E,
        "omitted_vector":list(VECTORS[E]),
        "ambient_flat_profile":list(profile(range(18))),
        "deletion_order":list(ORDER),
        "initial_blocker_word":"".join(map(str,blocker_word(ORDER))),
        "deletion_cbo":True,
        "initial_favorable":False,
        "one_step_favorable_neighbors":0,
        "maximum_deletion_rank_three_flat_size":deletion_hyperplane_max(),
        "deletion_rank_three_slack":
            3*(4*K+1)-4*deletion_hyperplane_max(),
        "all_two_deletions_rank_four":True,
        "all_two_deletions_uniform_density_16_over_4":True,
        "exact_fixed_e_four_block_distance":len(path),
        "shortest_path":path,
        "interpretation":(
            "One-step rigidity does not force rank-three slack <=7 or <=11. "
            "Here every deletion hyperplane has size <=9=3k-3, so the best "
            "rank-three slack is 15, yet the displayed bad deletion CBO has "
            "no favorable one-step four-block move. It repairs in two moves."
        ),
        "claim_level":"exact finite computation; not Lean certification",
    },indent=2,sort_keys=True))

if __name__=="__main__":
    main()
