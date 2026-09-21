#!/usr/bin/env python3
"""Explicit no-saturation t=0 witnesses with growing four-block repair distance.

Each witness is a binary rank-4 labelled multiset on n=4k+2 elements with:
  * the displayed deletion order a CBO of M\e;
  * every two-element deletion retaining rank four;
  * the two-deletion density caps (k,2k,3k);
  * no saturated 3k-point rank-three flat containing e;
  * exact fixed-e distance to insertion success under arbitrary
    CBO-preserving permutations of four consecutive positions.

Recorded exact distances:
  n=14 (k=3): 3
  n=18 (k=4): 4
  n=22 (k=5): 5
  n=26 (k=6): 6
  n=30 (k=7): 8

This disproves every proposed universal radius <= 6 immediately and gives
strong evidence that no constant-radius strengthening of the component theorem
should be expected.

Finite exact computation for the listed witnesses; not Lean certification.
"""

from collections import Counter, deque
from itertools import combinations, permutations
import json

import rank4_binary_n10_nonsimple_exact as base

ALL4=tuple(p for p in permutations(range(4)) if p!=(0,1,2,3))

WITNESSES=[
  {
    "k":3,
    "columns":(10,3,11,1,3,3,15,15,7,6,1,14,11,7),
    "e":10,
    "order":(0,7,1,8,11,9,4,13,12,3,6,5,2),
    "distance":3,
  },
  {
    "k":4,
    "columns":(10,3,11,1,3,3,15,15,7,6,1,14,11,7,3,7,8,1),
    "e":10,
    "order":(0,7,1,8,11,9,14,15,16,17,4,13,12,3,6,5,2),
    "distance":4,
  },
  {
    "k":5,
    "columns":(10,3,11,1,3,3,15,15,7,6,1,14,11,7,3,7,8,1,15,3,8,9),
    "e":10,
    "order":(0,18,19,20,21,7,1,8,11,9,14,15,16,17,4,13,12,3,6,5,2),
    "distance":5,
  },
  {
    "k":6,
    "columns":(10,3,11,1,3,3,15,15,7,6,1,14,11,7,3,7,8,1,15,3,8,9,1,11,6,3),
    "e":10,
    "order":(0,18,19,20,21,7,1,22,23,24,25,8,11,9,14,15,16,17,4,13,12,3,6,5,2),
    "distance":6,
  },
  {
    "k":7,
    "columns":(10,3,11,1,3,3,15,15,7,6,1,14,11,7,3,7,8,1,15,3,8,9,1,11,6,3,4,12,11,1),
    "e":10,
    "order":(0,18,19,20,21,7,1,22,23,24,25,8,11,9,14,15,16,17,4,13,12,3,26,27,28,29,6,5,2),
    "distance":8,
  },
]

def rank(vals):
    return base.rank2(vals)

def canonical(o):
    o=tuple(o)
    i=o.index(min(o))
    return o[i:]+o[:i]

def cbo(cols,o):
    n=len(o)
    return all(rank([cols[o[(i+j)%n]] for j in range(4)])==4 for i in range(n))

def blocker_word(cols,e,o):
    n=len(o); out=[]
    for i in range(n):
        tri=[o[(i+j)%n] for j in range(3)]
        r=rank([cols[x] for x in tri])
        out.append(int(rank([cols[x] for x in tri]+[cols[e]])==r))
    return "".join(map(str,out))

def favorable(cols,e,o):
    b=blocker_word(cols,e,o); n=len(b)
    return any(all(b[(i+j)%n]=="0" for j in range(4)) for i in range(n))

def neighbors(cols,o):
    out={}
    n=len(o)
    co=canonical(o)
    for st in range(n):
        inds=[(st+j)%n for j in range(4)]
        vals=[o[i] for i in inds]
        for p in ALL4:
            a=list(o)
            for dst,src in enumerate(p):
                a[inds[dst]]=vals[src]
            t=canonical(a)
            if t!=co and t not in out and cbo(cols,t):
                out[t]=(st,p)
    return out

def profile(cols,labels):
    cnt=Counter(cols[i] for i in labels)
    def occ(F): return sum(cnt[x] for x in F)
    return (
      max(cnt.values(),default=0),
      max(occ(F) for F in base.LINES),
      max(occ(F) for F in base.HYPERPLANES),
    )

def saturated_through_e(cols,e,k):
    cnt=Counter(cols)
    return any(
      cols[e] in H and sum(cnt[x] for x in H)==3*k
      for H in base.HYPERPLANES
    )

def shortest_path(cols,e,start,maxdepth):
    s=canonical(start)
    q=deque([(s,0)])
    prev={s:None}
    edge={}
    while q:
        u,d=q.popleft()
        if favorable(cols,e,u):
            path=[]
            x=u
            while prev[x] is not None:
                path.append({
                  "move_start":edge[x][0],
                  "pattern":list(edge[x][1]),
                  "order":list(x),
                  "blocker_word":blocker_word(cols,e,x),
                })
                x=prev[x]
            path.reverse()
            return d,path,len(prev)
        if d>=maxdepth:
            continue
        for v,mv in neighbors(cols,u).items():
            if v not in prev:
                prev[v]=u
                edge[v]=mv
                q.append((v,d+1))
    return None,None,len(prev)

def audit(W):
    k=W["k"]; cols=W["columns"]; e=W["e"]; order=W["order"]
    n=4*k+2
    assert len(cols)==n and len(order)==n-1
    assert rank(cols)==4

    p=profile(cols,range(n))
    assert p[0] <= k and p[1] <= 2*k and p[2] <= 3*k

    for D in combinations(range(n),2):
        keep=[i for i in range(n) if i not in D]
        assert rank([cols[i] for i in keep])==4
        q=profile(cols,keep)
        assert q[0] <= k and q[1] <= 2*k and q[2] <= 3*k

    assert not saturated_through_e(cols,e,k)
    assert cbo(cols,order)
    assert not favorable(cols,e,order)

    d,path,seen=shortest_path(cols,e,order,W["distance"])
    assert d==W["distance"]

    # Confirm no shorter path by the BFS return value itself.
    return {
      "k":k,
      "n":n,
      "columns":list(cols),
      "omitted_label":e,
      "omitted_point":cols[e],
      "deletion_order":list(order),
      "flat_profile":list(p),
      "initial_blocker_word":blocker_word(cols,e,order),
      "has_saturated_rank_three_flat_through_e":False,
      "exact_distance":d,
      "states_seen_by_shortest_path_bfs":seen,
      "shortest_path":path,
    }

def main():
    rows=[audit(W) for W in WITNESSES]
    assert [r["exact_distance"] for r in rows]==[3,4,5,6,8]
    print(json.dumps({
      "scope":"explicit binary strict/two-deletion-robust t=0 witnesses",
      "move_set":"arbitrary CBO-preserving permutations of four consecutive positions; omitted element fixed",
      "rows":rows,
      "interpretation":(
        "No-saturation does not imply any small fixed repair radius: explicit "
        "witnesses already realize exact distances 3,4,5,6,8 as k grows from "
        "3 to 7.  This strongly favors a genuine component-closure proof over "
        "a bounded-depth local theorem."
      ),
      "claim_level":"exact finite computation for listed witnesses; not Lean certification"
    },indent=2,sort_keys=True))

if __name__=="__main__":
    main()
