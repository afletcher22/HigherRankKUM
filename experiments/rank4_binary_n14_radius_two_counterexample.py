#!/usr/bin/env python3
"""Explicit n=14 counterexample to the no-saturation radius-two conjecture.

Binary rank-4 labelled columns:
    (10,3,11,1,3,3,15,15,7,6,1,14,11,7)

Omitted label e=10.

The displayed deletion CBO is bad, has no favorable one-step four-block
neighbor, and has no favorable state within two arbitrary CBO-preserving
four-block moves.  Nevertheless it repairs in exactly three moves.

The matroid satisfies:
  * rank 4;
  * flat profile (3,5,9);
  * every two-element deletion retains rank 4;
  * every two-element deletion satisfies the 12/4 density caps;
  * no 9-point rank-three flat contains e.

Finite exact computation for this witness; not Lean certification.
"""

from collections import Counter, deque
from itertools import combinations, permutations
import json

import rank4_binary_n10_nonsimple_exact as base

COLS=(10,3,11,1,3,3,15,15,7,6,1,14,11,7)
E=10
ORDER=(0,7,1,8,11,9,4,13,12,3,6,5,2)
ALL4=tuple(p for p in permutations(range(4)) if p!=(0,1,2,3))

def rank(vals):
    return base.rank2(vals)

def canonical(o):
    o=tuple(o)
    i=o.index(min(o))
    return o[i:]+o[:i]

def cbo(o):
    n=len(o)
    return all(rank([COLS[o[(i+j)%n]] for j in range(4)])==4 for i in range(n))

def blocker_word(o):
    n=len(o); out=[]
    for i in range(n):
        tri=[o[(i+j)%n] for j in range(3)]
        r=rank([COLS[x] for x in tri])
        out.append(int(rank([COLS[x] for x in tri]+[COLS[E]])==r))
    return "".join(map(str,out))

def favorable(o):
    b=blocker_word(o); n=len(b)
    return any(all(b[(i+j)%n]=="0" for j in range(4)) for i in range(n))

def neighbors(o):
    out={}
    n=len(o)
    for st in range(n):
        inds=[(st+j)%n for j in range(4)]
        vals=[o[i] for i in inds]
        for p in ALL4:
            a=list(o)
            for dst,src in enumerate(p):
                a[inds[dst]]=vals[src]
            t=canonical(a)
            if t!=canonical(o) and cbo(t):
                out.setdefault(t,(st,p))
    return out

def profile(labels):
    cnt=Counter(COLS[i] for i in labels)
    def occ(F): return sum(cnt[x] for x in F)
    return (
        max(cnt.values(),default=0),
        max(occ(F) for F in base.LINES),
        max(occ(F) for F in base.HYPERPLANES),
    )

def hyperplane_sizes_through_e():
    cnt=Counter(COLS)
    return sorted(
        sum(cnt[x] for x in H)
        for H in base.HYPERPLANES
        if COLS[E] in H
    )

def shortest_path(maxdepth=5):
    s=canonical(ORDER)
    q=deque([(s,0)])
    prev={s:None}
    edge={}
    while q:
        u,d=q.popleft()
        if favorable(u):
            path=[]
            x=u
            while prev[x] is not None:
                path.append({
                    "move_start":edge[x][0],
                    "pattern":list(edge[x][1]),
                    "order":list(x),
                    "blocker_word":blocker_word(x),
                    "favorable":favorable(x),
                })
                x=prev[x]
            path.reverse()
            return d,path
        if d>=maxdepth:
            continue
        for v,mv in neighbors(u).items():
            if v not in prev:
                prev[v]=u
                edge[v]=mv
                q.append((v,d+1))
    return None,None

def main():
    assert rank(COLS)==4
    assert profile(range(14))==(3,5,9)

    for D in combinations(range(14),2):
        keep=[i for i in range(14) if i not in D]
        assert rank([COLS[i] for i in keep])==4
        a,b,c=profile(keep)
        assert a<=3 and b<=6 and c<=9

    assert cbo(ORDER)
    assert not favorable(ORDER)

    hs=hyperplane_sizes_through_e()
    assert 9 not in hs

    d,path=shortest_path()
    assert d==3

    first=neighbors(ORDER)
    assert not any(favorable(x) for x in first)

    second=set()
    for x in first:
        second.update(neighbors(x))
    assert not any(favorable(x) for x in second)

    print(json.dumps({
        "columns":list(COLS),
        "omitted_label":E,
        "omitted_point":COLS[E],
        "deletion_order":list(ORDER),
        "ground_flat_profile":list(profile(range(14))),
        "all_two_deletions_rank_four":True,
        "all_two_deletions_uniform_density_12_over_4":True,
        "initial_blocker_word":blocker_word(ORDER),
        "initial_favorable":False,
        "one_step_neighbor_count":len(first),
        "one_step_favorable":0,
        "two_step_reachable_states":len(second),
        "two_step_favorable":0,
        "rank_three_flat_sizes_through_e":hs,
        "has_saturated_9_point_flat_through_e":False,
        "exact_four_block_distance_to_success":d,
        "shortest_path":path,
        "interpretation":(
            "No-saturation does not imply radius two.  This strict/two-deletion-"
            "robust t=0 state has no saturated rank-three flat through e and "
            "requires exactly three fixed-e arbitrary four-block moves."
        ),
        "claim_level":"exact finite computation for one explicit witness; not Lean certification"
    },indent=2,sort_keys=True))

if __name__=="__main__":
    main()
