#!/usr/bin/env python3
"""Explicit n=14 counterexample to the one-step saturation conjecture.

The witness is a binary rank-4 multiset on 14 labelled elements.  It satisfies:
  * strict rank-4 density for n=14;
  * no dangerous 10-point rank-3 flat;
  * every two-element deletion retains rank 4 and satisfies the 12/4 density caps;
  * the displayed deletion CBO for e=12 is bad;
  * no single CBO-preserving four-block permutation makes it favorable;
  * nevertheless there is no 9-point rank-3 flat through e;
  * a two-move fixed-e four-block path reaches a favorable order.

Finite exact computation; not Lean certification.
"""

from collections import Counter, deque
from itertools import combinations, permutations
import json

import rank4_binary_n10_nonsimple_exact as base

COLS=(10,3,11,1,3,3,15,15,6,6,1,14,11,7)
E=12
ORDER=(4,11,8,7,5,13,0,6,3,1,9,2,10)
ALL4=tuple(p for p in permutations(range(4)) if p!=(0,1,2,3))


def rank(vals):
    return base.rank2(vals)


def canonical(o):
    o=tuple(o)
    i=o.index(min(o))
    return o[i:]+o[:i]


def cbo(o):
    m=len(o)
    return all(rank([COLS[o[(i+j)%m]] for j in range(4)])==4 for i in range(m))


def successful(o):
    for g in range(len(o)):
        a=list(o); a.insert(g,E)
        if cbo(a):
            return True,g
    return False,None


def profile(labels):
    vals=[COLS[i] for i in labels]
    cnt=Counter(vals)
    def occ(F): return sum(cnt[x] for x in F)
    return (
        max(cnt.values(),default=0),
        max(occ(F) for F in base.LINES),
        max(occ(F) for F in base.HYPERPLANES),
    )


def four_neighbors(o):
    o=tuple(o); m=len(o); out={}
    for st in range(m):
        inds=[(st+j)%m for j in range(4)]
        vals=[o[i] for i in inds]
        for p in ALL4:
            a=list(o)
            for dst,src in enumerate(p):
                a[inds[dst]]=vals[src]
            t=canonical(a)
            if t!=canonical(o) and cbo(t):
                out.setdefault(t,(st,p))
    return out


def flat_sizes_through_e():
    cnt=Counter(COLS)
    rows=[]
    for H in base.HYPERPLANES:
        if COLS[E] in H:
            rows.append(sum(cnt[x] for x in H))
    return sorted(rows)


def blocker_word(o):
    m=len(o); bits=[]
    for i in range(m):
        tri=[o[(i+j)%m] for j in range(3)]
        r=rank([COLS[x] for x in tri])
        bits.append(int(rank([COLS[x] for x in tri]+[COLS[E]])==r))
    return "".join(map(str,bits))


def bfs():
    s=canonical(ORDER)
    q=deque([s]); prev={s:None}; edge={}
    while q:
        u=q.popleft()
        ok,g=successful(u)
        if ok:
            path=[]
            x=u
            while prev[x] is not None:
                path.append({
                    "order":list(x),
                    "move_start":edge[x][0],
                    "pattern":list(edge[x][1]),
                    "blocker_word":blocker_word(x),
                })
                x=prev[x]
            path.reverse()
            return len(path),path,g
        for v,d in four_neighbors(u).items():
            if v not in prev:
                prev[v]=u; edge[v]=d; q.append(v)
    raise AssertionError("component has no favorable state")


def main():
    assert rank(COLS)==4
    assert profile(range(14))==(3,5,8)

    # Strict n=14 density follows from these sharp flat maxima:
    # rank-1 <=3 < 14/4, rank-2 <=5 < 28/4, rank-3 <=8 < 42/4.
    assert all(rank([COLS[i] for i in range(14) if i not in D])==4
               for D in combinations(range(14),2))
    two_profiles=[profile([i for i in range(14) if i not in D])
                  for D in combinations(range(14),2)]
    assert all(a<=3 and b<=6 and c<=9 for a,b,c in two_profiles)

    assert cbo(ORDER)
    assert successful(ORDER)[0] is False

    ns=four_neighbors(ORDER)
    fav=[t for t in ns if successful(t)[0]]
    assert len(fav)==0

    sizes=flat_sizes_through_e()
    assert max(sizes)==8
    assert 9 not in sizes

    d,path,gap=bfs()
    assert d==2
    assert len(path)==2
    assert gap==9

    print(json.dumps({
        "columns":list(COLS),
        "omitted_label":E,
        "omitted_point":COLS[E],
        "deletion_order":list(ORDER),
        "ground_flat_profile":list(profile(range(14))),
        "all_two_deletions_rank_four":True,
        "all_two_deletions_uniform_density_12_over_4":True,
        "deletion_cbo":True,
        "initial_blocker_word":blocker_word(ORDER),
        "initial_favorable":False,
        "cbo_preserving_four_block_neighbors":len(ns),
        "one_step_favorable_neighbors":len(fav),
        "rank_three_flat_sizes_through_e":sizes,
        "maximum_rank_three_flat_size_through_e":max(sizes),
        "has_saturated_9_point_flat_through_e":False,
        "fixed_e_distance_to_success":d,
        "shortest_path":path,
        "final_insertion_gap":gap,
        "interpretation":(
            "The one-step saturation conjecture is false even under the full "
            "strict/no-dangerous/universal-two-deletion package. This state "
            "has no favorable one-step four-block move and no saturated "
            "9-point rank-three flat through e, but it reaches a favorable "
            "state in exactly two fixed-e four-block moves. The component-level "
            "dichotomy is not refuted."
        ),
        "claim_level":"exact finite computation; not Lean certification",
    },indent=2,sort_keys=True))


if __name__=="__main__":
    main()
