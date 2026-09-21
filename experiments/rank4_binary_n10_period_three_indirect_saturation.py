#!/usr/bin/env python3
"""Exact audit of the period-three indirect-saturation mechanism at binary n=10.

This isolates the one-step-rigid blocker word 001001001 in GL(4,2) orbit 14
of the complete two-deletion-robust n=10 census.

For every matching fixed-e deletion CBO it records:
  * whether each isolated blocker already has its endpoint pair spanning e;
  * sizes of the three blocker closures;
  * saturated rank-three flats through e;
  * the three adjacent blocker-killing swaps;
  * the two changed boundary failures for each such swap;
  * saturated flats obtained from pairwise intersections of those failure flats.

Finite exact computation; not Lean certification.
"""

from collections import Counter
from itertools import combinations, permutations
import json

import rank4_binary_n10_nonsimple_exact as base

ALL4 = tuple(p for p in permutations(range(4)) if p != (0,1,2,3))
TARGET = (0,0,1,0,0,1,0,0,1)


def canonical_word(bits):
    bits = tuple(bits)
    n = len(bits)
    rots = [bits[i:]+bits[:i] for i in range(n)]
    rb = tuple(reversed(bits))
    rots += [rb[i:]+rb[:i] for i in range(n)]
    return min(rots)


def blocker_word(cols,e,o):
    m=len(o); out=[]
    for i in range(m):
        tri=[o[(i+j)%m] for j in range(3)]
        vals=tuple(cols[x] for x in tri)
        out.append(int(base.rank2(vals+(cols[e],)) == base.rank2(vals)))
    return tuple(out)


def closure_labels(cols,S):
    vals=[cols[i] for i in S]
    r=base.rank2(vals)
    return frozenset(i for i,v in enumerate(cols)
                     if base.rank2(vals+[v]) == r)


def rank_labels(cols,S):
    return base.rank2([cols[i] for i in S])


def endpoint_pair_spans_e(cols,e,o,i):
    a=o[i]; c=o[(i+2)%len(o)]
    return base.rank2((cols[a],cols[c],cols[e])) == base.rank2((cols[a],cols[c]))


def blockers(cols,e,o):
    m=len(o); out=[]
    for i in range(m):
        tri=tuple(o[(i+j)%m] for j in range(3))
        vals=tuple(cols[x] for x in tri)
        if base.rank2(vals+(cols[e],)) == base.rank2(vals):
            out.append(i)
    return out


def is_one_step_rigid(cols,e,o):
    if base.successful(cols,(e,o)):
        return False
    m=len(o)
    states=set(base.deletion_cbos(cols,e))
    for st in range(m):
        inds=[(st+j)%m for j in range(4)]
        vals=[o[i] for i in inds]
        for patt in ALL4:
            a=list(o)
            for dst,src in enumerate(patt):
                a[inds[dst]]=vals[src]
            t=base.canonical(a)
            if t in states and base.successful(cols,(e,t)):
                return False
    return True


def saturated_flats(cols,e):
    out=set()
    for H in base.HYPERPLANES:
        labs=frozenset(i for i,v in enumerate(cols) if v in H)
        if e in labs and len(labs)==6:
            out.add(labs)
    return out


def swap_failure_flats(cols,o,j):
    n=len(o)
    a=list(o)
    a[j],a[(j+1)%n]=a[(j+1)%n],a[j]
    bad=[]
    for s in range(n):
        W=[a[(s+r)%n] for r in range(4)]
        if rank_labels(cols,W)<4:
            bad.append(s)

    ls=(j-3)%n
    Lcore=[o[(ls+r)%n] for r in range(3)]
    Rcore=[o[(j+2+r)%n] for r in range(3)]
    return bad, closure_labels(cols,Lcore), closure_labels(cols,Rcore)


def main():
    patterns,_=base.qualifying_patterns()
    reps=base.orbit_representatives(patterns)
    counts,orbit_size=reps[14]
    cols=base.labelled_columns(counts)
    assert cols == (5,6,7,9,10,11,12,13,14,15)

    rows=[]
    for e in range(10):
        for o in base.deletion_cbos(cols,e):
            w=blocker_word(cols,e,o)
            if canonical_word(w) != TARGET:
                continue
            if not is_one_step_rigid(cols,e,o):
                continue
            bs=blockers(cols,e,o)
            ep=sum(endpoint_pair_spans_e(cols,e,o,i) for i in bs)
            bcl=tuple(sorted(len(closure_labels(cols,[o[(i+j)%9] for j in range(3)]))
                             for i in bs))
            sats=saturated_flats(cols,e)

            row={
                "omitted_label":e,
                "omitted_point":cols[e],
                "order":list(o),
                "endpoint_pair_blockers":ep,
                "blocker_closure_sizes":list(bcl),
                "saturated_flats_through_e":len(sats),
            }

            if ep==3 and bcl==(4,4,4):
                js=sorted({(i+2)%9 for i in bs})
                F=[]
                swap_rows=[]
                for j in js:
                    bad,FL,FR=swap_failure_flats(cols,o,j)
                    swap_rows.append({
                        "swap_start":j,
                        "failed_window_starts":bad,
                        "left_flat_size":len(FL),
                        "right_flat_size":len(FR),
                        "left_contains_e":e in FL,
                        "right_contains_e":e in FR,
                    })
                    F += [FL,FR]
                generated=Counter()
                for A,B in combinations(F,2):
                    I=A & B
                    H=closure_labels(cols,set(I)|{e})
                    if rank_labels(cols,H)==3 and len(H)==6 and e in H:
                        generated[tuple(sorted(H))]+=1
                row["indirect"]={
                    "kill_swaps":swap_rows,
                    "failure_flats":len(F),
                    "all_failure_flats_size_five":
                        all(x["left_flat_size"]==5 and x["right_flat_size"]==5
                            for x in swap_rows),
                    "all_failure_flats_avoid_e":
                        all(not x["left_contains_e"] and not x["right_contains_e"]
                            for x in swap_rows),
                    "generated_saturated_flats":len(generated),
                    "generation_multiplicities":sorted(generated.values()),
                }
            rows.append(row)

    assert len(rows)==16
    assert {r["omitted_label"] for r in rows}=={6}
    classes=Counter((r["endpoint_pair_blockers"],
                     tuple(r["blocker_closure_sizes"])) for r in rows)
    assert classes == Counter({(2,(4,6,6)):12,(3,(4,4,4)):4})
    indirect=[r for r in rows if r["endpoint_pair_blockers"]==3]
    assert len(indirect)==4
    for r in indirect:
        z=r["indirect"]
        assert len(z["kill_swaps"])==3
        assert all(len(x["failed_window_starts"])==2 for x in z["kill_swaps"])
        assert z["all_failure_flats_size_five"]
        assert z["all_failure_flats_avoid_e"]
        assert z["generated_saturated_flats"]==3
        assert z["generation_multiplicities"]==[2,2,2]

    out={
        "scope":"exact binary n=10 orbit-14 period-three one-step-rigid states",
        "orbit_index":14,
        "orbit_size":orbit_size,
        "columns":list(cols),
        "states":len(rows),
        "omitted_label":6,
        "omitted_point":cols[6],
        "classification":{
            "direct_blocker_saturation":{
                "states":12,
                "endpoint_pair_blockers":2,
                "blocker_closure_sizes":[4,6,6],
                "saturated_flats_through_e":3,
            },
            "indirect_saturation":{
                "states":4,
                "endpoint_pair_blockers":3,
                "blocker_closure_sizes":[4,4,4],
                "saturated_flats_through_e":3,
                "unique_blocker_kill_swaps":3,
                "each_swap_fails_both_changed_windows":True,
                "failure_flats":6,
                "failure_flat_size":5,
                "failure_flats_avoid_e":True,
                "pair_intersections_generate_saturated_flats":3,
                "each_saturated_flat_generated_twice":True,
            },
        },
        "interpretation":(
            "The only exact period-three states in which no visible blocker "
            "closure is saturated are four highly symmetric states. In each, "
            "all three blocker endpoint pairs already span the omitted element. "
            "The three natural adjacent blocker-killing swaps each fail on both "
            "boundary windows, producing six five-point rank-three flats avoiding "
            "e. Pairwise intersections of these failure flats recover exactly the "
            "three saturated six-point rank-three flats through e."
        ),
        "claim_level":"exact finite computation; not Lean certification",
    }
    print(json.dumps(out,indent=2,sort_keys=True))


if __name__=="__main__":
    main()
