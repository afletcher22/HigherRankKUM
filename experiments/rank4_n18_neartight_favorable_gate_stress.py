#!/usr/bin/env python3
"""Seeded n=18 audit of the near-tight favorable Type-I gate conjecture.

Reuses the 730 deterministic bad type-states from
rank4_n18_four_block_type_stress.py.  For each state, with the omitted type
held fixed, enumerate all arbitrary four-block permutations.

A state is one-step rigid when no CBO-preserving four-block permutation makes
the blocker word favorable.  For each such state inspect every Type-I boundary
failure among the would-be favorable permutations and measure the ambient
rank-three hyperplane with multiplicity in the original 18-element matroid.

At k=4 the conjectured threshold is 3k-1 = 11.

Seeded finite computation; not exhaustive and not Lean certification.
"""

from collections import Counter
from itertools import permutations
import json

import rank4_n18_four_block_type_stress as hist

V=hist.V
TYPES=hist.TYPES
ALL4=hist.ALL4
K=4
THRESHOLD=3*K-1


def blocker_word(e,s):
    n=len(s); out=[]
    for i in range(n):
        tri=tuple(s[(i+j)%n] for j in range(3))
        out.append(int(hist.rank(tri+(e,)) == hist.rank(tri)))
    return tuple(out)


def favorable(e,s):
    b=blocker_word(e,s);n=len(b)
    return any(all(b[(i+j)%n]==0 for j in range(4)) for i in range(n))


def hyperplane_occupancy(common):
    assert len(common)==3
    assert hist.rank(common)==3
    return sum(hist.rank(common+(x,))==3 for x in V)


def type1_failed_gate_sizes(old,new):
    n=len(old); out=[]
    for i in range(n):
        oldw=tuple(old[(i+j)%n] for j in range(4))
        neww=tuple(new[(i+j)%n] for j in range(4))
        if hist.rank(neww)==4:
            continue
        co=Counter(oldw); cn=Counter(neww)
        common=co & cn
        if sum(common.values()) != 3:
            continue
        common_tuple=tuple(common.elements())
        if hist.rank(common_tuple)!=3:
            continue
        removed=co-common; added=cn-common
        if sum(removed.values())!=1 or sum(added.values())!=1:
            continue
        out.append((i,hyperplane_occupancy(common_tuple)))
    return out


def audit_state(e,s):
    n=len(s); any_legal_favorable=False; sizes=[]
    for q in range(n):
        ii=[(q+j)%n for j in range(4)]
        z=[s[i] for i in ii]
        for p in ALL4:
            a=list(s)
            for d,src in enumerate(p):
                a[ii[d]]=z[src]
            a=tuple(a)
            if not favorable(e,a):
                continue
            if hist.cbo(a):
                any_legal_favorable=True
                return False,None
            sizes.extend(x[1] for x in type1_failed_gate_sizes(s,a))
    return True,max(sizes) if sizes else 0


def main():
    bad={}
    for e in TYPES:
        S=set()
        for j in range(120):
            s=hist.find_cbo(e,1000+j)
            if s is not None and hist.gaps(e,s)==0:
                S.add(hist.canon(s))
        bad[e]=S
    assert sum(map(len,bad.values()))==730

    rigid=0; histo=Counter(); no_type1=0; counterexamples=[]
    by_e=Counter()
    minmax=10**9

    for e,S in bad.items():
        for s in S:
            isrigid,m=audit_state(e,s)
            if not isrigid:
                continue
            rigid+=1;by_e[e]+=1
            if not m:
                no_type1+=1
                counterexamples.append({
                    "omitted_type":e,"order":list(s),"reason":"no Type-I gate"
                })
                continue
            histo[m]+=1;minmax=min(minmax,m)
            if m<THRESHOLD:
                counterexamples.append({
                    "omitted_type":e,
                    "order":list(s),
                    "blocker_word":"".join(map(str,blocker_word(e,s))),
                    "max_gate_size":m,
                })

    assert rigid>0
    assert not counterexamples
    assert no_type1==0
    assert minmax>=THRESHOLD

    print(json.dumps({
        "scope":"historical strict binary t=0 n=18 witness; seeded bad type-states",
        "seeded_bad_states":730,
        "fixed_e_one_step_rigid_states":rigid,
        "threshold":THRESHOLD,
        "minimum_max_failed_favorable_type1_gate_size":minmax,
        "max_gate_size_histogram":dict(sorted(histo.items())),
        "rigid_by_omitted_type":dict(sorted((str(k),v) for k,v in by_e.items())),
        "states_with_no_failed_favorable_type1_gate":no_type1,
        "counterexamples":counterexamples,
        "interpretation":(
            "Every seeded fixed-e one-step-rigid state in the historical n=18 "
            "witness exposes a failed favorable Type-I gate whose ambient "
            "rank-three hyperplane has size at least 3k-1=11."
        ),
        "claim_level":"seeded finite computation; not exhaustive and not Lean certification",
    },indent=2,sort_keys=True))


if __name__=="__main__":
    main()
