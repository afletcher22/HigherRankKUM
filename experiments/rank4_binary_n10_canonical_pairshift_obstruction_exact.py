#!/usr/bin/env python3
"""Exact canonical pair-shift obstruction audit on the hard binary n=10 orbit.

For every omitted label and bad deletion CBO in orbit index 2, test the two
canonical four-block patterns:
  pair shift     (2,3,0,1): [a,b,c,d] -> [c,d,a,b]
  canonical twist(2,3,1,0): [a,b,c,d] -> [c,d,b,a]

Boundary offsets -3,-1,+1,+3 are one-element exchanges. Offsets -2,+2 are
two-element exchanges. Invalid moves are classified according to whether a
failed single-exchange boundary exists, a failed double-exchange boundary
exists, or the failure is visible only at the double boundaries.

Finite exact computation; not Lean certification.
"""

import json
import rank4_binary_n10_nonsimple_exact as base

PAIR_SHIFT = (2,3,0,1)
CANONICAL_TWIST = (2,3,1,0)
SINGLE = {-3,-1,1,3}
DOUBLE = {-2,2}


def permute_block(order,start,patt):
    a=list(order); n=len(a)
    inds=[(start+j)%n for j in range(4)]
    old=[order[i] for i in inds]
    for dst,src in enumerate(patt):
        a[inds[dst]]=old[src]
    return tuple(a)


def failed_offsets(columns,order,start,patt):
    new=permute_block(order,start,patt); n=len(order)
    out=[]
    for off in (-3,-2,-1,1,2,3):
        i=(start+off)%n
        vals=tuple(columns[new[(i+j)%n]] for j in range(4))
        if base.rank2(vals) != 4:
            out.append(off)
    return tuple(out)


def audit(columns,patt):
    rows=[]
    for omitted in range(10):
        orders=base.deletion_cbos(columns,omitted)
        bad=[o for o in orders if not base.successful(columns,(omitted,o))]
        valid=invalid=single_only=double_only=both=0
        for order in bad:
            for start in range(len(order)):
                new=permute_block(order,start,patt)
                if base.cbo(new,columns):
                    valid+=1
                    continue
                invalid+=1
                fs=failed_offsets(columns,order,start,patt)
                hs=any(x in SINGLE for x in fs)
                hd=any(x in DOUBLE for x in fs)
                assert hs or hd
                if hs and hd: both+=1
                elif hs: single_only+=1
                else: double_only+=1
        rows.append({
            "omitted_label":omitted,
            "deletion_cbos":len(orders),
            "bad_states":len(bad),
            "valid_attempts":valid,
            "invalid_attempts":invalid,
            "invalid_single_only":single_only,
            "invalid_double_only":double_only,
            "invalid_both":both,
        })
    return rows


def main():
    patterns,_=base.qualifying_patterns()
    reps=base.orbit_representatives(patterns)
    counts,orbit_size=reps[2]
    columns=base.labelled_columns(counts)
    assert columns==(7,9,10,11,12,13,14,14,15,15)

    pair=audit(columns,PAIR_SHIFT)
    twist=audit(columns,CANONICAL_TWIST)

    assert all(r["valid_attempts"]==0 for r in pair)
    assert sum(r["invalid_double_only"] for r in pair) > 0
    assert sum(r["invalid_double_only"] for r in twist) > 0
    assert twist[6]["valid_attempts"]==120
    assert twist[7]["valid_attempts"]==120

    print(json.dumps({
      "scope":"exact hard binary n=10 GL(4,2) orbit index 2",
      "orbit_size":orbit_size,
      "columns":list(columns),
      "single_exchange_offsets":[-3,-1,1,3],
      "double_exchange_offsets":[-2,2],
      "pair_shift":{"pattern":list(PAIR_SHIFT),"rows":pair},
      "canonical_twist":{"pattern":list(CANONICAL_TWIST),"rows":twist},
      "interpretation":(
        "The pair shift is never CBO-preserving from a bad state in this "
        "orbit, while the canonical twist has some valid moves. Both patterns "
        "have invalid attempts witnessed only at the double-exchange boundary "
        "windows. Therefore single-exchange closure rigidity alone cannot "
        "handle the canonical moves; the rank-two contraction/common-base "
        "branch is genuinely necessary."
      ),
      "claim_level":"exact finite computation; not Lean certification",
    },indent=2,sort_keys=True))


if __name__=="__main__":
    main()
