#!/usr/bin/env python3
"""Constructive saturated-flat gluing stress for rank-4 t=0.

Tests the fixed binary skeleton

    (HHHR)^(k-2)  HHHR HR HH RR

where H is a rank-three saturated flat of size 3k and R is its complement of
size k+2.  For every k>=2 this skeleton has 3k H-slots and k+2 R-slots,
every cyclic rank-four window has one or two R-slots, and exactly six windows
have two R-slots.

Audits:
  1. exact hard binary n=10 orbit index 2: all five rank-three flats of size 6;
  2. the recorded historical binary n=18 depth-three bad state: all three
     distinct saturated rank-three flats of size 12.

For each flat, exhaustively enumerate rank-three CBO type/orders (modulo one
rotation normalization) and complement permutations until the fixed skeleton
produces a full rank-four CBO.

Finite computation only; not Lean certification and not a general theorem.
"""

from collections import Counter
from itertools import combinations, permutations
import json

N10 = (7,9,10,11,12,13,14,14,15,15)

N18 = (1,2,4,8,9,6,2,8,1,4,3,12,1,8,2,4,5,10)
N18_HARD_OMITTED = 1
N18_HARD_ORDER = (
    1,2,4,12,9,10,1,4,8,2,3,4,8,5,2,6,8
)


def rank(vals):
    piv=[0]*4
    r=0
    for v in vals:
        x=v
        while x:
            i=x.bit_length()-1
            if piv[i]:
                x ^= piv[i]
            else:
                piv[i]=x
                r += 1
                break
    return r


def skeleton(k):
    assert k >= 2
    return (0,0,0,1)*(k-2) + (0,0,0,1,0,1,0,0,1,1)


def cbo_vals(order, r):
    n=len(order)
    return all(rank(order[(i+j)%n] for j in range(r)) == r
               for i in range(n))


def assemble(pattern, horder, rorder):
    hi=ri=0
    out=[]
    for bit in pattern:
        if bit == 0:
            out.append(horder[hi]); hi += 1
        else:
            out.append(rorder[ri]); ri += 1
    assert hi == len(horder) and ri == len(rorder)
    return tuple(out)


def unique_perms_multiset(counter):
    counter=counter.copy()
    items=sorted(counter)
    n=sum(counter.values())
    out=[]
    path=[]
    def rec():
        if len(path)==n:
            out.append(tuple(path))
            return
        for x in items:
            if counter[x]:
                counter[x]-=1
                path.append(x)
                rec()
                path.pop()
                counter[x]+=1
    rec()
    return out


def rank3_cbos_multiset(counter):
    """All rank-3 CBO type-orders with one rotation normalized."""
    counter=counter.copy()
    items=sorted(counter)
    n=sum(counter.values())
    first=items[0]
    counter[first]-=1
    path=[first]
    out=[]
    def rec():
        if len(path)==n:
            if cbo_vals(path,3):
                out.append(tuple(path))
            return
        for x in items:
            if counter[x]:
                if len(path)>=2 and rank((path[-2],path[-1],x)) < 3:
                    continue
                counter[x]-=1
                path.append(x)
                rec()
                path.pop()
                counter[x]+=1
    rec()
    return out


def find_multiset_witness(full_counter, hcounter, k):
    horders=rank3_cbos_multiset(hcounter)
    rcounter=full_counter.copy()
    for x,m in hcounter.items():
        rcounter[x]-=m
    rcounter=Counter({x:m for x,m in rcounter.items() if m})
    rorders=unique_perms_multiset(rcounter)
    patt=skeleton(k)
    for ho in horders:
        for t in range(len(ho)):
            hor=ho[t:]+ho[:t]
            for ro in rorders:
                full=assemble(patt,hor,ro)
                if cbo_vals(full,4):
                    return {
                        "rank3_cbo_count_rotation_normalized":len(horders),
                        "complement_permutations":len(rorders),
                        "h_order":list(hor),
                        "r_order":list(ro),
                        "full_order":list(full),
                    }
    return None


def n10_audit():
    def rlabels(labels):
        return rank(N10[i] for i in labels)
    def closure(labels):
        rr=rlabels(labels)
        vals=[N10[i] for i in labels]
        return frozenset(
            i for i in range(10)
            if rank(vals+[N10[i]]) == rr
        )

    flats=set()
    for T in combinations(range(10),3):
        if rlabels(T)==3:
            H=closure(T)
            if len(H)==6:
                flats.add(H)
    assert len(flats)==5

    patt=skeleton(2)
    assert sum(patt)==4 and len(patt)-sum(patt)==6
    counts=[sum(patt[(i+j)%len(patt)] for j in range(4))
            for i in range(len(patt))]
    assert min(counts)==1 and max(counts)==2 and counts.count(2)==6

    rows=[]
    for H in sorted(flats,key=lambda x:tuple(sorted(x))):
        horders=[]
        h0=min(H)
        for p in permutations(sorted(H-{h0})):
            o=(h0,)+p
            if all(rlabels([o[(i+j)%6] for j in range(3)])==3
                   for i in range(6)):
                horders.append(o)
        R=sorted(set(range(10))-set(H))
        witness=None
        for ho in horders:
            for t in range(6):
                hor=ho[t:]+ho[:t]
                for ro in permutations(R):
                    full=assemble(patt,hor,ro)
                    if all(rlabels([full[(i+j)%10] for j in range(4)])==4
                           for i in range(10)):
                        witness={
                          "h_order":list(hor),
                          "r_order":list(ro),
                          "full_order":list(full),
                        }
                        break
                if witness: break
            if witness: break
        assert witness is not None
        rows.append({
          "flat_labels":sorted(H),
          "rank3_cbo_count_rotation_normalized":len(horders),
          **witness,
        })
    return {
      "scope":"exact hard binary n=10 orbit index 2",
      "k":2,
      "columns":list(N10),
      "saturated_flats":len(rows),
      "all_fixed_skeleton_success":True,
      "rows":rows,
    }


def n18_saturated_flats():
    e=N18_HARD_OMITTED
    s=N18_HARD_ORDER
    assert len(s)==17 and Counter(s)==Counter(N18)-Counter({e:1})
    assert cbo_vals(s,4)

    flats={}
    for i in range(len(s)):
        tri=[s[(i+j)%len(s)] for j in range(3)]
        if rank(tri+[e]) != rank(tri):
            continue
        rr=rank(tri)
        H=[v for v in N18 if rank(tri+[v])==rr]
        if len(H)==12:
            key=tuple(sorted(Counter(H).items()))
            flats[key]=Counter(H)
    assert len(flats)==3
    return list(flats.values())


def n18_audit():
    patt=skeleton(4)
    counts=[sum(patt[(i+j)%len(patt)] for j in range(4))
            for i in range(len(patt))]
    assert len(patt)==18
    assert patt.count(0)==12 and patt.count(1)==6
    assert min(counts)==1 and max(counts)==2 and counts.count(2)==6

    rows=[]
    fullc=Counter(N18)
    for hc in n18_saturated_flats():
        w=find_multiset_witness(fullc,hc,4)
        assert w is not None
        rows.append({
          "flat_multiplicities":dict(sorted(hc.items())),
          **w,
        })
    return {
      "scope":"historical binary n=18 depth-three state",
      "k":4,
      "omitted_type":N18_HARD_OMITTED,
      "bad_order":list(N18_HARD_ORDER),
      "saturated_flats":len(rows),
      "all_fixed_skeleton_success":True,
      "rows":rows,
    }


def main():
    out={
      "skeleton_formula":"(HHHR)^(k-2) HHHR HR HH RR",
      "skeleton_encoding":"H=0, R=1",
      "structural_check":{
        "for_tested_k":[2,4],
        "rank_four_windows_have_R_count":[1,2],
        "two_R_windows":6,
      },
      "n10":n10_audit(),
      "n18":n18_audit(),
      "interpretation":(
        "Every saturated flat tested can be solved directly by first choosing "
        "a rank-three CBO of H and then interleaving its complement with the "
        "same six-defect skeleton. This supports replacing the terminal "
        "'saturation then oversaturate' strategy by a constructive saturated-"
        "flat gluing theorem. The only non-periodic obligations are the six "
        "2H+2R windows."
      ),
      "claim_level":(
        "n10 exact for all five saturated flats in the hard orbit; "
        "n18 finite audit for all three saturated flats of the recorded "
        "historical depth-three state; not Lean certified"
      ),
    }
    print(json.dumps(out,indent=2,sort_keys=True))


if __name__=="__main__":
    main()
