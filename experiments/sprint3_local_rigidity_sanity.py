#!/usr/bin/env python3
"""Exact normalized local audit for rank-four adjacent repair over GF(2)^4.

This is deliberately small.  Fix consecutive pair blocks
A=(1,2), B=(4,8), enumerate unordered nonzero-vector pairs C,D, require the
three aligned unions A∪B, B∪C, C∪D to be bases and both neighboring shifted
orientation relations to be forced bijections.  Then count all six ordered
2+2 repartitions of B∪C that preserve the two affected aligned bases.

The certificate exists to prevent witness-specific properties of the 18-element
component from being promoted to universal claims.
"""
import json
from collections import Counter
from itertools import combinations

A=(1,2)
B=(4,8)
PAIRS=tuple(combinations(range(1,16),2))

def rank_f2(vals):
    basis=[0]*4
    r=0
    for x in vals:
        y=x
        while y:
            p=y.bit_length()-1
            if basis[p]:
                y^=basis[p]
            else:
                basis[p]=y
                r+=1
                break
    return r

def is_base4(vals):
    vals=tuple(vals)
    return len(vals)==4 and rank_f2(vals)==4

def relation(left,core,right):
    return tuple(tuple(is_base4((left[a],core[0],core[1],right[b]))
                       for b in (0,1)) for a in (0,1))

def forced_bijection(R):
    return (sum(sum(row) for row in R)==2
            and all(any(row) for row in R)
            and all(any(R[a][b] for a in (0,1)) for b in (0,1)))

def valid_repartitions(C,D):
    vals=B+C  # four labelled slots; repeated vector values remain distinct slots
    out=[]
    for inds_tuple in combinations(range(4),2):
        inds=frozenset(inds_tuple)
        Q=tuple(vals[i] for i in range(4) if i in inds)
        Qc=tuple(vals[i] for i in range(4) if i not in inds)
        if is_base4(A+Q) and is_base4(Qc+D):
            out.append(tuple(sorted(inds)))
    return tuple(out)

def closure_count(core,pair):
    r=rank_f2(core)
    return sum(rank_f2(core+(x,))==r for x in pair)

def main():
    total=0
    repart_hist=Counter()
    rigid_side_hist=Counter()
    examples={}
    for C in PAIRS:
        for D in PAIRS:
            if not (is_base4(A+B) and is_base4(B+C) and is_base4(C+D)):
                continue
            Rleft=relation(A,B,C)
            Rright=relation(B,C,D)
            if not (forced_bijection(Rleft) and forced_bijection(Rright)):
                continue
            total+=1
            valid=valid_repartitions(C,D)
            repart_hist[len(valid)]+=1
            if len(valid)==1:
                left=closure_count(A,C)   # C-elements spanned by left core A
                right=closure_count(D,B)  # B-elements spanned by right core D
                side=('both' if left and right else
                      'left_only' if left else
                      'right_only' if right else 'neither')
                rigid_side_hist[side]+=1
                examples.setdefault(side,{
                    'C':C,'D':D,
                    'left_relation':Rleft,'right_relation':Rright,
                    'valid_repartitions':valid,
                    'left_closure_count':left,'right_closure_count':right,
                })
    assert total==256
    assert repart_hist==Counter({1:79,2:102,3:40,4:30,5:5})
    assert rigid_side_hist==Counter({'both':33,'left_only':23,'right_only':23})
    assert examples['left_only']['C']==(1,2) and examples['left_only']['D']==(5,9)
    out={
        'scope':'normalized four-block GF(2)^4 local audit; not a global matroid search',
        'fixed_A':A,'fixed_B':B,
        'forced_neighbor_local_configurations':total,
        'valid_repartition_count_histogram':dict(sorted(repart_hist.items())),
        'rigid_closure_side_histogram':dict(sorted(rigid_side_hist.items())),
        'left_only_rigid_example':examples['left_only'],
        'right_only_rigid_example':examples['right_only'],
        'status':'exact finite anti-overgeneralization certificate',
    }
    print(json.dumps(out,indent=2))

if __name__=='__main__':
    main()
