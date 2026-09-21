#!/usr/bin/env python3
"""Fixed-e four-block stress on the historical strict n=14 t=0 witness.

Witness from the deletion/insertion research report, repository label order:

    (4,12,10,11,4,6,10,15,6,11,7,15,3,14)

For every omitted label e=0,...,13:
  * deterministically sample five bad deletion CBOs;
  * hold e fixed throughout;
  * allow only arbitrary CBO-preserving permutations of four consecutive
    positions;
  * search breadth-first to depth four for an insertion-successful CBO.

No point pivots are used.

Finite seeded computation; not exhaustive and not Lean certification.
"""
from collections import deque, Counter
from itertools import permutations
import random, json

M=(4,12,10,11,4,6,10,15,6,11,7,15,3,14)
ALL4=tuple(p for p in permutations(range(4)) if p!=(0,1,2,3))

def rank2(vals):
    piv=[0]*4; r=0
    for value in vals:
        x=value
        while x:
            i=x.bit_length()-1
            if piv[i]:
                x ^= piv[i]
            else:
                piv[i]=x
                r += 1
                break
    return r

def cbo(order):
    m=len(order)
    return all(rank2([M[order[(i+j)%m]] for j in range(4)])==4
               for i in range(m))

def canonical(order):
    order=tuple(order)
    k=order.index(min(order))
    return order[k:]+order[:k]

def successful(e,order):
    for gap in range(len(order)):
        full=list(order)
        full.insert(gap,e)
        if cbo(full):
            return True
    return False

def random_cbo(e,rng,tries=30):
    labels=[i for i in range(14) if i!=e]
    for _ in range(tries):
        rng.shuffle(labels)
        if cbo(labels):
            return canonical(labels)
    return None

def neighbors(order):
    out=set(); m=len(order)
    for start in range(m):
        inds=[(start+j)%m for j in range(4)]
        old=[order[i] for i in inds]
        for patt in ALL4:
            a=list(order)
            for dst,src in enumerate(patt):
                a[inds[dst]]=old[src]
            t=canonical(a)
            if t != order and cbo(t):
                out.add(t)
    return out

def distance_to_success(e,start,maxdepth=4):
    if successful(e,start):
        return 0
    q=deque([(start,0)])
    seen={start}
    while q:
        u,d=q.popleft()
        if d>=maxdepth:
            continue
        for v in neighbors(u):
            if v in seen:
                continue
            seen.add(v)
            if successful(e,v):
                return d+1
            q.append((v,d+1))
    return None

def main():
    rng=random.Random(20260921)
    rows=[]
    hist=Counter()
    for e in range(14):
        bad=[]
        attempts=0
        while len(bad)<5 and attempts<10000:
            attempts+=1
            o=random_cbo(e,rng)
            if o is not None and not successful(e,o) and o not in bad:
                bad.append(o)
        assert len(bad)==5
        ds=[distance_to_success(e,o) for o in bad]
        assert all(d is not None for d in ds)
        hist.update(ds)
        rows.append({"omitted_label":e,"distances":ds})
    assert sum(hist.values())==70
    print(json.dumps({
      "witness_columns":list(M),
      "scope":"historical strict n=14 t=0 witness",
      "seed":20260921,
      "bad_states":70,
      "bad_states_per_omitted_label":5,
      "moves":"arbitrary CBO-preserving four-consecutive-position permutations; omitted element fixed; no pivots",
      "distance_histogram":dict(sorted(hist.items())),
      "maximum_observed_distance":max(hist),
      "rows":rows,
      "interpretation":"All sampled bad states for every omitted label repair without changing the omitted element.",
      "claim_level":"seeded finite computation; not exhaustive and not Lean certification"
    },indent=2,sort_keys=True))

if __name__=="__main__":
    main()
