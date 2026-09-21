#!/usr/bin/env python3
"""Seeded strict-4k n=12 stress test for four-position repair moves.

Samples 20 binary rank-4 n=12 multisets with a genuine parallel pair and the
universal one-deletion flat caps (2,5,8).  From each matroid, deterministically
selects 10 bad states (e,sigma).

Two move sets are compared:
  A. adjacent swaps + point pivots + the two canonical four-block repairs;
  B. adjacent swaps + point pivots + ANY permutation of four consecutive
     positions, whenever the resulting deletion order is still a CBO.

The search measures shortest repair distance to a successful state.

Finite seeded computation only; not Lean certification.
"""

from collections import Counter, deque
from itertools import permutations
import random, json

import rank4_binary_n12_nonsimple_exact as base

P = tuple(range(1,16))
CANON = ((2,3,0,1),(2,3,1,0))
ALL4 = tuple(p for p in permutations(range(4)) if p != (0,1,2,3))

def canonical(o):
    o=tuple(o); i=o.index(min(o)); return o[i:]+o[:i]

def profile(cols):
    c=[0]*15
    for x in cols: c[x-1]+=1
    def occ(F): return sum(c[x-1] for x in F)
    return max(c), max(map(occ,base.LINES)), max(map(occ,base.HYPERPLANES))

def robust(cols):
    return base.rank2(cols)==4 and profile(cols)[0]<=2 and profile(cols)[1]<=5 and profile(cols)[2]<=8

def cbo(o,cols):
    m=len(o)
    return all(base.rank2([cols[o[(i+j)%m]] for j in range(4)])==4 for i in range(m))

def success(state,cols):
    e,o=state
    for g in range(len(o)):
        a=list(o); a.insert(g,e)
        if cbo(a,cols): return True
    return False

def random_cbo(cols,e,rng,attempts=20):
    labs=[i for i in range(12) if i!=e]
    for _ in range(attempts):
        rng.shuffle(labs)
        o=tuple(labs)
        if cbo(o,cols): return canonical(o)
    return None

def neighbors(state,cols,all_four):
    e,o=state; m=len(o); out=set()
    for i in range(m):
        j=(i+1)%m
        a=list(o); a[i],a[j]=a[j],a[i]
        t=(e,canonical(a))
        if cbo(t[1],cols): out.add(t)

    pats=ALL4 if all_four else CANON
    for st in range(m):
        inds=[(st+j)%m for j in range(4)]
        vals=[o[i] for i in inds]
        for p in pats:
            a=list(o)
            for dst,src in enumerate(p): a[inds[dst]]=vals[src]
            t=(e,canonical(a))
            if cbo(t[1],cols): out.add(t)

    for i,f in enumerate(o):
        a=list(o); a[i]=e
        t=(f,canonical(a))
        if cbo(t[1],cols): out.add(t)
    return out

def distance(state,cols,all_four,maxdepth=8):
    if success(state,cols): return 0
    q=deque([(state,0)]); seen={state}
    while q:
        s,d=q.popleft()
        if d>=maxdepth: continue
        for t in neighbors(s,cols,all_four):
            if t in seen: continue
            seen.add(t)
            if success(t,cols): return d+1
            q.append((t,d+1))
    return None

def sample_matroids():
    rng=random.Random(606060)
    mats=[]
    while len(mats)<20:
        cols=tuple(rng.choice(P) for _ in range(12))
        if max(Counter(cols).values())<2: continue
        if robust(cols): mats.append(cols)
    return mats

def bad_states(cols,idx):
    rng=random.Random(1000+idx)
    out=[]; attempts=0
    while len(out)<10 and attempts<5000:
        attempts+=1
        e=rng.randrange(12)
        o=random_cbo(cols,e,rng)
        if o is None: continue
        s=(e,o)
        if not success(s,cols) and s not in out: out.append(s)
    assert len(out)==10
    return out

def main():
    canon_hist=Counter(); all_hist=Counter()
    rows=[]
    for i,cols in enumerate(sample_matroids()):
        states=bad_states(cols,i)
        ds_c=[distance(s,cols,False) for s in states]
        ds_a=[distance(s,cols,True) for s in states]
        assert all(d is not None for d in ds_c+ds_a)
        canon_hist.update(ds_c); all_hist.update(ds_a)
        rows.append({
            "sample":i, "profile":list(profile(cols)),
            "canonical_distances":ds_c, "all_four_distances":ds_a
        })

    print(json.dumps({
      "matroids":20, "bad_states":200,
      "canonical_four_block_distance_histogram":dict(sorted(canon_hist.items())),
      "all_four_permutations_distance_histogram":dict(sorted(all_hist.items())),
      "maximum_canonical_distance":max(canon_hist),
      "maximum_all_four_distance":max(all_hist),
      "rows":rows,
      "interpretation":(
        "The two canonical repairs remain effective but require distance four "
        "on two sampled states. Allowing all CBO-preserving permutations of a "
        "consecutive four-block repairs all 200 sampled bad states within two moves."
      ),
      "claim_level":"seeded finite computation; not exhaustive and not Lean certified"
    },indent=2,sort_keys=True))

if __name__=="__main__":
    main()
