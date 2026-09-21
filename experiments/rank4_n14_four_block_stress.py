#!/usr/bin/env python3
"""Seeded n=14 t=0 four-block repair stress.

Builds ten binary rank-4 n=14 multisets satisfying the exact t=0 /
two-deletion flat caps (3,6,9):
  * five ordinary random qualifying multisets;
  * five deliberately containing a 3-element parallel class.

For each matroid, selects ten deterministic bad states and searches up to
depth three using:
  * adjacent CBO-preserving swaps;
  * point pivots;
  * every CBO-preserving permutation of four consecutive order positions.

Finite seeded computation only; not Lean certification.
"""

from collections import Counter, deque
from itertools import permutations
import random, json

import rank4_binary_n12_nonsimple_exact as base

P=tuple(range(1,16))
ALL4=tuple(p for p in permutations(range(4)) if p!=(0,1,2,3))

def canonical(o):
    o=tuple(o); i=o.index(min(o)); return o[i:]+o[:i]

def profile(cols):
    c=[0]*15
    for x in cols:c[x-1]+=1
    def occ(F):return sum(c[x-1] for x in F)
    return max(c),max(map(occ,base.LINES)),max(map(occ,base.HYPERPLANES))

def robust(cols):
    p=profile(cols)
    return base.rank2(cols)==4 and p[0]<=3 and p[1]<=6 and p[2]<=9

def cbo(o,cols):
    m=len(o)
    return all(base.rank2([cols[o[(i+j)%m]] for j in range(4)])==4 for i in range(m))

def success(s,cols):
    e,o=s
    for g in range(len(o)):
        a=list(o);a.insert(g,e)
        if cbo(a,cols):return True
    return False

def random_cbo(cols,e,rng,attempts=100):
    labs=[i for i in range(14) if i!=e]
    for _ in range(attempts):
        rng.shuffle(labs)
        o=tuple(labs)
        if cbo(o,cols):return canonical(o)
    return None

def neighbors(s,cols):
    e,o=s;m=len(o);out=set()
    for i in range(m):
        j=(i+1)%m;a=list(o);a[i],a[j]=a[j],a[i]
        t=(e,canonical(a))
        if cbo(t[1],cols):out.add(t)
    for st in range(m):
        inds=[(st+j)%m for j in range(4)];vals=[o[i] for i in inds]
        for p in ALL4:
            a=list(o)
            for dst,src in enumerate(p):a[inds[dst]]=vals[src]
            t=(e,canonical(a))
            if cbo(t[1],cols):out.add(t)
    for i,f in enumerate(o):
        a=list(o);a[i]=e;t=(f,canonical(a))
        if cbo(t[1],cols):out.add(t)
    return out

def distance(s,cols,maxdepth=3):
    q=deque([(s,0)]);seen={s}
    while q:
        u,d=q.popleft()
        if d>=maxdepth:continue
        for v in neighbors(u,cols):
            if v in seen:continue
            seen.add(v)
            if success(v,cols):return d+1
            q.append((v,d+1))
    return None

def sample_random():
    rng=random.Random(141414);out=[]
    while len(out)<5:
        cols=tuple(rng.choice(P) for _ in range(14))
        if robust(cols):out.append(cols)
    return out

def sample_triple():
    rng=random.Random(424242);out=[]
    while len(out)<5:
        x=rng.choice(P)
        cols=tuple([x,x,x]+[rng.choice(P) for _ in range(11)])
        if max(Counter(cols).values())==3 and robust(cols):out.append(cols)
    return out

def bad_states(cols,seed):
    rng=random.Random(seed);out=[];attempts=0
    while len(out)<10 and attempts<10000:
        attempts+=1;e=rng.randrange(14);o=random_cbo(cols,e,rng)
        if o is None:continue
        s=(e,o)
        if not success(s,cols) and s not in out:out.append(s)
    assert len(out)==10
    return out

def main():
    mats=[("random",x) for x in sample_random()]+[("forced_triple",x) for x in sample_triple()]
    hist=Counter();rows=[]
    for i,(kind,cols) in enumerate(mats):
        ds=[distance(s,cols) for s in bad_states(cols,1400+i if kind=="random" else 2400+i-5)]
        assert all(d is not None for d in ds)
        hist.update(ds)
        rows.append({"sample":i,"kind":kind,"profile":list(profile(cols)),"distances":ds})
    print(json.dumps({
      "matroids":10,"bad_states":100,
      "distance_histogram":dict(sorted(hist.items())),
      "maximum_observed_distance":max(hist),
      "rows":rows,
      "interpretation":(
        "All sampled n=14 t=0 bad states escape within three all-four-block "
        "moves/pivots, including forced triple parallel classes and cap-saturating "
        "profiles (3,6,9)."
      ),
      "claim_level":"seeded finite computation; not exhaustive and not Lean certified"
    },indent=2,sort_keys=True))

if __name__=="__main__":
    main()
