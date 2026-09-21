#!/usr/bin/env python3
"""Seeded type-state stress test on the historical strict t=0 n=18 witness.

Witness columns:
  (1,2,4,8,9,6,2,8,1,4,3,12,1,8,2,4,5,10)

We quotient only by relabelling parallel copies and cyclic rotation.  For each
projective vector type that occurs, 120 deterministic randomized DFS runs find
a deletion CBO; distinct bad type-orders are retained.

Moves on states (e, sigma):
  * CBO-preserving adjacent cyclic swaps;
  * point pivots;
  * either TWO canonical 4-block patterns
      [a,b,c,d] -> [c,d,a,b], [c,d,b,a],
    or ALL nonidentity permutations of four consecutive positions.

Result at the recorded seed set:
  * 730 distinct bad type-states;
  * with the two canonical patterns, 3 states lie in three closed all-bad
    components of size 8 (omitted types 1,4,8);
  * with all four-block permutations, all 730 reach success by depth <=3.

This is seeded finite computation, not exhaustive over all deletion CBOs and
not Lean certification.
"""

from collections import Counter, deque
from functools import lru_cache
from itertools import permutations
import json, random

V = (1,2,4,8,9,6,2,8,1,4,3,12,1,8,2,4,5,10)
TYPES = tuple(sorted(set(V)))
IDX = {x:i for i,x in enumerate(TYPES)}
BASE = tuple(Counter(V)[x] for x in TYPES)
CANON = ((2,3,0,1),(2,3,1,0))
ALL4 = tuple(p for p in permutations(range(4)) if p != (0,1,2,3))

def rank(vals):
    piv=[0]*4; r=0
    for v in vals:
        x=v
        while x:
            i=x.bit_length()-1
            if piv[i]: x ^= piv[i]
            else:
                piv[i]=x; r+=1; break
    return r

def cbo(s):
    n=len(s)
    return all(rank(s[(i+j)%n] for j in range(4)) == 4 for i in range(n))

def canon(s):
    s=tuple(s); n=len(s)
    return min(s[i:]+s[:i] for i in range(n))

def gaps(e,s):
    out=0
    for i in range(len(s)):
        a=list(s); a.insert(i,e)
        out += cbo(a)
    return out

def find_cbo(e, seed):
    counts=list(BASE); counts[IDX[e]]-=1
    rng=random.Random(seed)
    starts=[]
    for a in range(len(TYPES)):
      for b in range(len(TYPES)):
       for c in range(len(TYPES)):
        cc=Counter((a,b,c))
        if any(cc[t] > counts[t] for t in cc): continue
        if rank((TYPES[a],TYPES[b],TYPES[c])) == 3: starts.append((a,b,c))
    rng.shuffle(starts)
    for st in starts:
        rem=list(counts)
        for x in st: rem[x]-=1
        path=list(st); dead=set()
        def rec(rm,last):
            key=(rm,last)
            if key in dead: return None
            if sum(rm)==0:
                s=tuple(TYPES[i] for i in path)
                return s if cbo(s) else None
            opts=[i for i,c in enumerate(rm)
                  if c and rank((TYPES[last[0]],TYPES[last[1]],
                                 TYPES[last[2]],TYPES[i])) == 4]
            rng.shuffle(opts)
            for x in opts:
                nr=list(rm); nr[x]-=1; path.append(x)
                z=rec(tuple(nr),(last[1],last[2],x))
                if z is not None: return z
                path.pop()
            dead.add(key); return None
        z=rec(tuple(rem),st)
        if z is not None: return z
    return None

def nbrs(state, patterns):
    e,s=state; s=list(s); n=len(s); out=set()
    for i in range(n):
        j=(i+1)%n; a=s.copy(); a[i],a[j]=a[j],a[i]
        if cbo(a): out.add((e,canon(a)))
    for i,f in enumerate(s):
        if f == e: continue
        a=s.copy(); a[i]=e
        if cbo(a): out.add((f,canon(a)))
    for p in patterns:
        for q in range(n):
            ii=[(q+j)%n for j in range(4)]
            z=[s[i] for i in ii]; a=s.copy()
            for d,src in enumerate(p): a[ii[d]]=z[src]
            if cbo(a): out.add((e,canon(a)))
    return out

def distance_to_success(start, patterns, maxdepth=4):
    start=(start[0],canon(start[1]))
    if gaps(*start): return 0,1
    seen={start}; q=deque([(start,0)])
    while q:
        u,d=q.popleft()
        if d == maxdepth: continue
        for v in nbrs(u,patterns):
            if v in seen: continue
            seen.add(v)
            if gaps(*v): return d+1,len(seen)
            q.append((v,d+1))
    return None,len(seen)

def full_component(start, patterns):
    start=(start[0],canon(start[1]))
    seen={start}; q=deque([start])
    while q:
        u=q.popleft()
        for v in nbrs(u,patterns):
            if v not in seen: seen.add(v); q.append(v)
    return seen

def main():
    bad={}
    for e in TYPES:
        S=set()
        for j in range(120):
            s=find_cbo(e,1000+j)
            if s is not None and gaps(e,s)==0: S.add(canon(s))
        bad[e]=S
    assert sum(map(len,bad.values())) == 730

    dcanon=Counter(); failures=[]
    for e,S in bad.items():
        for s in S:
            d,n=distance_to_success((e,s),CANON)
            if d is None: failures.append((e,s,n))
            else: dcanon[d]+=1
    assert len(failures)==3
    closed=[]
    for e,s,_ in failures:
        C=full_component((e,s),CANON)
        assert len(C)==8 and all(gaps(*u)==0 for u in C)
        closed.append({"omitted_type":e,"component_size":8,"representative":list(s)})

    dall=Counter()
    for e,S in bad.items():
        for s in S:
            d,_=distance_to_success((e,s),ALL4)
            assert d is not None and d <= 3
            dall[d]+=1

    print(json.dumps({
      "scope":"historical strict binary t=0 n=18 witness; parallel-type quotient",
      "seeded_bad_type_states":sum(map(len,bad.values())),
      "bad_states_by_omitted_type":{str(k):len(v) for k,v in bad.items()},
      "two_canonical_patterns":{
        "patterns":[list(p) for p in CANON],
        "escape_depth_histogram":dict(sorted(dcanon.items())),
        "closed_all_bad_components":closed,
      },
      "all_four_block_permutations":{
        "escape_depth_histogram":dict(sorted(dall.items())),
        "failures_within_depth_4":0,
        "maximum_observed_depth":max(dall),
      },
      "claim_level":"seeded finite computation; not exhaustive and not Lean certified",
    },indent=2,sort_keys=True))

if __name__=="__main__": main()
