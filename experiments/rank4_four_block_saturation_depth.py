#!/usr/bin/env python3
"""Saturation versus repair-distance audit for two hard t=0 witnesses.

The statistic is the number of blocker triples whose rank-three closure
contains the maximum number of deletion-ground elements allowed by the
certified no-dangerous cap:

    |cl(X) ∩ (E-e)| = 3k - 1.

Audits:
  1. exact all-state graph of binary n=10 orbit 2 from the non-simple census,
     using arbitrary CBO-preserving four-block permutations plus point pivots;
  2. the 730 seeded bad type-states of the historical binary n=18 witness.

This is finite computation only. The cap itself is Lean-certified separately
on rank4-t0-saturated-cap; the correlations here are not Lean theorems.
"""

from collections import Counter, defaultdict, deque
from itertools import permutations
import json

import rank4_binary_n10_nonsimple_exact as b10
import rank4_n18_four_block_type_stress as b18

ALL4 = tuple(p for p in permutations(range(4)) if p != (0,1,2,3))


def canonical(order):
    order = tuple(order)
    i = order.index(min(order))
    return order[i:] + order[:i]


# ---------- exact n=10 orbit ----------
N10_COUNTS = (0,0,0,0,0,0,1,0,1,1,1,1,1,2,2)


def n10_columns():
    out = []
    for i,c in enumerate(N10_COUNTS,1):
        out.extend([i]*c)
    return tuple(out)


def n10_success(cols, state):
    e,o = state
    return b10.successful(cols, state)


def n10_graph(cols):
    states = set()
    for e in range(10):
        states.update((e,o) for o in b10.deletion_cbos(cols,e))

    adj = {s:set() for s in states}
    for e,o in states:
        m=len(o)
        for st in range(m):
            inds=[(st+j)%m for j in range(4)]
            vals=[o[i] for i in inds]
            for p in ALL4:
                a=list(o)
                for dst,src in enumerate(p):
                    a[inds[dst]]=vals[src]
                t=(e,canonical(a))
                if t in states:
                    adj[(e,o)].add(t)
                    adj[t].add((e,o))
        for i,f in enumerate(o):
            a=list(o); a[i]=e
            t=(f,canonical(a))
            if t in states:
                adj[(e,o)].add(t)
                adj[t].add((e,o))
    return states,adj


def n10_blocker_data(cols,state):
    e,o=state
    m=len(o)
    blockers=[]
    for i in range(m):
        tri=[o[(i+j)%m] for j in range(3)]
        vals=[cols[x] for x in tri]
        r=b10.rank2(vals)
        if b10.rank2(vals+[cols[e]]) != r:
            continue
        closure=[
            j for j,v in enumerate(cols)
            if b10.rank2(vals+[v]) == r
        ]
        blockers.append(len(set(closure)-{e}))
    return blockers


def n10_audit():
    cols=n10_columns()
    states,adj=n10_graph(cols)
    good={s for s in states if n10_success(cols,s)}
    dist={s:0 for s in good}
    q=deque(good)
    while q:
        u=q.popleft()
        for v in adj[u]:
            if v not in dist:
                dist[v]=dist[u]+1
                q.append(v)
    assert len(dist)==len(states)

    bydist=defaultdict(Counter)
    hard=[]
    for s,d in dist.items():
        if d==0:
            continue
        sizes=n10_blocker_data(cols,s)
        score=sum(x==5 for x in sizes)
        bydist[d][score]+=1
        if d==3:
            hard.append((s,sizes))

    assert len(hard)==32
    assert all(sorted(sizes)==[5,5,5,5,5] for _,sizes in hard)

    return {
      "states":len(states),
      "distance_histogram":dict(sorted(Counter(dist.values()).items())),
      "saturated_blockers_by_distance":{
        str(d):dict(sorted(c.items())) for d,c in sorted(bydist.items())
      },
      "distance_three_states":len(hard),
      "distance_three_omitted_labels":
        dict(sorted(Counter(s[0] for s,_ in hard).items())),
      "distance_three_all_five_blockers_saturated":True,
    }


# ---------- historical n=18 seeded type-state audit ----------

def closure_count_excluding_omitted_n18(state,i):
    e,s=state
    tri=[s[(i+j)%len(s)] for j in range(3)]
    r=b18.rank(tri)
    full=sum(1 for v in b18.V if b18.rank(tri+[v])==r)
    return full-1


def n18_saturation_score(state):
    e,s=state
    n=len(s)
    sizes=[]
    for i in range(n):
        tri=[s[(i+j)%n] for j in range(3)]
        if b18.rank(tri+[e])==b18.rank(tri):
            sizes.append(closure_count_excluding_omitted_n18(state,i))
    return sum(x==11 for x in sizes),sizes


def n18_audit():
    bad=[]
    for e in b18.TYPES:
        seen=set()
        for j in range(120):
            s=b18.find_cbo(e,1000+j)
            if s is not None and b18.gaps(e,s)==0:
                seen.add(b18.canon(s))
        bad.extend((e,s) for s in seen)
    assert len(bad)==730

    bydist=defaultdict(Counter)
    hard=[]
    for state in bad:
        d,_=b18.distance_to_success(state,b18.ALL4)
        assert d is not None and d<=3
        score,sizes=n18_saturation_score(state)
        bydist[d][score]+=1
        if d==3:
            hard.append((state,sizes))

    assert len(hard)==1
    state,sizes=hard[0]
    return {
      "bad_states":len(bad),
      "distance_histogram":{
        str(d):sum(c.values()) for d,c in sorted(bydist.items())
      },
      "saturated_blockers_by_distance":{
        str(d):dict(sorted(c.items())) for d,c in sorted(bydist.items())
      },
      "unique_distance_three_state":{
        "omitted_type":state[0],
        "blocker_closure_sizes_excluding_omitted":sorted(sizes),
        "saturated_blockers":sum(x==11 for x in sizes),
      },
    }


def main():
    out={
      "n10_exact_hard_orbit":n10_audit(),
      "n18_historical_seeded":n18_audit(),
      "interpretation":(
        "Greater four-block repair distance is strongly associated with more "
        "blocker closures attaining the no-dangerous rank-three cap 3k-1. "
        "This supports a rigidity-to-saturation proof program but is not a "
        "monotonicity theorem."
      ),
      "claim_level":"finite computation; n10 exact for one orbit, n18 seeded"
    }
    print(json.dumps(out,indent=2,sort_keys=True))


if __name__=="__main__":
    main()
