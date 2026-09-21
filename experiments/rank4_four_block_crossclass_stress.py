#!/usr/bin/env python3
"""Four-block repair stress beyond binary coordinate examples.

Moves on a deletion CBO:
  * cyclic adjacent swaps;
  * the two canonical consecutive four-position repairs
      [a,b,c,d] -> [c,d,a,b]
      [a,b,c,d] -> [c,d,b,a]
    whenever the result is still a deletion CBO.

For the joint state graph we additionally allow point pivots exchanging the
omitted element with one order entry when the new deletion order is a CBO.

Audits:
  1. exact fixed-e graphs for all 10 omitted labels of the 30-block SQS(10)
     rank-4 sparse-paving matroid;
  2. deterministic GF(3)/GF(5) rank-4 n=10 samples, simple and with genuine
     parallel pairs, satisfying the exact two-deletion flat caps (2,4,6).

Finite computation only; not Lean certification.
"""

from __future__ import annotations
from collections import Counter
from itertools import combinations, permutations, product
import json, random

FOUR = ((2,3,0,1),(2,3,1,0))

def canonical(o):
    o=tuple(o); i=o.index(min(o)); return o[i:]+o[:i]

# ---------- sparse paving ----------
E=tuple(range(10))
def sqs10():
    H=set()
    for i in range(10):
        H.add(frozenset((i,(i+1)%10,(i+3)%10,(i+4)%10)))
        H.add(frozenset((i,(i+1)%10,(i+2)%10,(i+6)%10)))
        H.add(frozenset((i,(i+2)%10,(i+4)%10,(i+7)%10)))
    assert len(H)==30
    return frozenset(H)

def sp_base(S,H): return frozenset(S) not in H
def sp_cbo(o,H):
    m=len(o)
    return all(sp_base([o[(i+j)%m] for j in range(4)],H) for i in range(m))

def sp_orders(H,e):
    labs=[x for x in E if x!=e]; first=min(labs); path=[first]; out=[]
    def rec(rem):
        if not rem:
            o=tuple(path)
            if sp_cbo(o,H): out.append(o)
            return
        for x in rem:
            if len(path)>=3 and not sp_base(path[-3:]+[x],H): continue
            path.append(x); rec([y for y in rem if y!=x]); path.pop()
    rec([x for x in labs if x!=first])
    return out

def sp_success(H,e,o):
    for g in range(len(o)):
        a=list(o); a.insert(g,e)
        if sp_cbo(a,H): return True
    return False

# ---------- finite fields ----------
def inv(a,p): return pow(a,p-2,p)
def canonv(v,p):
    v=tuple(x%p for x in v)
    for x in v:
        if x:
            z=inv(x,p); return tuple(y*z%p for y in v)
    raise ValueError
def pg3(p):
    return sorted({canonv(v,p) for v in product(range(p),repeat=4) if any(v)})
def rank(vs,p):
    if not vs: return 0
    A=[list(v) for v in vs]; r=0
    for c in range(4):
        q=next((i for i in range(r,len(A)) if A[i][c]%p),None)
        if q is None: continue
        A[r],A[q]=A[q],A[r]
        z=inv(A[r][c]%p,p); A[r]=[(z*x)%p for x in A[r]]
        for i in range(len(A)):
            if i!=r and A[i][c]%p:
                f=A[i][c]%p
                A[i]=[(A[i][j]-f*A[r][j])%p for j in range(4)]
        r+=1
        if r==len(A): break
    return r

def robust(M,p):
    cnt=Counter(M)
    if max(cnt.values())>2 or rank(M,p)!=4: return False
    U=list(cnt)
    for a,b in combinations(U,2):
        if rank((a,b),p)<2: continue
        if sum(c for x,c in cnt.items() if rank((a,b,x),p)<=2)>4: return False
    for n in pg3(p):
        if sum(c for x,c in cnt.items()
               if sum(a*b for a,b in zip(n,x))%p==0)>6: return False
    return True

def ff_cbo(o,M,p):
    m=len(o)
    return all(rank([M[o[(i+j)%m]] for j in range(4)],p)==4 for i in range(m))

def ff_orders(M,e,p):
    labs=[i for i in range(10) if i!=e]; first=min(labs); path=[first]; out=[]
    def rec(rem):
        if not rem:
            o=tuple(path)
            if ff_cbo(o,M,p): out.append(o)
            return
        for x in rem:
            if len(path)>=3 and rank([M[i] for i in path[-3:]+[x]],p)<4: continue
            path.append(x); rec([y for y in rem if y!=x]); path.pop()
    rec([x for x in labs if x!=first])
    return out

def ff_success(M,e,o,p):
    for g in range(len(o)):
        a=list(o); a.insert(g,e)
        if ff_cbo(a,M,p): return True
    return False

def fixed_graph(orders, success):
    S=set(orders); good={o:success(o) for o in S}; adj={o:set() for o in S}
    for o in S:
        m=len(o)
        for i in range(m):
            j=(i+1)%m; a=list(o); a[i],a[j]=a[j],a[i]; t=canonical(a)
            if t in S: adj[o].add(t)
        for st in range(m):
            inds=[(st+j)%m for j in range(4)]; vals=[o[i] for i in inds]
            for patt in FOUR:
                a=list(o)
                for dst,src in enumerate(patt): a[inds[dst]]=vals[src]
                t=canonical(a)
                if t in S: adj[o].add(t)
    unseen=set(S); comps=[]
    while unseen:
        root=unseen.pop(); comp={root}; stack=[root]
        while stack:
            u=stack.pop()
            for v in adj[u]:
                if v not in comp:
                    comp.add(v); unseen.discard(v); stack.append(v)
        comps.append(comp)
    return {
      "states":len(S),"successful_states":sum(good.values()),
      "components":len(comps),
      "closed_all_bad_components":sum(not any(good[x] for x in c) for c in comps),
      "largest_components":sorted((len(c) for c in comps),reverse=True)[:10],
    }

def sample(p,seed,count,require_duplicate):
    rng=random.Random(seed); P=pg3(p); out=[]
    while len(out)<count:
        M=tuple(rng.choice(P) for _ in range(10)) if require_duplicate else tuple(rng.sample(P,10))
        if require_duplicate and max(Counter(M).values())<2: continue
        if robust(M,p): out.append(M)
    return out

def first_nontrivial(M,p):
    for e in range(10):
        O=ff_orders(M,e,p)
        s=sum(ff_success(M,e,o,p) for o in O)
        if s<len(O):
            return e,fixed_graph(O,lambda o:ff_success(M,e,o,p))
    e=0; O=ff_orders(M,e,p)
    return e,fixed_graph(O,lambda o:ff_success(M,e,o,p))

def main():
    H=sqs10()
    sqs=[]
    for e in E:
        O=sp_orders(H,e)
        row=fixed_graph(O,lambda o,e=e:sp_success(H,e,o))
        sqs.append({"omitted":e,**row})

    rows=[]
    specs=[(3,12345,False),(5,54321,False),(3,7777,True),(5,8888,True)]
    for p,seed,dup in specs:
        for i,M in enumerate(sample(p,seed,3,dup)):
            e,row=first_nontrivial(M,p)
            rows.append({
              "field":p,"seed":seed,"sample_index":i,
              "parallel_required":dup,
              "max_multiplicity":max(Counter(M).values()),
              "omitted":e,**row
            })

    assert all(x["closed_all_bad_components"]==0 for x in sqs+rows)
    print(json.dumps({
      "sqs10_exact":sqs,
      "odd_field_samples":rows,
      "interpretation":(
        "The two canonical four-block repairs have no closed all-bad fixed-e "
        "component in the extremal SQS(10) or in these deterministic GF(3)/GF(5) "
        "samples. Fixed-e connectivity is not universal, but every observed "
        "component contains success."
      ),
      "claim_level":"SQS fixed-e graphs exact; odd-field samples deterministic finite computation"
    },indent=2,sort_keys=True))

if __name__=="__main__":
    main()
