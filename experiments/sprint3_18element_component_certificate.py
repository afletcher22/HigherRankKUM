#!/usr/bin/env python3
"""Exact audit of one preserved 18-element binary rank-4 pair-cycle obstruction."""
import json
from collections import Counter, deque
from itertools import combinations, permutations, product

N,H=9,2
V=(1,2,4,8,1,6,2,8,1,4,2,12,1,8,2,4,5,8)
L=tuple(range(18))
INITIAL=tuple((i,i+1) for i in range(0,18,2))

def rank_elim(vals):
    b=[0]*4; r=0
    for x in vals:
        while x:
            p=x.bit_length()-1
            if b[p]: x^=b[p]
            else: b[p]=x; r+=1; break
    return r

def rank_span(vals):
    s={0}
    for v in vals: s|={x^v for x in tuple(s)}
    return len(s).bit_length()-1

def mask(xs):
    xs=tuple(xs); assert len(set(xs))==len(xs)
    return sum(1<<x for x in xs)

BASES={mask(c) for c in combinations(L,4) if rank_elim(V[x] for x in c)==4}

def canon(S):
    S=tuple(tuple(sorted(p)) for p in S)
    assert sorted(x for p in S for x in p)==list(L)
    return min(S[i:]+S[:i] for i in range(N))

def aligned(S,i): return tuple(x for j in range(H) for x in S[(i+j)%N])
def admissible(S): return all(mask(aligned(S,i)) in BASES for i in range(N))

def relations(S):
    return tuple(tuple(tuple(mask((S[i][1-a],)+tuple(x for j in range(1,H) for x in S[(i+j)%N])+(S[(i+H)%N][b],)) in BASES for b in (0,1)) for a in (0,1)) for i in range(N))

def orientation(S):
    R=relations(S)
    assert all(all(any(row) for row in q) and all(any(q[a][b] for a in (0,1)) for b in (0,1)) for q in R)
    ans=next((z for z in product((0,1),repeat=N) if all(R[i][z[i]][z[(i+H)%N]] for i in range(N))),None)
    forced=all(sum(map(sum,q))==2 for q in R)
    parity=sum(q[0][1] for q in R)%2 if forced else None
    assert (ans is None)==(forced and parity==1)
    return ans

def flatten(S,z): return tuple(x for p,b in zip(S,z) for x in (p[b],p[1-b]))
def cbo(o): return all(rank_span(V[o[(i+j)%18]] for j in range(4))==4 for i in range(18))

def moves(S):
    for i in range(N):
        j=(i+1)%N
        for a,b in product((0,1),repeat=2):
            T=list(S); p,q=list(S[i]),list(S[j]); p[a],q[b]=q[b],p[a]; T[i],T[j]=tuple(p),tuple(q); T=tuple(T)
            ok=all(mask(aligned(T,k)) in BASES for k in ((i-1)%N,(i+1)%N))
            assert ok==admissible(T)
            yield (i,a,b),canon(T),ok

def density_check():
    assert rank_elim(V)==rank_span(V)==4
    n=0
    for m in range(1,(1<<18)-1):
        vals=[V[i] for i in L if m>>i&1]; r=rank_elim(vals)
        assert r==rank_span(vals) and 2*m.bit_count()<9*r
        n+=1
    return n

def one_break_check():
    n=0
    for i in range(N):
        B=INITIAL[i:]+INITIAL[:i]; chunk=B[0]+B[1]; rest=B[2:]
        for p in permutations(chunk):
            for z in product((0,1),repeat=7):
                o=list(p)
                for pair,b in zip(rest,z): o.extend((pair[b],pair[1-b]))
                assert not cbo(tuple(o)); n+=1
    return n

def component():
    start=canon(INITIAL); assert admissible(start) and orientation(start) is None
    G={}; seen={start}; Q=deque([start])
    while Q:
        S=Q.popleft(); G[S]={T for _,T,ok in moves(S) if ok}
        for T in G[S]:
            if T not in seen: seen.add(T); Q.append(T)
    assert all(S in G[T] for S in G for T in G[S])
    ori={S:orientation(S) for S in seen}; bad={S for S in seen if ori[S] is None}; good=seen-bad
    d={S:0 for S in good}; Q=deque(good)
    while Q:
        S=Q.popleft()
        for T in G[S]:
            if T not in d: d[T]=d[S]+1; Q.append(T)
    assert len(d)==len(seen)
    Q=deque([start]); par={start:None}; pm={}; target=None
    while Q:
        S=Q.popleft()
        if ori[S] is not None: target=S; break
        for mv,T,ok in moves(S):
            if ok and T not in par: par[T]=S; pm[T]=mv; Q.append(T)
    path=[]; T=target
    while par[T] is not None: path.append({'exchange':pm[T],'pairs_by_label':T}); T=par[T]
    path.reverse(); z=ori[target]; order=flatten(target,z); assert cbo(order)
    return {'component_vertices':len(seen),'orientable_vertices':len(good),'unorientable_vertices':len(bad),'directed_admissible_moves':sum(map(len,G.values())),'unorientable_distance_histogram':dict(sorted(Counter(d[S] for S in bad).items())),'maximum_distance_to_orientable':max(d.values()),'starting_cycle_distance_to_orientable':d[start],'repair_path':path,'repaired_orientations':z,'repaired_cbo_labels':order,'repaired_cbo_vectors':tuple(V[x] for x in order),'boundary_criterion_checks':len(seen)*N*4}

def main():
    out={'scope':'one labelled 18-element binary rank-four matroid and one adjacent-exchange component','vectors_by_label':V,'initial_pairs_by_label':INITIAL,'initial_pairs_by_vector':tuple((V[a],V[b]) for a,b in INITIAL),'strict_density_proper_subsets_checked':density_check(),'historical_one_break_orders_checked':one_break_check(),**component(),'status':'exact finite computational certificate; not a universal bounded-repair theorem'}
    print(json.dumps(out,indent=2))

if __name__=='__main__': main()
