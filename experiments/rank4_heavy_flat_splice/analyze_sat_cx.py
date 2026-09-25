"""Inspect SAT counterexamples to 10-element base lemmas; re-solve under extra class constraints."""
import itertools, sys
from pysat.solvers import Cadical153
import base_sat_general as G
from kum import Mat, classify, find_cbo, pc, bits

def solve(rho,f,extra):
    cl,_=G.build(rho,f); cl+=extra
    s=Cadical153(bootstrap_with=cl)
    if not s.solve(): return None
    m=set(l for l in s.get_model() if l>0)
    r=lambda S: sum(1 for v in range(1,5) if G.var(S,v) in m)
    return Mat(10,lambda L: r(sum(1<<x for x in L)))

def no_big(j,size):
    """forbid any set of `size` elements with rank <= j  (i.e. flats of rank j have < size)."""
    return [[G.var(sum(1<<x for x in S),j+1)] for S in itertools.combinations(range(10),size)]

for rho,f in ((3,5),(2,3)):
    for label,extra in (("plain",[]),
                        ("strict k=2 (points<=2, lines<=4, planes<=6)", no_big(1,3)+no_big(2,5)+no_big(3,7)),
                        ("strict, no 6-plane", no_big(1,3)+no_big(2,5)+no_big(3,6)),
                        ("strict, no 6-plane, no 2-point", no_big(1,2)+no_big(2,5)+no_big(3,6)),
                        ("strict, no 6-plane, no 4-line", no_big(1,3)+no_big(2,4)+no_big(3,6))):
        M=solve(rho,f,extra)
        if M is None:
            print(f"rho={rho} |F0|={f} [{label}]: UNSAT -> base lemma holds in this class"); continue
        info=classify(M)
        anyc=find_cbo(M,limit=10**7)
        print(f"rho={rho} |F0|={f} [{label}]: SAT  profile={info['profile']} t={info['t']} #6planes={len(info['planes3k'])} hasCBO={'yes' if anyc else 'NO'}")
