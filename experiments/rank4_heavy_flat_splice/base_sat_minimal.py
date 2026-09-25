"""Which single restriction on the 10-element base suffices for the |F0|=5 plane / |F0|=3 line lemmas?"""
import itertools
from pysat.solvers import Cadical153
import base_sat_general as G
def no_big(j,size):
    return [[G.var(sum(1<<x for x in S),j+1)] for S in itertools.combinations(range(10),size)]
tests={"no 7-plane (planes<=6)":no_big(3,7),"no 5-line (lines<=4)":no_big(2,5),"no 3-point":no_big(1,3),
       "no 7-plane & no 5-line":no_big(3,7)+no_big(2,5)}
for rho,f in ((3,5),(2,3)):
    base,_=G.build(rho,f)
    for name,extra in tests.items():
        s=Cadical153(bootstrap_with=base+extra)
        print(f"rho={rho} |F0|={f} [{name}]: {'SAT (fails)' if s.solve() else 'UNSAT (holds)'}",flush=True)
