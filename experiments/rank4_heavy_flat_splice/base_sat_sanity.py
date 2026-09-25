import itertools, time
from pysat.solvers import Cadical153
import base_sat as B
from kum import binary, is_cbo
cl,ns=B.build(None)
site=[c for c in cl if len(c)>=7 and all(l<0 for l in c)]   # site clauses are all-negative, 7-10 lits
core=[c for c in cl if not (len(c)>=7 and all(l<0 for l in c))]
print("site clauses",len(site),"core clauses",len(core))
s=Cadical153(bootstrap_with=core); print("core satisfiable:",s.solve())
m=set(l for l in s.get_model() if l>0)
r=lambda S: sum(1 for v in range(1,5) if B.var(S,v) in m)
ok=all(r(S)<=r(S|1<<x)<=r(S)+1 for S in range(1024) for x in range(10))
sub=all(r(S|1<<x)+r(S|1<<y)>=r(S|1<<x|1<<y)+r(S) for S in range(1024) for x in range(10) for y in range(10))
print("model is a matroid rank function:",ok and sub and r(0)==0, " r(K)=",r(63)," r(E)=",r(1023))
# known matroid must satisfy all core clauses: binary orbit-8 example (K=labels 0..5)
M=binary([6,7,10,11,12,13,14,14,15,15])
asg={B.var(S,v): (M.r(S)>=v) for S in range(1024) for v in range(1,5)}
print("orbit-8 matroid satisfies core:",all(any((asg[abs(l)] if l>0 else not asg[abs(l)]) for l in c) for c in core))
# and violates some site clause iff it has a site CBO (it does) -> check one site clause is falsified
print("orbit-8 falsifies some site clause (has a site CBO):",any(all(asg[abs(l)] for l in c) for c in site))
