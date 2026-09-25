import itertools, time
from kum import *
cols=(4,1,3,6,6,3,2,5,7,13,9,13,9,13); e=11
sigma=(0,10,2,6,13,3,1,12,7,5,9,8,4)
M=binary(cols); n=14; k=3
K=set(range(9))
info=classify(M)
print("rank",M.rank(),"profile",info["profile"],"strict",info["strict"],"t",info["t"])
print("K is flat of rank",M.rk(sorted(K)),"closure==K:",bits(M.cl(sum(1<<x for x in K)))==sorted(K))
print("sigma is CBO of M-e:", sorted(sigma)==[x for x in range(n) if x!=e], is_cbo(M,list(sigma)))
tau=[x for x in sigma if x in K]
print("tau",tau,"values",[cols[x] for x in tau])
print("tau triples ranks",[M.rk([tau[(i+j)%9] for j in range(3)]) for i in range(9)])
# independent brute force: enumerate ALL CBOs of M starting at label tau[0]; record induced K orders
t=time.time()
allc=find_cbo(M,first=tau[0],want_all=True,limit=10**9)
print("all CBOs of M with tau[0] first:",len(allc),f"{time.time()-t:.0f}s")
def canon(c):
    c=list(c); i=c.index(min(c)); a=tuple(c[i:]+c[:i]); c2=c[::-1]; j=c2.index(min(c2)); b=tuple(c2[j:]+c2[:j]); return min(a,b)
target=canon(tau)
ind={canon([x for x in o if x in K]) for o in allc}
print("distinct induced K-orders:",len(ind)," tau among them:",target in ind)
