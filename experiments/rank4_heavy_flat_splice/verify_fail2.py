import time
from kum import *
vecs=[(1,1,2,0),(1,2,1,0),(1,0,2,0),(1,1,0,0),(1,0,2,0),(1,1,0,0),(1,2,0,0),(1,2,0,0),(1,2,2,0),(1,1,1,1),(0,1,1,2),(0,1,1,2),(0,1,1,2),(1,1,1,1)]
e=12; sigma=(0,13,3,11,2,8,6,10,5,1,9,7,4)
M=gfp(vecs,3); K=set(range(9)); n=14
info=classify(M)
print("GF(3) n=14: rank",M.rank(),"profile",info["profile"],"strict",info["strict"],"t",info["t"])
print("K flat rank 3:",M.rk(sorted(K))==3 and bits(M.cl(sum(1<<x for x in K)))==sorted(K))
print("sigma CBO of M-e:",sorted(sigma)==[x for x in range(n) if x!=e] and is_cbo(M,list(sigma)))
C=[x for x in range(n) if x not in K]; print("complement rank",M.rk(C),"complement vectors",[vecs[x] for x in C])
tau=[x for x in sigma if x in K]
t=time.time(); allc=find_cbo(M,first=tau[0],want_all=True,limit=10**9)
def canon(c):
    c=list(c); i=c.index(min(c)); a=tuple(c[i:]+c[:i]); c2=c[::-1]; j=c2.index(min(c2)); return min(a,tuple(c2[j:]+c2[:j]))
ind={canon([x for x in o if x in K]) for o in allc}
print("all CBOs:",len(allc),"distinct induced K-orders:",len(ind),"tau among them:",canon(tau) in ind,f"{time.time()-t:.0f}s")
