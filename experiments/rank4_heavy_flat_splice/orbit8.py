from kum import *
from collections import Counter
cols=[6,7,10,11,12,13,14,14,15,15]
M=binary(cols)
H=[0,1,2,3,4,5]; Hs=set(H)
allc=find_cbo(M,first=0,want_all=True)
print("CBOs with label0 first:",len(allc))
sk=Counter(); bad=Counter()
for o in allc:
    s="".join("H" if x in Hs else "R" for x in o)
    # gaps between R's
    n=len(o); Rpos=[i for i in range(n) if o[i] not in Hs]
    gaps=tuple(sorted(((Rpos[(j+1)%4]-Rpos[j])%n-1) for j in range(4)))
    hs=[x for x in o if x in Hs]
    badtr=sum(1 for i in range(6) if M.rk([hs[(i+j)%6] for j in range(3)])<3)
    sk[gaps]+=1; bad[badtr]+=1
print("gap multisets:",dict(sk)); print("#bad H-triples:",dict(bad))
o=allc[0]; print("example:",[cols[x] for x in o], "".join("H" if x in Hs else "R" for x in o))
