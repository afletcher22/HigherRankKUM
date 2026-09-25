from kum import *
from gtest import extend_tau_any
cols=[6,7,10,11,12,13,14,14,15,15]
M=binary(cols); K=[0,1,2,3,4,5]; C=[6,7,8,9]
taus=find_cbo(M,elems=K,r=3,first=0,want_all=True)
cls={6:'X',7:'X',10:'Y',11:'Y',12:'Z',13:'Z'}
for t in taus:
    print([cols[x] for x in t], "".join(cls[cols[x]] for x in t), "extends:", extend_tau_any(M,list(t),C) is not None)
# what do actual CBOs look like
allc=find_cbo(M,first=0,want_all=True)
o=allc[0]
print("sample CBO:",[cols[x] for x in o])
tri=[x for x in o if x in K]
print("its K-order",[cols[x] for x in tri],"triple ranks",[M.rk([tri[(i+j)%6] for j in range(3)]) for i in range(6)])
