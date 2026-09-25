"""Anatomy of a light blocked insertion (binary n=18, profile (3,6,10))."""
import itertools
from kum import *
from light_block import blocked_orders
cols=[1,1,2,2,3,3,4,4,5,5,8,8,9,10,12,15,15,15]
M=binary(cols)
B=[cols.index(v) for v in (1,2,4,8)]
found,st=blocked_orders(M,B,limit=10**7,want=3)
print("blocked orders found:",len(found),st)
sig=found[0]; n=len(sig)
print("sigma' (values):",[cols[x] for x in sig])
supp=lambda x: [cols[b] for b in B if not (M.rk([y for y in B if y!=b]+[x])==4) is False and M.rk([y for y in B if y!=b]+[x])==4]
print("supports of M-B elements w.r.t. B (which B-element each can replace):")
for v in sorted(set(cols[x] for x in sig)):
    x=next(i for i in sig if cols[i]==v)
    print("  ",v,"->",[cols[b] for b in B if M.rk([y for y in B if y!=b]+[x])==4])
# for each gap, the reason every order fails: count which window index fails first
from collections import Counter
reasons=Counter()
for g in range(n):
    L3=[sig[(g-3+t)%n] for t in range(3)]; R3=[sig[(g+t)%n] for t in range(3)]
    fails=Counter()
    for pi in itertools.permutations(B):
        seq=L3+list(pi)+R3
        bad=[i for i in range(7) if M.rk(seq[i:i+4])<4]
        fails[tuple(bad)]+=1
    print(f"gap {g:2d}: L={[cols[x] for x in L3]} R={[cols[x] for x in R3]}  failing-window patterns (window idx 0..6):",dict(fails.most_common(3)))
