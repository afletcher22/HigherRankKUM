"""Hitting lemma for heavy-flat splice: B basis of M, B∩F basis of F, M-B uniformly dense.
M-B uniformly dense  <=>  for every flat G of M of rank j in {1,2,3}: 4|G-B| <= j(n-4)."""
import itertools, random, sys, time
from collections import Counter
from kum import *
from gen import proj_points, mk

def near_tight(M):
    n=M.n; fl=M.flats(); out=[]
    for j in (1,2,3):
        for G in fl[j]:
            need=pc(G)-(j*(n-4))//4   # hits needed so that |G-B| <= floor(j(n-4)/4)
            if need>0: out.append((G,j,need))
    return fl,out

def heavy_flats(M,fl):
    """flats meeting the HFS counting thresholds (plane/point/line)."""
    n=M.n; N=n-4; H=[]
    for P in fl[1]:
        if 5*(pc(P)-1)>N: H.append(P)
    for L in fl[2]:
        if 20*(pc(L)-2)>=9*N: H.append(L)
    for Pi in fl[3]:
        if 3*(pc(Pi)-3)>2*N: H.append(Pi)
    return H

def find_hitting(M,F,NT,limit=200000):
    rho=M.r(F); Fl=bits(F); X=[x for x in range(M.n) if not (F>>x)&1]
    cnt=0
    for TF in itertools.combinations(Fl,rho):
        if M.rk(TF)!=rho: continue
        for TX in itertools.combinations(X,4-rho):
            cnt+=1
            if cnt>limit: return "limit"
            B=list(TF)+list(TX)
            if M.rk(B)!=4: continue
            Bm=sum(1<<x for x in B)
            if all(pc(G&Bm)>=need for G,j,need in NT):
                return B
    return None
