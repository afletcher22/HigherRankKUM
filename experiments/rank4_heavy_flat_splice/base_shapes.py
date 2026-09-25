"""Site skeletons for the 10-element base (6 K, 4 C), gaps listed from a 3-run:
S1=(3,1,1,1)  k1k2k3 c1 k4 c2 k5 c3 k6 c4
S2=(3,1,0,2)  k1k2k3 c1 k4 c2 c3 k5k6 c4
S3=(3,2,0,1)  k1k2k3 c1 k4k5 c2 c3 k6 c4
"""
import itertools
SHAPES={"S1":"KKKCKCKCKC","S2":"KKKCKCCKKC","S3":"KKKCKKCCKC"}
def realize(shape,tau,cs):
    o=[];ti=ci=0
    for s in SHAPES[shape]:
        if s=="K": o.append(tau[ti]); ti+=1
        else: o.append(cs[ci]); ci+=1
    return o
def shapes_working(M,tau,C,is_cbo):
    """which shapes work for SOME rotation of tau (and its reverse) and SOME order of C."""
    out=set(); m=len(tau)
    for t0 in (list(tau),list(tau)[::-1]):
        for r in range(m):
            t=t0[r:]+t0[:r]
            for cs in itertools.permutations(C):
                for sh in SHAPES:
                    if sh in out: continue
                    if is_cbo(M,realize(sh,t,cs)): out.add(sh)
    return out
