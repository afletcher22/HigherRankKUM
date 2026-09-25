import itertools, time
from pysat.solvers import Cadical153
import base_sat as B
from kum import Mat, is_cbo
for shapes,rC,expect in ((["KKKCKCKCKC"],3,"SAT"),(["KKKCKCKCKC"],2,"UNSAT"),(["KKKCKCCKKC"],2,"SAT"),([],3,"SAT")):
    B.SHAPES=shapes
    cl,ns=B.build(rC); s=Cadical153(bootstrap_with=cl); res=s.solve()
    msg=f"shapes={shapes} r(C)={rC}: {'SAT' if res else 'UNSAT'} (expected {expect})"
    if res:
        m=set(l for l in s.get_model() if l>0)
        r=lambda S: sum(1 for v in range(1,5) if B.var(S,v) in m)
        M=Mat(10,lambda L: r(sum(1<<x for x in L)))
        # independent check: the model is a matroid; list whether it has ANY site CBO with all 3 shapes
        allshapes=["KKKCKCKCKC","KKKCKCCKKC","KKKCKKCCKC"]
        has=False
        for sh in allshapes:
            for ko in itertools.permutations(range(6)):
                for co in itertools.permutations(range(6,10)):
                    seq=[];ki=ci=0
                    for ch in sh:
                        if ch=="K": seq.append(ko[ki]);ki+=1
                        else: seq.append(co[ci]);ci+=1
                    if is_cbo(M,seq): has=True;break
                if has: break
            if has: break
        msg+=f"; model has a site-CBO using all shapes: {has}"
    print(msg,flush=True)
