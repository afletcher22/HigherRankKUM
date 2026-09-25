import json, time
from kum import *
from gtest import *
from bin_class import PTS
reps=json.load(open("orbits_n10_t0.json"))
tot=dict(planes=0,s00_any=0,s00_all=0,repo_any=0,every_ok=0)
for i,r in enumerate(reps):
    cols=[]
    for p,c in zip(PTS,r["counts"]): cols+=[p]*c
    M=binary(cols)
    info=classify(M)
    assert info["strict"] and info["t"]==0
    line=f"orbit {i:2d} cols={cols} prof={info['profile']} #6planes={len(info['planes3k'])}"
    for H in info["planes3k"]:
        res=analyse(M,H,do_repo=True,do_every=True)
        tot["planes"]+=1
        tot["s00_any"]+=res["s00_tau"]>0
        tot["s00_all"]+=res["s00_tau"]==res["ntau"]
        tot["repo_any"]+=res["repo_tau"]>0
        tot["every_ok"]+=res["every_fail"]==0
        line+=f"\n    H={bits(H)} ntau={res['ntau']} S00={res['s00_tau']} repo={res['repo_tau']} tau-nonextendable={res['every_fail']}"
    print(line)
print(tot)
