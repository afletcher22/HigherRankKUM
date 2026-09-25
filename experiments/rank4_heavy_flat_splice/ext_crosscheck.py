"""Brute-force validation of ext.extend and nonext.nonext_orders at n=10."""
import sys, random, itertools
from collections import Counter
from kum import *
from gen import proj_points, mk
from ext import extend
from nonext import nonext_orders

def canon(order):
    i = order.index(min(order))
    return tuple(order[i:] + order[:i])

rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
stats = Counter()
for p in (2, 3, 5):
    pts = proj_points(p, 4)
    done = 0
    while done < 25:
        vecs = []
        base = rng.sample(pts, rng.randint(4, min(len(pts), 9)))
        while len(vecs) < 10:
            vecs.append(rng.choice(vecs) if vecs and rng.random() < 0.4 else rng.choice(base))
        M = mk(p, vecs)
        if M.rank() != 4:
            continue
        bases = [B for B in itertools.combinations(range(10), 4) if M.rk(B) == 4]
        S = list(rng.choice(bases))
        Y = [x for x in range(10) if x not in S]
        try:
            cbos_Y = find_cbo(M, elems=Y, want_all=True, limit=10 ** 6)
        except Timeout:
            continue
        if not cbos_Y:
            continue
        try:
            cbos_M = find_cbo(M, want_all=True, limit=10 ** 7)
        except Timeout:
            continue
        restr = {canon([x for x in o if x in Y]) for o in (cbos_M or [])}
        brute_bad = [o for o in cbos_Y if canon(list(o)) not in restr]
        ext_bad = []
        for o in cbos_Y:
            e = extend(M.rk, S, list(o))
            if e is not None:
                assert is_cbo(M, e) and canon([x for x in e if x in Y]) == canon(list(o)), "bad extension"
            else:
                ext_bad.append(o)
        agree = {canon(list(o)) for o in brute_bad} == {canon(list(o)) for o in ext_bad}
        f, st, _ = nonext_orders(M, S, limit=10 ** 7, want=10 ** 6)
        agree2 = (len(f) > 0) == (len(ext_bad) > 0) and {canon(o) for o in f} <= {canon(list(o)) for o in ext_bad}
        stats[(p, "agree" if agree else "DISAGREE", "nonext-agree" if agree2 else "NONEXT-DISAGREE",
               "has-nonext" if ext_bad else "all-extend")] += 1
        done += 1
for k, v in sorted(stats.items(), key=str):
    print(k, v)
