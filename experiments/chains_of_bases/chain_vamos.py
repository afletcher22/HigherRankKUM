import itertools, random, sys
sys.path.insert(0, '.')
import cyclic_chain as C
# Vamos matroid on 0..7 with pairs (01)(23)(45)(67); non-bases: 0123 0145 2345 2367 0167  (4567 is a basis)
nonb = {frozenset(s) for s in [(0,1,2,3),(0,1,4,5),(2,3,4,5),(2,3,6,7),(0,1,6,7)]}
vb = [frozenset(c) for c in itertools.combinations(range(8), 4) if frozenset(c) not in nonb]
vbs = set(vb)
perms = list(itertools.permutations(range(4)))
rng = random.Random(5)
def test(k, trials):
    agg = {}; fails = 0
    for _ in range(trials):
        Bs = [sorted(rng.choice(vb)) for _ in range(k)]
        pts = [x for B in Bs for x in B]            # element i is a copy of Vamos point pts[i]
        tab = set()
        for c in itertools.combinations(range(4 * k), 4):
            s = {pts[i] for i in c}
            if len(s) == 4 and frozenset(s) in vbs:
                tab.add(sum(1 << i for i in c))
        res = C.analyse([tuple(range(4 * i, 4 * i + 4)) for i in range(k)], tab, perms)
        for o, d in res.items():
            for key, val in d.items():
                s = agg.setdefault(key, [0, 0]); s[0] += 1; s[1] += val
        if not all(all(d.values()) for d in res.values()):
            fails += 1
            if fails <= 2: print('  failure', Bs, res)
    print('Vamos (parallel copies), k=%d, %d samples, %d with a failure' % (k, trials, fails))
    for key, (t, ok) in agg.items(): print('   %-10s holds %d / %d' % (str(key), ok, t))
test(3, 4000); test(4, 1500)
