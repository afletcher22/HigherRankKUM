import itertools, random, sys
sys.path.insert(0, '.')
import cyclic_chain as C

def exhaustive_r3():
    p, r = 2, 3
    pts = [v for v in itertools.product(range(2), repeat=3) if any(v)]
    bases = [b for b in itertools.combinations(pts, 3) if C.rank_gfp(b, p) == 3]
    perms = list(itertools.permutations(range(r)))
    B1 = ((1,0,0),(0,1,0),(0,0,1))
    tot = fail = 0
    for B2 in bases:
        for B3 in bases:
            vecs = list(B1) + list(B2) + list(B3)
            tab = C.base_table(vecs, p, r)
            res = C.analyse([(0,1,2),(3,4,5),(6,7,8)], tab, perms)
            tot += 1
            if not all(all(d.values()) for d in res.values()):
                fail += 1
                if fail <= 3: print('  fail', B2, B3, res)
    print('rank 3 GF(2) exhaustive (B1 fixed), k=3: %d triples, %d with some failure' % (tot, fail), flush=True)

def r10():
    circ = ['11001','11100','01110','00111','10011']
    cols = [tuple(1 if i == j else 0 for i in range(5)) for j in range(5)]
    cols += [tuple(int(circ[i][j]) for i in range(5)) for j in range(5)]
    p, r = 2, 5
    perms = list(itertools.permutations(range(r)))
    tab10 = C.base_table(cols, p, r)
    full = (1 << 10) - 1
    pairs = [(b, full ^ b) for b in tab10 if (full ^ b) in tab10 and b < (full ^ b)]
    print('R10 complementary base pairs:', len(pairs), flush=True)
    stat = {}
    for b, cb in pairs:
        B = tuple(i for i in range(10) if b >> i & 1); Bc = tuple(i for i in range(10) if cb >> i & 1)
        res = C.analyse([B, Bc], tab10, perms)[(0, 1)]
        key = tuple(sorted((str(k), v) for k, v in res.items()))
        stat[key] = stat.get(key, 0) + 1
    for k, v in stat.items(): print('  k=2 pattern', dict(k), 'x', v)
    sys.stdout.flush()
    # k = 3: an R10 pair plus a third basis
    rng = random.Random(3)
    b, cb = pairs[0]
    B = tuple(i for i in range(10) if b >> i & 1); Bc = tuple(i for i in range(10) if cb >> i & 1)
    tot = 0; agg = {}
    thirds = []
    for _ in range(40):
        thirds.append(C.random_bases(5, 1, 2, rng)[0])
    thirds.append([cols[i] for i in B]); thirds.append([cols[i] for i in Bc])
    for B3 in thirds:
        vecs = cols + list(B3)
        tab = C.base_table(vecs, p, r)
        res = C.analyse([B, Bc, tuple(range(10, 15))], tab, perms)
        tot += 1
        for o, d in res.items():
            for key, val in d.items():
                s = agg.setdefault(key, [0, 0]); s[0] += 1; s[1] += val
        s = agg.setdefault('interval_some_order', [0, 0]); s[0] += 1; s[1] += any(d['interval'] for d in res.values())
        if not all(all(d.values()) for d in res.values()):
            print('  k=3 failure with third basis', B3, res, flush=True)
    print('R10 pair + third basis, k=3, %d cases' % tot)
    for key, (t, ok) in agg.items(): print('   %-22s holds %d / %d' % (str(key), ok, t))

exhaustive_r3()
r10()
