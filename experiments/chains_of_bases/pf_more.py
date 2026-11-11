import itertools, random, sys, time
sys.path.insert(0, '.')
import chainlib as L

def perm_vec(v, p, r):
    w = 0
    for i in range(r):
        if v >> i & 1:
            w |= 1 << p[i]
    return w

def gf2_exhaustive(r, k):
    """All chains of k bases of GF(2)^r with B_0 standard, up to coordinate permutations."""
    t0 = time.time()
    ctx = L.Ctx(r); isb = L.gf2_is_basis(r)
    bases = [c for c in itertools.combinations(range(1, 1 << r), r) if L.gf2_rank(c) == r]
    std = tuple(1 << i for i in range(r))
    seen = set(); n = bad_any = bad_pf = 0; ex = []
    for rest in itertools.product(bases, repeat=k - 1):
        if k == 3 and rest[0] > rest[1]:
            continue
        key = min(tuple(tuple(sorted(perm_vec(v, p, r) for v in B)) for B in rest) for p in ctx.perms)
        if key in seen:
            continue
        seen.add(key)
        a, pf = L.analyse(ctx, [std] + list(rest), isb)
        n += 1; bad_any += (not a); bad_pf += (not pf)
        if not pf and len(ex) < 3: ex.append(rest)
    print("GF(2) rank %d, k=%d exhaustive: %d cases; no ordering: %d; PF fails: %d  (%.0fs)" % (
        r, k, n, bad_any, bad_pf, time.time() - t0), flush=True)
    for e in ex: print("   PF failure:", e)

def vamos(k, samples):
    nonb = {frozenset(s) for s in [(0,1,2,3),(0,1,4,5),(2,3,4,5),(2,3,6,7),(0,1,6,7)]}
    vb = [c for c in itertools.combinations(range(8), 4) if frozenset(c) not in nonb]
    vbs = {frozenset(c) for c in vb}
    isb = lambda es: len(set(es)) == 4 and frozenset(es) in vbs
    ctx = L.Ctx(4); rng = random.Random(4)
    if samples is None:
        gen = itertools.product(vb, repeat=k)
    else:
        gen = (tuple(rng.choice(vb) for _ in range(k)) for _ in range(samples))
    n = bad_any = bad_pf = 0; ex = []
    for Bs in gen:
        a, pf = L.analyse(ctx, list(Bs), isb)
        n += 1; bad_any += (not a); bad_pf += (not pf)
        if not pf and len(ex) < 3: ex.append(Bs)
    print("Vamos, k=%d (%s): %d cases; no ordering: %d; PF fails: %d" % (
        k, "exhaustive" if samples is None else "sample", n, bad_any, bad_pf), flush=True)
    for e in ex: print("   PF failure:", e)

if __name__ == "__main__":
    for a in sys.argv[1:]:
        if a == "vamos2": vamos(2, None)
        elif a == "vamos3": vamos(3, 20000)
        else:
            r, k = map(int, a.split(","))
            gf2_exhaustive(r, k)
