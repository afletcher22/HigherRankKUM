"""Executable form of Lemma H (hitting lemma, reduced strict t=0 case).

M strict t=0 on 4k+2 elements, no 3k-plane, no 2k-line.  For EVERY starting basis S that contains
the k-point element p (if a k-point exists) and misses a (3k-1)-plane, run the swap step of the
ledger proof and assert each claim: the missed plane is unique, at most two of the Q_s are
nonempty, X_s is nonempty, and the swapped basis is deletable (M-S uniformly dense)."""
import sys, random, itertools, time
from collections import Counter
from kum import *
from gen import proj_points, mk
from hitting import near_tight
from hit_general import span_pts

def reduced_instance(p, k, rng):
    pts = proj_points(p, 4)
    n = 4 * k + 2
    for _ in range(20000):
        g = rng.sample(pts, 4)
        Pl = span_pts(p, g[:3])
        vecs = [rng.choice(Pl) for _ in range(3 * k - 1)]
        if rng.random() < 0.5:                       # second big plane through a line of the first
            out2 = [v for v in span_pts(p, [g[0], g[1], g[3]]) if v not in Pl]
            if out2:
                vecs += [rng.choice(out2) for _ in range(rng.randint(1, k + 3))]
        if rng.random() < 0.4:                       # a k-point outside
            v = rng.choice([v for v in pts if v not in Pl])
            vecs += [v] * rng.randint(1, k)
        base = rng.sample(pts, rng.randint(3, 8))
        while len(vecs) < n:
            vecs.append(rng.choice(base))
        vecs = vecs[:n]
        M = mk(p, vecs)
        if M.rank() != 4:
            continue
        info = classify(M)
        a, b, c = info["profile"]
        if info["strict"] and info["t"] == 0 and b <= 2 * k - 1 and c <= 3 * k - 1 and c == 3 * k - 1:
            return M, info
    return None, None

def check_all_starts(M, k, stats):
    n = M.n
    fl = M.flats()
    full = (1 << n) - 1
    kpts = [P for P in fl[1] if pc(P) == k]
    H = [F for F in fl[3] if pc(F) == 3 * k - 1]
    assert len(kpts) <= 1
    C = {Pi: full & ~Pi for Pi in H}
    for a, b in itertools.combinations(H, 2):
        assert pc(C[a] & C[b]) <= 3
    _, NT = near_tight(M)
    p = bits(kpts[0])[0] if kpts else None
    for B in itertools.combinations(range(n), 4):
        if (p is not None and p not in B) or M.rk(B) != 4:
            continue
        Sm = sum(1 << s for s in B)
        missed = [Pi for Pi in H if Sm & Pi == 0]
        assert len(missed) <= 1
        if not missed:
            stats["start hits all"] += 1
            continue
        Pi = missed[0]
        I = [s for s in B if s != p]
        Q = {s: [P2 for P2 in H if P2 != Pi and C[Pi] & C[P2] == Sm & ~(1 << s)] for s in I}
        nq = sum(1 for s in I if Q[s])
        stats[f"swap start, nonempty Q = {nq}"] += 1
        assert nq <= 2, "three nonempty Q_s"
        s = next(s for s in I if not Q[s])
        rest = [t for t in B if t != s]
        X = [x for x in bits(Pi) if M.rk(rest + [x]) == 4]
        assert X
        for x in X:
            S2 = rest + [x]
            Bm = sum(1 << y for y in S2)
            assert all(pc(G & Bm) >= need for G, j, need in NT), "swapped basis not deletable"
        stats["swaps verified"] += len(X)

if __name__ == "__main__":
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    NI = int(sys.argv[2]) if len(sys.argv) > 2 else 15
    T = time.time()
    for k in (3, 4, 5, 6):
        for p in (2, 3, 5):
            stats = Counter()
            got = 0
            for _ in range(NI):
                M, info = reduced_instance(p, k, rng)
                if M is None:
                    continue
                got += 1
                check_all_starts(M, k, stats)
            print(f"k={k} p={p}: {got} instances", dict(stats), f"{time.time()-T:.0f}s", flush=True)
