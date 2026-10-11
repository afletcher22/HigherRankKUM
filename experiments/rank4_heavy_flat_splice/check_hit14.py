"""Test the paper proofs of hit14g (9-plane) and hit14line (6-line, no 9-plane) at k = 3.

Random rank-4 matroids on 14 elements over GF(p), biased toward heavy structure, filtered to the
strict t=0 profile (loopless, points <= 3, lines <= 6, planes <= 9). For each instance, every
choice allowed by the proof is tried, and the resulting S must be a basis with M - S uniformly
dense at 10/4 (points <= 2, lines <= 5, planes <= 7 outside S).
Usage: python check_hit14.py N_INSTANCES SEED [G|L|GL]  (G: build around a 9-plane, L: a 6-line)
Runs of 2026-10-10: `40 1`, `150 2 L`, `200 3 GL`; 390 instances, 367,802 choices, all deletable.
"""
import itertools, random, sys

N = 14


class Mat:
    def __init__(self, p, vecs):
        self.p, self.v, self.cache = p, vecs, {}

    def rk(self, mask):
        if mask in self.cache:
            return self.cache[mask]
        p = self.p
        rows = [list(self.v[i]) for i in range(N) if mask >> i & 1]
        r = 0
        for c in range(4):
            piv = next((i for i in range(r, len(rows)) if rows[i][c] % p), None)
            if piv is None:
                continue
            rows[r], rows[piv] = rows[piv], rows[r]
            inv = pow(rows[r][c], p - 2, p)
            rows[r] = [x * inv % p for x in rows[r]]
            for i in range(len(rows)):
                if i != r and rows[i][c] % p:
                    f = rows[i][c]
                    rows[i] = [(a - f * b) % p for a, b in zip(rows[i], rows[r])]
            r += 1
        self.cache[mask] = r
        return r

    def cl(self, mask):
        r = self.rk(mask)
        out = mask
        for e in range(N):
            if not mask >> e & 1 and self.rk(mask | 1 << e) == r:
                out |= 1 << e
        return out


pc = lambda m: bin(m).count("1")
bits = lambda m: [i for i in range(N) if m >> i & 1]
FULL = (1 << N) - 1


def flats(M):
    fl = {1: set(), 2: set(), 3: set()}
    for j in (1, 2, 3):
        for c in itertools.combinations(range(N), j):
            m = sum(1 << x for x in c)
            if M.rk(m) == j:
                fl[j].add(M.cl(m))
    return fl


def profile_ok(M, fl):
    if M.rk(FULL) != 4 or any(M.rk(1 << e) == 0 for e in range(N)):
        return False
    caps = {1: 3, 2: 6, 3: 9}
    return all(pc(F) <= caps[j] for j in fl for F in fl[j])


def deletable(M, fl, S):
    if pc(S) != 4 or M.rk(S) != 4:
        return False
    caps = {1: 2, 2: 5, 3: 7}
    return all(pc(F & ~S) <= caps[j] for j in fl for F in fl[j])


def proj_points(p):
    pts = []
    for v in itertools.product(range(p), repeat=4):
        if any(v):
            lead = next(x for x in v if x)
            if lead == 1:
                pts.append(v)
    return pts


def span(p, gens):
    out = set()
    for cs in itertools.product(range(p), repeat=len(gens)):
        w = tuple(sum(c * g[i] for c, g in zip(cs, gens)) % p for i in range(4))
        if any(w):
            lead = next(x for x in w if x)
            inv = pow(lead, p - 2, p)
            out.add(tuple(x * inv % p for x in w))
    return sorted(out)


def gen_plane(p, rng, pts):
    a, b, c = rng.sample(pts, 3)
    pl = span(p, [a, b, c])
    if len(pl) < 3:
        return None
    pool = rng.sample(pl, min(len(pl), rng.randint(3, 7)))
    vecs = [rng.choice(pool) for _ in range(9)]
    off = [v for v in pts if v not in set(pl)]
    mode = rng.randint(0, 3)
    if mode == 0:                                   # C on a line
        d, e = rng.sample(off, 2)
        ln = [v for v in span(p, [d, e]) if v not in set(pl)]
        vecs += [rng.choice(ln) for _ in range(5)]
    elif mode == 1:                                 # C in a plane
        d, e, f = rng.sample(off, 3)
        q = [v for v in span(p, [d, e, f]) if v not in set(pl)]
        pool2 = rng.sample(q, min(len(q), rng.randint(2, 5)))
        vecs += [rng.choice(pool2) for _ in range(5)]
    elif mode == 2:                                 # a second heavy plane
        pl2 = span(p, [a, b, rng.choice(off)])
        q = [v for v in pl2 if v not in set(pl)]
        vecs += [rng.choice(q) for _ in range(rng.randint(3, 5))]
        vecs += [rng.choice(off) for _ in range(14 - len(vecs))]
    else:
        pool2 = rng.sample(off, rng.randint(2, 5))
        vecs += [rng.choice(pool2) for _ in range(5)]
    return vecs[:14]


def gen_line(p, rng, pts):
    a, b = rng.sample(pts, 2)
    ln = span(p, [a, b])
    pool = rng.sample(ln, min(len(ln), rng.randint(2, 6)))
    vecs = [rng.choice(pool) for _ in range(6)]
    off = [v for v in pts if v not in set(ln)]
    mode = rng.randint(0, 3)
    if mode == 0:                                   # a second 6-line
        d, e = rng.sample(off, 2)
        l2 = [v for v in span(p, [d, e]) if v not in set(ln)]
        vecs += [rng.choice(l2) for _ in range(6)]
    elif mode == 1:                                 # heavy planes through points of L
        for _ in range(2):
            d, e = rng.sample(off, 2)
            q = [v for v in span(p, [rng.choice(pool), d, e]) if v not in set(ln)]
            vecs += [rng.choice(q) for _ in range(4)]
    elif mode == 2:                                 # X in a plane
        d, e, f = rng.sample(off, 3)
        q = [v for v in span(p, [d, e, f]) if v not in set(ln)]
        vecs += [rng.choice(q) for _ in range(8)]
    pool2 = rng.sample(off, rng.randint(3, 8))
    while len(vecs) < 14:
        vecs.append(rng.choice(pool2))
    return vecs[:14]


def check_G(M, fl, K):
    """Every choice allowed by the proof gives a deletable basis. Returns #choices tried."""
    C = FULL & ~K
    Ks = bits(K)
    tried = 0
    parts = []
    for D0 in itertools.combinations(Ks, 3):
        if Ks[0] not in D0:
            continue
        rest = [x for x in Ks if x not in D0]
        for D1 in itertools.combinations(rest, 3):
            if rest[0] not in D1:
                continue
            D2 = [x for x in rest if x not in D1]
            Ds = [sum(1 << x for x in D) for D in (D0, D1, D2)]
            if all(M.rk(D) == 3 for D in Ds):
                parts.append(Ds)
    assert parts, "no Edmonds partition"
    three_pts = [F for F in fl[1] if pc(F) == 3 and F & C == F]
    cs = []
    for c in bits(C):
        if M.rk(C & ~(1 << c)) != M.rk(C):
            continue
        if any(not (F >> c & 1) for F in three_pts):
            continue
        cs.append(c)
    assert cs, "no c"
    planesC = [F for F in fl[3] if F != K and F & C == C]
    for Ds in parts:
        good = []
        for a, b in itertools.combinations(range(3), 2):
            if all(pc(F & Ds[a]) + pc(F & Ds[b]) <= 3 for F in planesC):
                good.append((a, b))
        assert good, "no (a,b)"
        for a, b in good:
            e = 3 - a - b
            for c in cs:
                S = Ds[e] | 1 << c
                tried += 1
                assert deletable(M, fl, S), ("G fails", Ds, a, b, c)
    return tried


def check_L(M, fl, L):
    X = FULL & ~L
    others = [F for F in fl[2] if pc(F) == 6 and F != L]
    assert len(others) <= 1 and all(F & L == 0 for F in others), "6-lines"
    assert all(F & L == F for F in fl[1] if pc(F) == 3), "3-point off L"
    tried = 0
    xs = [x for x in bits(X) if all(F >> x & 1 for F in others)]
    assert xs
    for x in xs:
        clx = M.cl(L | 1 << x)
        for y in bits(X & ~clx):
            req = [F for F in fl[1] if pc(F) == 3 and F & L == F]
            for P in fl[3]:
                if pc(P) == 8 and P & L != L and not (P >> x & 1) and not (P >> y & 1):
                    q = P & L
                    assert M.rk(q) == 1 and pc(q) >= 2 and M.cl(q) == q, "q not a point"
                    req.append(q)
            req = list(set(req))
            assert len(req) <= 2, ("too many required points", req)
            found = False
            for a, b in itertools.combinations(bits(L), 2):
                if M.rk(1 << a | 1 << b) != 2:
                    continue
                if not all(F >> a & 1 or F >> b & 1 for F in req):
                    continue
                found = True
                S = 1 << a | 1 << b | 1 << x | 1 << y
                tried += 1
                assert deletable(M, fl, S), ("L fails", a, b, x, y)
            assert found, "no (a,b)"
    return tried


def main():
    n_inst, seed = int(sys.argv[1]), int(sys.argv[2])
    rng = random.Random(seed)
    stats = {"G": 0, "L": 0, "Gtried": 0, "Ltried": 0, "rejected": 0, "multiG": 0, "twoL": 0}
    ptsc = {p: proj_points(p) for p in (3, 5, 7)}
    while stats["G"] + stats["L"] < n_inst:
        p = rng.choice((3, 5, 7))
        kind = rng.choice(sys.argv[3] if len(sys.argv) > 3 else "GL")
        vecs = (gen_plane if kind == "G" else gen_line)(p, rng, ptsc[p])
        if vecs is None or len(vecs) != 14:
            continue
        M = Mat(p, vecs)
        fl = flats(M)
        if not profile_ok(M, fl):
            stats["rejected"] += 1
            continue
        nine = [F for F in fl[3] if pc(F) == 9]
        six = [F for F in fl[2] if pc(F) == 6]
        if nine:
            stats["G"] += 1
            stats["multiG"] += len(nine) > 1
            for K in nine:
                stats["Gtried"] += check_G(M, fl, K)
        elif six:
            stats["L"] += 1
            stats["twoL"] += len(six) > 1
            for L in six:
                stats["Ltried"] += check_L(M, fl, L)
        else:
            stats["rejected"] += 1
    print(stats)


main()
