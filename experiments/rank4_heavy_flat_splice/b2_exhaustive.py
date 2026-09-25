"""(B2) exhaustive, representation-free check.

Base M0: 10 elements, rank 4, uniformly dense (points<=2, lines<=5, planes<=7), K a 6-point
plane, C = 4 elements with r(C)=2, L = cl(C).  Every site CBO must use skeleton
S1 = k1 k2 k3 c1 k4 c2 k5 c3 k6 c4, and its windows are bases iff
  * triples (k1,k2,k3), (k2,k3,k4), (k6,k1,k2) are independent in M|K;
  * pairs (k3,k4),(k4,k5),(k5,k6),(k6,k1) are bases of N = (M/L)|K;
  * c1,c2,c3,c4 alternate between distinct points of L (always possible: C has >=2 points,
    each point of multiplicity <=2).
N is described by: loops Lam = L∩K (|Lam|<=1, a non-parallel element) and classes
X = (Pi∩K) - Lam for planes Pi ⊇ L, where each F = X ∪ Lam is a flat of K of rank <=2,
|F| <= 3 (|Pi|<=7), and distinct F's meet exactly in Lam.

We enumerate ALL loopless rank-3 matroids on 6 labelled elements with points<=2, lines<=5
(up to isomorphism), ALL admissible (Lam, class partitions), and search an S1 ordering.
Any realizable configuration satisfies these necessary conditions, so success on all of
them proves (B2).
"""
import itertools, sys, time

E = range(6)


def set_partitions(items):
    items = list(items)
    if not items:
        yield []
        return
    first, rest = items[0], items[1:]
    for p in set_partitions(rest):
        yield [[first]] + p
        for i in range(len(p)):
            yield p[:i] + [[first] + p[i]] + p[i + 1:]


def linear_spaces(points):
    """all families of lines (size>=3 subsets) pairwise meeting in <=1 point."""
    pts = list(points)
    cands = [frozenset(s) for r in range(3, len(pts) + 1) for s in itertools.combinations(pts, r)]
    out = []

    def rec(i, chosen):
        if i == len(cands):
            out.append(list(chosen))
            return
        rec(i + 1, chosen)
        c = cands[i]
        if all(len(c & d) <= 1 for d in chosen):
            # maximality: a line must not be a proper subset of another chosen line
            chosen.append(c)
            rec(i + 1, chosen)
            chosen.pop()
    rec(0, [])
    # a linear space: lines are maximal (no chosen line contained in another), pairs <=1 line
    res = []
    for fam in out:
        if any(a < b for a in fam for b in fam):
            continue
        res.append(fam)
    return res


def make_rank(classes, lines_on_classes):
    """rank function on subsets of E for matroid given by parallel classes + linear space."""
    cls_of = {}
    for i, c in enumerate(classes):
        for x in c:
            cls_of[x] = i
    m = len(classes)

    def rk(S):
        cs = {cls_of[x] for x in S}
        if len(cs) <= 1:
            return len(cs)
        if len(cs) == 2:
            return 2
        for L in lines_on_classes:
            if cs <= L:
                return 2
        return 3
    return rk


def all_matroids():
    seen = set()
    out = []
    for part in set_partitions(E):
        if any(len(b) > 2 for b in part):
            continue
        m = len(part)
        if m < 3:
            continue
        for ls in linear_spaces(range(m)):
            if any(len(L) == m for L in ls):
                continue  # all points collinear -> rank 2
            rk = make_rank(part, ls)
            # line sizes (as element counts) <= 5
            ok = True
            for L in ls:
                if sum(len(part[i]) for i in L) > 5:
                    ok = False
            for i, j in itertools.combinations(range(m), 2):
                if not any(i in L and j in L for L in ls) and len(part[i]) + len(part[j]) > 5:
                    ok = False
            if not ok:
                continue
            dep3 = frozenset(t for t in itertools.combinations(E, 3) if rk(t) < 3)
            dep2 = frozenset(t for t in itertools.combinations(E, 2) if rk(t) < 2)
            key = None
            for perm in itertools.permutations(E):
                k2 = tuple(sorted(tuple(sorted(perm[x] for x in t)) for t in dep2))
                k3 = tuple(sorted(tuple(sorted(perm[x] for x in t)) for t in dep3))
                if key is None or (k2, k3) < key:
                    key = (k2, k3)
            if key in seen:
                continue
            seen.add(key)
            out.append((part, ls, rk))
    return out


def flats_rank_le2(rk):
    """closure within K of a set."""
    def cl(S):
        r = rk(S)
        return frozenset(x for x in E if rk(set(S) | {x}) == r)
    return cl


def admissible_N(rk):
    cl = flats_rank_le2(rk)
    lam_choices = [frozenset()] + [frozenset([x]) for x in E if cl([x]) == frozenset([x])]
    for Lam in lam_choices:
        rest = [x for x in E if x not in Lam]
        for part in set_partitions(rest):
            ok = True
            Fs = []
            for X in part:
                F = cl(set(X) | set(Lam))
                if rk(F) > 2 or len(F) > 3 or (F - Lam) != frozenset(X):
                    ok = False
                    break
                Fs.append(F)
            if not ok:
                continue
            if any((F & G) != Lam for F, G in itertools.combinations(Fs, 2)):
                continue
            yield Lam, part


def s1_exists(rk, Lam, part):
    cls = {}
    for i, X in enumerate(part):
        for x in X:
            cls[x] = i

    def good(a, b):
        return a not in Lam and b not in Lam and cls[a] != cls[b]
    for o in itertools.permutations(E):
        k1, k2, k3, k4, k5, k6 = o
        if not (good(k3, k4) and good(k4, k5) and good(k5, k6) and good(k6, k1)):
            continue
        if rk((k1, k2, k3)) == 3 and rk((k2, k3, k4)) == 3 and rk((k6, k1, k2)) == 3:
            return o
    return None


if __name__ == "__main__":
    t = time.time()
    Ms = all_matroids()
    print("loopless rank-3 matroids on 6 elements (points<=2, lines<=5), up to iso:", len(Ms),
          f"({time.time()-t:.1f}s)", flush=True)
    total = fails = 0
    for part, ls, rk in Ms:
        for Lam, Npart in admissible_N(rk):
            total += 1
            if s1_exists(rk, Lam, Npart) is None:
                fails += 1
                print("FAIL: classes", part, "lines", [sorted(L) for L in ls], "Lam", sorted(Lam),
                      "N-classes", Npart, flush=True)
    print("admissible (M|K, N) configurations:", total, " without S1 ordering:", fails,
          f"({time.time()-t:.1f}s)")
