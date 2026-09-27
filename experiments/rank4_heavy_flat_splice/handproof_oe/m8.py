"""8-element framework: S = {s0,s1,s2,s3} basis, A0 = (a, ab), A1 = (b, bb), A0+A1 basis.

Rank-4 matroid rank axioms as in local_xp.py (var(X, v) = "r(X) >= v").
Predicates on ordered splits (P, Q):
  valid     : A0+P and Q+A1 bases
  Pcross    : exists labelling u,v of P: u||b, v||bb in M/A0 and u||bb, v||b in M/Q
  Qcross    : exists labelling w,z of Q: w||a, z||ab in M/P and w||ab, z||a in M/A1
  alpha     : P matched to {b,bb} in M/A0; gamma: P matched to {b,bb} in M/Q
  beta      : Q matched to {a,ab} in M/P;  delta: Q matched to {a,ab} in M/A1
  pa, pc, pb, pd : parities (relative to the sorted orientation of P / Q)
"""
import itertools
from pysat.solvers import Cadical195

n, r = 8, 4
var = lambda X, v: 5 * X + v
pc = lambda X: bin(X).count("1")
mask = lambda c: sum(1 << x for x in c)
s0, s1, s2, s3, a, ab, b, bb = range(8)
S = [s0, s1, s2, s3]
A0, A1 = (a, ab), (b, bb)
names = ["s0", "s1", "s2", "s3", "a", "ab", "b", "bb"]


def base_clauses(nn=n, rr=r):
    cls = []
    for X in range(1 << nn):
        for v in range(1, rr):
            cls.append([-var(X, v + 1), var(X, v)])
        for v in range(pc(X) + 1, rr + 1):
            cls.append([-var(X, v)])
        if pc(X) >= 1:
            cls.append([var(X, 1)])
    for X in range(1 << nn):
        for p in range(nn):
            if X >> p & 1:
                continue
            T = X | 1 << p
            for v in range(1, rr + 1):
                cls.append([-var(X, v), var(T, v)])
                if v < rr:
                    cls.append([-var(T, v + 1), var(X, v)])
            for q in range(p + 1, nn):
                if X >> q & 1:
                    continue
                U, Xq = T | 1 << q, X | 1 << q
                for v in range(1, rr + 1):
                    c = [-var(U, v), var(T, v), var(Xq, v), var(X, v)]
                    if v >= 2:
                        c.append(-var(X, v - 1))
                    cls.append(c)
    return cls


Bs = lambda xs: var(mask(xs), 4)


class F:
    """Formula builder with Tseitin gates."""

    def __init__(self, nn=n):
        self.cls = base_clauses(nn)
        self.nv = 5 * (1 << nn) + 10

    def new(self):
        self.nv += 1
        return self.nv

    def AND(self, lits):
        g = self.new()
        for l in lits:
            self.cls.append([-g, l])
        self.cls.append([g] + [-l for l in lits])
        return g

    def OR(self, lits):
        g = self.new()
        self.cls.append([-g] + list(lits))
        for l in lits:
            self.cls.append([g, -l])
        return g

    def NOT(self, l):
        return -l

    def XOR(self, x, y):
        g = self.new()
        self.cls += [[-g, x, y], [-g, -x, -y], [g, -x, y], [g, x, -y]]
        return g

    def solve(self, extra=(), assumptions=()):
        s = Cadical195(bootstrap_with=self.cls + [list(c) for c in extra])
        res = s.solve(assumptions=list(assumptions))
        m = s.get_model() if res else None
        s.delete()
        return res, m


def par(ctx, u, t):
    """u || t in M/ctx (ctx a 2-set, u, t non-loops assumed): ctx+u+t not a basis"""
    return -Bs(tuple(ctx) + (u, t))


def splits():
    out = []
    for P in itertools.combinations(S, 2):
        Q = tuple(s for s in S if s not in P)
        out.append((P, Q))
    return out


def preds(f, P, Q):
    """returns dict of literals for split (P,Q), P,Q sorted tuples (orientation = sorted)."""
    p, pb = P
    q, qb = Q
    d = {}
    d["valid"] = f.AND([Bs(A0 + P), Bs(Q + A1)])
    # alpha: P matched to b,bb in M/A0.  straight: p||b, pb||bb ; twisted: p||bb, pb||b
    a_str = f.AND([par(A0, p, b), par(A0, pb, bb)])
    a_tw = f.AND([par(A0, p, bb), par(A0, pb, b)])
    c_str = f.AND([par(Q, p, b), par(Q, pb, bb)])
    c_tw = f.AND([par(Q, p, bb), par(Q, pb, b)])
    b_str = f.AND([par(P, q, a), par(P, qb, ab)])
    b_tw = f.AND([par(P, q, ab), par(P, qb, a)])
    d_str = f.AND([par(A1, q, a), par(A1, qb, ab)])
    d_tw = f.AND([par(A1, q, ab), par(A1, qb, a)])
    d["alpha"] = f.OR([a_str, a_tw])
    d["gamma"] = f.OR([c_str, c_tw])
    d["beta"] = f.OR([b_str, b_tw])
    d["delta"] = f.OR([d_str, d_tw])
    d["a_str"], d["a_tw"], d["c_str"], d["c_tw"] = a_str, a_tw, c_str, c_tw
    d["b_str"], d["b_tw"], d["d_str"], d["d_tw"] = b_str, b_tw, d_str, d_tw
    d["Pcross"] = f.OR([f.AND([a_str, c_tw]), f.AND([a_tw, c_str])])
    d["Qcross"] = f.OR([f.AND([b_str, d_tw]), f.AND([b_tw, d_str])])
    d["Pstraight"] = f.OR([f.AND([a_str, c_str]), f.AND([a_tw, c_tw])])
    d["Qstraight"] = f.OR([f.AND([b_str, d_str]), f.AND([b_tw, d_tw])])
    allm = f.AND([d["alpha"], d["beta"], d["gamma"], d["delta"]])
    d["allmatched"] = allm
    d["oddbad"] = f.AND([allm, f.XOR(d["Pcross"], d["Qcross"])])
    d["evenbad"] = f.OR([d["Pcross"], d["Qcross"]])
    return d


def fmt(sp):
    return "{" + ",".join(names[x] for x in sp[0]) + "|" + ",".join(names[x] for x in sp[1]) + "}"
