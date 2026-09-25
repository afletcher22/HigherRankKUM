"""Heavy-flat splice (HFS): constructive reinsertion of B = T_F + T_X into a CBO of M-B
inside a regular stretch w.r.t. a flat F of rank rho in {1,2,3}.

rho=3 (plane):  stretch  w u x1 x2 x3 v y   (F: w,x*,y ; outside: u,v)   -> two-gap in M|F
rho=1 (point):  stretch  w p x1 x2 x3 p' y  (F: p,p' ; outside: w,x*,y)  -> two-gap in M/F
rho=2 (line):   stretches  LXXLLX / XLLXXL / LXLXLX / XLXLXL           -> rank-2 splices in M|F, M/F
Every construction is verified with is_cbo by the caller.
"""
import itertools
from kum import *
from bsl import two_gap as two_gap_M


class Contract:
    """rank oracle of M/F restricted (for rank-3 two-gap in M/P)."""
    def __init__(self, M, Fmask):
        self.M = M
        self.F = Fmask
        self.rF = M.r(Fmask)

    def rk(self, elems):
        m = self.F
        for e in elems:
            m |= 1 << e
        return self.M.r(m) - self.rF


def two_gap_oracle(R, T, p, a, b, c, q):
    for d in itertools.permutations(T):
        if (R.rk([p, a, d[0]]) == 3 and R.rk([a, d[0], d[1]]) == 3 and
                R.rk([d[1], d[2], b]) == 3 and R.rk([d[2], b, c]) == 3):
            return ("first", d)
    for d in itertools.permutations(T):
        if (R.rk([a, b, d[0]]) == 3 and R.rk([b, d[0], d[1]]) == 3 and
                R.rk([d[1], d[2], c]) == 3 and R.rk([d[2], c, q]) == 3):
            return ("second", d)
    return None


def rank2_splice(R, left, right, pair):
    """order (s,t) of pair with {left,s},{s,t},{t,right} all rank 2 in oracle R."""
    for s, t in (pair, pair[::-1]):
        if R.rk([left, s]) == 2 and R.rk([s, t]) == 2 and R.rk([t, right]) == 2:
            return (s, t)
    return None


def splice_hfs(M, F, TF, TX, sigma):
    n = len(sigma)
    inF = [(F >> x) & 1 for x in sigma]
    rho = M.r(F)
    at = lambda i: sigma[i % n]
    f = lambda i: inF[i % n]
    for i in range(n):
        if rho == 3:
            # w u x1 x2 x3 v y at i..i+6
            if [f(i + j) for j in range(7)] == [1, 0, 1, 1, 1, 0, 1]:
                w, u, x1, x2, x3, v, y = (at(i + j) for j in range(7))
                g = two_gap_oracle(M, list(TF), w, x1, x2, x3, y)
                if g is None:
                    raise AssertionError("two-gap failed (rank 3 plane)")
                c = TX[0]
                block = ([x1, g[1][0], g[1][1], c, g[1][2], x2, x3] if g[0] == "first"
                         else [x1, x2, g[1][0], c, g[1][1], g[1][2], x3])
                rot = [at(i + 2 + j) for j in range(n)]
                return block + rot[3:], ("plane", g[0])
        elif rho == 1:
            if [f(i + j) for j in range(7)] == [0, 1, 0, 0, 0, 1, 0]:
                w, p1, x1, x2, x3, p2, y = (at(i + j) for j in range(7))
                R = Contract(M, F)
                g = two_gap_oracle(R, list(TX), w, x1, x2, x3, y)
                if g is None:
                    raise AssertionError("two-gap failed (point)")
                p = TF[0]
                block = ([x1, g[1][0], g[1][1], p, g[1][2], x2, x3] if g[0] == "first"
                         else [x1, x2, g[1][0], p, g[1][1], g[1][2], x3])
                rot = [at(i + 2 + j) for j in range(n)]
                return block + rot[3:], ("point", g[0])
        else:
            RL = M  # rank on L-elements (line restriction)
            RX = Contract(M, F)
            pat = [f(i + j) for j in range(6)]
            s = [at(i + j) for j in range(6)]
            if pat == [1, 0, 0, 1, 1, 0]:      # l2 x1 x2 | l3 l4 x3  -> insert L L X X after x2
                l2, x1, x2, l3, l4, x3 = s
                lo = rank2_splice(RL, l2, l3, TF); xo = rank2_splice(RX, x2, x3, TX)
                ins = [lo[0], lo[1], xo[0], xo[1]] if lo and xo else None
                cut = 3
            elif pat == [0, 1, 1, 0, 0, 1]:    # x2 l3 l4 | x3 x4 l5 -> insert X X L L after l4
                x2, l3, l4, x3, x4, l5 = s
                xo = rank2_splice(RX, x2, x3, TX); lo = rank2_splice(RL, l4, l5, TF)
                ins = [xo[0], xo[1], lo[0], lo[1]] if lo and xo else None
                cut = 3
            elif pat == [0, 1, 0, 1, 0, 1]:    # x1 l2 x2 | l3 x3 l4 -> insert L X L X after x2
                x1, l2, x2, l3, x3, l4 = s
                lo = rank2_splice(RL, l2, l3, TF); xo = rank2_splice(RX, x2, x3, TX)
                ins = [lo[0], xo[0], lo[1], xo[1]] if lo and xo else None
                cut = 3
            elif pat == [1, 0, 1, 0, 1, 0]:    # l1 x1 l2 | x2 l3 x3 -> insert X L X L after l2
                l1, x1, l2, x2, l3, x3 = s
                xo = rank2_splice(RX, x1, x2, TX); lo = rank2_splice(RL, l2, l3, TF)
                ins = [xo[0], lo[0], xo[1], lo[1]] if lo and xo else None
                cut = 3
            else:
                continue
            if ins is None:
                raise AssertionError("rank-2 splice failed")
            rot = [at(i + j) for j in range(n)]
            return rot[:cut] + ins + rot[cut:], ("line", tuple(pat))
    return None, None
