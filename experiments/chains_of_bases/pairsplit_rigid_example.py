"""A chain of three bases in rank 5 with a valid root split whose pair split does not close.

x_0 = e0, W_0 = {e1, e2, e3, e4}.  Modulo x_1 the block W_1 is elementwise parallel to W_0, modulo
x_2 the block W_2 is elementwise parallel to W_1, and modulo x_0 the block W_0 is parallel to W_2
after a 3-cycle.  All three relations are rigid and the holonomy permutation is a 3-cycle, which
fixes no 2-subset.  The matroid is not strict (span(e0..e3) holds 12 of the 15 elements).
"""
from chainlib import Ctx
from pairsplit_chain import all_bases, study_chain


def v(*idx): return sum(1 << i for i in idx)


B0 = [v(0), v(1), v(2), v(3), v(4)]
B1 = [v(0, 1, 2), v(0, 2), v(2), v(0, 1, 2, 3), v(4)]
B2 = [v(0, 2, 3), v(0, 2), v(0, 3), v(1), v(4)]
bases = all_bases(B0 + B1 + B2)
res = list(study_chain([list(range(0, 5)), list(range(5, 10)), list(range(10, 15))], bases, Ctx(4)))
print("valid root splits: %d; pair split closes: %d; chain closes: %d" % (
    len(res), sum(r[2] for r in res), sum(r[3] for r in res)))
for x, slack, split, full in res:
    if not split: print("root split", x, "does not close")
