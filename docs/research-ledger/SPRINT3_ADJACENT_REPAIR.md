# Adjacent re-pairing: bounded continuation after Sprint 2

Date: 2026-09-15. Branch: `rank4-sprint2-fixes-repair`.

## Scope and evidence

This continuation tests an admissibility-preserving exchange of one element
between neighboring pair blocks. It concerns exactly the labelled binary
rank-four matroid from the Sprint 2 certificate, not all rank-four matroids.
The new general boundary criterion below has an informal proof; it is not
yet a Lean theorem. The finite results are exact Python certificates.

## General boundary criterion (checked informal derivation)

Let `0 < h < N` and let `P` be an admissible cycle of `N` disjoint pairs.
Replace `P_i,P_{i+1}` by disjoint pairs `Q_i,Q_{i+1}` with the same four-element
union. Leave other blocks unchanged. Exactly two aligned windows can change
their underlying element sets:

1. the `h`-block window ending at `i`, starting at `i-h+1` modulo `N`;
2. the `h`-block window starting at `i+1`.

Proof: a consecutive block interval containing both changed positions has
the same union as before; one containing neither is unchanged. To contain
`i` but not its successor it must end at `i`. To contain `i+1` but not its
predecessor it must start at `i+1`. The proper-window condition `h<N` makes
these two boundary windows distinct. This includes `h=1` and `N=2,h=1`.

Therefore the new cycle is admissible **if and only if those two new windows
are bases**. This is only a criterion for an individual move; it does not
prove existence of a useful move or termination of repeated moves.

There is a rank-two interpretation. Let `U=P_i ∪ P_{i+1}` and let `L` and `R`
be the unchanged `h-1`-block cores of the two boundary windows. Each core is
independent with `2h-2` elements and disjoint from `U`. Define the rank-two
matroids on `U` by restricting `M/L` and `M/R` to `U`. A choice `S⊆U`, `|S|=2`,
can occupy position `i` precisely when `S` is a basis of the left matroid and
`U\S` is a basis of the right matroid. Equivalently, `S` is a common basis of
the left matroid and the dual of the right one. This gives a six-choice local
test, with the old assignment and whole-block swap distinguished from the
four single-element exchanges investigated here.

## Reproducible exact experiment

Run from the repository root:

```bash
python3 experiments/sprint2_pair_obstruction_certificate.py
python3 experiments/sprint3_adjacent_repair_certificate.py
```

Expected output is preserved in
`experiments/sprint3_adjacent_repair_result.json`.

Elements are labels `0,...,9`, with vector values
`[1,2,4,8,1,14,4,7,6,9]`. Equal vector values at different labels remain
distinct parallel elements. Internal pair orientation and cyclic rotation
are quotiented out; reflection is retained. Fixing the pair containing label
0 first and sorting within each pair gives exactly `9! / 2^4 = 22,680`
candidate pair cycles, with no matroid-isomorphism quotient.

| Exact quantity | Result |
| --- | ---: |
| Candidate cyclic pair decompositions | 22,680 |
| Admissible pair cycles | 576 |
| Unorientable admissible pair cycles | 8 |
| Unorientable cycles without a one-step successful adjacent exchange | 0 |
| Directed admissible exchange edges | 2,864 |
| Connected components of the exchange graph | 1 |
| Admissible neighbors of the original obstruction | 6 |
| Orientable neighbors of the original obstruction | 6 |
| Two-boundary vs all-window checks | 11,520 |

The checker verifies full support and the forced-parity characterization on
all 576 admissible cycles. Positive orientation witnesses are checked by a
separate rank implementation on every cyclic four-window. The original
certificate compares both rank implementations on all 1,024 subsets and
checks strict density on all 1,022 nonempty proper subsets.

## Explicit repair and CBO

Original pair labels:

`(0,1), (2,3), (4,5), (6,7), (8,9)`.

Exchange labels 1 and 2 between the first two blocks:

`(0,2), (1,3), (4,5), (6,7), (8,9)`.

The second local relation now allows three combinations. Orient the sorted
pairs by bits `(1,1,1,0,1)`. This gives the CBO in element labels

`2,0,3,1,5,4,6,7,9,8`.

Its vector values are

`4,1,8,2,14,1,4,7,9,6`.

All ten cyclic four-windows have rank four. Thus this particular matroid is
explicitly cyclically orderable despite the original fixed-pair obstruction.

## Research decision

The adjacent exchange operation has passed a complete test over the pair
cycles of this one matroid. It is worth investigating structurally, but this
does not establish a universal one-step repair, connectivity of all such
graphs, or gcd-two KUM. The older eighteen-element one-break failures, if
independently certified, would also obstruct a universal one-step repair:
an orientable re-pairing is included in the more permissive four-element
chunk permutation operation. They would not rule out several consecutive
admissibility-preserving exchanges.

Recommended next question: characterize when the two rank-two boundary
matroids permit a nontrivial common basis that creates local slack or changes
the total forced parity. Before positing universal connectivity, certify one
historical larger obstruction and explore its entire admissible exchange
component within an explicit budget. Keep that task separate from completing
the Lean bridge from compatibility solutions to flattened cyclic orderings.
