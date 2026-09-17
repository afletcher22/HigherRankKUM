# Sprint 5 continuation — parity beyond binary and intrinsic circuit bridge

Date: 2026-09-16/17.

Branch: `rank4-sprint5-six-block-audit`.

This note continues `SPRINT5_SIX_BLOCK_AUDIT.md` and the handoff
`docs/handoffs/SPRINT5_SOL_HANDOFF.md`.  It records work performed after the
original Sprint 5 checkpoint `77f388f0d1d1c8b5874f6058a50719ad9984dcf6`.

## 1. Validation repair

The first post-handoff parity formalization had a narrow compiler failure: the
last step of `BinaryRelationParity.cyclicSatisfiable_four_relabel` used
`native_decide` on an opaque existential relation proposition and Lean could
not synthesize a `Decidable` instance.

Commit `880edce19d530df3fb2a07a3b4bdf21e05070296` replaced this with explicit
case splitting on the two Boolean relabellings followed by simplification of
the four Boolean relations.  GitHub Actions run `35164729776` then passed the
targeted Lean stack, every Sprint 2--5 certificate, and the full build.

The mathematical statement is unchanged: if four local relations are forced
bijections, paired input/output label swaps preserve cyclic satisfiability.

## 2. Exact finite-field extension of the six-block audit

A new certificate

`experiments/sprint5_finite_field_parity_audit.py`

extends the local forced-preserving parity audit from GF(2) to GF(3) and
GF(5).  The calculation is exact, not randomized sampling.

### Normalization

For a represented rank-four local context, the middle blocks `C,D` have
`C union D` a basis.  Row operations send these four columns to the coordinate
basis of the four-dimensional vector space, while independent nonzero scaling
of individual columns does not change the represented matroid.  Thus the
remaining columns may be enumerated as projective points of `PG(3,q)`.

Repeated projective points in different labelled blocks are retained as
parallel labelled elements.  Each pair itself contains distinct projective
points because adjacent two-block unions are bases.

The enumeration then exhausts every old six-block context

`A,B,C,D,E,F`

whose five adjacent pair unions are bases and whose four old endpoint
relations are forced bijections, and every legal nonidentity repartition
`C,D -> Q,R`.  If all four new relations remain forced, it tests whether the
combined Boolean parity changes.

The implementation factorizes the independent left/right endpoint lifts, so
very large context counts can be certified without iterating over every full
six-block tuple separately.  The GF(2) output independently reproduces the
previous binary certificate exactly.

### Exact counts

| field | projective points | six-block contexts | legal move occurrences | forced-preserving | slack created | parity flips |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| GF(2) | 15 | 65,536 | 74,752 | 5,120 | 69,632 | **0** |
| GF(3) | 40 | 43,046,721 | 91,644,048 | 1,364,688 | 90,279,360 | **0** |
| GF(5) | 156 | 152,587,890,625 | 480,625,000,000 | 1,025,000,000 | 479,600,000,000 | **0** |

The committed output is
`experiments/sprint5_finite_field_parity_result.json`, and the certificate is
now included in `experiments/sprint5_verify.py`.

### What this establishes and what it does not

The exact evidence strongly rejects the hypothesis that forced-preserving
parity conservation is a peculiarity of binary representations.  It holds for
all normalized represented local contexts over GF(2), GF(3), and GF(5).

It does **not** by itself prove:

- the statement over every field;
- the statement for every representable matroid;
- a representation-free matroid theorem;
- a global escape-or-ascent existence theorem.

The first two now look like natural symbolic targets rather than speculative
generalizations.

## 3. Representation-free Boolean structure

`HigherRankKUM/BinaryRelationParity.lean` now proves

`complementary_of_disjoint_bijections`:

> two pointwise-disjoint full-support functional relations on `Bool` are
> exactly the two complementary perfect matchings, identity/flip in one order
> or the other.

Combining this with the pre-existing local repair rigidity theorem yields
`HigherRankKUM/Rank4/GcdTwoRepairParity.lean` and the theorem

`swap_only_crossRelations_are_complementary`.

Consequently the exceptional swap-only boundary geometry has an exact
representation-free description: its two boundary cross-relations are the
complementary Boolean matchings.  This sharpens the earlier theorem that they
are merely bijections.

No representability, simplicity, or finite-field hypothesis is used in this
statement.

## 4. Fundamental-circuit bridge

The post-handoff file `FundamentalCircuitExchange.lean` proved the fixed-basis
exchange criterion

`f in fundCircuit e B  <->  insert e B \ {f} is a base`.

The continuation adds `PairCycleFundamentalCircuit.lean`, whose intended
bridge is

`crossBaseRelation_iff_mem_fundCircuit`:

> for two disjoint labelled two-element bases, a Boolean cross-base cell is
> exactly membership of the *replaced* first-base element in the fundamental
> circuit of the chosen outside element.

This is the useful intrinsic translation of the pair-cycle orientation
relation.  It removes coordinates from the local state description and makes
the next parity theorem a question about transformations of two singleton
fundamental-circuit incidences.

The file is exported by `HigherRankKUM.lean`; its current validation status is
to be read from the continuation handoff/current CI rather than inferred from
this research note.

## 5. Emerging all-field proof shape

The finite-field audit suggests a compact coordinate proof may exist over an
arbitrary field.  Normalize

`C = {c0,c1}` and `D = {d0,d1}`

to a basis.  After relabelling/scaling in one forced orientation, neighboring
blocks can be written schematically as

```
b0 = d0 + a c0 + b c1
b1 = d1 + c c0 + d c1

e0 = c0 + u d0 + v d1
e1 = c1 + w d0 + z d1.
```

For the representative cross repartition

`Q={c0,d0}, R={c1,d1}`,

direct determinant reduction gives the following pattern:

- the new middle-left relation is forced only under a zero/nonzero pattern
  such as `b != 0, d = 0`;
- retaining forcedness at the adjacent outer relation then forces the paired
  condition `a = 0`;
- symmetrically the right side forces `w != 0, u = 0` and then the paired
  outer zero condition;
- the resulting changes of the four Boolean forced relations occur in an
  even pattern.

The other cross partitions are relabellings of this calculation; the wholesale
swap is the remaining case.  This is a proof skeleton only.  It should not be
cited as an all-field theorem until the cases are written cleanly and audited.

A representation-free proof via the new fundamental-circuit bridge would be
stronger and should be preferred if it stays manageable.

## 6. Global status

The main Sprint 5 bottleneck is unchanged.

For binary N=5 and N=7 the exhaustive certificates show that every obstructed
strict state has a productive cross repair.  The six-block audits show that a
forced-preserving repair cannot change parity in GF(2), GF(3), or GF(5).
But no theorem yet proves that, in every obstructed rank-four state, some
boundary necessarily creates slack or raises the chosen potential.

In particular, do not upgrade the current results to any of the following:

- universal one-step orientability;
- global escape-or-ascent for arbitrary N;
- representation-free parity conservation under every legal repartition;
- full rank-four KUM;
- full KUM.

The next mathematically meaningful target is to close local parity
conservation intrinsically (or first over arbitrary represented fields), then
use that rigidity to attack existence of a productive boundary rather than
searching for a new potential by brute force.
