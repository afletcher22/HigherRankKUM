# Sprint 5 continuation handoff for Sol

Date: 2026-09-16/17

Repository: `afletcher22/HigherRankKUM`

Branch: `rank4-sprint5-six-block-audit`

Draft validation PR: #14, `Sprint 5 validation: six-block audit and exchange bridge`.
Keep it draft; do not merge to `main` yet.

This document continues `SPRINT5_SOL_HANDOFF.md`.  The old handoff was correct
for commit `77f388f0d1d1c8b5874f6058a50719ad9984dcf6`, but substantial work has
landed since then.

## 1. First read these files

- `docs/research-ledger/SPRINT5_SIX_BLOCK_AUDIT.md`
- `docs/research-ledger/SPRINT5_CONTINUATION_PARITY.md`
- `HigherRankKUM/FundamentalCircuitExchange.lean`
- `HigherRankKUM/BinaryRelationParity.lean`
- `HigherRankKUM/PairCycleFundamentalCircuit.lean`
- `HigherRankKUM/Rank4/GcdTwoRepairDichotomy.lean`
- `HigherRankKUM/Rank4/GcdTwoRepairParity.lean`
- `experiments/sprint5_finite_field_parity_audit.py`
- `experiments/sprint5_finite_field_parity_result.json`

## 2. Certified checkpoint already obtained during this continuation

Commit `880edce19d530df3fb2a07a3b4bdf21e05070296` is a known green checkpoint.
GitHub Actions run `35164729776` passed:

- dependency lock and vendored Rank3KUM integrity;
- targeted pair-cycle/local-repair Lean modules;
- every Sprint 2--5 certificate present at that commit;
- the full `lake build`.

This commit repaired the post-handoff Boolean parity theorem, whose only issue
was use of `native_decide` on an opaque existential proposition.

Later code commits are listed below.  The final code head targeted by the
current validation sequence is
`27b6cda75f9db470dc58e1fa75c834c8a594c9e3`; check the latest PR Actions run
before treating that later head as certified.  Documentation commits after it
do not alter Lean or certificates.

## 3. Post-handoff Lean work

### Fundamental circuit exchange criterion

`FundamentalCircuitExchange.lean` proves

`Matroid.IsBase.mem_fundCircuit_iff_exchange_isBase`.

For a basis `B`, an outside ground element `e`, and `f in B`, replacing `f`
with `e` is a basis iff `f` lies in the fundamental circuit of `e` over `B`.
This is the fixed-basis exchange lemma needed to rewrite local basis tests as
circuit incidences.

### Abstract Boolean parity algebra

`BinaryRelationParity.lean` contains:

- `flipRel`;
- input/output relabellings;
- classification of every Boolean bijection relation as identity or flip;
- `cyclicSatisfiable_four_relabel`: paired relabellings of four forced
  relations preserve cyclic satisfiability;
- `complementary_of_disjoint_bijections`: two disjoint Boolean bijections are
  exactly identity/flip in opposite order.

The last theorem is representation-free.

### Swap-only boundary is exactly complementary matchings

`Rank4/GcdTwoRepairParity.lean` proves

`swap_only_crossRelations_are_complementary`.

Using the existing local repair rigidity theorem, if a boundary admits the
wholesale swap but no common cross cell, then the left and dual-right
cross-relations are exactly the two complementary perfect matchings of the
Boolean square.  No representability assumption is used.

### Pair-cycle relation to fundamental circuits

`PairCycleFundamentalCircuit.lean` adds

`crossBaseRelation_iff_mem_fundCircuit`.

For two disjoint labelled two-element bases, a Boolean cross-base cell is
rewritten as membership of the replaced element of the first basis in the
fundamental circuit of the chosen outside element.  This is intended to be the
intrinsic bridge for the next parity proof.

## 4. Exact finite-field extension

A new exhaustive local certificate tests forced-preserving parity conservation
not only in binary representations but over GF(3) and GF(5).

Normalization sends the middle basis `C union D` to the coordinate basis in
`PG(3,q)`, then exhausts all projective lifts of the neighboring blocks.  It
is exact and factorized, not sampled.

| field | six-block contexts | legal nonidentity move occurrences | forced-preserving | parity flips |
| --- | ---: | ---: | ---: | ---: |
| GF(2) | 65,536 | 74,752 | 5,120 | **0** |
| GF(3) | 43,046,721 | 91,644,048 | 1,364,688 | **0** |
| GF(5) | 152,587,890,625 | 480,625,000,000 | 1,025,000,000 | **0** |

GF(2) independently reproduces the old binary audit counts exactly.  The new
script is included in `sprint5_verify.py`, so CI now reruns it with the other
Sprint 5 certificates.

Interpretation: parity conservation is very unlikely to be a binary accident.
This is still computational evidence, not an all-field or representation-free
theorem.

## 5. Strongest current proof direction

Do not restart the potential search.  The best next move is to finish the local
rigidity theorem.

There are two routes, in preferred order:

1. **Intrinsic fundamental-circuit route.** Use
   `crossBaseRelation_iff_mem_fundCircuit` to encode a forced relation as the
   two singleton incidences of outside fundamental circuits with a
   two-element basis.  Show that if an adjacent repartition preserves
   forcedness at all four affected positions, the four induced identity/flip
   changes have even parity.  If this works, it should be representation-free.

2. **All-field representable route.** Normalize `C,D` to a coordinate basis.
   In one forced orientation write neighboring columns schematically as

   ```
   b0 = d0 + a c0 + b c1
   b1 = d1 + c c0 + d c1
   e0 = c0 + u d0 + v d1
   e1 = c1 + w d0 + z d1.
   ```

   For a representative cross repartition `Q={c0,d0}, R={c1,d1}`, determinant
   reduction forces paired zero/nonzero conditions when all four new relations
   remain forced; the four relation changes then have even parity.  The other
   cross partitions are label permutations and the wholesale swap is the last
   case.  This skeleton explains the GF(2)/GF(3)/GF(5) data, but it has not yet
   been promoted to a theorem.

The intrinsic route is more valuable if it remains tractable.

## 6. Global bottleneck remains open

The finite binary N=5/N=7 audits still show every obstructed strict state has
a productive cross repair.  N=7 has 25,152 normalized obstructed states; all
25,152 have a direct orientable cross repair, while 728 have no strict
closure-potential ascent.

The missing theorem is still an **existence** theorem: from an arbitrary
obstructed rank-four state, prove that some boundary/repartition creates slack
(or otherwise escapes) or gives whatever ascent mechanism is ultimately
needed.  Local parity conservation alone does not produce such a boundary.

Do not claim:

- universal one-step repair;
- arbitrary-N escape-or-ascent;
- representation-free forced-parity conservation yet;
- full rank-four KUM;
- full KUM.

## 7. Commit chronology after the old handoff

Important continuation commits:

- `97d867994e04bd133cab608961c5baaaa97ae177` — fundamental-circuit exchange criterion.
- `880edce19d530df3fb2a07a3b4bdf21e05070296` — fix Boolean parity proof; fully green checkpoint.
- `ad30776b8ec027eaf98a7755f6d57d1a63263d1e` — finite-field parity audit script.
- `b5eac2ac10327a8635c02cf58cfaed27b9977b2d` — exact GF(2)/GF(3)/GF(5) output.
- `da82a0a5e2dc9c69ff8f2cb4c014ead58b572996` — wire finite-field audit into Sprint 5 verifier.
- `bbb469513346f035665794555619aa4c4c9207f9` — disjoint Boolean bijections are complementary.
- `66d3a6ae21b96bfdaf603aa333ed999c16d66de2` — rank-four swap-only complementary theorem.
- `25e3ef74b31f4d02ffff435889706a38149623c7` — export Sprint 5 repair parity theorem.
- `dbc44fc0258c0ea4ca3b292c4dc8ed08c915e052` — pair-cycle/fundamental-circuit bridge.
- `27b6cda75f9db470dc58e1fa75c834c8a594c9e3` — export that bridge.

## 8. Reproduction

For the finite certificates:

```bash
python3 experiments/sprint5_verify.py
```

The finite-field audit has an internal GF(2) regression against the earlier
binary totals and committed exact expected output.

For formal validation, use the existing GitHub Actions workflow/`lake build`;
do not infer green status merely because a file is exported.
