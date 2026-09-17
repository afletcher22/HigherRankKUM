# Sprint 5 continuation handoff for Sol

Date: 2026-09-16/17

Repository: `afletcher22/HigherRankKUM`

Branch: `rank4-sprint5-six-block-audit`

Draft validation PR: #14, `Sprint 5 validation: six-block audit and exchange bridge`.
Keep it draft; do not merge to `main` yet.

This document continues `SPRINT5_SOL_HANDOFF.md`. The old handoff was correct
for commit `77f388f0d1d1c8b5874f6058a50719ad9984dcf6`, but substantial work has
landed since then.

## 1. First read these files

- `docs/research-ledger/SPRINT5_SIX_BLOCK_AUDIT.md`
- `docs/research-ledger/SPRINT5_CONTINUATION_PARITY.md`
- `docs/research-ledger/SPRINT5_ALL_FIELD_PARITY_PROOF.md`
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

Later code commits are listed below. The final code head targeted by the
current validation sequence is
`27b6cda75f9db470dc58e1fa75c834c8a594c9e3`; check the latest PR Actions run
before treating that later head as certified. Documentation commits after it
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
Boolean square. No representability assumption is used.

### Pair-cycle relation to fundamental circuits

`PairCycleFundamentalCircuit.lean` adds

`crossBaseRelation_iff_mem_fundCircuit`.

For two disjoint labelled two-element bases, a Boolean cross-base cell is
rewritten as membership of the replaced element of the first basis in the
fundamental circuit of the chosen outside element. This is the intrinsic
bridge for the next representation-free parity proof.

A useful immediate corollary to formalize next is: once the cross relation is
known to be a bijection, its identity-vs-flip bit is determined by one such
fundamental-circuit incidence. That turns the parity obstruction into an XOR
of ordinary circuit-membership bits.

## 4. Exact finite-field extension

A new exhaustive local certificate tests forced-preserving parity conservation
not only in binary representations but over GF(3) and GF(5).

Normalization sends the middle basis `C union D` to the coordinate basis in
`PG(3,q)`, then exhausts all projective lifts of the neighboring blocks. It is
exact and factorized, not sampled.

| field | six-block contexts | legal nonidentity move occurrences | forced-preserving | parity flips |
| --- | ---: | ---: | ---: | ---: |
| GF(2) | 65,536 | 74,752 | 5,120 | **0** |
| GF(3) | 43,046,721 | 91,644,048 | 1,364,688 | **0** |
| GF(5) | 152,587,890,625 | 480,625,000,000 | 1,025,000,000 | **0** |

GF(2) independently reproduces the old binary audit counts exactly. The new
script is included in `sprint5_verify.py`, so CI reruns it with the other
Sprint 5 certificates.

The forced-preserving totals fit the closed form

`q^8 * 4 (q-1)^2 (q^2 + (q-1)^2)`

for q=2,3,5. This is now explained by the arbitrary-field determinant proof
below: the four cross repartitions contribute the first family of cases and
the wholesale swap contributes the second.

## 5. New result: represented local parity holds over every field

`docs/research-ledger/SPRINT5_ALL_FIELD_PARITY_PROOF.md` gives a complete
checked informal linear-algebra proof of the following local result:

> In a rank-four matroid represented over an arbitrary field, a legal adjacent
> repartition that keeps all four affected endpoint relations forced preserves
> their total identity/flip parity.

This is no longer merely GF(2)/GF(3)/GF(5) evidence.

### Proof shape

Gauge-relabel the six old blocks so the four old forced relations are all
identity. Since the middle union `C union D` is a basis, send it to a coordinate
basis and write

```
b0 = d0 + a c0 + b c1
b1 = d1 + c c0 + d c1

e0 = c0 + u d0 + v d1
e1 = c1 + w d0 + z d1.
```

The outer identity relations similarly express `A` modulo `B` and `F` modulo
`E`; their extra coefficients cancel from the relevant determinants.

There are exactly five nonidentity ordered repartitions of `C union D`: four
cross partitions and the wholesale swap. For each cross partition, the four
new 2x2 determinant-support matrices are explicit. Requiring all four to be
permutation supports forces zero/nonzero conditions under which the new
orientations are respectively

- `id,id,id,id`;
- `id,flip,id,flip`;
- `flip,id,flip,id`;
- `flip,flip,flip,flip`.

Every case has even parity. For the wholesale swap, the left two relation bits
are equal and the right two relation bits are equal, again giving even parity.
No finiteness or characteristic assumption is used.

### Scope

This proves the local parity statement for every **field-representable**
rank-four matroid. It does not yet prove the representation-free matroid
statement. The GF(2), GF(3), and GF(5) computations should now be viewed as
exact regression certificates for the general represented proof.

## 6. Strongest next proof direction

Do not spend more time testing additional finite fields unless needed as a
regression. The representable case is conceptually closed.

The best next move is now the **intrinsic fundamental-circuit route**:

1. Use `crossBaseRelation_iff_mem_fundCircuit` to encode the identity/flip bit
   of every forced relation by one fundamental-circuit incidence.
2. Formalize that one-bit orientation corollary in Lean.
3. Re-express the five repartition cases entirely through basis exchange /
   fundamental circuits and prove the even-flip statement without a
   representation hypothesis.
4. If a nonrepresentable counterexample appears, isolate the exact matroid
   configuration instead of weakening the represented theorem.

The determinant proof is a detailed template for what the intrinsic argument
must reproduce.

## 7. Global bottleneck remains open

The finite binary N=5/N=7 audits still show every obstructed strict state has
a productive cross repair. N=7 has 25,152 normalized obstructed states; all
25,152 have a direct orientable cross repair, while 728 have no strict
closure-potential ascent.

The missing theorem is still an **existence** theorem: from an arbitrary
obstructed rank-four state, prove that some boundary/repartition creates slack
(or otherwise escapes) or gives whatever ascent mechanism is ultimately
needed. Local parity conservation alone does not produce such a boundary.

Do not claim:

- universal one-step repair;
- arbitrary-N escape-or-ascent;
- representation-free forced-parity conservation yet;
- full rank-four KUM;
- full KUM.

## 8. Commit chronology after the old handoff

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
- `1dd88755ccbc4ceb93f2f6d1714a5054633827b9` — arbitrary-field represented parity proof note.

## 9. Reproduction

For the finite certificates:

```bash
python3 experiments/sprint5_verify.py
```

The finite-field audit has an internal GF(2) regression against the earlier
binary totals and committed exact expected output.

For formal validation, use the existing GitHub Actions workflow/`lake build`;
do not infer green status merely because a file is exported.
