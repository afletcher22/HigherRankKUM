# Sprint 4 — global closure geometry after local repair

**Start date:** 2026-09-15 (America/Phoenix)

**Branch:** `rank4-research-sprint4`

**Base checkpoint:** `checkpoint/sprint3-gcd-two-local-repair`

**Base SHA:** `b4ffc82e8b7d6d02a39e7f4b3d8cdfd7e894f08e`

**Base validation:** GitHub Actions run `35042601035` green, including all committed finite certificates, the targeted pair-cycle/local-repair Lean stack, and full `lake build`.

## Bounded question

Study the **global geometry forced by repeated rank-four neighbor-closure obstructions** in the strict `gcd(|E|,4)=2` branch.

Sprint 3 proved a local statement: if an adjacent `2+2` repair is unique, then one of four neighboring ambient closure incidences must occur. Equivalently, if all four such incidences are absent, some alternative common-base repartition exists.

Sprint 4 asks what happens when those closure obstructions accumulate around an odd admissible pair cycle. The immediate aim is to find either:

1. a structural contradiction to persistent closure saturation under strict uniform density; or
2. a monotone invariant / potential showing that admissibility-preserving repartitions can leave the rigid region and eventually create Boolean slack.

This sprint does **not** assume that every strict gcd-two rank-four matroid already has an admissible pair-cycle representation. Pair-cycle existence remains a separate unresolved hypothesis.

## Initial abstract guardrail

`experiments/sprint4_abstract_repartition_guardrail.py` enumerates all rank-two matroids on a labelled four-element ground and all ordered pairs `(L,S)` of such boundary matroids.

Fix the current pair `B={0,1}` and opposite pair `D={2,3}`. Retain configurations where:

- `B` is a common base of `L` and `S`;
- neither element of `D` is a loop of `L`;
- neither element of `B` is a coloop of `S`.

These are the abstract four-element hypotheses corresponding to the negation of the local rigidity alternatives.

Exact result:

- 36 rank-two matroids occur on the labelled four-element ground;
- 1,296 ordered boundary pairs are checked;
- 100 satisfy the closure-free surrogate together with the current common base;
- none has the current pair as its unique common base;
- 98 have a one-element cross common base;
- exactly 2 have **no** cross common base, with the wholesale opposite block `D` as the only alternative;
- common-base counts among the 100 qualifying pairs are `2:22`, `3:28`, `4:34`, `5:15`, `6:1`.

The two wholesale-swap-only examples are the swapped ordered pair of base families

- `{01,03,12,23}` and `{01,02,13,23}`.

This is an exact finite abstract guardrail, not a representability theorem and not a global KUM result.

## Guardrail carried forward

Do **not** silently replace

> an alternative local `2+2` repartition exists

by

> a one-element cross exchange exists.

The latter is false for the abstract local hypotheses presently formalized. Any future cross-exchange theorem needs an additional hypothesis derived from the ambient pair-cycle geometry, strict density, representability, or another global condition.

## First structural targets

### A. Closure-saturation bookkeeping

For each boundary of an admissible rank-four pair cycle, record which of the four neighbor-closure incidences hold. Determine what cyclic patterns are compatible with strict uniform density.

The goal is a theorem or finite reduction, not witness pattern-mining. In particular, the 18-element witness's exact rigid-gap classes `(1,3,5)`, `(1,1,7)`, `(3,3,3)` remain witness-specific.

### B. Propagation through rank-two flats

In rank four, each relevant core is one pair block. Repeated closure incidences therefore constrain how neighboring pair blocks sit in rank-two flats. Search for implications of the form:

- repeated one-sided closure forces a larger low-rank flat;
- alternating closure directions force a short periodic configuration;
- sufficiently dense closure saturation contradicts strict uniform density.

Any such statement must be tested against the existing 10- and 18-element witnesses before formalization.

### C. Repair potential

If closure saturation itself is not contradictory, seek a potential on admissible pair cycles that changes under a legal full `2+2` repartition. Candidate potentials may use:

- number of rigid boundaries;
- weighted closure incidences;
- sizes/ranks of neighboring closure flats;
- Boolean-relation slack from the Sprint 2 obstruction formalization.

A useful potential must prevent cycling and must distinguish a genuine move from the wholesale block swap when that swap leaves the state essentially unchanged.

## Non-goals

- no claim that rank-four KUM is solved;
- no universal pair-cycle-existence theorem unless separately proved;
- no assumption that the local-repair graph is connected;
- no universal one- or two-step repair theorem inferred from the 18-element component;
- no broad random rank-four search until the closure-propagation question is sharper;
- no representability assumption in the abstract local statements unless explicitly introduced.

## Success criterion for this sprint

Produce at least one reusable global structural lemma about closure accumulation, or a rigorously certified finite reduction that narrows the possible closure-saturated cyclic patterns enough to support the next Lean theorem. Preserve a clean distinction between:

1. fixed-cycle orientability;
2. existence of alternative admissible repartitions;
3. reachability of an orientable cycle;
4. existence of an admissible pair cycle in the first place.
