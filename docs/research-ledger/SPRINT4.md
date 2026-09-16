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

## Candidate closure potential

`experiments/sprint4_closure_potential_audit.py` tests a concrete repair-potential candidate on both preserved binary witnesses. For pair blocks `B_i`, define

`Phi = sum_i (|B_(i+1) ∩ cl(B_(i-1))| + |B_i ∩ cl(B_(i+2))|)`.

These are precisely the two directional families of neighbor-closure incidences appearing in the Sprint 3 local-rigidity obstruction.

### Ten-element witness

Across all 576 admissible pair cycles:

- 8 are unorientable and 568 orientable;
- all 8 unorientable cycles have `Phi = 4`;
- orientable cycles have scores `4:40`, `5:208`, `6:272`, `7:48`;
- every unorientable cycle has a legal full `2+2` repartition with strictly larger `Phi`;
- every such unorientable cycle reaches an orientable cycle in one strictly score-increasing repair.

This already shows that `Phi` is **not** an orientability classifier: 40 orientable cycles also have score 4.

### Eighteen-element witness

Across the exact 30,720-vertex adjacent-exchange component:

- all 7,680 unorientable states have `Phi` equal to 18 or 20, with histogram `18:3072`, `20:4608`;
- all 23,040 orientable states have `Phi` equal to 21, 22, or 23, with histogram `21:9216`, `22:4608`, `23:9216`;
- every unorientable state is closure-saturated at all 9 local boundaries;
- orientable states have either 8 or 9 closure-saturated boundaries (`8:4608`, `9:18432`);
- every unorientable state has a legal full `2+2` repartition that strictly increases `Phi`;
- 6,912 reach an orientable state in one strictly score-increasing repair;
- the remaining 768 reach one in two strictly score-increasing repairs.

This is the first finite evidence in the project for a **monotone closure-ascent mechanism** rather than merely bounded repair distance.

It remains witness-specific. A universal theorem would need to show, for an arbitrary unorientable admissible pair cycle, that some legal repartition strictly increases a suitably bounded matroidal potential, and that maximal potential forces Boolean slack / orientability. Neither implication is currently proved.

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

The finite audits now identify `Phi` above as the first concrete candidate. The next question is to understand a **single legal repartition's effect on `Phi` abstractly**.

A useful theorem would have the form: under unorientability plus appropriate local/global closure hypotheses, at least one legal full `2+2` repartition strictly increases a bounded potential. It must distinguish a genuine move from the wholesale block swap when that swap leaves the effective geometry unchanged.

If `Phi` itself fails abstractly, use the counterexample to refine it with rank-two-flat sizes or Boolean-relation slack rather than reverting immediately to broad search.

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
