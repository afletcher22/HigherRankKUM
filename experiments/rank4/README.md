# Rank-Four Experiments

This directory is intentionally outside the trusted Lean dependency graph.

Candidate structures, finite searches, failed approaches, and partially formalized lemmas should remain here until their mathematical role is understood well enough to promote them into `HigherRankKUM/Rank4/`.

## Track A — strictly dense divisible rank four

Assume:

- `r(M)=4`;
- `|E(M)|=4k`;
- `M` is uniformly dense with parameter `k`;
- there is no nonempty proper tight set.

The generic tight-set machinery does not further reduce this branch. Matroid partition already supplies integral basis decompositions, so the open issue is **controlled** deletion/reinsertion rather than mere existence of a deletable basis.

Questions to investigate before porting rank-three code:

1. What extra property of a deleted basis preserves enough structure for reinsertion?
2. After solving the smaller instance, what is the correct rank-four reinsertion obstruction?
3. Is there a useful analogue of the rank-three two-gap lemma, or does rank four require a matching/exchange-support formulation?
4. Can the obstruction be encoded as a finite Hall-type problem on fundamental circuits or exchange supports?
5. What are the smallest finite configurations where naive block reinsertion fails?
6. Does strict density force enough expansion in the exchange graph to eliminate those configurations?

Rank3KUM's `StrictDensity`, `TwoGap`, `Splicing`, `NearTightGeometry`, and six-point files are references for proof patterns only. They should not be copied mechanically.

## Track B — strict gcd-two rank four

Assume:

- `r(M)=4`;
- `|E(M)|=4k+2`;
- `M` is strictly uniformly dense.

Sprint 1 already handles the **proper-tight** gcd-two branch at the rational-density level, conditional in Lean on the odd-size rank-two solver and settled mathematically by the external coprime theorem. Experiments here should therefore target the strict branch rather than rediscover proper-tight gluing.

Sprints 2–3 established a concrete pair-cycle route. For an `AdmissiblePairCycle.Data`, fixed-cycle orientation failure is characterized exactly by forced Boolean transitions. Local re-pairing is controlled by two rank-two boundary minors, and uniqueness of the current `2+2` split forces a neighboring ambient closure incidence. A closure-free boundary therefore has another valid full `2+2` repartition.

Current experimental questions are:

1. What general hypothesis guarantees the existence of a useful admissible pair cycle in a strict gcd-two matroid?
2. Can neighbor-closure incidences accumulate around the odd pair cycle without forcing a forbidden large rank-two flat or another strict-density violation?
3. Is there a monotone potential for local full `2+2` repartitions that eventually creates Boolean slack or reaches an orientable pair cycle?
4. When the only alternative local repartition is the wholesale block swap, how does that operation change the global forced-transition pattern?
5. Which structural feature distinguishes the known 18-element distance-two states from distance-one states, beyond the witness-specific rigid-gap pattern?

Do not replace “full local `2+2` repartition” by “single-element exchange” without an additional argument. Closure-freeness alone does not justify that strengthening.

## Promotion rule

An experiment should move into the trusted Lean tree only when:

- its statement is mathematically stable;
- its hypotheses are understood and recorded;
- it does not silently specialize a supposedly generic definition;
- it has a clear role in the rank-four coverage map;
- and, once formalized, the main CI build remains green.
