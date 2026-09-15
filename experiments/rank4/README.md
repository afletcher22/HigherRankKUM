# Rank-Four Experiments

This directory is intentionally outside the trusted Lean dependency graph.

Candidate structures, finite searches, failed approaches, and partially formalized lemmas should remain here until their mathematical role is understood well enough to promote them into `HigherRankKUM/Rank4/`.

## Track A — strictly dense divisible rank four

Assume:

- `r(M)=4`;
- `|E(M)|=4k`;
- `M` is uniformly dense with parameter `k`;
- there is no nonempty proper tight set.

The generic tight-set machinery does not further reduce this branch. This is the direct higher-rank analogue of the point where the rank-three proof needed genuinely new strict-density machinery.

Questions to investigate before porting rank-three code:

1. What deletion condition preserves enough density to invoke induction?
2. After deleting a basis-sized block, what is the correct rank-four reinsertion obstruction?
3. Is there a useful analogue of the rank-three two-gap lemma, or does rank four require a matching/exchange-support formulation instead?
4. Can the obstruction be encoded as a finite Hall-type problem on fundamental circuits or exchange supports?
5. What are the smallest finite configurations where naive block reinsertion fails?
6. Does strict density force enough expansion in the exchange graph to eliminate those configurations?

Rank3KUM's `StrictDensity`, `TwoGap`, `Splicing`, `NearTightGeometry`, and six-point files are references for proof patterns only. They should not be copied here mechanically.

## Track B — gcd-two rank four

Assume:

- `r(M)=4`;
- `|E(M)| = 4k+2`;
- hence `gcd(|E(M)|,4)=2`.

This arithmetic regime is neither covered by the coprime theorem nor by the current divisible `r*k` interface. It should be investigated separately rather than treated as a small variation of Track A.

Initial questions:

1. Is there a natural two-phase or doubled-cycle reformulation adapted to the common divisor `2`?
2. Can the problem be reduced to rank-two structure after grouping positions modulo two?
3. Does a tight-set decomposition preserve a common density parameter in a form useful for `4k+2` ground sizes?
4. Are there existing KUM partial results for `gcd(n,r)=2` that should become an additional literature filter before new proof search?
5. What are the smallest computational instances not covered by known theorems?

## Promotion rule

An experiment should move into the trusted Lean tree only when:

- its statement is mathematically stable;
- its hypotheses are understood and recorded;
- it does not silently specialize a supposedly generic definition;
- it has a clear role in the rank-four coverage map;
- and, once formalized, the main CI build remains green.
