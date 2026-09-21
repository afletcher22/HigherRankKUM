# Sprint 1 — Rational Tight-Set Gluing

**Status:** complete

**Lean source checkpoint:** `875d03def7517e80f764f5f327eea0eb5536c85a`

**Branch:** `rank4-research-sprint1`

## Principal result

Sprint 1 formalizes rational-density proper-tight gluing while preserving the existing divisible interface.

The implementation is deliberately layered:

1. periodic cyclic-window arithmetic independent of matroid density;
2. density-free restriction/contraction gluing;
3. rational density and tightness inheritance;
4. full-rank / exact-rank-size solver interfaces alongside the old divisible solver;
5. generic rational proper-tight reduction;
6. rank-four `4k+2` proper-tight specialization with its remaining rank-two dependency explicit.

## Main declarations

- `UniformlyDenseRatio`
- `TightRatio`
- `SolvesKUMAtRankSize`
- `SolvesKUMAtRank`
- `SolvesKUMBelow`
- `exists_cyclicBasisOrder_congr`
- `exists_cyclicBasisOrder_of_periodic_restrict_contract`
- `exists_cyclicBasisOrder_of_ratio_tight_of_rank_solutions`
- `exists_tight_rank_factorization`
- `exists_cyclicBasisOrder_of_ratio_nonempty_proper_tight_of_lower_ranks`
- `exists_cyclicBasisOrder_of_rank_four_gcd_two_of_nonempty_proper_tight`

## Semantic checks

- `CyclicBasisOrder` remains the existing production predicate; no alternate notion of cyclic ordering was introduced.
- The periodic interleaving theorem itself uses no density hypothesis.
- Rational density is represented cross-multiplicatively as `q * |X| <= p * r(X)` rather than by field-valued division.
- The old divisible solver interface remains intact.
- The old balanced/integer gluing construction is recovered as the `q = 1` specialization of the new periodic construction.
- The public rank-four `4k+2` wrapper accepts the standard KUM density ratio `(4k+2)/4` and reduces it internally to `(2k+1)/2`.

## Rank-four dependency boundary

HigherRankKUM does **not** currently prove full rank-two KUM. It proves the divisible rank-two case only.

Therefore the formal rank-four `4k+2` proper-tight theorem assumes exactly:

`SolvesKUMAtRankSize α 2 (2 * k + 1)`.

Mathematically this exact-size rank-two instance follows from the van den Heuvel–Thomassé coprime theorem because `2k+1` is odd. That literature theorem has not been silently imported as a Lean axiom.

Consequently:

- generic rational tight-set gluing is Lean verified;
- the rank-four `4k+2` proper-tight reduction is Lean verified **conditionally on the explicit odd-size rank-two solver**;
- end-to-end internal discharge of that rank-two hypothesis remains future infrastructure, not a hidden assumption.

## Build evidence

### Targeted Sprint 1 validation

GitHub Actions run `34945435242` completed successfully on source commit `edb2efaa5efae430cf621b34b0b78177cbac1037` after the final rank-four transport fix.

The targeted chain included:

- `HigherRankKUM.PeriodicGluingRegression`
- `HigherRankKUM.Rank4.RationalTightReduction`

### Full repository validation

GitHub Actions run `34946281862` completed successfully on source commit `875d03def7517e80f764f5f327eea0eb5536c85a`.

The workflow executed plain:

`lake build`

and completed successfully with **3,085 jobs**. Dependency-lock verification, vendored Rank3KUM checksum verification, and the standalone Rank3KUM import boundary all passed before the build.

No Lean errors remain in the Sprint 1 stack at this checkpoint. Remaining messages are linter/style warnings and the already known standard axiom reports (`propext`, `Classical.choice`, `Quot.sound`) from the vendored/formal environment.

## Research conclusions

**Lean verified:** periodic scaled-window decomposition; density-free periodic restriction/contraction gluing; rational density/tight factor inheritance; reduced-ratio tight-rank factorization; generic rational proper-tight reduction; `q=1` regression; conditional rank-four `4k+2` proper-tight corollary.

**Not claimed:** full rank-two KUM inside HigherRankKUM; the van den Heuvel–Thomassé theorem in Lean; any strict rank-four KUM theorem; any conclusion from the provisional pair-cycle search beyond its separately recorded computational status.

**Refuted during proof engineering:** no mathematical statement. All failed CI iterations were dependent-type/arithmetic transport, import, or elaboration issues.

## Next task

Begin the strict rank-four research sprint. Keep the two main fronts separate:

1. integral `|E| = 4k`: controlled deletion/reinsertion, not mere deletion existence;
2. strict `|E| = 4k+2`: structural scheduling/repair, with recovered pair-cycle obstructions independently certified before relying on them.
