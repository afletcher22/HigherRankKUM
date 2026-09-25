# Formalization plan: van den Heuvel–Thomassé, Theorem 2.1

Source: J. van den Heuvel and S. Thomassé, *Cyclic orderings and cyclic arboricity of matroids*,
arXiv:0912.2929 (JCTB 2012). Phase 1 of the Palomar roadmap.

Mathlib (v4.35.0-rc3) has no matroid union, partition or covering theorem, so this has to be
built from scratch. Theorem 2.1 is the right target because the project uses it in four ways:

* weights 1, `D = k`: Edmonds' covering (Theorem D, and the choice lemmas of Theorems G/L4);
* weights 2, `D = 2k+1`: the double covers of Lemma U;
* weights `r`, `D = m`, `gcd(r, m) = 1`: coprime KUM (Theorem 3.1, a half-page argument). This
  covers odd `n` at rank 4, the rank-3 sizes that the dangerous-hyperplane theorem requires, and
  odd rank-2 sizes;
* integer weights in general: cyclic arboricity, which is not needed now.

## Statement

For a finite loopless matroid `M`, weights `ω : α → ℕ` and `D > 0`, the following are
equivalent:

* **(a)** there is `φ : α → Fin D` such that for every point `x : Fin D`, the set
  `E_φ(x) = {e ∈ E | (x - φ e).val < ω e}` is independent;
* **(b)** for every `A ⊆ E`, `Σ_{e∈A} ω e ≤ D · r(A)`.

**(a) ⇒ (b)** is double counting: each `e` lies in exactly `ω e` of the sets `E_φ(x)`, and each
`E_φ(x) ∩ A` is independent.

## (b) ⇒ (a): proof by strong induction on `|E|`

**Step 0 (reductions).**

* An element with `ω e = 0` lies in no `E_φ(x)`: delete it and extend `φ` arbitrarily.
* An element with `ω e = D` lies in every `E_φ(x)`: contract it. Condition (b) passes to `M ／ e`,
  which stays loopless because (b) applied to pairs gives `r{e,f} = 2`. Then extend `φ`. The
  combination step uses the basis-lifting lemmas already in the repository.
* From now on `1 ≤ ω e ≤ D - 1` for every `e`.

**Step 1 (a best mapping).**

* Let `Φ(φ) = Σ_x |cl(E_φ(x))|`, where `cl` is the matroid closure (the span). Pick `φ` that
  maximizes `Φ`; there are finitely many mappings.
* If `ψ` has `cl(E_ψ(x)) ⊇ cl(E_φ(x))` for all `x`, with strict inclusion somewhere, then
  `Φ(ψ) > Φ(φ)`. So a maximizer is "best possible" in the paper's sense.
* This replaces the paper's order-theoretic choice.

**Step 2 (pushes).**

* `e` is *pushable* in `φ` if `e` lies in a circuit of `E_φ(φ e)`. Pushing sets
  `φ e := φ e + 1`.
* A push does not decrease any closure. It removes `e` from `E(φ e)`, which is harmless because
  `e ∈ cl(E(φ e) - e)`, and it adds `e` to `E(φ e + ω e)`.
* So a push applied to a maximizer is again a maximizer, with the same closures (Claim 1).
* If some `E_φ(x)` is dependent, then some element is pushable. Take a circuit `C` in `E(x)` and
  walk back from `x` to the last `y` with `C ⊆ E(y)`; this uses `ω e ≤ D - 1`.

**Step 3 (deterministic dynamics on a finite state space).**

* A state is a mapping together with a list ordering of `E`.
* The step pushes the first pushable element in the list and moves it to the back.
* The state space is finite, so the orbit enters a cycle.
* **Unbounded** elements are those pushed somewhere on the cycle; all others are **bounded**.

**Step 4 (fairness).**

* On the cycle, every element ahead of a bounded element `e` in the list is itself bounded. A
  pushed element moves behind `e` and can never get back ahead of it, yet the cycle revisits every
  state.
* Hence a bounded element is never pushable on the cycle (Claim 2).

**Step 5 (Claims 3–5).**

* These are closure manipulations exactly as in the paper.
* They give: `cl(E_U) = E_U`, and every circuit of every `E_i(x)` lies in `E_U`.
* `E_B ≠ ∅`: otherwise every element cycles through every point, and each `E(x)` would span `E`.
  That is impossible, because some `E(x)` is dependent and `Σ |E(x)| = ω(E) ≤ D r(E)`.
* `E_U ≠ ∅`: the orbit makes infinitely many pushes.

**Step 6 (combine).**

* `φ|E_B` satisfies (a) for `M ／ E_U`.
* By induction (`|E_U| < |E|`), `M | E_U` has a mapping satisfying (a).
* Independent in the contraction plus independent in the restriction gives independent in `M`.

## Corollaries to formalize immediately after

* **Theorem 3.1 (coprime KUM).** `ω ≡ r`, `D = m`. Every length-`r` arc contains exactly `r`
  mapped elements, `gcd(r, m) = 1` forces `φ` to be a bijection, and the arcs are the windows.
  Delivers `SolvesKUMAtRankSize α r m` for `gcd(r, m) = 1`.
* **Edmonds' covering.** `ω ≡ 1`, `D = k`, giving a partition into `k` independent sets. When
  `|E| = k·r(M)`, the parts are bases.
* **Double covers.** `ω ≡ 2`, `D = 2k+1` on `4k+2` elements, giving `2k+1` bases with every
  element in exactly two. This is Lemma U's hypothesis.

## Where it lives

* Development happens on probe branches, built by CI only (no local Lean).
* The modules then move to `HigherRankKUM/VHT/`, with the coprime solver exposed through the
  existing `SolvesKUMAtRankSize` interface. That removes the explicit coprime hypotheses in the
  rank-2 and rank-3 reductions.
