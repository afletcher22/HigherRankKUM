# HigherRankKUM: the Kajitani–Ueno–Miyano conjecture in rank 4

A Lean 4 / Mathlib proof that **every finite uniformly dense matroid of rank 4 has a cyclic basis
ordering**: a cyclic ordering of the ground set in which every 4 cyclically consecutive elements
form a basis. Uniform density means `r(M) · |X| ≤ |E| · r(X)` for every `X ⊆ E`. There is no
condition on `|E|`. Kajitani, Ueno and Miyano (1988) conjectured this for every rank.

The proof depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`. One step, the
10-element case, uses a SAT certificate that the Lean kernel checks in full (no `native_decide`,
no `ofReduceBool`). Every other step is an ordinary Lean proof.

## The theorem

The statement is in `Challenge.lean`, which imports only Mathlib:

```lean
theorem HigherRankKUM.Palomar.rankFourKUM (M : Matroid α) (hfin : M.E.Finite)
    (hrank : M.eRank = 4) (hdense : UniformlyDense M) :
    ∃ (n : ℕ) (hn : 0 < n) (σ : Fin n ≃ M.E), IsCyclicBasisOrdering M 4 hn σ
```

`Solution.lean` proves it from `HigherRankKUM.solvesKUMAtRank_four`
(`HigherRankKUMCert/Final.lean`), whose definitions unfold to the same statement.

## Proof outline

Strong induction on `n = |E|`.

| `n` | argument | Lean |
|---|---|---|
| odd | coprime case: van den Heuvel–Thomassé, Theorem 3.1 | `HigherRankKUM/VHT/` |
| `4k` | Theorem D: Edmonds splits `E` into `k` bases; delete one, order the rest by induction, and reinsert it by pair-chain insertion (XP). Base case `n = 8` by the Kotlar–Ziv serial symmetric exchange | `Rank4/TheoremD.lean`, `Rank4/TheoremDCert.lean`, `Rank4/XP/`, `Rank4/SerialExchange.lean`, `Rank4/Kum8.lean` |
| 6 | duality with rank-2 KUM | `Rank4/SixElementBoundary.lean`, `LowRank/RankTwo.lean` |
| 10 | a van den Heuvel–Thomassé chain of five pairs, ordered by the certificate `chain10` | `HigherRankKUMCert/Chain10.lean`, `HigherRankKUMCert/Kum10Chain.lean` |
| `4k+2 ≥ 14`, with a proper tight set | rational tight reduction; its rank-2 input at the odd size `2k+1` is the coprime case | `Rank4/RationalTightReduction.lean` |
| `4k+2 ≥ 14`, strict | delete a basis `S` with `M \ S` uniformly dense, order `M \ S` by induction, reinsert `S` by XP. `S` comes from the hitting lemma: Lemma U for `k ≥ 4`, Lemma H and `HitThree` for `k = 3`, Lemma D when there is a plane with `3k+1` elements | `Rank4/Hitting.lean`, `Rank4/LemmaU.lean`, `Rank4/LemmaH.lean`, `Rank4/HitThree.lean`, `Rank4/HitDanger.lean`, `HigherRankKUMCert/Full.lean` |

Paths under `Rank4/`, `VHT/` and `LowRank/` are in `HigherRankKUM/`. Paper proofs and the history
of each step are in `docs/GENERALIZATION_STATUS.md` and `docs/research-ledger/`.

## The certificate

`chain10` (`HigherRankKUMCert/data/`, 14,738 LRAT hints) states that a chain of five pairs in a
rank-4 matroid, with every two consecutive pairs forming a basis, can be oriented (or re-split at
one window) into a cyclic basis ordering. The kernel checks three things:

* the LRAT refutation of the CNF, in chunks (`HigherRankKUM/SAT/LRATChunked.lean`);
* that the CNF is exactly the encoding generated from the clause witnesses
  (`HigherRankKUM/SAT/Cert.lean`);
* that a matroid with no such ordering would satisfy the CNF (`HigherRankKUM/SAT/EncF.lean`,
  `HigherRankKUM/SAT/EncFBridge.lean`).

The scripts that generate the encoding and the certificate are in `experiments/`.

## Layout

* `HigherRankKUM/`: the library. Uniform density, cyclic orders and gluing; the
  van den Heuvel–Thomassé theorem and its corollaries (`VHT/`); rank-2 KUM (`LowRank/`); the
  rank-4 lemmas (`Rank4/`); the SAT encoding layer (`SAT/`).
* `HigherRankKUMCert/`: the certificate `chain10`, its data, and the assembly of the proof.
* `Challenge.lean`, `Solution.lean`, `comparator.json`, `formalization.yaml`: the
  [Palomar Registry](https://palomar-registry.org) package.
* `docs/`: the status of the project (`GENERALIZATION_STATUS.md`) and the research ledger.
* `experiments/`: SAT encoders, checks and search scripts (Python). They are not part of the Lean
  build.

Every Lean file uses the Lean module system, as Palomar requires.

## Building and checking

```sh
lake exe cache get
lake build
lake env leanchecker Solution
```

CI (`.github/workflows/ci.yml`) builds everything, replays `Solution` with `leanchecker`, and
checks the axioms of `HigherRankKUM.Palomar.rankFourKUM`. `.github/workflows/palomar.yml` runs
Palomar's own verifier as a preflight on `palomar/**` branches.

The toolchain is Lean and Mathlib `v4.35.0-rc3`, with the dependency graph pinned in
`lake-manifest.json`.

## Provenance

* HigherRankKUM is a successor to [`afletcher22/Rank3KUM`](https://github.com/afletcher22/Rank3KUM),
  from which its generic density and gluing infrastructure was migrated (`docs/PROVENANCE.md`).
  The rank-three theorem itself is not used by this proof.
* Formalized literature: J. van den Heuvel and S. Thomassé, *Cyclic orderings and cyclic
  arboricity of matroids*, JCTB 102 (2012); D. Kotlar and R. Ziv, *On serial symmetric exchanges
  of matroid bases*, J. Graph Theory 73 (2013).
* The `main` branch holds only the rank-4 proof. The full research history, the other research
  modules and the vendored rank-three snapshot are on the branch
  `rank4-heavy-flat-splice-research`.

## License

MIT (`LICENSE`).
