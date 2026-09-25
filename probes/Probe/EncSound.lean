import Probe.Enc

/-!
# Palomar probe: semantic soundness of the KUM clause witnesses (round 2)

`RankModel N` is an abstract rank function on bitmasks over `N` elements.  It has exactly the
properties the KUM clauses use, together with the hypothesis that no cyclic ordering has all its
4-windows of rank at least 4.  Under the valuation `val m`, which reads variable `4X + v - 1` as
`r(X) ≥ v`, every valid witness generates a satisfied clause.  So a kernel-checked refutation of
the regenerated formula shows that no rank model exists.

Everything here is elementary arithmetic on `ℕ`; the bridge from matroids to `RankModel` is kept
separate.
-/

namespace Probe.Enc

/-- An abstract rank function on bitmasks with exactly the properties the KUM clauses use. -/
structure RankModel (N : ℕ) where
  r : ℕ → ℕ
  card : ∀ X, X < 2 ^ N → r X ≤ pc N X
  dens : ∀ X, X < 2 ^ N → 4 * pc N X ≤ N * r X
  mono : ∀ X a, X < 2 ^ N → a < N → X.testBit a = false → r X ≤ r (X ||| 1 <<< a)
  ins : ∀ X a, X < 2 ^ N → a < N → X.testBit a = false → r (X ||| 1 <<< a) ≤ r X + 1
  sub : ∀ X a b, X < 2 ^ N → a < b → b < N → X.testBit a = false → X.testBit b = false →
    r (X ||| 1 <<< a ||| 1 <<< b) + r X ≤ r (X ||| 1 <<< a) + r (X ||| 1 <<< b)
  noCBO : ∀ s : List ℕ, s.length = N → (∀ x < N, x ∈ s) → (∀ x ∈ s, x < N) →
    ∃ i < N, r (window s i) < 4

/-- Variable `4X + v - 1` is true when `r(X) ≥ v`. -/
def val {N : ℕ} (m : RankModel N) : Sat.Valuation := fun i => i % 4 + 1 ≤ m.r (i / 4)

theorem val_idx {N : ℕ} (m : RankModel N) {v : ℕ} (h1 : 1 ≤ v) (h4 : v ≤ 4) (X : ℕ) :
    val m (idx X v) ↔ v ≤ m.r X := by
  have hd : (4 * X + v - 1) / 4 = X := by omega
  have hm : (4 * X + v - 1) % 4 + 1 = v := by omega
  simp only [val, idx, hd, hm]

theorem satisfies_map_neg (w : Sat.Valuation) (L : List ℕ) (f : ℕ → ℕ) :
    w.satisfies (L.map fun i => Sat.Literal.neg (f i)) ↔ ¬ ∀ i ∈ L, w (f i) := by
  induction L with
  | nil => simp [Sat.Valuation.satisfies]
  | cons a L ih =>
    simp only [List.map_cons, Sat.Valuation.satisfies, Sat.Valuation.neg, ih, List.mem_cons,
      forall_eq_or_imp]
    exact ⟨fun h ⟨h1, h2⟩ => h h1 h2, fun h h1 h2 => h ⟨h1, h2⟩⟩

/-- Every valid witness generates a clause satisfied by `val m`. -/
theorem gen_sound {N : ℕ} (m : RankModel N) : ∀ w, valid N w = true → (val m).satisfies (gen N w)
  | .order X v, hv => by
    simp only [valid, decide_eq_true_eq] at hv
    obtain ⟨_, h1, h3⟩ := hv
    simp only [gen, Sat.Valuation.satisfies, Sat.Valuation.neg,
      val_idx m (by omega : 1 ≤ v + 1) (by omega : v + 1 ≤ 4), val_idx m h1 (by omega : v ≤ 4)]
    omega
  | .cap X v, hv => by
    simp only [valid, decide_eq_true_eq] at hv
    obtain ⟨hX, hp, h4⟩ := hv
    have := m.card X hX
    simp only [gen, Sat.Valuation.satisfies, Sat.Valuation.neg,
      val_idx m (by omega : 1 ≤ v) h4]
    omega
  | .dens X k, hv => by
    simp only [valid, decide_eq_true_eq] at hv
    obtain ⟨hX, h1, h4, hlt⟩ := hv
    simp only [gen, Sat.Valuation.satisfies, Sat.Valuation.neg, val_idx m h1 h4]
    intro h
    have hle : m.r X ≤ k - 1 := by omega
    have h2 := m.dens X hX
    have h3 := Nat.mul_le_mul_left N hle
    exact absurd (Nat.lt_of_le_of_lt (Nat.le_trans h2 h3) hlt) (Nat.lt_irrefl _)
  | .mono X a v, hv => by
    simp only [valid, decide_eq_true_eq] at hv
    obtain ⟨hX, ha, hb, h1, h4⟩ := hv
    have := m.mono X a hX ha hb
    simp only [gen, Sat.Valuation.satisfies, Sat.Valuation.neg, val_idx m h1 h4]
    omega
  | .inc X a v, hv => by
    simp only [valid, decide_eq_true_eq] at hv
    obtain ⟨hX, ha, hb, h1, h3⟩ := hv
    have := m.ins X a hX ha hb
    simp only [gen, Sat.Valuation.satisfies, Sat.Valuation.neg,
      val_idx m (by omega : 1 ≤ v + 1) (by omega : v + 1 ≤ 4), val_idx m h1 (by omega : v ≤ 4)]
    omega
  | .sub X a b v, hv => by
    simp only [valid, decide_eq_true_eq] at hv
    obtain ⟨hX, hab, hbN, ha, hb, h1, h4⟩ := hv
    have := m.sub X a b hX hab hbN ha hb
    by_cases h2 : 2 ≤ v
    · simp only [gen, h2, ↓reduceIte, List.cons_append, List.nil_append,
        Sat.Valuation.satisfies, Sat.Valuation.neg, val_idx m h1 h4,
        val_idx m (by omega : 1 ≤ v - 1) (by omega : v - 1 ≤ 4)]
      omega
    · simp only [gen, h2, ↓reduceIte, List.append_nil,
        Sat.Valuation.satisfies, Sat.Valuation.neg, val_idx m h1 h4]
      omega
  | .win s, hv => by
    simp only [valid, decide_eq_true_eq] at hv
    obtain ⟨i, hi, hr⟩ := m.noCBO s hv.1 hv.2.1 hv.2.2
    refine (satisfies_map_neg (val m) (List.range N) (fun i => idx (window s i) 4)).2 ?_
    intro hall
    have := (val_idx m (by omega : 1 ≤ 4) (Nat.le_refl 4) (window s i)).1 (hall i (List.mem_range.2 hi))
    omega

/-- A kernel-checked refutation of a formula regenerated from valid witnesses rules out every
rank model. -/
theorem no_model {N : ℕ} (m : RankModel N) (f : Sat.Fmla) (hf : f.proof Sat.Clause.nil)
    (ws : List W) (heq : (f : List (List Sat.Literal)) = ws.map (gen N))
    (hv : ws.all (valid N) = true) : False := by
  refine hf (val m) ⟨fun c hc => ?_⟩
  rw [heq] at hc
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hc
  exact gen_sound m w (List.all_eq_true.1 hv w hw)

end Probe.Enc
