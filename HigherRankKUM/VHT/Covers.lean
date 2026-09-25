import HigherRankKUM.VHT.Coprime

/-!
# Constant-weight covers from Theorem 2.1: Edmonds' partition and double covers

Give every element the same weight `w ≤ D`. If moreover `|E| · w = D · r(M)`, counting forces
every arc of the mapping from Theorem 2.1 to be a basis. There are `D` arcs, and every element
lies in exactly `w` of them.

* `w = 1`, `D = k`: Edmonds' partition of a set of `k·r(M)` elements into `k` bases (Theorem D).
* `w = 2`, `D = 2k+1`, `|E| = 4k+2`, rank 4: the double covers used by Lemma U.
-/

namespace HigherRankKUM.VHT

open Set

variable {α : Type*}

/-- Uniform density at ratio `D / w` makes a matroid with `w > 0` loopless. -/
theorem loopless_of_ratio {M : Matroid α} {D w : ℕ} (hw : 0 < w)
    (hDense : UniformlyDenseRatio M D w) : M.Loopless := by
  rw [Matroid.loopless_iff_forall_not_isLoop]
  intro e heE heLoop
  have h := hDense {e} (by simpa using heE)
  rw [Set.encard_singleton, heLoop.eRk_eq] at h
  simp at h
  omega

/-- Uniform density at ratio `D / w` is exactly condition (b) for the constant weight `w`. -/
theorem weightBounded_of_ratio {M : Matroid α} {D w : ℕ} (hDense : UniformlyDenseRatio M D w) :
    WeightBounded M (fun _ => w) D := by
  intro A hA
  have h := hDense (A : Set α) hA
  rw [Set.encard_coe_eq_coe_finsetCard] at h
  simp only [Finset.sum_const, smul_eq_mul]
  push_cast
  exact le_of_eq_of_le (mul_comm _ _) h

/-- If `w ≤ D` and `|E| · w = D · r(M)`, every arc of a Theorem 2.1 mapping is a basis. -/
theorem exists_arc_bases (hV : Statement α) (M : Matroid α) {w D n r : ℕ} (hw : 0 < w)
    (hwD : w ≤ D) (hE : M.E.Finite) (hEcard : M.E.encard = n) (hRank : M.eRank = r)
    (htight : n * w = D * r) (hDense : UniformlyDenseRatio M D w) :
    ∃ φ : α → ZMod D, ∀ x, M.IsBase (arcSet M φ (fun _ => w) x) := by
  have hD : 0 < D := by omega
  haveI : NeZero D := ⟨hD.ne'⟩
  classical
  set S := hE.toFinset with hS
  have hScard : S.card = n := by
    have h : ((S.card : ℕ) : ℕ∞) = n := by
      rw [hS, ← Set.encard_coe_eq_coe_finsetCard, Set.Finite.coe_toFinset]
      exact hEcard
    exact_mod_cast h
  obtain ⟨φ, hφ⟩ := hV M (fun _ => w) D hD hE (loopless_of_ratio hw hDense)
    (weightBounded_of_ratio hDense)
  have harc : ∀ x, arcSet M φ (fun _ => w) x = ↑(S.filter fun e => (x - φ e).val < w) := by
    intro x
    ext e
    simp [arcSet, hS]
  have hle : ∀ x, (S.filter fun e => (x - φ e).val < w).card ≤ r := by
    intro x
    have h1 := (hφ x).eRk_eq_encard
    have h2 := M.eRk_le_eRank (arcSet M φ (fun _ => w) x)
    rw [h1, hRank, harc x, Set.encard_coe_eq_coe_finsetCard] at h2
    exact_mod_cast h2
  have heq : ∀ x, (S.filter fun e => (x - φ e).val < w).card = r := by
    have hsum : ∑ x : ZMod D, (S.filter fun e => (x - φ e).val < w).card =
        ∑ _x : ZMod D, r := by
      rw [sum_card_arcs S φ hwD, Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul,
        hScard, htight]
    intro x
    exact (Finset.sum_eq_sum_iff_of_le (fun x _ => hle x)).1 hsum x (Finset.mem_univ x)
  refine ⟨φ, fun x => ?_⟩
  have hfin : (arcSet M φ (fun _ => w) x).Finite := hE.subset (arcSet_subset M φ _ x)
  refine (hφ x).isBase_of_eRk_ge hfin ?_
  rw [(hφ x).eRk_eq_encard, hRank, harc x, Set.encard_coe_eq_coe_finsetCard, heq x]

/-- **Edmonds' partition.** A uniformly dense matroid on `k · r(M)` elements is the disjoint
union of `k` bases. -/
theorem edmonds_partition (hV : Statement α) (M : Matroid α) {k n r : ℕ} (hk : 0 < k)
    (hE : M.E.Finite) (hEcard : M.E.encard = n) (hRank : M.eRank = r) (hn : n = k * r)
    (hDense : UniformlyDenseRatio M k 1) :
    ∃ P : ZMod k → Set α, (∀ x, M.IsBase (P x)) ∧ ∀ e ∈ M.E, ∃! x, e ∈ P x := by
  obtain ⟨φ, hφ⟩ := exists_arc_bases hV M (w := 1) (D := k) Nat.one_pos hk hE hEcard hRank
    (by rw [hn]; ring) hDense
  refine ⟨fun x => arcSet M φ (fun _ => 1) x, hφ, fun e he => ⟨φ e, ⟨he, by simp⟩, ?_⟩⟩
  rintro x ⟨-, hx⟩
  simp only [Nat.lt_one_iff, ZMod.val_eq_zero, sub_eq_zero] at hx
  exact hx

/-- **Double covers.** A uniformly dense rank-4 matroid on `4k+2` elements has `2k+1` bases,
indexed by `ZMod (2k+1)`, in which every element lies in exactly two: the arcs of a mapping with
weight `2`. -/
theorem double_cover (hV : Statement α) (M : Matroid α) {k : ℕ} (hk : 0 < k) (hE : M.E.Finite)
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞)) (hRank : M.eRank = ((4 : ℕ) : ℕ∞))
    (hDense : UniformlyDenseRatio M (4 * k + 2) 4) :
    ∃ φ : α → ZMod (2 * k + 1), ∀ x, M.IsBase (arcSet M φ (fun _ => 2) x) := by
  have hDense' : UniformlyDenseRatio M (2 * k + 1) 2 := by
    intro X hX
    have h := hDense X hX
    have h2 : ((4 : ℕ) : ℕ∞) * X.encard = 2 * (((2 : ℕ) : ℕ∞) * X.encard) := by
      push_cast
      ring
    have h3 : (((4 * k + 2 : ℕ) : ℕ) : ℕ∞) * M.eRk X = 2 * (((2 * k + 1 : ℕ) : ℕ∞) * M.eRk X) := by
      push_cast
      ring
    rw [h2, h3] at h
    exact (ENat.mul_le_mul_left_iff (by norm_num) (by simp)).1 h
  exact exists_arc_bases hV M (w := 2) (D := 2 * k + 1) (n := 4 * k + 2) (r := 4) two_pos
    (by omega) hE hEcard hRank (by ring) hDense'

end HigherRankKUM.VHT
