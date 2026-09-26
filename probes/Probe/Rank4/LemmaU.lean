import Probe.Rank4.LemmaUBasic

/-!
# Lemma U: some basis of every double cover meets the demands

Let `M` be strict with t=0 on `4k+2` elements (`StrictT0 M k`), `k ≥ 4`, and let
`B 0, ..., B 2k` be a double cover of `M` by bases (every element lies in exactly two of them).
Then some `B i` meets every `k`-point, `2k`-line and `(3k-1)`-plane, and meets every `3k`-plane
at least twice (`lemmaU`).

## Proof

Suppose not, and choose for each `i` a demand flat `F i` of rank `ρ i` that `B i` misses
(`exists_viol`). The standing hypotheses are bundled in `UFam`.

* **Deficits.** For `X ⊆ E` of rank `r`, `∑ i |B i ∩ X| = 2|X|` (`UFam.sum_inter`), and every term
  is at most `r`. Hence `2|X| ≤ (2k-1) r + |B i ∩ X| + |B j ∩ X|` for `i ≠ j`
  (`UFam.two_mul_le`). So every demand flat has at most one victim, `F` is injective
  (`UFam.inj`), and the other bases meet a family `k`-point (`2k`-line) in at least one (two)
  elements (`UFam.meet_pt`, `UFam.meet_ln`).
* **Lines.** Two family lines are disjoint: otherwise their intersection is a `k`-point missed by
  both victims (`UFam.ln_disjoint`). So there are at most two (`UFam.card_lns_le`).
* **Points.** Three family points `P₁, P₂, P₃` are pairwise disjoint. Every other basis meets
  each of them, and a flat meeting a point contains it. So the flat of every other index is a
  `k`-point (`UFam.pt_of_three`), and then `(2k+1) k ≤ 4k+2`. So there are at most two points
  (`UFam.card_pts_le`), and `m ≥ 2k-3` planes (`UFam.card_partition`).
* **Deficit budget.** A family plane is met in at most two elements by at most three bases
  (`UFam.card_low_le`). A basis meets at most four family planes in three elements (its faces),
  and at most two if it is not the victim of a family line `L`: it meets `L` in two elements,
  the faces through them contain `L`, and no family plane contains a family line
  (`UFam.faces_le_four`, `UFam.faces_le_two`). Double counting the pairs (basis, family plane met
  in at most two elements) gives `(2k+1)(m-4) ≤ 3m`, or `2k(m-2) ≤ 3m` when there is a family
  line. Both fail for `k ≥ 4` (`UFam.not_ufam`).

This is the argument of `docs/research-ledger/RANK4_EXTENSION_THEOREM.md` ("Lemma U"), with the
budget step sharpened so that the cases `m = 5, 6` at `k = 4` need no separate treatment.
-/

namespace HigherRankKUM
namespace Hitting

open Set
open scoped Matroid

variable {α : Type*} {M : Matroid α} {k : ℕ}

/-- The standing hypotheses of the proof of Lemma U: a double cover `B` of a strict t=0 matroid
by bases, and for each `i` a demand flat `F i` of rank `ρ i` that `B i` misses. -/
structure UFam (M : Matroid α) (k : ℕ) (B F : Fin (2 * k + 1) → Set α)
    (ρ : Fin (2 * k + 1) → ℕ) : Prop where
  k4 : 4 ≤ k
  strict : StrictT0 M k
  base : ∀ i, M.IsBase (B i)
  cover : ∀ e ∈ M.E, ∃ i j, i ≠ j ∧ e ∈ B i ∧ e ∈ B j ∧ ∀ l, e ∈ B l → l = i ∨ l = j
  flat : ∀ i, M.IsFlat (F i)
  rk : ∀ i, M.eRk (F i) = ρ i
  kind : ∀ i, (ρ i = 1 ∧ (F i).ncard = k ∧ (B i ∩ F i).ncard = 0) ∨
    (ρ i = 2 ∧ (F i).ncard = 2 * k ∧ (B i ∩ F i).ncard = 0) ∨
    (ρ i = 3 ∧ (F i).ncard = 3 * k ∧ (B i ∩ F i).ncard ≤ 1) ∨
    (ρ i = 3 ∧ (F i).ncard = 3 * k - 1 ∧ (B i ∩ F i).ncard = 0)

/-- The indices whose chosen demand flat is a plane. -/
def planes {k : ℕ} (ρ : Fin (2 * k + 1) → ℕ) : Finset (Fin (2 * k + 1)) :=
  Finset.univ.filter fun j => ρ j = 3

theorem mem_planes {ρ : Fin (2 * k + 1) → ℕ} {j : Fin (2 * k + 1)} :
    j ∈ planes ρ ↔ ρ j = 3 := by
  simp [planes]

namespace UFam

variable {B F : Fin (2 * k + 1) → Set α} {ρ : Fin (2 * k + 1) → ℕ}

theorem sub (S : UFam M k B F ρ) (i : Fin (2 * k + 1)) : F i ⊆ M.E := (S.flat i).subset_ground

theorem rk_le (S : UFam M k B F ρ) {i : Fin (2 * k + 1)} {r : ℕ} (hr : ρ i = r) :
    M.eRk (F i) ≤ r :=
  le_of_eq (by rw [S.rk i, hr])

theorem inter_le (S : UFam M k B F ρ) (i : Fin (2 * k + 1)) {X : Set α} {r : ℕ}
    (hr : M.eRk X ≤ r) : (B i ∩ X).ncard ≤ r :=
  S.strict.ncard_inter_le (S.base i) hr

theorem inter_fin (S : UFam M k B F ρ) (i : Fin (2 * k + 1)) (X : Set α) : (B i ∩ X).Finite :=
  S.strict.finite.subset (inter_subset_left.trans (S.base i).subset_ground)

/-- **Double counting.** Every element lies in exactly two bases of the cover. -/
theorem sum_inter (S : UFam M k B F ρ) {X : Set α} (hX : X ⊆ M.E) :
    ∑ i, (B i ∩ X).ncard = 2 * X.ncard := by
  classical
  have hXfin : X.Finite := S.strict.finite.subset hX
  have h1 : ∀ i, (B i ∩ X).ncard = ∑ x ∈ hXfin.toFinset, if x ∈ B i then 1 else 0 := by
    intro i
    rw [← Finset.card_filter, ← Set.ncard_coe_finset]
    congr 1
    ext x
    simp [and_comm]
  have h2 : ∀ x ∈ hXfin.toFinset, ∑ i, (if x ∈ B i then 1 else 0) = 2 := by
    intro x hx
    obtain ⟨i, j, hij, hi, hj, huniq⟩ := S.cover x (hX (hXfin.mem_toFinset.mp hx))
    have heq : (Finset.univ.filter fun l => x ∈ B l) = {i, j} := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      exact ⟨huniq l, by rintro (rfl | rfl) <;> assumption⟩
    calc ∑ l, (if x ∈ B l then 1 else 0) = (Finset.univ.filter fun l => x ∈ B l).card :=
          (Finset.card_filter _ _).symm
      _ = 2 := by rw [heq, Finset.card_pair hij]
  rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_comm, Finset.sum_congr rfl h2,
    Finset.sum_const, smul_eq_mul, ← Set.ncard_eq_toFinset_card X hXfin]
  ring

/-- **Deficit inequality.** For `X` of rank at most `r` and `i ≠ j`,
`2|X| ≤ (2k-1) r + |B i ∩ X| + |B j ∩ X|`. -/
theorem two_mul_le (S : UFam M k B F ρ) {X : Set α} (hX : X ⊆ M.E) {r : ℕ} (hr : M.eRk X ≤ r)
    {i j : Fin (2 * k + 1)} (hij : i ≠ j) :
    2 * X.ncard ≤ (2 * k - 1) * r + (B i ∩ X).ncard + (B j ∩ X).ncard := by
  have hj : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
  have hsum := S.sum_inter hX
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), ← Finset.add_sum_erase _ _ hj] at hsum
  have hle : ∑ l ∈ (Finset.univ.erase i).erase j, (B l ∩ X).ncard ≤
      ∑ l ∈ (Finset.univ.erase i).erase j, r := Finset.sum_le_sum fun l _ => S.inter_le l hr
  rw [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem hj,
    Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin] at hle
  have hc : 2 * k + 1 - 1 - 1 = 2 * k - 1 := by omega
  rw [hc] at hle
  generalize (2 * k - 1) * r = c at hle ⊢
  omega

/-- **At most one victim.** The chosen demand flats are distinct. -/
theorem inj (S : UFam M k B F ρ) {i j : Fin (2 * k + 1)} (h : F i = F j) : i = j := by
  by_contra hij
  have hk := S.k4
  have hρ : ρ i = ρ j := by
    have h1 := S.rk i
    rw [h, S.rk j] at h1
    exact_mod_cast h1.symm
  have ki := S.kind i
  rw [h] at ki
  have hle := S.two_mul_le (S.sub j) (S.rk j).le hij
  rcases S.kind j with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;>
    rw [h1] at hle <;> omega

/-- The bases other than its victim meet a family `k`-point. -/
theorem meet_pt (S : UFam M k B F ρ) {i j : Fin (2 * k + 1)} (hj : ρ j = 1) (hij : i ≠ j) :
    1 ≤ (B i ∩ F j).ncard := by
  have hk := S.k4
  have hle := S.two_mul_le (S.sub j) (S.rk_le hj) hij
  rcases S.kind j with h | h | h | h <;> omega

/-- The bases other than its victim meet a family `2k`-line in two elements. -/
theorem meet_ln (S : UFam M k B F ρ) {i j : Fin (2 * k + 1)} (hj : ρ j = 2) (hij : i ≠ j) :
    2 ≤ (B i ∩ F j).ncard := by
  have hk := S.k4
  have hle := S.two_mul_le (S.sub j) (S.rk_le hj) hij
  rcases S.kind j with h | h | h | h <;> omega

/-- A flat meeting a family `k`-point contains it. -/
theorem pt_subset (S : UFam M k B F ρ) {j : Fin (2 * k + 1)} (hj : ρ j = 1) {G : Set α}
    (hG : M.IsFlat G) (hne : (G ∩ F j).Nonempty) : F j ⊆ G := by
  obtain ⟨x, hxG, hxP⟩ := hne
  have hx : ({x} : Set α) ⊆ M.E := Set.singleton_subset_iff.mpr (S.sub j hxP)
  refine S.strict.subset_flat hG (Set.singleton_subset_iff.mpr hxG)
    (Set.singleton_subset_iff.mpr hxP) (S.sub j) ?_
  rw [S.rk j, hj, Nat.cast_one]
  exact S.strict.one_le_eRk hx (Set.singleton_nonempty x)

/-- A flat missing one element of a family `k`-point is disjoint from it. -/
theorem disjoint_pt (S : UFam M k B F ρ) {j : Fin (2 * k + 1)} (hj : ρ j = 1) {G : Set α}
    (hG : M.IsFlat G) {x : α} (hxP : x ∈ F j) (hxG : x ∉ G) : Disjoint G (F j) := by
  by_contra hnd
  rw [Set.not_disjoint_iff_nonempty_inter] at hnd
  exact hxG (S.pt_subset hj hG hnd hxP)

/-- Distinct family `k`-points are disjoint. -/
theorem pt_disjoint (S : UFam M k B F ρ) {a b : Fin (2 * k + 1)} (ha : ρ a = 1) (hb : ρ b = 1)
    (hab : a ≠ b) : Disjoint (F a) (F b) := by
  by_contra hnd
  rw [Set.not_disjoint_iff_nonempty_inter] at hnd
  have h1 : F b ⊆ F a := S.pt_subset hb (S.flat a) hnd
  have h2 : F a ⊆ F b := S.pt_subset ha (S.flat b) (by rwa [Set.inter_comm])
  exact hab (S.inj (subset_antisymm h2 h1))

/-- **Family lines are pairwise disjoint.** Otherwise they span a plane, and their intersection
is a `k`-point missed by both of their victims. -/
theorem ln_disjoint (S : UFam M k B F ρ) {a b : Fin (2 * k + 1)} (ha : ρ a = 2) (hb : ρ b = 2)
    (hab : a ≠ b) : Disjoint (F a) (F b) := by
  have h := S.strict
  have hk := S.k4
  have hna : (F a).ncard = 2 * k := by rcases S.kind a with h1 | h1 | h1 | h1 <;> omega
  have hnb : (F b).ncard = 2 * k := by rcases S.kind b with h1 | h1 | h1 | h1 <;> omega
  have hva : (B a ∩ F a).ncard = 0 := by rcases S.kind a with h1 | h1 | h1 | h1 <;> omega
  have hvb : (B b ∩ F b).ncard = 0 := by rcases S.kind b with h1 | h1 | h1 | h1 <;> omega
  have hfa : (F a).Finite := h.finite.subset (S.sub a)
  have hfb : (F b).Finite := h.finite.subset (S.sub b)
  by_contra hnd
  rw [Set.not_disjoint_iff_nonempty_inter] at hnd
  -- `F a ∪ F b` is bigger than a line
  have hnsub : ¬ F b ⊆ F a := fun hsub =>
    hab (S.inj (Set.eq_of_subset_of_ncard_le hsub (by omega) hfa).symm)
  obtain ⟨x, hxb, hxa⟩ := Set.not_subset.mp hnsub
  have hU : 2 * k + 1 ≤ (F a ∪ F b).ncard := by
    have h1 := Set.ncard_insert_of_notMem hxa hfa
    have h2 := Set.ncard_le_ncard
      (Set.insert_subset (Set.mem_union_right (F a) hxb) subset_union_left) (hfa.union hfb)
    omega
  -- submodularity: the union has rank 3 and the intersection rank 1
  obtain ⟨u, hu, -⟩ := h.exists_eRk_eq (F a ∪ F b)
  obtain ⟨v, hv, -⟩ := h.exists_eRk_eq (F a ∩ F b)
  have hsubm := M.eRk_inter_add_eRk_union_le (F a) (F b)
  rw [hu, hv, S.rk a, S.rk b, ha, hb] at hsubm
  have hsubm2 : v + u ≤ 2 + 2 := by exact_mod_cast hsubm
  have hv1 : 1 ≤ v := by
    have h1 := h.one_le_eRk (inter_subset_left.trans (S.sub a)) hnd
    rw [hv] at h1
    exact_mod_cast h1
  have hUle := h.ncard_le (union_subset (S.sub a) (S.sub b)) hu (by omega)
  have hu3 : u = 3 := by
    by_contra hne
    have : u * k ≤ 2 * k := Nat.mul_le_mul_right k (by omega)
    omega
  subst hu3
  -- `F a ∩ F b` is a `k`-point missed by `B a` and `B b`
  have hIU := Set.ncard_inter_add_ncard_union (F a) (F b) hfa hfb
  have hle := S.two_mul_le (X := F a ∩ F b) (inter_subset_left.trans (S.sub a)) (r := 1)
    (by rw [hv]; exact_mod_cast (by omega : v ≤ 1)) hab
  have h0a := Set.ncard_le_ncard
    (inter_subset_inter_right (B a) (inter_subset_left : F a ∩ F b ⊆ F a)) (S.inter_fin a (F a))
  have h0b := Set.ncard_le_ncard
    (inter_subset_inter_right (B b) (inter_subset_right : F a ∩ F b ⊆ F b)) (S.inter_fin b (F b))
  omega

/-- **No family line lies in a family plane**: the plane's victim would meet the line at most
once, so it would be the line's victim. -/
theorem ln_not_subset (S : UFam M k B F ρ) {a b : Fin (2 * k + 1)} (ha : ρ a = 2)
    (hb : ρ b = 3) : ¬ F a ⊆ F b := by
  intro hsub
  have hba : b ≠ a := by
    rintro rfl
    omega
  have h2 := S.meet_ln ha hba
  have h1 : (B b ∩ F b).ncard ≤ 1 := by rcases S.kind b with h | h | h | h <;> omega
  have h3 := Set.ncard_le_ncard (inter_subset_inter_right (B b) hsub) (S.inter_fin b (F b))
  omega

/-- A basis meets a family `k`-point that it is not the victim of. -/
theorem exists_meet (S : UFam M k B F ρ) {a i : Fin (2 * k + 1)} (ha : ρ a = 1) (hia : i ≠ a) :
    (B i ∩ F a).Nonempty :=
  Set.nonempty_of_ncard_ne_zero (by have := S.meet_pt ha hia; omega)

theorem not_mem_of_zero (S : UFam M k B F ρ) {i : Fin (2 * k + 1)} (hv : (B i ∩ F i).ncard = 0)
    {x : α} (hx : x ∈ B i) : x ∉ F i := by
  intro hxF
  have := (Set.ncard_pos (S.inter_fin i (F i))).mpr ⟨x, hx, hxF⟩
  omega

/-- **Three family points force the rest.** If `a₁, a₂, a₃` index three family `k`-points, then
the flat of every other index is a `k`-point: the basis `B i` meets each of the three points,
and a flat that `B i` misses (or meets only once) must avoid all (or two) of them, which is too
big for the `k+2` (or `2k+2`) remaining elements. -/
theorem pt_of_three (S : UFam M k B F ρ) {a₁ a₂ a₃ i : Fin (2 * k + 1)} (h₁ : ρ a₁ = 1)
    (h₂ : ρ a₂ = 1) (h₃ : ρ a₃ = 1) (h₁₂ : a₁ ≠ a₂) (h₁₃ : a₁ ≠ a₃) (h₂₃ : a₂ ≠ a₃)
    (hi₁ : i ≠ a₁) (hi₂ : i ≠ a₂) (hi₃ : i ≠ a₃) : ρ i = 1 := by
  have h := S.strict
  have hk := S.k4
  have hn : ∀ {a : Fin (2 * k + 1)}, ρ a = 1 → (F a).ncard = k := fun {a} ha => by
    rcases S.kind a with h1 | h1 | h1 | h1 <;> omega
  have hd₁₂ := S.pt_disjoint h₁ h₂ h₁₂
  have hd₁₃ := S.pt_disjoint h₁ h₃ h₁₃
  have hd₂₃ := S.pt_disjoint h₂ h₃ h₂₃
  obtain ⟨x₁, hx₁B, hx₁P⟩ := S.exists_meet h₁ hi₁
  obtain ⟨x₂, hx₂B, hx₂P⟩ := S.exists_meet h₂ hi₂
  obtain ⟨x₃, hx₃B, hx₃P⟩ := S.exists_meet h₃ hi₃
  have hG := S.flat i
  -- a flat avoiding two of the three points has at most `2k+2` elements
  have htwo : ∀ {s t : Fin (2 * k + 1)}, ρ s = 1 → ρ t = 1 → Disjoint (F s) (F t) →
      ∀ {xs xt : α}, xs ∈ F s → xt ∈ F t → xs ∉ F i → xt ∉ F i →
      (F i).ncard + 2 * k ≤ 4 * k + 2 := by
    intro s t hs ht hst xs xt hxs hxt hxsG hxtG
    have h3 := h.ncard_add3_le (S.sub i) (S.sub s) (S.sub t) (S.disjoint_pt hs hG hxs hxsG)
      (S.disjoint_pt ht hG hxt hxtG) hst
    rw [hn hs, hn ht] at h3
    omega
  -- a flat avoiding all three points has at most `k+2` elements
  have hthree : (B i ∩ F i).ncard = 0 → (F i).ncard + 3 * k ≤ 4 * k + 2 := by
    intro hv
    have hnot := fun {x : α} (hx : x ∈ B i) => S.not_mem_of_zero hv hx
    have h4 := h.ncard_add4_le (S.sub i) (S.sub a₁) (S.sub a₂) (S.sub a₃)
      (S.disjoint_pt h₁ hG hx₁P (hnot hx₁B)) (S.disjoint_pt h₂ hG hx₂P (hnot hx₂B))
      (S.disjoint_pt h₃ hG hx₃P (hnot hx₃B)) hd₁₂ hd₁₃ hd₂₃
    rw [hn h₁, hn h₂, hn h₃] at h4
    omega
  -- two distinct elements of `B i` cannot both lie in a `3k`-plane that `B i` meets once
  have hpair : (B i ∩ F i).ncard ≤ 1 → ∀ {x y : α}, x ∈ B i → y ∈ B i → x ∈ F i → y ∈ F i →
      x ≠ y → False := by
    intro hv x y hxB hyB hxG hyG hxy
    have hsub : ({x, y} : Set α) ⊆ B i ∩ F i :=
      Set.insert_subset ⟨hxB, hxG⟩ (Set.singleton_subset_iff.mpr ⟨hyB, hyG⟩)
    have h2 := Set.ncard_le_ncard hsub (S.inter_fin i (F i))
    rw [Set.ncard_pair hxy] at h2
    omega
  have hne : ∀ {s t : Fin (2 * k + 1)} {xs xt : α}, Disjoint (F s) (F t) → xs ∈ F s →
      xt ∈ F t → xs ≠ xt := by
    intro s t xs xt hst hxs hxt heq
    rw [heq] at hxs
    exact Set.disjoint_left.mp hst hxs hxt
  rcases S.kind i with ⟨hr, -, -⟩ | ⟨-, hni, hv⟩ | ⟨-, hni, hv⟩ | ⟨-, hni, hv⟩
  · exact hr
  · have := hthree hv
    omega
  · by_cases hin₁ : x₁ ∈ F i
    · have hout₂ : x₂ ∉ F i := fun hin => hpair hv hx₁B hx₂B hin₁ hin (hne hd₁₂ hx₁P hx₂P)
      have hout₃ : x₃ ∉ F i := fun hin => hpair hv hx₁B hx₃B hin₁ hin (hne hd₁₃ hx₁P hx₃P)
      have := htwo h₂ h₃ hd₂₃ hx₂P hx₃P hout₂ hout₃
      omega
    · by_cases hin₂ : x₂ ∈ F i
      · have hout₃ : x₃ ∉ F i := fun hin => hpair hv hx₂B hx₃B hin₂ hin (hne hd₂₃ hx₂P hx₃P)
        have := htwo h₁ h₃ hd₁₃ hx₁P hx₃P hin₁ hout₃
        omega
      · have := htwo h₁ h₂ hd₁₂ hx₁P hx₂P hin₁ hin₂
        omega
  · have := hthree hv
    omega

/-- **At most two family points.** -/
theorem card_pts_le (S : UFam M k B F ρ) : (Finset.univ.filter fun i => ρ i = 1).card ≤ 2 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨a₁, ha₁, a₂, ha₂, a₃, ha₃, h₁₂, h₁₃, h₂₃⟩ := Finset.two_lt_card.mp hlt
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha₁ ha₂ ha₃
  have hall : ∀ i, ρ i = 1 := by
    intro i
    by_cases hi₁ : i = a₁
    · rw [hi₁]; exact ha₁
    by_cases hi₂ : i = a₂
    · rw [hi₂]; exact ha₂
    by_cases hi₃ : i = a₃
    · rw [hi₃]; exact ha₃
    exact S.pt_of_three ha₁ ha₂ ha₃ h₁₂ h₁₃ h₂₃ hi₁ hi₂ hi₃
  have hk := S.k4
  have hsum := S.strict.sum_ncard_le Finset.univ F S.sub
    (fun i _ j _ hij => S.pt_disjoint (hall i) (hall j) hij)
  have hn : ∀ i, (F i).ncard = k := fun i => by
    have := hall i
    rcases S.kind i with h1 | h1 | h1 | h1 <;> omega
  rw [Finset.sum_congr rfl fun i _ => hn i, Finset.sum_const, smul_eq_mul, Finset.card_univ,
    Fintype.card_fin] at hsum
  have h9 : 9 * k ≤ (2 * k + 1) * k := Nat.mul_le_mul_right k (by omega)
  omega

/-- **At most two family lines.** -/
theorem card_lns_le (S : UFam M k B F ρ) : (Finset.univ.filter fun i => ρ i = 2).card ≤ 2 := by
  have hk := S.k4
  have hsum := S.strict.sum_ncard_le (Finset.univ.filter fun i => ρ i = 2) F S.sub
    (fun i hi j hj hij =>
      S.ln_disjoint (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2 hij)
  have hn : ∀ i ∈ (Finset.univ.filter fun i => ρ i = 2), (F i).ncard = 2 * k := fun i hi => by
    have := (Finset.mem_filter.mp hi).2
    rcases S.kind i with h1 | h1 | h1 | h1 <;> omega
  rw [Finset.sum_congr rfl hn, Finset.sum_const, smul_eq_mul] at hsum
  by_contra hlt
  have h3 : 3 * (2 * k) ≤ (Finset.univ.filter fun i => ρ i = 2).card * (2 * k) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-- Every index is a point, a line or a plane. -/
theorem card_partition (S : UFam M k B F ρ) :
    2 * k + 1 ≤ (Finset.univ.filter fun i => ρ i = 1).card +
      (Finset.univ.filter fun i => ρ i = 2).card + (planes ρ).card := by
  have hsub : (Finset.univ : Finset (Fin (2 * k + 1))) ⊆
      ((Finset.univ.filter fun i => ρ i = 1) ∪ (Finset.univ.filter fun i => ρ i = 2)) ∪
        planes ρ := by
    intro i _
    simp only [planes, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases S.kind i with h | h | h | h <;> omega
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, Fintype.card_fin] at h1
  exact h1.trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_right (Finset.card_union_le _ _) _))

/-- **Faces.** The family planes that `B i` meets in three elements inject into any set `T`
containing, for each of them, the element of `B i` it misses. -/
theorem card_faces_le (S : UFam M k B F ρ) (i : Fin (2 * k + 1)) {T : Set α} (hTfin : T.Finite)
    (hT : ∀ j, ρ j = 3 → 3 ≤ (B i ∩ F j).ncard → ∀ b ∈ B i, b ∉ F j → b ∈ T) :
    ((planes ρ).filter fun j => ¬ (B i ∩ F j).ncard ≤ 2).card ≤ T.ncard := by
  have h := S.strict
  have hB := S.base i
  have hmem : ∀ j ∈ (planes ρ).filter (fun j => ¬ (B i ∩ F j).ncard ≤ 2),
      ρ j = 3 ∧ 3 ≤ (B i ∩ F j).ncard := by
    intro j hj
    rw [Finset.mem_filter, mem_planes] at hj
    exact ⟨hj.1, by have := hj.2; omega⟩
  have hex : ∀ j ∈ (planes ρ).filter (fun j => ¬ (B i ∩ F j).ncard ≤ 2),
      ∃ b, b ∈ B i ∧ b ∉ F j := fun j hj => h.exists_mem_not_mem hB (S.rk_le (hmem j hj).1)
  obtain ⟨x₀, -⟩ : (B i).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by rw [h.ncard_base hB]; norm_num)
  have : Nonempty α := ⟨x₀⟩
  choose! g hg using hex
  rw [Set.ncard_eq_toFinset_card T hTfin]
  refine Finset.card_le_card_of_injOn g (fun j hj => ?_) (fun j hj j2 hj2 hgg => ?_)
  · exact hTfin.mem_toFinset.mpr (hT j (hmem j hj).1 (hmem j hj).2 (g j) (hg j hj).1 (hg j hj).2)
  · have hs := h.sdiff_subset_of_three hB (hmem j hj).2 (hg j hj).1 (hg j hj).2
    have hs2 := h.sdiff_subset_of_three hB (hmem j2 hj2).2 (hg j2 hj2).1 (hg j2 hj2).2
    rw [← hgg] at hs2
    exact S.inj (subset_antisymm
      (h.plane_subset hB (hg j hj).1 (S.flat j2) (S.flat j) (S.rk_le (hmem j hj).1) hs2 hs)
      (h.plane_subset hB (hg j hj).1 (S.flat j) (S.flat j2) (S.rk_le (hmem j2 hj2).1) hs hs2))

/-- A basis has at most four faces. -/
theorem faces_le_four (S : UFam M k B F ρ) (i : Fin (2 * k + 1)) :
    ((planes ρ).filter fun j => ¬ (B i ∩ F j).ncard ≤ 2).card ≤ 4 := by
  have := S.card_faces_le i (S.strict.finite.subset (S.base i).subset_ground)
    (fun _ _ _ b hb _ => hb)
  rwa [S.strict.ncard_base (S.base i)] at this

/-- **Faces through a family line.** If `B i` is not the victim of the family line `F a`, it
meets `F a` in two elements. A face of `B i` through both would contain `F a`, so it is not a
family plane. Hence at most two faces of `B i` are family planes. -/
theorem faces_le_two (S : UFam M k B F ρ) {i a : Fin (2 * k + 1)} (ha : ρ a = 2) (hia : i ≠ a) :
    ((planes ρ).filter fun j => ¬ (B i ∩ F j).ncard ≤ 2).card ≤ 2 := by
  have h := S.strict
  have hD := S.meet_ln ha hia
  have hT : ∀ j, ρ j = 3 → 3 ≤ (B i ∩ F j).ncard → ∀ b ∈ B i, b ∉ F j → b ∈ B i ∩ F a := by
    intro j hj h3 b hb hbF
    refine ⟨hb, ?_⟩
    by_contra hba
    apply S.ln_not_subset ha hj
    have hs := h.sdiff_subset_of_three (S.base i) h3 hb hbF
    have hDs : B i ∩ F a ⊆ F j := by
      rintro x ⟨hxB, hxa⟩
      refine hs ⟨hxB, fun hxb => hba ?_⟩
      rw [Set.mem_singleton_iff] at hxb
      rw [← hxb]
      exact hxa
    refine h.subset_flat (S.flat j) hDs inter_subset_right (S.sub a) ?_
    rw [S.rk a, ha, h.eRk_indep ((S.base i).indep.subset inter_subset_left)]
    exact_mod_cast hD
  exact (S.card_faces_le i (S.inter_fin i (F a)) hT).trans (S.inter_le i (S.rk_le ha))

/-- **Deficit of a family plane.** At most three bases meet a family plane in two elements or
fewer: its total deficit is `3` or `5`, of which its victim takes `2` or `3`. -/
theorem card_low_le (S : UFam M k B F ρ) {j : Fin (2 * k + 1)} (hj : ρ j = 3) :
    (Finset.univ.filter fun i => (B i ∩ F j).ncard ≤ 2).card ≤ 3 := by
  have hk := S.k4
  have hsum := S.sum_inter (S.sub j)
  have hx : ∀ i, (B i ∩ F j).ncard ≤ 3 := fun i => S.inter_le i (S.rk_le hj)
  have hc : (Finset.univ.filter fun i => (B i ∩ F j).ncard ≤ 2).card =
      ∑ i, if (B i ∩ F j).ncard ≤ 2 then 1 else 0 := Finset.card_filter _ _
  have key : ∑ i, ((B i ∩ F j).ncard + if (B i ∩ F j).ncard ≤ 2 then 1 else 0) ≤
      ((B j ∩ F j).ncard + 1) + 3 * (2 * k) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    have h1 : ((B j ∩ F j).ncard + if (B j ∩ F j).ncard ≤ 2 then 1 else 0) ≤
        (B j ∩ F j).ncard + 1 := by
      split_ifs <;> omega
    have h2 : ∑ i ∈ Finset.univ.erase j,
        ((B i ∩ F j).ncard + if (B i ∩ F j).ncard ≤ 2 then 1 else 0) ≤
        ∑ i ∈ Finset.univ.erase j, 3 :=
      Finset.sum_le_sum fun i _ => by have := hx i; split_ifs <;> omega
    rw [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ j),
      Finset.card_univ, Fintype.card_fin] at h2
    omega
  rw [Finset.sum_add_distrib, hsum] at key
  rcases S.kind j with h | h | h | h <;> omega

/-- **Double counting** the pairs (basis, family plane met in at most two elements). -/
theorem sum_low_le (S : UFam M k B F ρ) :
    ∑ i, ((planes ρ).filter fun j => (B i ∩ F j).ncard ≤ 2).card ≤ 3 * (planes ρ).card := by
  calc ∑ i, ((planes ρ).filter fun j => (B i ∩ F j).ncard ≤ 2).card
      = ∑ i, ∑ j ∈ planes ρ, if (B i ∩ F j).ncard ≤ 2 then 1 else 0 :=
        Finset.sum_congr rfl fun i _ => Finset.card_filter _ _
    _ = ∑ j ∈ planes ρ, ∑ i, if (B i ∩ F j).ncard ≤ 2 then 1 else 0 := Finset.sum_comm
    _ = ∑ j ∈ planes ρ, (Finset.univ.filter fun i => (B i ∩ F j).ncard ≤ 2).card :=
        Finset.sum_congr rfl fun j _ => (Finset.card_filter _ _).symm
    _ ≤ ∑ j ∈ planes ρ, 3 := Finset.sum_le_sum fun j hj => S.card_low_le (mem_planes.mp hj)
    _ = 3 * (planes ρ).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- **The budget fails.** There are `m ≥ 2k-3` family planes. With a family line, each of the
`2k` bases other than its victim meets at least `m-2` family planes in two elements or fewer, so
`2k(m-2) ≤ 3m`. Without one, `m ≥ 2k-1` and every basis meets at least `m-4` family planes in
two elements or fewer, so `(2k+1)(m-4) ≤ 3m`. Both are false for `k ≥ 4`. -/
theorem not_ufam (S : UFam M k B F ρ) : False := by
  have hk := S.k4
  have hpt := S.card_pts_le
  have hln := S.card_lns_le
  have hpart := S.card_partition
  have hsum := S.sum_low_le
  have hdf : ∀ i, ((planes ρ).filter fun j => (B i ∩ F j).ncard ≤ 2).card +
      ((planes ρ).filter fun j => ¬ (B i ∩ F j).ncard ≤ 2).card = (planes ρ).card :=
    fun i => Finset.card_filter_add_card_filter_not _
  by_cases hl : ∃ a, ρ a = 2
  · obtain ⟨a, ha⟩ := hl
    have hlow : ∀ i ∈ Finset.univ.erase a,
        (planes ρ).card - 2 ≤ ((planes ρ).filter fun j => (B i ∩ F j).ncard ≤ 2).card := by
      intro i hi
      have h1 := S.faces_le_two ha (Finset.ne_of_mem_erase hi)
      have h2 := hdf i
      omega
    have h1 := Finset.sum_le_sum hlow
    have h2 : ∑ i ∈ Finset.univ.erase a, ((planes ρ).filter fun j => (B i ∩ F j).ncard ≤ 2).card
        ≤ ∑ i, ((planes ρ).filter fun j => (B i ∩ F j).ncard ≤ 2).card :=
      Finset.sum_le_sum_of_subset (Finset.erase_subset a _)
    rw [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ a),
      Finset.card_univ, Fintype.card_fin] at h1
    have h3 : 8 * ((planes ρ).card - 2) ≤ (2 * k + 1 - 1) * ((planes ρ).card - 2) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  · push Not at hl
    have hl0 : (Finset.univ.filter fun i => ρ i = 2).card = 0 :=
      Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun i _ => hl i)
    have hlow : ∀ i ∈ (Finset.univ : Finset (Fin (2 * k + 1))),
        (planes ρ).card - 4 ≤ ((planes ρ).filter fun j => (B i ∩ F j).ncard ≤ 2).card := by
      intro i _
      have h1 := S.faces_le_four i
      have h2 := hdf i
      omega
    have h1 := Finset.sum_le_sum hlow
    rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fin] at h1
    have h3 : 9 * ((planes ρ).card - 4) ≤ (2 * k + 1) * ((planes ρ).card - 4) :=
      Nat.mul_le_mul_right _ (by omega)
    omega

end UFam

/-- **Lemma U.** For `k ≥ 4`, some basis of every double cover of a strict t=0 matroid meets the
demands. -/
theorem lemmaU {α : Type*} : LemmaUStatement α := by
  intro M k hk h B hB hcov
  by_contra hno
  have hno2 : ∀ i, ¬ MeetsDemands M k (B i) := fun i hi => hno ⟨i, hi⟩
  choose F ρ hF using fun i => exists_viol h (hB i) (hno2 i)
  exact UFam.not_ufam ⟨hk, h, hB, hcov, fun i => (hF i).1, fun i => (hF i).2.1,
    fun i => (hF i).2.2⟩

end Hitting
end HigherRankKUM

#print axioms HigherRankKUM.Hitting.lemmaU
