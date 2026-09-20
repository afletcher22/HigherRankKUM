import HigherRankKUM.Rank4.DangerousHyperplaneSelection
import HigherRankKUM.Rank4.FiniteSchedule
import HigherRankKUM.CyclicRotation
import Mathlib.Logic.Equiv.Set
import Mathlib.Tactic

namespace HigherRankKUM
namespace Rank4DangerousBranches

open Set
open scoped Matroid

noncomputable section

variable {α : Type*}

/-- Partition the ground into the complement of a dangerous hyperplane and
the hyperplane itself. -/
def dangerous_hyperplane_parts_equiv_ground
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hH : DangerousHyperplane M k H) :
    (M.E \ H : Set α) ⊕ (H : Set α) ≃ M.E := by
  have hd : Disjoint (M.E \ H) H := disjoint_sdiff_left
  let e : (M.E \ H : Set α) ⊕ (H : Set α) ≃
      ((M.E \ H) ∪ H : Set α) :=
    (Equiv.Set.union hd).symm
  have hEq : (M.E \ H) ∪ H = M.E := by
    rw [sdiff_union_self, union_eq_self_of_subset_right hH.subset_ground]
  exact e.trans (Equiv.setCongr hEq)

@[simp] theorem dangerous_hyperplane_parts_equiv_ground_left
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hH : DangerousHyperplane M k H)
    (c : (M.E \ H : Set α)) :
    (dangerous_hyperplane_parts_equiv_ground hH (Sum.inl c) : α) = c := by
  simp [dangerous_hyperplane_parts_equiv_ground]

@[simp] theorem dangerous_hyperplane_parts_equiv_ground_right
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hH : DangerousHyperplane M k H)
    (g : (H : Set α)) :
    (dangerous_hyperplane_parts_equiv_ground hH (Sum.inr g) : α) = g := by
  simp [dangerous_hyperplane_parts_equiv_ground]

/-- The global separated-good schedule
C G G C G G (C G G G)^(k-1), assembled from a complement enumeration
and a core cyclic order. -/
def dangerousSeparatedScheduleOrder
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hk : 2 ≤ k)
    (hH : DangerousHyperplane M k H)
    (eC : Fin (k + 1) ≃ (M.E \ H : Set α))
    (order : Fin (3 * k + 1) ≃ (M.restrict H).E) :
    Fin (4 * k + 2) ≃ M.E := by
  let eG : Fin (3 * k + 1) ≃ (H : Set α) := by
    simpa using order
  exact
    (FiniteSchedule.hyperSeparatedIndexEquiv k hk).trans
      ((Equiv.sumCongr eC eG).trans
        (dangerous_hyperplane_parts_equiv_ground hH))

@[simp] theorem dangerousSeparatedScheduleOrder_head0
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hk : 2 ≤ k) (hH : DangerousHyperplane M k H)
    (eC : Fin (k + 1) ≃ (M.E \ H : Set α))
    (order : Fin (3 * k + 1) ≃ (M.restrict H).E) :
    (dangerousSeparatedScheduleOrder hk hH eC order
      ⟨0, by omega⟩ : α) =
      (eC ⟨0, by omega⟩ : α) := by
  simp [dangerousSeparatedScheduleOrder,
    FiniteSchedule.hyperSeparatedHeadSlot,
    dangerous_hyperplane_parts_equiv_ground]

@[simp] theorem dangerousSeparatedScheduleOrder_head1
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hk : 2 ≤ k) (hH : DangerousHyperplane M k H)
    (eC : Fin (k + 1) ≃ (M.E \ H : Set α))
    (order : Fin (3 * k + 1) ≃ (M.restrict H).E) :
    (dangerousSeparatedScheduleOrder hk hH eC order
      ⟨1, by omega⟩ : α) =
      (order ⟨0, by omega⟩ : α) := by
  simp [dangerousSeparatedScheduleOrder,
    FiniteSchedule.hyperSeparatedHeadSlot,
    dangerous_hyperplane_parts_equiv_ground]

@[simp] theorem dangerousSeparatedScheduleOrder_head2
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hk : 2 ≤ k) (hH : DangerousHyperplane M k H)
    (eC : Fin (k + 1) ≃ (M.E \ H : Set α))
    (order : Fin (3 * k + 1) ≃ (M.restrict H).E) :
    (dangerousSeparatedScheduleOrder hk hH eC order
      ⟨2, by omega⟩ : α) =
      (order ⟨1, by omega⟩ : α) := by
  simp [dangerousSeparatedScheduleOrder,
    FiniteSchedule.hyperSeparatedHeadSlot,
    dangerous_hyperplane_parts_equiv_ground]

@[simp] theorem dangerousSeparatedScheduleOrder_head3
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hk : 2 ≤ k) (hH : DangerousHyperplane M k H)
    (eC : Fin (k + 1) ≃ (M.E \ H : Set α))
    (order : Fin (3 * k + 1) ≃ (M.restrict H).E) :
    (dangerousSeparatedScheduleOrder hk hH eC order
      ⟨3, by omega⟩ : α) =
      (eC ⟨1, by omega⟩ : α) := by
  simp [dangerousSeparatedScheduleOrder,
    FiniteSchedule.hyperSeparatedHeadSlot,
    dangerous_hyperplane_parts_equiv_ground]

@[simp] theorem dangerousSeparatedScheduleOrder_head4
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hk : 2 ≤ k) (hH : DangerousHyperplane M k H)
    (eC : Fin (k + 1) ≃ (M.E \ H : Set α))
    (order : Fin (3 * k + 1) ≃ (M.restrict H).E) :
    (dangerousSeparatedScheduleOrder hk hH eC order
      ⟨4, by omega⟩ : α) =
      (order ⟨2, by omega⟩ : α) := by
  simp [dangerousSeparatedScheduleOrder,
    FiniteSchedule.hyperSeparatedHeadSlot,
    dangerous_hyperplane_parts_equiv_ground]

@[simp] theorem dangerousSeparatedScheduleOrder_head5
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hk : 2 ≤ k) (hH : DangerousHyperplane M k H)
    (eC : Fin (k + 1) ≃ (M.E \ H : Set α))
    (order : Fin (3 * k + 1) ≃ (M.restrict H).E) :
    (dangerousSeparatedScheduleOrder hk hH eC order
      ⟨5, by omega⟩ : α) =
      (order ⟨3, by omega⟩ : α) := by
  simp [dangerousSeparatedScheduleOrder,
    FiniteSchedule.hyperSeparatedHeadSlot,
    dangerous_hyperplane_parts_equiv_ground]

@[simp] theorem dangerousSeparatedScheduleOrder_blockC
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hk : 2 ≤ k) (hH : DangerousHyperplane M k H)
    (eC : Fin (k + 1) ≃ (M.E \ H : Set α))
    (order : Fin (3 * k + 1) ≃ (M.restrict H).E)
    (j : Fin (k - 1)) :
    (dangerousSeparatedScheduleOrder hk hH eC order
      ⟨6 + 4 * j.val, by omega⟩ : α) =
      (eC ⟨j.val + 2, by omega⟩ : α) := by
  have hpos :
      (⟨6 + 4 * j.val, by omega⟩ : Fin (4 * k + 2)) =
        ⟨6 + (0 : Fin 4).val + 4 * j.val, by omega⟩ := by
    apply Fin.ext
    simp
  rw [hpos]
  simp [dangerousSeparatedScheduleOrder,
    FiniteSchedule.hyperSeparatedBlockSlot,
    dangerous_hyperplane_parts_equiv_ground]

@[simp] theorem dangerousSeparatedScheduleOrder_blockG0
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hk : 2 ≤ k) (hH : DangerousHyperplane M k H)
    (eC : Fin (k + 1) ≃ (M.E \ H : Set α))
    (order : Fin (3 * k + 1) ≃ (M.restrict H).E)
    (j : Fin (k - 1)) :
    (dangerousSeparatedScheduleOrder hk hH eC order
      ⟨7 + 4 * j.val, by omega⟩ : α) =
      (order ⟨3 * j.val + 4, by omega⟩ : α) := by
  have hpos :
      (⟨7 + 4 * j.val, by omega⟩ : Fin (4 * k + 2)) =
        ⟨6 + (1 : Fin 4).val + 4 * j.val, by omega⟩ := by
    apply Fin.ext
    simp
  rw [hpos]
  simp [dangerousSeparatedScheduleOrder,
    FiniteSchedule.hyperSeparatedBlockSlot,
    dangerous_hyperplane_parts_equiv_ground]

@[simp] theorem dangerousSeparatedScheduleOrder_blockG1
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hk : 2 ≤ k) (hH : DangerousHyperplane M k H)
    (eC : Fin (k + 1) ≃ (M.E \ H : Set α))
    (order : Fin (3 * k + 1) ≃ (M.restrict H).E)
    (j : Fin (k - 1)) :
    (dangerousSeparatedScheduleOrder hk hH eC order
      ⟨8 + 4 * j.val, by omega⟩ : α) =
      (order ⟨3 * j.val + 5, by omega⟩ : α) := by
  have hpos :
      (⟨8 + 4 * j.val, by omega⟩ : Fin (4 * k + 2)) =
        ⟨6 + (2 : Fin 4).val + 4 * j.val, by omega⟩ := by
    apply Fin.ext
    simp
  rw [hpos]
  simp [dangerousSeparatedScheduleOrder,
    FiniteSchedule.hyperSeparatedBlockSlot,
    dangerous_hyperplane_parts_equiv_ground]

@[simp] theorem dangerousSeparatedScheduleOrder_blockG2
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hk : 2 ≤ k) (hH : DangerousHyperplane M k H)
    (eC : Fin (k + 1) ≃ (M.E \ H : Set α))
    (order : Fin (3 * k + 1) ≃ (M.restrict H).E)
    (j : Fin (k - 1)) :
    (dangerousSeparatedScheduleOrder hk hH eC order
      ⟨9 + 4 * j.val, by omega⟩ : α) =
      (order ⟨3 * j.val + 6, by omega⟩ : α) := by
  have hpos :
      (⟨9 + 4 * j.val, by omega⟩ : Fin (4 * k + 2)) =
        ⟨6 + (3 : Fin 4).val + 4 * j.val, by omega⟩ := by
    apply Fin.ext
    simp
  rw [hpos]
  simp [dangerousSeparatedScheduleOrder,
    FiniteSchedule.hyperSeparatedBlockSlot,
    dangerous_hyperplane_parts_equiv_ground]

/-- Every nonexceptional length-four window of the separated-good
schedule consists of one complement element and three consecutive core
elements. The only exceptional starts are 0 and 3. -/
theorem dangerousSeparatedSchedule_window_classification
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hk : 2 ≤ k)
    (hH : DangerousHyperplane M k H)
    (eC : Fin (k + 1) ≃ (M.E \ H : Set α))
    (order : Fin (3 * k + 1) ≃ (M.restrict H).E)
    (s : Fin (4 * k + 2))
    (hs0 : s.val ≠ 0)
    (hs3 : s.val ≠ 3) :
    ∃ m : Fin (k + 1), ∃ q : Fin (3 * k + 1),
      ({(dangerousSeparatedScheduleOrder hk hH eC order s : α),
        (dangerousSeparatedScheduleOrder hk hH eC order
          (cyclicIndex (4 * k + 2) (by omega) s 1) : α),
        (dangerousSeparatedScheduleOrder hk hH eC order
          (cyclicIndex (4 * k + 2) (by omega) s 2) : α),
        (dangerousSeparatedScheduleOrder hk hH eC order
          (cyclicIndex (4 * k + 2) (by omega) s 3) : α)} : Set α) =
      ({(eC m : α),
        (order q : α),
        (order (cyclicIndex (3 * k + 1) (by omega) q 1) : α),
        (order (cyclicIndex (3 * k + 1) (by omega) q 2) : α)} : Set α) := by
  let σ := dangerousSeparatedScheduleOrder hk hH eC order
  have hglobal_add
      (a d : ℕ) (ha : a < 4 * k + 2) (had : a + d < 4 * k + 2) :
      cyclicIndex (4 * k + 2) (by omega)
          (⟨a, ha⟩ : Fin (4 * k + 2)) d =
        ⟨a + d, had⟩ := by
    exact cyclicIndex_eq_mk_add_of_lt _ _ _ _ had
  have hcore_add
      (a d : ℕ) (ha : a < 3 * k + 1) (had : a + d < 3 * k + 1) :
      cyclicIndex (3 * k + 1) (by omega)
          (⟨a, ha⟩ : Fin (3 * k + 1)) d =
        ⟨a + d, had⟩ := by
    exact cyclicIndex_eq_mk_add_of_lt _ _ _ _ had

  by_cases hs6 : s.val < 6
  · have hcases :
        s.val = 1 ∨ s.val = 2 ∨ s.val = 4 ∨ s.val = 5 := by
      omega
    rcases hcases with h1 | h2 | h4 | h5
    · have hs : s = ⟨1, by omega⟩ := Fin.ext h1
      subst s
      have hg1 := hglobal_add 1 1 (by omega) (by omega)
      have hg2 := hglobal_add 1 2 (by omega) (by omega)
      have hg3 := hglobal_add 1 3 (by omega) (by omega)
      have hc1 := hcore_add 0 1 (by omega) (by omega)
      have hc2 := hcore_add 0 2 (by omega) (by omega)
      refine ⟨⟨1, by omega⟩, ⟨0, by omega⟩, ?_⟩
      rw [hg1, hg2, hg3, hc1, hc2]
      simp [σ]
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    · have hs : s = ⟨2, by omega⟩ := Fin.ext h2
      subst s
      have hg1 := hglobal_add 2 1 (by omega) (by omega)
      have hg2 := hglobal_add 2 2 (by omega) (by omega)
      have hg3 := hglobal_add 2 3 (by omega) (by omega)
      have hc1 := hcore_add 1 1 (by omega) (by omega)
      have hc2 := hcore_add 1 2 (by omega) (by omega)
      refine ⟨⟨1, by omega⟩, ⟨1, by omega⟩, ?_⟩
      rw [hg1, hg2, hg3, hc1, hc2]
      simp [σ]
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    · have hs : s = ⟨4, by omega⟩ := Fin.ext h4
      subst s
      have hg1 := hglobal_add 4 1 (by omega) (by omega)
      have hg2 := hglobal_add 4 2 (by omega) (by omega)
      have hg3 := hglobal_add 4 3 (by omega) (by omega)
      have hc1 := hcore_add 2 1 (by omega) (by omega)
      have hc2 := hcore_add 2 2 (by omega) (by omega)
      refine ⟨⟨2, by omega⟩, ⟨2, by omega⟩, ?_⟩
      rw [hg1, hg2, hg3, hc1, hc2]
      simp [σ]
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    · have hs : s = ⟨5, by omega⟩ := Fin.ext h5
      subst s
      have hg1 := hglobal_add 5 1 (by omega) (by omega)
      have hg2 := hglobal_add 5 2 (by omega) (by omega)
      have hg3 := hglobal_add 5 3 (by omega) (by omega)
      have hc1 := hcore_add 3 1 (by omega) (by omega)
      have hc2 := hcore_add 3 2 (by omega) (by omega)
      refine ⟨⟨2, by omega⟩, ⟨3, by omega⟩, ?_⟩
      rw [hg1, hg2, hg3, hc1, hc2]
      simp [σ]
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto

  by_cases hwrap : 4 * k - 1 ≤ s.val
  · have hcases :
        s.val = 4 * k - 1 ∨
        s.val = 4 * k ∨
        s.val = 4 * k + 1 := by
      have hslt := s.isLt
      omega
    let jlast : Fin (k - 1) := ⟨k - 2, by omega⟩
    have hC_last :
        (σ ⟨4 * k - 2, by omega⟩ : α) =
          (eC ⟨k, by omega⟩ : α) := by
      have h := dangerousSeparatedScheduleOrder_blockC
        hk hH eC order jlast
      simpa [σ, jlast] using h
    have hG_last0 :
        (σ ⟨4 * k - 1, by omega⟩ : α) =
          (order ⟨3 * k - 2, by omega⟩ : α) := by
      have h := dangerousSeparatedScheduleOrder_blockG0
        hk hH eC order jlast
      simpa [σ, jlast] using h
    have hG_last1 :
        (σ ⟨4 * k, by omega⟩ : α) =
          (order ⟨3 * k - 1, by omega⟩ : α) := by
      have h := dangerousSeparatedScheduleOrder_blockG1
        hk hH eC order jlast
      simpa [σ, jlast] using h
    have hG_last2 :
        (σ ⟨4 * k + 1, by omega⟩ : α) =
          (order ⟨3 * k, by omega⟩ : α) := by
      have h := dangerousSeparatedScheduleOrder_blockG2
        hk hH eC order jlast
      simpa [σ, jlast] using h
    rcases hcases with hA | hB | hC
    · have hs : s = ⟨4 * k - 1, by omega⟩ := Fin.ext hA
      subst s
      have hg1 := hglobal_add (4 * k - 1) 1 (by omega) (by omega)
      have hg2 := hglobal_add (4 * k - 1) 2 (by omega) (by omega)
      have hg3 :
          cyclicIndex (4 * k + 2) (by omega)
              (⟨4 * k - 1, by omega⟩ : Fin (4 * k + 2)) 3 =
            ⟨0, by omega⟩ := by
        apply Fin.ext
        simp [cyclicIndex]
        omega
      have hc1 := hcore_add (3 * k - 2) 1 (by omega) (by omega)
      have hc2 := hcore_add (3 * k - 2) 2 (by omega) (by omega)
      refine ⟨⟨0, by omega⟩, ⟨3 * k - 2, by omega⟩, ?_⟩
      rw [hg1, hg2, hg3, hc1, hc2,
        hG_last0, hG_last1, hG_last2]
      simp [σ]
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    · have hs : s = ⟨4 * k, by omega⟩ := Fin.ext hB
      subst s
      have hg1 := hglobal_add (4 * k) 1 (by omega) (by omega)
      have hg2 :
          cyclicIndex (4 * k + 2) (by omega)
              (⟨4 * k, by omega⟩ : Fin (4 * k + 2)) 2 =
            ⟨0, by omega⟩ := by
        apply Fin.ext
        simp [cyclicIndex]
      have hg3 :
          cyclicIndex (4 * k + 2) (by omega)
              (⟨4 * k, by omega⟩ : Fin (4 * k + 2)) 3 =
            ⟨1, by omega⟩ := by
        apply Fin.ext
        simp [cyclicIndex]
      have hc1 := hcore_add (3 * k - 1) 1 (by omega) (by omega)
      have hc2 :
          cyclicIndex (3 * k + 1) (by omega)
              (⟨3 * k - 1, by omega⟩ : Fin (3 * k + 1)) 2 =
            ⟨0, by omega⟩ := by
        apply Fin.ext
        simp [cyclicIndex]
      refine ⟨⟨0, by omega⟩, ⟨3 * k - 1, by omega⟩, ?_⟩
      rw [hg1, hg2, hg3, hc1, hc2,
        hG_last1, hG_last2]
      simp [σ]
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    · have hs : s = ⟨4 * k + 1, by omega⟩ := Fin.ext hC
      subst s
      have hg1 :
          cyclicIndex (4 * k + 2) (by omega)
              (⟨4 * k + 1, by omega⟩ : Fin (4 * k + 2)) 1 =
            ⟨0, by omega⟩ := by
        apply Fin.ext
        simp [cyclicIndex]
      have hg2 :
          cyclicIndex (4 * k + 2) (by omega)
              (⟨4 * k + 1, by omega⟩ : Fin (4 * k + 2)) 2 =
            ⟨1, by omega⟩ := by
        apply Fin.ext
        simp [cyclicIndex]
      have hg3 :
          cyclicIndex (4 * k + 2) (by omega)
              (⟨4 * k + 1, by omega⟩ : Fin (4 * k + 2)) 3 =
            ⟨2, by omega⟩ := by
        apply Fin.ext
        simp [cyclicIndex]
      have hc1 :
          cyclicIndex (3 * k + 1) (by omega)
              (⟨3 * k, by omega⟩ : Fin (3 * k + 1)) 1 =
            ⟨0, by omega⟩ := by
        apply Fin.ext
        simp [cyclicIndex]
      have hc2 :
          cyclicIndex (3 * k + 1) (by omega)
              (⟨3 * k, by omega⟩ : Fin (3 * k + 1)) 2 =
            ⟨1, by omega⟩ := by
        apply Fin.ext
        simp [cyclicIndex]
      refine ⟨⟨0, by omega⟩, ⟨3 * k, by omega⟩, ?_⟩
      rw [hg1, hg2, hg3, hc1, hc2, hG_last2]
      simp [σ]
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto

  have hslo : 6 ≤ s.val := by omega
  have hshi : s.val < 4 * k - 1 := by omega
  let t := s.val - 6
  let j : Fin (k - 1) := ⟨t / 4, by
    dsimp [t]
    omega⟩
  have hmod : t % 4 < 4 := Nat.mod_lt _ (by omega)
  interval_cases hr : t % 4
  · have hsval : s.val = 6 + 4 * j.val := by
      dsimp [j, t]
      have hm := Nat.mod_add_div t 4
      omega
    have hs : s = ⟨6 + 4 * j.val, by omega⟩ := Fin.ext hsval
    subst s
    have hg1 := hglobal_add (6 + 4 * j.val) 1 (by omega) (by omega)
    have hg2 := hglobal_add (6 + 4 * j.val) 2 (by omega) (by omega)
    have hg3 := hglobal_add (6 + 4 * j.val) 3 (by omega) (by omega)
    let q : Fin (3 * k + 1) := ⟨3 * j.val + 4, by omega⟩
    have hc1 := hcore_add (3 * j.val + 4) 1 (by omega) (by omega)
    have hc2 := hcore_add (3 * j.val + 4) 2 (by omega) (by omega)
    refine ⟨⟨j.val + 2, by omega⟩, q, ?_⟩
    rw [hg1, hg2, hg3, hc1, hc2]
    simp [σ, q]
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  · have hsval : s.val = 7 + 4 * j.val := by
      dsimp [j, t]
      have hm := Nat.mod_add_div t 4
      omega
    have hjnext : j.val + 1 < k - 1 := by omega
    let jn : Fin (k - 1) := ⟨j.val + 1, hjnext⟩
    have hs : s = ⟨7 + 4 * j.val, by omega⟩ := Fin.ext hsval
    subst s
    have hg1 := hglobal_add (7 + 4 * j.val) 1 (by omega) (by omega)
    have hg2 := hglobal_add (7 + 4 * j.val) 2 (by omega) (by omega)
    have hg3 := hglobal_add (7 + 4 * j.val) 3 (by omega) (by omega)
    let q : Fin (3 * k + 1) := ⟨3 * j.val + 4, by omega⟩
    have hc1 := hcore_add (3 * j.val + 4) 1 (by omega) (by omega)
    have hc2 := hcore_add (3 * j.val + 4) 2 (by omega) (by omega)
    refine ⟨⟨j.val + 3, by omega⟩, q, ?_⟩
    rw [hg1, hg2, hg3, hc1, hc2]
    have hnextC :=
      dangerousSeparatedScheduleOrder_blockC hk hH eC order jn
    simp [σ, q, jn] at hnextC ⊢
    rw [hnextC]
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  · have hsval : s.val = 8 + 4 * j.val := by
      dsimp [j, t]
      have hm := Nat.mod_add_div t 4
      omega
    have hjnext : j.val + 1 < k - 1 := by omega
    let jn : Fin (k - 1) := ⟨j.val + 1, hjnext⟩
    have hs : s = ⟨8 + 4 * j.val, by omega⟩ := Fin.ext hsval
    subst s
    have hg1 := hglobal_add (8 + 4 * j.val) 1 (by omega) (by omega)
    have hg2 := hglobal_add (8 + 4 * j.val) 2 (by omega) (by omega)
    have hg3 := hglobal_add (8 + 4 * j.val) 3 (by omega) (by omega)
    let q : Fin (3 * k + 1) := ⟨3 * j.val + 5, by omega⟩
    have hc1 := hcore_add (3 * j.val + 5) 1 (by omega) (by omega)
    have hc2 := hcore_add (3 * j.val + 5) 2 (by omega) (by omega)
    refine ⟨⟨j.val + 3, by omega⟩, q, ?_⟩
    rw [hg1, hg2, hg3, hc1, hc2]
    have hnextC :=
      dangerousSeparatedScheduleOrder_blockC hk hH eC order jn
    have hnextG :=
      dangerousSeparatedScheduleOrder_blockG0 hk hH eC order jn
    simp [σ, q, jn] at hnextC hnextG ⊢
    rw [hnextC, hnextG]
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  · have hsval : s.val = 9 + 4 * j.val := by
      dsimp [j, t]
      have hm := Nat.mod_add_div t 4
      omega
    have hjnext : j.val + 1 < k - 1 := by omega
    let jn : Fin (k - 1) := ⟨j.val + 1, hjnext⟩
    have hs : s = ⟨9 + 4 * j.val, by omega⟩ := Fin.ext hsval
    subst s
    have hg1 := hglobal_add (9 + 4 * j.val) 1 (by omega) (by omega)
    have hg2 := hglobal_add (9 + 4 * j.val) 2 (by omega) (by omega)
    have hg3 := hglobal_add (9 + 4 * j.val) 3 (by omega) (by omega)
    let q : Fin (3 * k + 1) := ⟨3 * j.val + 6, by omega⟩
    have hc1 := hcore_add (3 * j.val + 6) 1 (by omega) (by omega)
    have hc2 := hcore_add (3 * j.val + 6) 2 (by omega) (by omega)
    refine ⟨⟨j.val + 3, by omega⟩, q, ?_⟩
    rw [hg1, hg2, hg3, hc1, hc2]
    have hnextC :=
      dangerousSeparatedScheduleOrder_blockC hk hH eC order jn
    have hnextG0 :=
      dangerousSeparatedScheduleOrder_blockG0 hk hH eC order jn
    have hnextG1 :=
      dangerousSeparatedScheduleOrder_blockG1 hk hH eC order jn
    simp [σ, q, jn] at hnextC hnextG0 hnextG1 ⊢
    rw [hnextC, hnextG0, hnextG1]
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto

/-- Rotate a core CBO so a chosen source index appears at a chosen target
index. The returned pointwise identity tracks every later cyclic offset. -/
theorem exists_shifted_cbo_with_start
    {M : Matroid α} {n r : ℕ}
    (hn : 0 < n)
    (order : Fin n ≃ M.E)
    (hOrder : CyclicBasisOrder M r hn order)
    (src target : Fin n) :
    ∃ order' : Fin n ≃ M.E,
      CyclicBasisOrder M r hn order' ∧
      ∀ j : ℕ,
        (order' (cyclicIndex n hn target j) : α) =
          (order (cyclicIndex n hn src j) : α) := by
  obtain ⟨t, ht, _⟩ :=
    existsUnique_cyclicIndex_offset n hn target src
  let order' : Fin n ≃ M.E :=
    (cyclicShiftEquiv n hn t.val).trans order
  have hCBO : CyclicBasisOrder M r hn order' :=
    hOrder.shift hn order t.val
  refine ⟨order', hCBO, ?_⟩
  intro j
  change
    (order
      (cyclicShiftEquiv n hn t.val
        (cyclicIndex n hn target j)) : α) =
      (order (cyclicIndex n hn src j) : α)
  rw [cyclicShiftEquiv_cyclicIndex, cyclicShiftEquiv_apply, ← ht]

/-- Rotate adjacent good edges so they become the two wrap-adjacent core
edges at indices 3k-1 and 3k. -/
theorem exists_shifted_adjacent_good_at_end
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hk : 2 ≤ k)
    (order : Fin (3 * k + 1) ≃ (M.restrict H).E)
    (hOrder :
      CyclicBasisOrder (M.restrict H) 3 (by omega) order)
    (i : Fin (3 * k + 1))
    (hgood0 : DangerousHyperplaneEdgeGood order i)
    (hgood1 :
      DangerousHyperplaneEdgeGood order
        (cyclicIndex (3 * k + 1) (by omega) i 1)) :
    ∃ order' : Fin (3 * k + 1) ≃ (M.restrict H).E,
      CyclicBasisOrder (M.restrict H) 3 (by omega) order' ∧
      DangerousHyperplaneEdgeGood order'
        ⟨3 * k - 1, by omega⟩ ∧
      DangerousHyperplaneEdgeGood order'
        ⟨3 * k, by omega⟩ := by
  let n := 3 * k + 1
  let hn : 0 < n := by
    dsimp [n]
    omega
  let target : Fin n := ⟨3 * k - 1, by omega⟩
  obtain ⟨order', hOrder', hmap⟩ :=
    exists_shifted_cbo_with_start hn order hOrder i target
  have hmap0 :
      (order' target : α) = (order i : α) := by
    simpa [target, n, hn] using hmap 0
  have hmap1 :
      (order' (cyclicIndex n hn target 1) : α) =
        (order (cyclicIndex n hn i 1) : α) :=
    hmap 1
  have hmap2 :
      (order' (cyclicIndex n hn target 2) : α) =
        (order (cyclicIndex n hn i 2) : α) :=
    hmap 2

  have ht1 :
      cyclicIndex n hn target 1 = ⟨3 * k, by omega⟩ := by
    apply cyclicIndex_eq_mk_add_of_lt
    dsimp [target, n]
    omega
  have ht2 :
      cyclicIndex n hn target 2 = ⟨0, by omega⟩ := by
    apply Fin.ext
    simp [cyclicIndex, target, n]
    omega

  have hgoodEnd :
      DangerousHyperplaneEdgeGood order'
        ⟨3 * k - 1, by omega⟩ := by
    unfold DangerousHyperplaneEdgeGood at hgood0 ⊢
    rw [show (⟨3 * k - 1, by omega⟩ : Fin n) = target by rfl,
      ht1, hmap0]
    have hmap1' :
        (order' ⟨3 * k, by omega⟩ : α) =
          (order (cyclicIndex n hn i 1) : α) := by
      rw [← ht1]
      exact hmap1
    rw [hmap1']
    simpa [n, hn] using hgood0

  have hgoodWrap :
      DangerousHyperplaneEdgeGood order'
        ⟨3 * k, by omega⟩ := by
    unfold DangerousHyperplaneEdgeGood at hgood1 ⊢
    have hnext :
        cyclicIndex n hn (⟨3 * k, by omega⟩ : Fin n) 1 =
          ⟨0, by omega⟩ := by
      apply Fin.ext
      simp [cyclicIndex, n]
      omega
    rw [hnext]
    have hmap1' :
        (order' ⟨3 * k, by omega⟩ : α) =
          (order (cyclicIndex n hn i 1) : α) := by
      rw [← ht1]
      exact hmap1
    have hmap2' :
        (order' ⟨0, by omega⟩ : α) =
          (order (cyclicIndex n hn i 2) : α) := by
      rw [← ht2]
      exact hmap2
    rw [hmap1', hmap2']
    have hadd :
        cyclicIndex n hn
            (cyclicIndex n hn i 1) 1 =
          cyclicIndex n hn i 2 := by
      rw [cyclicIndex_add]
      norm_num
    simpa [n, hn, hadd] using hgood1

  exact ⟨order', hOrder', hgoodEnd, hgoodWrap⟩

/-- Rotate distance-two good edges so they become the core edges at
indices 0 and 2. -/
theorem exists_shifted_distance_two_good_at_start
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hk : 2 ≤ k)
    (order : Fin (3 * k + 1) ≃ (M.restrict H).E)
    (hOrder :
      CyclicBasisOrder (M.restrict H) 3 (by omega) order)
    (i : Fin (3 * k + 1))
    (hgood0 : DangerousHyperplaneEdgeGood order i)
    (hgood2 :
      DangerousHyperplaneEdgeGood order
        (cyclicIndex (3 * k + 1) (by omega) i 2)) :
    ∃ order' : Fin (3 * k + 1) ≃ (M.restrict H).E,
      CyclicBasisOrder (M.restrict H) 3 (by omega) order' ∧
      DangerousHyperplaneEdgeGood order' ⟨0, by omega⟩ ∧
      DangerousHyperplaneEdgeGood order' ⟨2, by omega⟩ := by
  let n := 3 * k + 1
  let hn : 0 < n := by
    dsimp [n]
    omega
  let target : Fin n := ⟨0, by omega⟩
  obtain ⟨order', hOrder', hmap⟩ :=
    exists_shifted_cbo_with_start hn order hOrder i target

  have hmap0 :
      (order' ⟨0, by omega⟩ : α) = (order i : α) := by
    simpa [target, n, hn] using hmap 0
  have hmap1 :
      (order' ⟨1, by omega⟩ : α) =
        (order (cyclicIndex n hn i 1) : α) := by
    have h := hmap 1
    have ht :
        cyclicIndex n hn target 1 = ⟨1, by omega⟩ := by
      apply cyclicIndex_eq_mk_add_of_lt
      dsimp [target, n]
      omega
    rw [ht] at h
    exact h
  have hmap2 :
      (order' ⟨2, by omega⟩ : α) =
        (order (cyclicIndex n hn i 2) : α) := by
    have h := hmap 2
    have ht :
        cyclicIndex n hn target 2 = ⟨2, by omega⟩ := by
      apply cyclicIndex_eq_mk_add_of_lt
      dsimp [target, n]
      omega
    rw [ht] at h
    exact h
  have hmap3 :
      (order' ⟨3, by omega⟩ : α) =
        (order (cyclicIndex n hn i 3) : α) := by
    have h := hmap 3
    have ht :
        cyclicIndex n hn target 3 = ⟨3, by omega⟩ := by
      apply cyclicIndex_eq_mk_add_of_lt
      dsimp [target, n]
      omega
    rw [ht] at h
    exact h

  have hgoodStart :
      DangerousHyperplaneEdgeGood order' ⟨0, by omega⟩ := by
    unfold DangerousHyperplaneEdgeGood at hgood0 ⊢
    have hnext :
        cyclicIndex n hn (⟨0, by omega⟩ : Fin n) 1 =
          ⟨1, by omega⟩ := by
      apply cyclicIndex_eq_mk_add_of_lt
      omega
    rw [hnext, hmap0, hmap1]
    simpa [n, hn] using hgood0

  have hgoodTwo :
      DangerousHyperplaneEdgeGood order' ⟨2, by omega⟩ := by
    unfold DangerousHyperplaneEdgeGood at hgood2 ⊢
    have hnext :
        cyclicIndex n hn (⟨2, by omega⟩ : Fin n) 1 =
          ⟨3, by omega⟩ := by
      apply cyclicIndex_eq_mk_add_of_lt
      omega
    rw [hnext, hmap2, hmap3]
    have hadd :
        cyclicIndex n hn
            (cyclicIndex n hn i 2) 1 =
          cyclicIndex n hn i 3 := by
      rw [cyclicIndex_add]
      norm_num
    simpa [n, hn, hadd] using hgood2

  exact ⟨order', hOrder', hgoodStart, hgoodTwo⟩

/-- The adjacent-good compressed schedule has a cyclic basis ordering.

The core order is normalized so the two good edges are
(g_(3k-1),g_(3k)) and (g_(3k),g_0). The common complement pair is placed at
the tail/wrap complement slots C_k,C_0. -/
theorem exists_cbo_of_adjacent_good_normalized
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hk : 2 ≤ k)
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hH : DangerousHyperplane M k H)
    (order : Fin (3 * k + 1) ≃ (M.restrict H).E)
    (hOrder :
      CyclicBasisOrder (M.restrict H) 3 (by omega) order)
    (hgoodEnd :
      DangerousHyperplaneEdgeGood order
        ⟨3 * k - 1, by omega⟩)
    (hgoodWrap :
      DangerousHyperplaneEdgeGood order
        ⟨3 * k, by omega⟩) :
    ∃ σ : Fin (4 * k + 2) ≃ M.E,
      CyclicBasisOrder M 4 (by omega) σ := by
  obtain ⟨cT, cW, hcne, hcT, hcW, hExcEnd, hExcWrap⟩ :=
    dangerous_hyperplane_adjacent_good_selection
      hk hE hRank hEcard hStrict hH order hOrder
      ⟨3 * k - 1, by omega⟩ hgoodEnd hgoodWrap

  let C : Set α := M.E \ H
  have hCfin : C.Finite := by
    dsimp [C]
    exact hE.sdiff
  have hCcard : C.ncard = k + 1 := by
    dsimp [C]
    exact dangerous_complement_ncard_eq hE hEcard hH
  let iT : Fin (k + 1) := ⟨k, by omega⟩
  let iW : Fin (k + 1) := ⟨0, by omega⟩
  have hiTW : iT ≠ iW := by
    intro h
    have hv := congrArg Fin.val h
    simp [iT, iW] at hv
    omega
  obtain ⟨eC, heT, heW⟩ :=
    FiniteSchedule.exists_fin_equiv_with_two_prescribed
      hCfin hCcard iT iW hiTW hcT hcW hcne

  let eG : Fin (3 * k + 1) ≃ (H : Set α) := by
    simpa using order
  let eSlots : FiniteSchedule.HyperplaneSlots k ≃
      (M.E \ H : Set α) ⊕ (H : Set α) :=
    Equiv.sumCongr eC eG
  let eGround := dangerous_hyperplane_parts_equiv_ground hH
  let σ : Fin (4 * k + 2) ≃ M.E :=
    (FiniteSchedule.hyperAdjacentIndexEquiv k (by omega)).trans
      (eSlots.trans eGround)

  have hCpos (j : Fin k) :
      (σ ⟨4 * j.val, by omega⟩ : α) =
        (eC ⟨j.val, by omega⟩ : α) := by
    change
      (eGround
        (eSlots
          (FiniteSchedule.hyperAdjacentIndexEquiv k (by omega)
            ⟨4 * j.val, by omega⟩)) : α) =
        (eC ⟨j.val, by omega⟩ : α)
    have hpos :
        (⟨4 * j.val, by omega⟩ : Fin (4 * k + 2)) =
          ⟨(0 : Fin 4).val + 4 * j.val, by omega⟩ := by
      apply Fin.ext
      simp
    rw [hpos, FiniteSchedule.hyperAdjacentIndexEquiv_block]
    exact dangerous_hyperplane_parts_equiv_ground_left hH _

  have hGpos (j : Fin k) (r : Fin 3) :
      (σ ⟨4 * j.val + 1 + r.val, by omega⟩ : α) =
        (order ⟨3 * j.val + r.val, by omega⟩ : α) := by
    change
      (eGround
        (eSlots
          (FiniteSchedule.hyperAdjacentIndexEquiv k (by omega)
            ⟨4 * j.val + 1 + r.val, by omega⟩)) : α) =
        (order ⟨3 * j.val + r.val, by omega⟩ : α)
    let s : Fin 4 := ⟨r.val + 1, by omega⟩
    have hpos :
        (⟨4 * j.val + 1 + r.val, by omega⟩ : Fin (4 * k + 2)) =
          ⟨s.val + 4 * j.val, by omega⟩ := by
      apply Fin.ext
      dsimp [s]
      omega
    rw [hpos, FiniteSchedule.hyperAdjacentIndexEquiv_block]
    fin_cases r <;>
      simp [s, FiniteSchedule.hyperAdjacentBlockSlot, eSlots, eG,
        eGround, dangerous_hyperplane_parts_equiv_ground]

  have hTailC :
      (σ ⟨4 * k, by omega⟩ : α) = cT := by
    change
      (eGround
        (eSlots
          (FiniteSchedule.hyperAdjacentIndexEquiv k (by omega)
            ⟨4 * k, by omega⟩)) : α) = cT
    have hpos :
        (⟨4 * k, by omega⟩ : Fin (4 * k + 2)) =
          ⟨4 * k + (0 : Fin 2).val, by omega⟩ := by
      apply Fin.ext
      simp
    rw [hpos, FiniteSchedule.hyperAdjacentIndexEquiv_tail]
    change (eGround (Sum.inl (eC iT)) : α) = cT
    rw [dangerous_hyperplane_parts_equiv_ground_left, heT]

  have hTailG :
      (σ ⟨4 * k + 1, by omega⟩ : α) =
        (order ⟨3 * k, by omega⟩ : α) := by
    change
      (eGround
        (eSlots
          (FiniteSchedule.hyperAdjacentIndexEquiv k (by omega)
            ⟨4 * k + 1, by omega⟩)) : α) =
        (order ⟨3 * k, by omega⟩ : α)
    rw [show
      (⟨4 * k + 1, by omega⟩ : Fin (4 * k + 2)) =
        ⟨4 * k + (1 : Fin 2).val, by omega⟩ by
          apply Fin.ext
          simp,
      FiniteSchedule.hyperAdjacentIndexEquiv_tail]
    change (eGround (Sum.inr (eG ⟨3 * k, by omega⟩)) : α) =
      (order ⟨3 * k, by omega⟩ : α)
    simp [eG, eGround, dangerous_hyperplane_parts_equiv_ground]

  have hWrapC :
      (σ ⟨0, by omega⟩ : α) = cW := by
    have h := hCpos (⟨0, by omega⟩ : Fin k)
    calc
      (σ ⟨0, by omega⟩ : α) =
          (eC ⟨0, by omega⟩ : α) := by simpa using h
      _ = cW := by simpa [iW] using heW

  have hCstream (m : Fin (k + 1)) :
      (σ ⟨4 * m.val, by omega⟩ : α) = (eC m : α) := by
    by_cases hm : m.val < k
    · let j : Fin k := ⟨m.val, hm⟩
      have h := hCpos j
      have hEq :
          (⟨4 * m.val, by omega⟩ : Fin (4 * k + 2)) =
            ⟨4 * j.val, by omega⟩ := by
        apply Fin.ext
        rfl
      rw [hEq]
      simpa [j] using h
    · have hmEq : m.val = k := by omega
      have hEq :
          (⟨4 * m.val, by omega⟩ : Fin (4 * k + 2)) =
            ⟨4 * k, by omega⟩ := by
        apply Fin.ext
        omega
      rw [hEq, hTailC]
      have hmIT : m = iT := by
        apply Fin.ext
        simpa [iT] using hmEq
      subst m
      exact heT.symm

  have hGnext0 (j : Fin k) :
      (σ ⟨4 * j.val + 5, by omega⟩ : α) =
        (order ⟨3 * j.val + 3, by omega⟩ : α) := by
    by_cases hj : j.val + 1 < k
    · let jn : Fin k := ⟨j.val + 1, hj⟩
      have h := hGpos jn (0 : Fin 3)
      have hEq :
          (⟨4 * j.val + 5, by omega⟩ : Fin (4 * k + 2)) =
            ⟨4 * jn.val + 1, by omega⟩ := by
        apply Fin.ext
        dsimp [jn]
        omega
      rw [hEq]
      simpa [jn] using h
    · have hjEq : j.val = k - 1 := by omega
      have hEq :
          (⟨4 * j.val + 5, by omega⟩ : Fin (4 * k + 2)) =
            ⟨4 * k + 1, by omega⟩ := by
        apply Fin.ext
        omega
      rw [hEq, hTailG]
      congr 2
      apply Fin.ext
      omega

  have hOrdinaryCoreTriple (q : Fin (3 * k + 1)) :
      M.IsBasis
        ({(order q : α),
          (order (cyclicIndex (3 * k + 1) (by omega) q 1) : α),
          (order (cyclicIndex (3 * k + 1) (by omega) q 2) : α)} : Set α)
        H :=
    dangerous_hyperplane_core_triple_isBasis hH order hOrder q

  have hOneCThreeG
      (c : α) (hc : c ∈ M.E \ H)
      (q : Fin (3 * k + 1)) :
      M.IsBase
        ({c,
          (order q : α),
          (order (cyclicIndex (3 * k + 1) (by omega) q 1) : α),
          (order (cyclicIndex (3 * k + 1) (by omega) q 2) : α)} : Set α) := by
    have h :=
      dangerous_one_hyperplane_basis_plus_complement_isBase
        hRank hH (hOrdinaryCoreTriple q) hc
    convert h using 1
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto

  refine ⟨σ, (cyclicBasisOrder_four_iff (by omega) σ).2 ?_⟩
  intro s
  by_cases hEnd : s.val = 4 * k - 1
  · have hs : s = ⟨4 * k - 1, by omega⟩ := Fin.ext hEnd
    subst s
    have h1 :
        cyclicIndex (4 * k + 2) (by omega)
          ⟨4 * k - 1, by omega⟩ 1 = ⟨4 * k, by omega⟩ := by
      apply cyclicIndex_eq_mk_add_of_lt
      omega
    have h2 :
        cyclicIndex (4 * k + 2) (by omega)
          ⟨4 * k - 1, by omega⟩ 2 = ⟨4 * k + 1, by omega⟩ := by
      apply cyclicIndex_eq_mk_add_of_lt
      omega
    have h3 :
        cyclicIndex (4 * k + 2) (by omega)
          ⟨4 * k - 1, by omega⟩ 3 = ⟨0, by omega⟩ := by
      apply Fin.ext
      simp [cyclicIndex]
      omega
    have hGend :
        (σ ⟨4 * k - 1, by omega⟩ : α) =
          (order ⟨3 * k - 1, by omega⟩ : α) := by
      let j : Fin k := ⟨k - 1, by omega⟩
      have h := hGpos j (2 : Fin 3)
      simpa [j] using h
    rw [h1, h2, h3, hGend, hTailC, hTailG, hWrapC]
    convert hExcEnd using 1
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_union]
    tauto

  by_cases hWrap : s.val = 4 * k
  · have hs : s = ⟨4 * k, by omega⟩ := Fin.ext hWrap
    subst s
    have h1 :
        cyclicIndex (4 * k + 2) (by omega)
          ⟨4 * k, by omega⟩ 1 = ⟨4 * k + 1, by omega⟩ := by
      apply cyclicIndex_eq_mk_add_of_lt
      omega
    have h2 :
        cyclicIndex (4 * k + 2) (by omega)
          ⟨4 * k, by omega⟩ 2 = ⟨0, by omega⟩ := by
      apply Fin.ext
      simp [cyclicIndex]
      omega
    have h3 :
        cyclicIndex (4 * k + 2) (by omega)
          ⟨4 * k, by omega⟩ 3 = ⟨1, by omega⟩ := by
      apply Fin.ext
      simp [cyclicIndex]
      omega
    have hG0 :
        (σ ⟨1, by omega⟩ : α) = (order ⟨0, by omega⟩ : α) := by
      have h := hGpos (⟨0, by omega⟩ : Fin k) (0 : Fin 3)
      simpa using h
    rw [h1, h2, h3, hTailC, hTailG, hWrapC, hG0]
    convert hExcWrap using 1
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_union]
    tauto

  by_cases hLast : s.val = 4 * k + 1
  · have hs : s = ⟨4 * k + 1, by omega⟩ := Fin.ext hLast
    subst s
    have h1 :
        cyclicIndex (4 * k + 2) (by omega)
          ⟨4 * k + 1, by omega⟩ 1 = ⟨0, by omega⟩ := by
      apply Fin.ext
      simp [cyclicIndex]
    have h2 :
        cyclicIndex (4 * k + 2) (by omega)
          ⟨4 * k + 1, by omega⟩ 2 = ⟨1, by omega⟩ := by
      apply Fin.ext
      simp [cyclicIndex]
    have h3 :
        cyclicIndex (4 * k + 2) (by omega)
          ⟨4 * k + 1, by omega⟩ 3 = ⟨2, by omega⟩ := by
      apply Fin.ext
      simp [cyclicIndex]
    have hG0 :
        (σ ⟨1, by omega⟩ : α) = (order ⟨0, by omega⟩ : α) := by
      have h := hGpos (⟨0, by omega⟩ : Fin k) (0 : Fin 3)
      simpa using h
    have hG1 :
        (σ ⟨2, by omega⟩ : α) = (order ⟨1, by omega⟩ : α) := by
      have h := hGpos (⟨0, by omega⟩ : Fin k) (1 : Fin 3)
      simpa using h
    rw [h1, h2, h3, hTailG, hWrapC, hG0, hG1]
    have hbase :=
      hOneCThreeG cW hcW ⟨3 * k, by omega⟩
    convert hbase using 1
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    have hnext1 :
        cyclicIndex (3 * k + 1) (by omega)
          (⟨3 * k, by omega⟩ : Fin (3 * k + 1)) 1 =
          ⟨0, by omega⟩ := by
      apply Fin.ext
      simp [cyclicIndex]
    have hnext2 :
        cyclicIndex (3 * k + 1) (by omega)
          (⟨3 * k, by omega⟩ : Fin (3 * k + 1)) 2 =
          ⟨1, by omega⟩ := by
      apply Fin.ext
      simp [cyclicIndex]
    rw [hnext1, hnext2]
    tauto

  have hslt : s.val < 4 * k - 1 := by
    have hsmax := s.isLt
    omega
  let j : Fin k := ⟨s.val / 4, by omega⟩
  have hrem : s.val % 4 < 4 := Nat.mod_lt _ (by omega)
  interval_cases hr : s.val % 4
  · have hsval : s.val = 4 * j.val := by
      dsimp [j]
      have hm := Nat.mod_add_div s.val 4
      omega
    have hsEq : s = ⟨4 * j.val, by omega⟩ := Fin.ext hsval
    subst s
    have hc := (eC ⟨j.val, by omega⟩).property
    have h1 :
        cyclicIndex (4 * k + 2) (by omega)
          ⟨4 * j.val, by omega⟩ 1 =
          ⟨4 * j.val + 1, by omega⟩ := by
      apply cyclicIndex_eq_mk_add_of_lt
      omega
    have h2 :
        cyclicIndex (4 * k + 2) (by omega)
          ⟨4 * j.val, by omega⟩ 2 =
          ⟨4 * j.val + 2, by omega⟩ := by
      apply cyclicIndex_eq_mk_add_of_lt
      omega
    have h3 :
        cyclicIndex (4 * k + 2) (by omega)
          ⟨4 * j.val, by omega⟩ 3 =
          ⟨4 * j.val + 3, by omega⟩ := by
      apply cyclicIndex_eq_mk_add_of_lt
      omega
    have hg0 := hGpos j (0 : Fin 3)
    have hg1 := hGpos j (1 : Fin 3)
    have hg2 := hGpos j (2 : Fin 3)
    rw [h1, h2, h3, hCpos j, hg0, hg1, hg2]
    let q : Fin (3 * k + 1) := ⟨3 * j.val, by omega⟩
    have hq1 :
        cyclicIndex (3 * k + 1) (by omega) q 1 =
          ⟨3 * j.val + 1, by omega⟩ := by
      apply cyclicIndex_eq_mk_add_of_lt
      omega
    have hq2 :
        cyclicIndex (3 * k + 1) (by omega) q 2 =
          ⟨3 * j.val + 2, by omega⟩ := by
      apply cyclicIndex_eq_mk_add_of_lt
      omega
    have hbase :=
      hOneCThreeG (eC ⟨j.val, by omega⟩ : α)
        (by simpa [C] using hc) q
    rw [hq1, hq2] at hbase
    simpa [q] using hbase

  · have hsval : s.val = 4 * j.val + 1 := by
      dsimp [j]
      have hm := Nat.mod_add_div s.val 4
      omega
    have hsEq : s = ⟨4 * j.val + 1, by omega⟩ := Fin.ext hsval
    subst s
    let m : Fin (k + 1) := ⟨j.val + 1, by omega⟩
    have hc := (eC m).property
    have h1 :
        cyclicIndex (4 * k + 2) (by omega)
          ⟨4 * j.val + 1, by omega⟩ 1 =
          ⟨4 * j.val + 2, by omega⟩ := by
      apply cyclicIndex_eq_mk_add_of_lt
      omega
    have h2 :
        cyclicIndex (4 * k + 2) (by omega)
          ⟨4 * j.val + 1, by omega⟩ 2 =
          ⟨4 * j.val + 3, by omega⟩ := by
      apply cyclicIndex_eq_mk_add_of_lt
      omega
    have h3 :
        cyclicIndex (4 * k + 2) (by omega)
          ⟨4 * j.val + 1, by omega⟩ 3 =
          ⟨4 * (j.val + 1), by omega⟩ := by
      apply Fin.ext
      have h := cyclicIndex_eq_mk_add_of_lt
        (4 * k + 2) (by omega)
        (⟨4 * j.val + 1, by omega⟩ : Fin (4 * k + 2)) 3
        (by omega)
      rw [h]
      omega
    have hg0 := hGpos j (0 : Fin 3)
    have hg1 := hGpos j (1 : Fin 3)
    have hg2 := hGpos j (2 : Fin 3)
    have hcEval := hCstream m
    rw [h1, h2, h3, hg0, hg1, hg2, hcEval]
    let q : Fin (3 * k + 1) := ⟨3 * j.val, by omega⟩
    have hq1 :
        cyclicIndex (3 * k + 1) (by omega) q 1 =
          ⟨3 * j.val + 1, by omega⟩ := by
      apply cyclicIndex_eq_mk_add_of_lt
      omega
    have hq2 :
        cyclicIndex (3 * k + 1) (by omega) q 2 =
          ⟨3 * j.val + 2, by omega⟩ := by
      apply cyclicIndex_eq_mk_add_of_lt
      omega
    have hbase :=
      hOneCThreeG (eC m : α) (by simpa [C] using hc) q
    rw [hq1, hq2] at hbase
    convert hbase using 1
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto

  · have hsval : s.val = 4 * j.val + 2 := by
      dsimp [j]
      have hm := Nat.mod_add_div s.val 4
      omega
    have hsEq : s = ⟨4 * j.val + 2, by omega⟩ := Fin.ext hsval
    subst s
    let m : Fin (k + 1) := ⟨j.val + 1, by omega⟩
    have hc := (eC m).property
    have h1 :
        cyclicIndex (4 * k + 2) (by omega)
          ⟨4 * j.val + 2, by omega⟩ 1 =
          ⟨4 * j.val + 3, by omega⟩ := by
      apply cyclicIndex_eq_mk_add_of_lt
      omega
    have h2 :
        cyclicIndex (4 * k + 2) (by omega)
          ⟨4 * j.val + 2, by omega⟩ 2 =
          ⟨4 * (j.val + 1), by omega⟩ := by
      apply Fin.ext
      have h := cyclicIndex_eq_mk_add_of_lt
        (4 * k + 2) (by omega)
        (⟨4 * j.val + 2, by omega⟩ : Fin (4 * k + 2)) 2
        (by omega)
      rw [h]
      omega
    have h3 :
        cyclicIndex (4 * k + 2) (by omega)
          ⟨4 * j.val + 2, by omega⟩ 3 =
          ⟨4 * j.val + 5, by omega⟩ := by
      apply cyclicIndex_eq_mk_add_of_lt
      omega
    have hg1 := hGpos j (1 : Fin 3)
    have hg2 := hGpos j (2 : Fin 3)
    have hcEval := hCstream m
    have hg3 := hGnext0 j
    rw [h1, h2, h3, hg1, hg2, hcEval, hg3]
    let q : Fin (3 * k + 1) := ⟨3 * j.val + 1, by omega⟩
    have hq1 :
        cyclicIndex (3 * k + 1) (by omega) q 1 =
          ⟨3 * j.val + 2, by omega⟩ := by
      apply cyclicIndex_eq_mk_add_of_lt
      omega
    have hq2 :
        cyclicIndex (3 * k + 1) (by omega) q 2 =
          ⟨3 * j.val + 3, by omega⟩ := by
      apply cyclicIndex_eq_mk_add_of_lt
      omega
    have hbase :=
      hOneCThreeG (eC m : α) (by simpa [C] using hc) q
    rw [hq1, hq2] at hbase
    convert hbase using 1
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto

  · have hsval : s.val = 4 * j.val + 3 := by
      dsimp [j]
      have hm := Nat.mod_add_div s.val 4
      omega
    have hsEq : s = ⟨4 * j.val + 3, by omega⟩ := Fin.ext hsval
    subst s
    have hjNext : j.val + 1 < k := by
      omega
    let jn : Fin k := ⟨j.val + 1, hjNext⟩
    let m : Fin (k + 1) := ⟨j.val + 1, by omega⟩
    have hc := (eC m).property
    have h1 :
        cyclicIndex (4 * k + 2) (by omega)
          ⟨4 * j.val + 3, by omega⟩ 1 =
          ⟨4 * (j.val + 1), by omega⟩ := by
      apply Fin.ext
      have h := cyclicIndex_eq_mk_add_of_lt
        (4 * k + 2) (by omega)
        (⟨4 * j.val + 3, by omega⟩ : Fin (4 * k + 2)) 1
        (by omega)
      rw [h]
      omega
    have h2 :
        cyclicIndex (4 * k + 2) (by omega)
          ⟨4 * j.val + 3, by omega⟩ 2 =
          ⟨4 * j.val + 5, by omega⟩ := by
      apply cyclicIndex_eq_mk_add_of_lt
      omega
    have h3 :
        cyclicIndex (4 * k + 2) (by omega)
          ⟨4 * j.val + 3, by omega⟩ 3 =
          ⟨4 * j.val + 6, by omega⟩ := by
      apply cyclicIndex_eq_mk_add_of_lt
      omega
    have hg2 := hGpos j (2 : Fin 3)
    have hcEval := hCstream m
    have hg3 := hGpos jn (0 : Fin 3)
    have hg4 := hGpos jn (1 : Fin 3)
    rw [h1, h2, h3, hg2, hcEval]
    have hEq2 :
        (⟨4 * j.val + 5, by omega⟩ : Fin (4 * k + 2)) =
          ⟨4 * jn.val + 1, by omega⟩ := by
      apply Fin.ext
      dsimp [jn]
      omega
    have hEq3 :
        (⟨4 * j.val + 6, by omega⟩ : Fin (4 * k + 2)) =
          ⟨4 * jn.val + 2, by omega⟩ := by
      apply Fin.ext
      dsimp [jn]
      omega
    rw [hEq2, hEq3, hg3, hg4]
    let q : Fin (3 * k + 1) := ⟨3 * j.val + 2, by omega⟩
    have hq1 :
        cyclicIndex (3 * k + 1) (by omega) q 1 =
          ⟨3 * j.val + 3, by omega⟩ := by
      apply cyclicIndex_eq_mk_add_of_lt
      omega
    have hq2 :
        cyclicIndex (3 * k + 1) (by omega) q 2 =
          ⟨3 * j.val + 4, by omega⟩ := by
      apply cyclicIndex_eq_mk_add_of_lt
      omega
    have hbase :=
      hOneCThreeG (eC m : α) (by simpa [C] using hc) q
    rw [hq1, hq2] at hbase
    convert hbase using 1
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto


/-- The distance-two-good compressed schedule has a cyclic basis ordering.

The normalized good core edges are 0 and 2.  The complementary path
c₀-c₁-c₂ is placed in complement slots 0,1,2 of the schedule
C G G C G G (C G G G)^(k-1).  Starts 0 and 3 are the only exceptional
windows; every other window is ordinary. -/
theorem exists_cbo_of_distance_two_good_normalized
    {M : Matroid α} {k : ℕ} {H : Set α}
    (hk : 2 ≤ k)
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hH : DangerousHyperplane M k H)
    (order : Fin (3 * k + 1) ≃ (M.restrict H).E)
    (hOrder :
      CyclicBasisOrder (M.restrict H) 3 (by omega) order)
    (hgood0 :
      DangerousHyperplaneEdgeGood order ⟨0, by omega⟩)
    (hgood2 :
      DangerousHyperplaneEdgeGood order ⟨2, by omega⟩) :
    ∃ σ : Fin (4 * k + 2) ≃ M.E,
      CyclicBasisOrder M 4 (by omega) σ := by
  have hidx2 :
      cyclicIndex (3 * k + 1) (by omega)
          (⟨0, by omega⟩ : Fin (3 * k + 1)) 2 =
        ⟨2, by omega⟩ := by
    apply cyclicIndex_eq_mk_add_of_lt
    omega
  obtain ⟨c₀, c₁, c₂, hc01, hc12, hc02,
      hc₀, hc₁, hc₂, hExc0, hExc2⟩ :=
    dangerous_hyperplane_distance_two_good_selection
      hk hE hRank hEcard hStrict hH order hOrder
      ⟨0, by omega⟩ hgood0 (by simpa [hidx2] using hgood2)

  let C : Set α := M.E \ H
  have hCfin : C.Finite := by
    dsimp [C]
    exact hE.sdiff
  have hCcard : C.ncard = k + 1 := by
    dsimp [C]
    exact dangerous_complement_ncard_eq hE hEcard hH

  let i0 : Fin (k + 1) := ⟨0, by omega⟩
  let i1 : Fin (k + 1) := ⟨1, by omega⟩
  let i2 : Fin (k + 1) := ⟨2, by omega⟩
  have hi01 : i0 ≠ i1 := by
    intro h
    have := congrArg Fin.val h
    simp [i0, i1] at this
  have hi02 : i0 ≠ i2 := by
    intro h
    have := congrArg Fin.val h
    simp [i0, i2] at this
  have hi12 : i1 ≠ i2 := by
    intro h
    have := congrArg Fin.val h
    simp [i1, i2] at this

  obtain ⟨eC, he0, he1, he2⟩ :=
    FiniteSchedule.exists_fin_equiv_with_three_at_positions
      hCfin hCcard i0 i1 i2 hi01 hi02 hi12
      hc₀ hc₁ hc₂ hc01 hc02 hc12

  let σ : Fin (4 * k + 2) ≃ M.E :=
    dangerousSeparatedScheduleOrder hk hH eC order

  have hs0 : (σ ⟨0, by omega⟩ : α) = c₀ := by
    change
      (dangerousSeparatedScheduleOrder hk hH eC order
        ⟨0, by omega⟩ : α) = c₀
    rw [dangerousSeparatedScheduleOrder_head0]
    simpa [i0] using he0
  have hs1 :
      (σ ⟨1, by omega⟩ : α) = (order ⟨0, by omega⟩ : α) := by
    change
      (dangerousSeparatedScheduleOrder hk hH eC order
        ⟨1, by omega⟩ : α) = (order ⟨0, by omega⟩ : α)
    exact dangerousSeparatedScheduleOrder_head1 hk hH eC order
  have hs2 :
      (σ ⟨2, by omega⟩ : α) = (order ⟨1, by omega⟩ : α) := by
    change
      (dangerousSeparatedScheduleOrder hk hH eC order
        ⟨2, by omega⟩ : α) = (order ⟨1, by omega⟩ : α)
    exact dangerousSeparatedScheduleOrder_head2 hk hH eC order
  have hs3 : (σ ⟨3, by omega⟩ : α) = c₁ := by
    change
      (dangerousSeparatedScheduleOrder hk hH eC order
        ⟨3, by omega⟩ : α) = c₁
    rw [dangerousSeparatedScheduleOrder_head3]
    simpa [i1] using he1
  have hs4 :
      (σ ⟨4, by omega⟩ : α) = (order ⟨2, by omega⟩ : α) := by
    change
      (dangerousSeparatedScheduleOrder hk hH eC order
        ⟨4, by omega⟩ : α) = (order ⟨2, by omega⟩ : α)
    exact dangerousSeparatedScheduleOrder_head4 hk hH eC order
  have hs5 :
      (σ ⟨5, by omega⟩ : α) = (order ⟨3, by omega⟩ : α) := by
    change
      (dangerousSeparatedScheduleOrder hk hH eC order
        ⟨5, by omega⟩ : α) = (order ⟨3, by omega⟩ : α)
    exact dangerousSeparatedScheduleOrder_head5 hk hH eC order
  have hs6 : (σ ⟨6, by omega⟩ : α) = c₂ := by
    change
      (dangerousSeparatedScheduleOrder hk hH eC order
        ⟨6, by omega⟩ : α) = c₂
    have h :=
      dangerousSeparatedScheduleOrder_blockC
        hk hH eC order (⟨0, by omega⟩ : Fin (k - 1))
    rw [show
      (⟨6, by omega⟩ : Fin (4 * k + 2)) =
        ⟨6 + 4 * (0 : Fin (k - 1)).val, by omega⟩ by
          apply Fin.ext
          simp]
    rw [h]
    simpa [i2] using he2

  refine ⟨σ, (cyclicBasisOrder_four_iff (by omega) σ).2 ?_⟩
  intro s
  by_cases h0 : s.val = 0
  · have hs : s = ⟨0, by omega⟩ := Fin.ext h0
    subst s
    have h1 :
        cyclicIndex (4 * k + 2) (by omega)
          (⟨0, by omega⟩ : Fin (4 * k + 2)) 1 =
          ⟨1, by omega⟩ := by
      apply cyclicIndex_eq_mk_add_of_lt
      omega
    have h2 :
        cyclicIndex (4 * k + 2) (by omega)
          (⟨0, by omega⟩ : Fin (4 * k + 2)) 2 =
          ⟨2, by omega⟩ := by
      apply cyclicIndex_eq_mk_add_of_lt
      omega
    have h3 :
        cyclicIndex (4 * k + 2) (by omega)
          (⟨0, by omega⟩ : Fin (4 * k + 2)) 3 =
          ⟨3, by omega⟩ := by
      apply cyclicIndex_eq_mk_add_of_lt
      omega
    rw [h1, h2, h3, hs0, hs1, hs2, hs3]
    have hP :
        cyclicIndex (3 * k + 1) (by omega)
            (⟨0, by omega⟩ : Fin (3 * k + 1)) 1 =
          ⟨1, by omega⟩ := by
      apply cyclicIndex_eq_mk_add_of_lt
      omega
    dsimp only at hExc0
    rw [hP] at hExc0
    convert hExc0 using 1
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    tauto

  by_cases h3s : s.val = 3
  · have hs : s = ⟨3, by omega⟩ := Fin.ext h3s
    subst s
    have h1 :
        cyclicIndex (4 * k + 2) (by omega)
          (⟨3, by omega⟩ : Fin (4 * k + 2)) 1 =
          ⟨4, by omega⟩ := by
      apply cyclicIndex_eq_mk_add_of_lt
      omega
    have h2 :
        cyclicIndex (4 * k + 2) (by omega)
          (⟨3, by omega⟩ : Fin (4 * k + 2)) 2 =
          ⟨5, by omega⟩ := by
      apply cyclicIndex_eq_mk_add_of_lt
      omega
    have h3 :
        cyclicIndex (4 * k + 2) (by omega)
          (⟨3, by omega⟩ : Fin (4 * k + 2)) 3 =
          ⟨6, by omega⟩ := by
      apply cyclicIndex_eq_mk_add_of_lt
      omega
    rw [h1, h2, h3, hs3, hs4, hs5, hs6]
    have hP :
        cyclicIndex (3 * k + 1) (by omega)
            (⟨2, by omega⟩ : Fin (3 * k + 1)) 1 =
          ⟨3, by omega⟩ := by
      apply cyclicIndex_eq_mk_add_of_lt
      omega
    dsimp only at hExc2
    rw [hP] at hExc2
    convert hExc2 using 1
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    tauto

  obtain ⟨m, q, hclass⟩ :=
    dangerousSeparatedSchedule_window_classification
      hk hH eC order s h0 h3s
  have hbase :=
    dangerous_hyperplane_complement_plus_core_triple_isBase
      hRank hH order hOrder (eC m).property q
  rw [hclass]
  exact hbase


/-- Unified dangerous-hyperplane theorem.

For strict rank four on 4k+2 elements with k >= 2, the existence of even one
dangerous hyperplane implies a cyclic basis ordering, assuming a full
rank-three KUM solver.  No count or uniqueness hypothesis on dangerous
hyperplanes is needed. -/
theorem exists_cbo_of_dangerous_hyperplane
    {M : Matroid α} {k : ℕ}
    (hSolve3 : SolvesKUMAtRank α 3)
    (hk : 2 ≤ k)
    (hE : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hEcard : M.E.encard = ((4 * k + 2 : ℕ) : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    {H : Set α}
    (hH : DangerousHyperplane M k H) :
    ∃ σ : Fin (4 * k + 2) ≃ M.E,
      CyclicBasisOrder M 4 (by omega) σ := by
  obtain ⟨order, hOrder⟩ :=
    exists_hyperplane_cbo_of_one_dangerous
      hSolve3 hE hRank hStrict hH

  obtain ⟨i, hconfig⟩ :=
    dangerous_hyperplane_exists_good_edge_configuration
      hk hE hRank hEcard hStrict hH order hOrder

  rcases hconfig with hAdj | hTwo
  · obtain ⟨order', hOrder', hgoodEnd, hgoodWrap⟩ :=
      exists_shifted_adjacent_good_at_end
        hk order hOrder i hAdj.1 hAdj.2
    exact exists_cbo_of_adjacent_good_normalized
      hk hE hRank hEcard hStrict hH
      order' hOrder' hgoodEnd hgoodWrap

  · obtain ⟨order', hOrder', hgood0, hgood2⟩ :=
      exists_shifted_distance_two_good_at_start
        hk order hOrder i hTwo.1 hTwo.2
    exact exists_cbo_of_distance_two_good_normalized
      hk hE hRank hEcard hStrict hH
      order' hOrder' hgood0 hgood2

end

end Rank4DangerousBranches
end HigherRankKUM
