import HigherRankKUM.Rank4.DangerousBranchT1Geometry
import HigherRankKUM.Rank4.DangerousBranchFactors
import HigherRankKUM.Rank4.CyclicPigeonhole
import HigherRankKUM.Rank4.CyclicWindowFour
import Mathlib.Tactic

namespace HigherRankKUM
namespace Rank4DangerousBranches

open Set
open scoped Matroid

noncomputable section

variable {α : Type*}

/-- Pure rank form of the key dangerous-hyperplane observation.

Let C have rank 2, 3, or 4 in a rank-four matroid. If adjoining each of the
overlapping triples {a,b,c} and {b,c,d} to C has full rank four, then at
least one of the three overlapping pairs {a,b}, {b,c}, {c,d} already raises
C to full rank four.

For a cyclic basis order of a dangerous hyperplane, this says that three
consecutive bad edges are impossible. -/
theorem one_of_three_pair_extensions_has_rank_four
    {M : Matroid α} {C : Set α} {a b c d : α}
    (hRank : M.eRank = (4 : ℕ∞))
    (hC :
      M.eRk C = (2 : ℕ∞) ∨
      M.eRk C = (3 : ℕ∞) ∨
      M.eRk C = (4 : ℕ∞))
    (hABC : M.eRk (C ∪ ({a, b, c} : Set α)) = (4 : ℕ∞))
    (hBCD : M.eRk (C ∪ ({b, c, d} : Set α)) = (4 : ℕ∞)) :
    M.eRk (C ∪ ({a, b} : Set α)) = (4 : ℕ∞) ∨
    M.eRk (C ∪ ({b, c} : Set α)) = (4 : ℕ∞) ∨
    M.eRk (C ∪ ({c, d} : Set α)) = (4 : ℕ∞) := by
  let X : Set α := C ∪ ({a, b} : Set α)
  let Y : Set α := C ∪ ({b, c} : Set α)
  let Z : Set α := C ∪ ({c, d} : Set α)

  have hupper (S : Set α) : M.eRk S ≤ (4 : ℕ∞) := by
    rw [← hRank]
    exact M.eRk_le_eRank S

  have rank_nat_le_four (S : Set α) :
      ∃ r : ℕ, M.eRk S = (r : ℕ∞) ∧ r ≤ 4 := by
    obtain ⟨r, hr, hrle⟩ := ENat.le_natCast_iff.mp (hupper S)
    refine ⟨r, hr, ?_⟩
    exact_mod_cast hrle

  have rank_nat_le_three_of_ne_four
      (S : Set α) (hne : M.eRk S ≠ (4 : ℕ∞)) :
      ∃ r : ℕ, M.eRk S = (r : ℕ∞) ∧ r ≤ 3 := by
    obtain ⟨r, hr, hrle⟩ := rank_nat_le_four S
    refine ⟨r, hr, ?_⟩
    by_contra h
    have hr4 : r = 4 := by omega
    apply hne
    simpa [hr, hr4]

  rcases hC with hC2 | hC3 | hC4
  · by_contra hgood
    push_neg at hgood
    have hXbad : M.eRk X ≠ (4 : ℕ∞) := by
      simpa [X] using hgood.1
    have hYbad : M.eRk Y ≠ (4 : ℕ∞) := by
      simpa [Y] using hgood.2.1
    have hZbad : M.eRk Z ≠ (4 : ℕ∞) := by
      simpa [Z] using hgood.2.2

    obtain ⟨rx, hXr, hrx3⟩ :=
      rank_nat_le_three_of_ne_four X hXbad
    obtain ⟨ry, hYr, hry3⟩ :=
      rank_nat_le_three_of_ne_four Y hYbad
    obtain ⟨rz, hZr, hrz3⟩ :=
      rank_nat_le_three_of_ne_four Z hZbad

    have hXYunion : X ∪ Y = C ∪ ({a, b, c} : Set α) := by
      ext x
      simp [X, Y]
      tauto
    have hYZunion : Y ∪ Z = C ∪ ({b, c, d} : Set α) := by
      ext x
      simp [Y, Z]
      tauto
    have hCXY : C ⊆ X ∩ Y := by
      intro x hx
      exact ⟨Or.inl hx, Or.inl hx⟩
    have hCYZ : C ⊆ Y ∩ Z := by
      intro x hx
      exact ⟨Or.inl hx, Or.inl hx⟩

    obtain ⟨rxy, hXYr, hrxy4⟩ := rank_nat_le_four (X ∩ Y)
    obtain ⟨ryz, hYZr, hryz4⟩ := rank_nat_le_four (Y ∩ Z)
    have hxyLower := M.eRk_mono hCXY
    have hyzLower := M.eRk_mono hCYZ
    rw [hC2, hXYr] at hxyLower
    rw [hC2, hYZr] at hyzLower
    have hxyLowerNat : 2 ≤ rxy := by exact_mod_cast hxyLower
    have hyzLowerNat : 2 ≤ ryz := by exact_mod_cast hyzLower

    have hsubXY := M.eRk_inter_add_eRk_union_le X Y
    rw [hXYr, hXYunion, hABC, hXr, hYr] at hsubXY
    have hsubXYNat : rxy + 4 ≤ rx + ry := by exact_mod_cast hsubXY
    have hrx : rx = 3 := by omega
    have hry : ry = 3 := by omega
    have hrxy : rxy = 2 := by omega

    have hsubYZ := M.eRk_inter_add_eRk_union_le Y Z
    rw [hYZr, hYZunion, hBCD, hYr, hZr] at hsubYZ
    have hsubYZNat : ryz + 4 ≤ ry + rz := by exact_mod_cast hsubYZ
    have hrz : rz = 3 := by omega
    have hryz : ryz = 2 := by omega

    let B : Set α := C ∪ ({b} : Set α)
    let D : Set α := C ∪ ({c} : Set α)
    have hBXY : B ⊆ X ∩ Y := by
      intro x hx
      rcases hx with hxC | hxb
      · exact ⟨Or.inl hxC, Or.inl hxC⟩
      · have : x = b := by simpa [B] using hxb
        subst x
        simp [X, Y]
    have hDYZ : D ⊆ Y ∩ Z := by
      intro x hx
      rcases hx with hxC | hxc
      · exact ⟨Or.inl hxC, Or.inl hxC⟩
      · have : x = c := by simpa [D] using hxc
        subst x
        simp [Y, Z]
    have hCB : C ⊆ B := by
      intro x hx
      exact Or.inl hx
    have hCD : C ⊆ D := by
      intro x hx
      exact Or.inl hx

    have hB_le : M.eRk B ≤ (2 : ℕ∞) := by
      calc
        M.eRk B ≤ M.eRk (X ∩ Y) := M.eRk_mono hBXY
        _ = (2 : ℕ∞) := by rw [hXYr, hrxy]
    have hB_ge : (2 : ℕ∞) ≤ M.eRk B := by
      rw [← hC2]
      exact M.eRk_mono hCB
    have hBrank : M.eRk B = (2 : ℕ∞) :=
      le_antisymm hB_le hB_ge

    have hD_le : M.eRk D ≤ (2 : ℕ∞) := by
      calc
        M.eRk D ≤ M.eRk (Y ∩ Z) := M.eRk_mono hDYZ
        _ = (2 : ℕ∞) := by rw [hYZr, hryz]
    have hD_ge : (2 : ℕ∞) ≤ M.eRk D := by
      rw [← hC2]
      exact M.eRk_mono hCD
    have hDrank : M.eRk D = (2 : ℕ∞) :=
      le_antisymm hD_le hD_ge

    have hBDunion : B ∪ D = Y := by
      ext x
      simp [B, D, Y]
      tauto
    have hCBD : C ⊆ B ∩ D := by
      intro x hx
      exact ⟨Or.inl hx, Or.inl hx⟩
    obtain ⟨rbd, hBDr, hrbd4⟩ := rank_nat_le_four (B ∩ D)
    have hbdLower := M.eRk_mono hCBD
    rw [hC2, hBDr] at hbdLower
    have hbdLowerNat : 2 ≤ rbd := by exact_mod_cast hbdLower
    have hsubBD := M.eRk_inter_add_eRk_union_le B D
    rw [hBDr, hBDunion, hYr, hry, hBrank, hDrank] at hsubBD
    have hsubBDNat : rbd + 3 ≤ 2 + 2 := by exact_mod_cast hsubBD
    omega

  · by_contra hgood
    push_neg at hgood
    have hXbad : M.eRk X ≠ (4 : ℕ∞) := by
      simpa [X] using hgood.1
    have hYbad : M.eRk Y ≠ (4 : ℕ∞) := by
      simpa [Y] using hgood.2.1
    obtain ⟨rx, hXr, hrx3⟩ :=
      rank_nat_le_three_of_ne_four X hXbad
    obtain ⟨ry, hYr, hry3⟩ :=
      rank_nat_le_three_of_ne_four Y hYbad
    have hXYunion : X ∪ Y = C ∪ ({a, b, c} : Set α) := by
      ext x
      simp [X, Y]
      tauto
    have hCXY : C ⊆ X ∩ Y := by
      intro x hx
      exact ⟨Or.inl hx, Or.inl hx⟩
    obtain ⟨rxy, hXYr, hrxy4⟩ := rank_nat_le_four (X ∩ Y)
    have hxyLower := M.eRk_mono hCXY
    rw [hC3, hXYr] at hxyLower
    have hxyLowerNat : 3 ≤ rxy := by exact_mod_cast hxyLower
    have hsubXY := M.eRk_inter_add_eRk_union_le X Y
    rw [hXYr, hXYunion, hABC, hXr, hYr] at hsubXY
    have hsubXYNat : rxy + 4 ≤ rx + ry := by exact_mod_cast hsubXY
    omega

  · left
    apply le_antisymm
    · exact hupper _
    · rw [← hC4]
      exact M.eRk_mono (by
        intro x hx
        exact Or.inl hx)

end

end Rank4DangerousBranches
end HigherRankKUM
