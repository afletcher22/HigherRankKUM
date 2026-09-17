import HigherRankKUM.PairCycleTriangle
import HigherRankKUM.BinaryRelationRelabel
import Mathlib.Combinatorics.Matroid.Minor.Restrict
import Mathlib.Combinatorics.Matroid.Dual

namespace HigherRankKUM
namespace Rank4ThreePairDual

open Set
open BinaryRelationCycle
open PairCycle

variable {α : Type*}

private lemma bitPick_mem_pair (x₀ x₁ : α) (b : Bool) :
    bitPick x₀ x₁ b ∈ ({x₀, x₁} : Set α) := by
  cases b <;> simp [bitPick]

private lemma bitPick_ne_other (x₀ x₁ : α) (h : x₀ ≠ x₁) (b : Bool) :
    bitPick x₀ x₁ b ≠ bitPick x₀ x₁ (Bool.not b) := by
  cases b
  · simpa [bitPick] using h
  · simpa [bitPick] using h.symm

private lemma mem_pair_eq_bitPick_or_other
    (x₀ x₁ : α) (b : Bool) {e : α}
    (he : e ∈ ({x₀, x₁} : Set α)) :
    e = bitPick x₀ x₁ b ∨ e = bitPick x₀ x₁ (Bool.not b) := by
  cases b <;> simpa [bitPick, or_comm] using he

/-- The rank-four local relation with a whole two-element middle block. -/
def middlePairRelation (M : Matroid α)
    (x₀ x₁ y₀ y₁ z₀ z₁ : α) : Relation :=
  fun x z => M.IsBase
    ({bitPick x₀ x₁ x, y₀, y₁, bitPick z₀ z₁ z} : Set α)

/-- Reversing the two endpoint pairs transposes the middle-pair relation. -/
theorem middlePairRelation_reverse
    (M : Matroid α) (x₀ x₁ y₀ y₁ z₀ z₁ : α) :
    middlePairRelation M z₀ z₁ y₀ y₁ x₀ x₁ =
      transpose (middlePairRelation M x₀ x₁ y₀ y₁ z₀ z₁) := by
  funext z x
  apply propext
  have hset :
      ({bitPick z₀ z₁ z, y₀, y₁, bitPick x₀ x₁ x} : Set α) =
        {bitPick x₀ x₁ x, y₀, y₁, bitPick z₀ z₁ z} := by
    ext e
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  simpa [middlePairRelation, transpose, hset]

/-- On six elements partitioned into three pairs `X,Y,Z`, a rank-four basis
cell using all of the middle pair `Y` is dual to the complementary rank-two
basis cell between `X` and `Z`.

Restrict to the six-element union and dualize.  The three pairwise-union
basis hypotheses put all six elements in the ground set and make the union
spanning.  Taking dual complements turns

`{x, y₀, y₁, z}`

into the pair consisting of the *other* element of `X` and the *other*
element of `Z`.  This is the representation-free bridge behind the
rank-four three-pair parity law. -/
theorem middlePairRelation_eq_dual_crossBaseRelation
    (M : Matroid α) {x₀ x₁ y₀ y₁ z₀ z₁ : α}
    (hx : x₀ ≠ x₁) (hy : y₀ ≠ y₁) (hz : z₀ ≠ z₁)
    (hXY : Disjoint ({x₀, x₁} : Set α) ({y₀, y₁} : Set α))
    (hYZ : Disjoint ({y₀, y₁} : Set α) ({z₀, z₁} : Set α))
    (hXZ : Disjoint ({x₀, x₁} : Set α) ({z₀, z₁} : Set α))
    (hXYbase : M.IsBase (({x₀, x₁} : Set α) ∪ {y₀, y₁}))
    (hYZbase : M.IsBase (({y₀, y₁} : Set α) ∪ {z₀, z₁}))
    (hXZbase : M.IsBase (({x₀, x₁} : Set α) ∪ {z₀, z₁})) :
    middlePairRelation M x₀ x₁ y₀ y₁ z₀ z₁ =
      doubleRelabel
        (crossBaseRelation
          ((M.restrict (({x₀, x₁} : Set α) ∪ {y₀, y₁} ∪ {z₀, z₁}))✶)
          x₀ x₁ z₀ z₁) := by
  let X : Set α := {x₀, x₁}
  let Y : Set α := {y₀, y₁}
  let Z : Set α := {z₀, z₁}
  let U : Set α := X ∪ Y ∪ Z
  let R : Matroid α := M.restrict U
  let N : Matroid α := R✶

  have hXYsub : (({x₀, x₁} : Set α) ∪ {y₀, y₁}) ⊆ U := by
    intro e he
    exact Or.inl (by simpa [X, Y] using he)
  have hUground : U ⊆ M.E := by
    intro e he
    change e ∈ X ∪ Y ∪ Z at he
    rcases he with heXY | heZ
    · exact hXYbase.subset_ground (by simpa [X, Y] using heXY)
    · exact hXZbase.subset_ground (by
        have : e ∈ X ∪ Z := Or.inr heZ
        simpa [X, Z] using this)
  have hUspan : M.Spanning U :=
    hXYbase.spanning_of_superset hXYsub hUground

  funext x z
  apply propext
  let B : Set α := {bitPick x₀ x₁ x, y₀, y₁, bitPick z₀ z₁ z}
  have hBU : B ⊆ U := by
    intro e he
    change e ∈ {bitPick x₀ x₁ x, y₀, y₁, bitPick z₀ z₁ z} at he
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    change e ∈ X ∪ Y ∪ Z
    rcases he with h | h | h | h
    · subst e
      exact Or.inl (Or.inl (bitPick_mem_pair x₀ x₁ x))
    · subst e
      exact Or.inl (Or.inr (by simp [Y]))
    · subst e
      exact Or.inl (Or.inr (by simp [Y]))
    · subst e
      exact Or.inr (bitPick_mem_pair z₀ z₁ z)
  have hBR : B ⊆ R.E := by
    simpa [R, U] using hBU
  have hrestrict : R.IsBase B ↔ M.IsBase B := by
    rw [hUspan.isBase_restrict_iff]
    exact and_iff_left hBU
  have hdual : R.IsBase B ↔ N.IsBase (R.E \ B) := by
    simpa [N] using R.base_iff_dual_isBase_compl hBR
  have hcompl : R.E \ B =
      ({bitPick x₀ x₁ (Bool.not x), bitPick z₀ z₁ (Bool.not z)} : Set α) := by
    change U \ B =
      ({bitPick x₀ x₁ (Bool.not x), bitPick z₀ z₁ (Bool.not z)} : Set α)
    ext e
    change (e ∈ U ∧ e ∉ B) ↔
      (e = bitPick x₀ x₁ (Bool.not x) ∨
        e = bitPick z₀ z₁ (Bool.not z))
    constructor
    · rintro ⟨heU, heB⟩
      change e ∈ X ∪ Y ∪ Z at heU
      rcases heU with heXY | heZ
      · rcases heXY with heX | heY
        · rcases mem_pair_eq_bitPick_or_other x₀ x₁ x heX with hsel | hother
          · exfalso
            apply heB
            subst e
            simp [B]
          · exact Or.inl hother
        · exfalso
          apply heB
          have heY' : e = y₀ ∨ e = y₁ := by simpa [Y] using heY
          rcases heY' with rfl | rfl <;> simp [B]
      · rcases mem_pair_eq_bitPick_or_other z₀ z₁ z heZ with hsel | hother
        · exfalso
          apply heB
          subst e
          simp [B]
        · exact Or.inr hother
    · intro he
      rcases he with hxother | hzother
      · subst e
        have hxmem : bitPick x₀ x₁ (Bool.not x) ∈ X := by
          exact bitPick_mem_pair x₀ x₁ (Bool.not x)
        refine ⟨Or.inl (Or.inl hxmem), ?_⟩
        intro hmem
        change bitPick x₀ x₁ (Bool.not x) ∈
          ({bitPick x₀ x₁ x, y₀, y₁, bitPick z₀ z₁ z} : Set α) at hmem
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
        rcases hmem with hsel | hy0 | hy1 | hzsel
        · exact (bitPick_ne_other x₀ x₁ hx x) hsel.symm
        · exact Set.disjoint_left.1 hXY hxmem (by rw [hy0]; simp [Y])
        · exact Set.disjoint_left.1 hXY hxmem (by rw [hy1]; simp [Y])
        · exact Set.disjoint_left.1 hXZ hxmem (by
            rw [hzsel]
            exact bitPick_mem_pair z₀ z₁ z)
      · subst e
        have hzmem : bitPick z₀ z₁ (Bool.not z) ∈ Z := by
          exact bitPick_mem_pair z₀ z₁ (Bool.not z)
        refine ⟨Or.inr hzmem, ?_⟩
        intro hmem
        change bitPick z₀ z₁ (Bool.not z) ∈
          ({bitPick x₀ x₁ x, y₀, y₁, bitPick z₀ z₁ z} : Set α) at hmem
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
        rcases hmem with hxsel | hy0 | hy1 | hsel
        · exact Set.disjoint_left.1 hXZ (bitPick_mem_pair x₀ x₁ x) (by
            rw [← hxsel]
            exact hzmem)
        · exact Set.disjoint_left.1 hYZ (by rw [hy0]; simp [Y]) hzmem
        · exact Set.disjoint_left.1 hYZ (by rw [hy1]; simp [Y]) hzmem
        · exact (bitPick_ne_other z₀ z₁ hz z) hsel.symm
  rw [doubleRelabel_apply]
  change M.IsBase B ↔
    N.IsBase {bitPick x₀ x₁ (Bool.not x), bitPick z₀ z₁ (Bool.not z)}
  rw [← hrestrict, hdual, hcompl]

end Rank4ThreePairDual
end HigherRankKUM
