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

  have hneXY (a : α) (ha : a ∈ X) (b : α) (hb : b ∈ Y) : a ≠ b := by
    intro hab
    subst b
    exact Set.disjoint_left.1 hXY ha hb
  have hneYZ (a : α) (ha : a ∈ Y) (b : α) (hb : b ∈ Z) : a ≠ b := by
    intro hab
    subst b
    exact Set.disjoint_left.1 hYZ ha hb
  have hneXZ (a : α) (ha : a ∈ X) (b : α) (hb : b ∈ Z) : a ≠ b := by
    intro hab
    subst b
    exact Set.disjoint_left.1 hXZ ha hb

  have hxy00 : x₀ ≠ y₀ := hneXY x₀ (by simp [X]) y₀ (by simp [Y])
  have hxy01 : x₀ ≠ y₁ := hneXY x₀ (by simp [X]) y₁ (by simp [Y])
  have hxy10 : x₁ ≠ y₀ := hneXY x₁ (by simp [X]) y₀ (by simp [Y])
  have hxy11 : x₁ ≠ y₁ := hneXY x₁ (by simp [X]) y₁ (by simp [Y])
  have hyz00 : y₀ ≠ z₀ := hneYZ y₀ (by simp [Y]) z₀ (by simp [Z])
  have hyz01 : y₀ ≠ z₁ := hneYZ y₀ (by simp [Y]) z₁ (by simp [Z])
  have hyz10 : y₁ ≠ z₀ := hneYZ y₁ (by simp [Y]) z₀ (by simp [Z])
  have hyz11 : y₁ ≠ z₁ := hneYZ y₁ (by simp [Y]) z₁ (by simp [Z])
  have hxz00 : x₀ ≠ z₀ := hneXZ x₀ (by simp [X]) z₀ (by simp [Z])
  have hxz01 : x₀ ≠ z₁ := hneXZ x₀ (by simp [X]) z₁ (by simp [Z])
  have hxz10 : x₁ ≠ z₀ := hneXZ x₁ (by simp [X]) z₀ (by simp [Z])
  have hxz11 : x₁ ≠ z₁ := hneXZ x₁ (by simp [X]) z₁ (by simp [Z])

  funext x z
  apply propext
  let B : Set α := {bitPick x₀ x₁ x, y₀, y₁, bitPick z₀ z₁ z}
  have hBU : B ⊆ U := by
    cases x <;> cases z <;> simp [B, U, X, Y, Z, bitPick]
  have hBR : B ⊆ R.E := by
    simpa [R, U] using hBU
  have hrestrict : R.IsBase B ↔ M.IsBase B := by
    rw [hUspan.isBase_restrict_iff]
    exact and_iff_left hBU
  have hdual : R.IsBase B ↔ N.IsBase (R.E \ B) := by
    simpa [N] using R.base_iff_dual_isBase_compl hBR
  have hcompl : R.E \ B =
      ({bitPick x₀ x₁ (Bool.not x), bitPick z₀ z₁ (Bool.not z)} : Set α) := by
    cases x <;> cases z <;>
      simp [R, U, X, Y, Z, B, bitPick, hx, hy, hz,
        hxy00, hxy01, hxy10, hxy11,
        hyz00, hyz01, hyz10, hyz11,
        hxz00, hxz01, hxz10, hxz11]
  rw [doubleRelabel_apply]
  change M.IsBase B ↔
    N.IsBase {bitPick x₀ x₁ (Bool.not x), bitPick z₀ z₁ (Bool.not z)}
  rw [← hrestrict, hdual, hcompl]

end Rank4ThreePairDual
end HigherRankKUM
