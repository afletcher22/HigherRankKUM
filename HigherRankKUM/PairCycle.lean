import HigherRankKUM.BinaryRelationCycle
import Mathlib.Combinatorics.Matroid.Minor.Contract
import Mathlib.Combinatorics.Matroid.Rank.ENat

namespace HigherRankKUM
namespace PairCycle

open Set
open BinaryRelationCycle

variable {α : Type*}

/-- Select one of two labelled endpoint elements by a Boolean state. -/
def bitPick (x₀ x₁ : α) : Bool → α
  | false => x₀
  | true => x₁

/-- The cross-basis compatibility relation between two labelled two-element bases. -/
def crossBaseRelation (N : Matroid α) (a₀ a₁ b₀ b₁ : α) : Relation :=
  fun x y => N.IsBase {bitPick a₀ a₁ x, bitPick b₀ b₁ y}

/-- Two disjoint labelled two-element bases induce a full-support Boolean
compatibility relation.  No simplicity or representability is used. -/
theorem crossBaseRelation_fullSupport
    (N : Matroid α) {a₀ a₁ b₀ b₁ : α}
    (ha : a₀ ≠ a₁) (hb : b₀ ≠ b₁)
    (hAB : Disjoint ({a₀, a₁} : Set α) {b₀, b₁})
    (hA : N.IsBase {a₀, a₁}) (hB : N.IsBase {b₀, b₁}) :
    FullSupport (crossBaseRelation N a₀ a₁ b₀ b₁) := by
  constructor
  · intro x
    cases x
    · have ha₁notB : a₁ ∉ ({b₀, b₁} : Set α) := by
        intro hmem
        exact Set.disjoint_left.1 hAB (by simp) hmem
      obtain ⟨b, hbmem, hbase⟩ :=
        N.isBase_exchange {a₀, a₁} {b₀, b₁} hA hB a₁ ⟨by simp, ha₁notB⟩
      have hb' : b = b₀ ∨ b = b₁ := by simpa using hbmem.1
      rcases hb' with rfl | rfl
      · refine ⟨false, ?_⟩
        simpa [crossBaseRelation, bitPick, ha, insert_comm] using hbase
      · refine ⟨true, ?_⟩
        simpa [crossBaseRelation, bitPick, ha, insert_comm] using hbase
    · have ha₀notB : a₀ ∉ ({b₀, b₁} : Set α) := by
        intro hmem
        exact Set.disjoint_left.1 hAB (by simp) hmem
      obtain ⟨b, hbmem, hbase⟩ :=
        N.isBase_exchange {a₀, a₁} {b₀, b₁} hA hB a₀ ⟨by simp, ha₀notB⟩
      have hb' : b = b₀ ∨ b = b₁ := by simpa using hbmem.1
      rcases hb' with rfl | rfl
      · refine ⟨false, ?_⟩
        simpa [crossBaseRelation, bitPick, ha, insert_comm] using hbase
      · refine ⟨true, ?_⟩
        simpa [crossBaseRelation, bitPick, ha, insert_comm] using hbase
  · intro y
    cases y
    · have hb₁notA : b₁ ∉ ({a₀, a₁} : Set α) := by
        intro hmem
        exact Set.disjoint_left.1 hAB hmem (by simp)
      obtain ⟨a, hamem, hbase⟩ :=
        N.isBase_exchange {b₀, b₁} {a₀, a₁} hB hA b₁ ⟨by simp, hb₁notA⟩
      have ha' : a = a₀ ∨ a = a₁ := by simpa using hamem.1
      rcases ha' with rfl | rfl
      · refine ⟨false, ?_⟩
        simpa [crossBaseRelation, bitPick, hb, insert_comm] using hbase
      · refine ⟨true, ?_⟩
        simpa [crossBaseRelation, bitPick, hb, insert_comm] using hbase
    · have hb₀notA : b₀ ∉ ({a₀, a₁} : Set α) := by
        intro hmem
        exact Set.disjoint_left.1 hAB hmem (by simp)
      obtain ⟨a, hamem, hbase⟩ :=
        N.isBase_exchange {b₀, b₁} {a₀, a₁} hB hA b₀ ⟨by simp, hb₀notA⟩
      have ha' : a = a₀ ∨ a = a₁ := by simpa using hamem.1
      rcases ha' with rfl | rfl
      · refine ⟨false, ?_⟩
        simpa [crossBaseRelation, bitPick, hb, insert_comm] using hbase
      · refine ⟨true, ?_⟩
        simpa [crossBaseRelation, bitPick, hb, insert_comm] using hbase

/-- Local contraction package behind a shifted pair window.  If `C` is the
independent middle core and adjoining either endpoint pair gives a base of
`M`, then after contracting `C` both endpoint pairs are bases. -/
theorem endpoint_pairs_are_bases_after_contract
    (M : Matroid α) {C : Set α} {a₀ a₁ b₀ b₁ : α}
    (hC : M.Indep C)
    (hAC : Disjoint ({a₀, a₁} : Set α) C)
    (hBC : Disjoint ({b₀, b₁} : Set α) C)
    (hA : M.IsBase ({a₀, a₁} ∪ C))
    (hB : M.IsBase ({b₀, b₁} ∪ C)) :
    (M ／ C).IsBase {a₀, a₁} ∧ (M ／ C).IsBase {b₀, b₁} := by
  exact ⟨hC.contract_isBase_iff.2 ⟨hA, hAC⟩,
    hC.contract_isBase_iff.2 ⟨hB, hBC⟩⟩

/-- In the local pair-cycle setup, the contracted matroid has rank exactly two. -/
theorem endpoint_contract_eRank_eq_two
    (M : Matroid α) {C : Set α} {a₀ a₁ b₀ b₁ : α}
    (ha : a₀ ≠ a₁)
    (hC : M.Indep C)
    (hAC : Disjoint ({a₀, a₁} : Set α) C)
    (hA : M.IsBase ({a₀, a₁} ∪ C)) :
    (M ／ C).eRank = 2 := by
  have hbase : (M ／ C).IsBase {a₀, a₁} :=
    hC.contract_isBase_iff.2 ⟨hA, hAC⟩
  rw [← hbase.encard_eq_eRank]
  simp [ha]

/-- Therefore the endpoint compatibility relation in the contracted rank-two
matroid has full support. -/
theorem contracted_endpoint_relation_fullSupport
    (M : Matroid α) {C : Set α} {a₀ a₁ b₀ b₁ : α}
    (ha : a₀ ≠ a₁) (hb : b₀ ≠ b₁)
    (hAB : Disjoint ({a₀, a₁} : Set α) {b₀, b₁})
    (hC : M.Indep C)
    (hAC : Disjoint ({a₀, a₁} : Set α) C)
    (hBC : Disjoint ({b₀, b₁} : Set α) C)
    (hA : M.IsBase ({a₀, a₁} ∪ C))
    (hB : M.IsBase ({b₀, b₁} ∪ C)) :
    FullSupport (crossBaseRelation (M ／ C) a₀ a₁ b₀ b₁) := by
  obtain ⟨hA', hB'⟩ :=
    endpoint_pairs_are_bases_after_contract M hC hAC hBC hA hB
  exact crossBaseRelation_fullSupport (M ／ C) ha hb hAB hA' hB'

end PairCycle
end HigherRankKUM
