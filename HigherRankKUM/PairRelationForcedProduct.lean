import HigherRankKUM.BinaryRelationForcedCommutative
import HigherRankKUM.PairCycleObstruction
import Mathlib.Data.List.FinRange

namespace HigherRankKUM
namespace PairCycleObstruction

open BinaryRelationCycle

/-- In the coprime regime, the successor-orbit list is a permutation of the
ordinary physical-index list. For forced Boolean relations the order is
irrelevant, so the two total composed transitions are exactly equal.

This is the bridge that lets local repair arguments work with the natural
physical starts `s,s+1,s+2,s+3` even though `PairRelationOrientable` stores
relations in repeated-`+h` successor order. -/
theorem compose_relationCycleList_eq_compose_ofFn_of_bijections
    {N h : ℕ} (hN : 0 < N) (hcop : Nat.gcd N h = 1)
    (R : Fin N → Relation) (hR : ∀ i, BijectionRelation (R i)) :
    composeList (relationCycleList N h hN R) =
      composeList (List.ofFn R) := by
  let σ := stepEquiv N h hN hcop
  have hperm : List.Perm (relationCycleList N h hN R) (List.ofFn R) := by
    have hp := σ.ofFn_comp_perm R
    simpa [relationCycleList, σ, stepEquiv, Function.comp_def] using hp
  apply composeList_eq_of_perm_bijections hperm
  intro S hS
  simp [relationCycleList] at hS
  obtain ⟨j, rfl⟩ := hS
  exact hR _

/-- Equality of the physical-index products of two forced relation systems
upgrades to equality of their successor-orbit products in the coprime regime. -/
theorem compose_relationCycleList_eq_of_compose_ofFn_eq
    {N h : ℕ} (hN : 0 < N) (hcop : Nat.gcd N h = 1)
    (old new : Fin N → Relation)
    (hold : ∀ i, BijectionRelation (old i))
    (hnew : ∀ i, BijectionRelation (new i))
    (hprod : composeList (List.ofFn old) = composeList (List.ofFn new)) :
    composeList (relationCycleList N h hN old) =
      composeList (relationCycleList N h hN new) := by
  rw [compose_relationCycleList_eq_compose_ofFn_of_bijections hN hcop old hold,
    compose_relationCycleList_eq_compose_ofFn_of_bijections hN hcop new hnew]
  exact hprod

/-- Forced local replacement principle for a coprime successor cycle.

`I` can be any noduplicated list of affected physical indices. If the old and
new relation systems are forced everywhere, agree away from `I`, and have the
same cyclic satisfiability on the affected sublists, then the whole pair-cycle
orientability is unchanged. The affected indices need not be consecutive in
the successor-orbit order. -/
theorem pairRelationOrientable_iff_of_index_replacement
    {N h : ℕ} (hN : 0 < N) (hcop : Nat.gcd N h = 1)
    (old new : Fin N → Relation) (I : List (Fin N))
    (hI : I.Nodup)
    (hold : ∀ i, BijectionRelation (old i))
    (hnew : ∀ i, BijectionRelation (new i))
    (hout : ∀ i, i ∉ I → new i = old i)
    (hcyc : CyclicSatisfiable (I.map old) ↔
      CyclicSatisfiable (I.map new)) :
    PairRelationOrientable N h hN old ↔
      PairRelationOrientable N h hN new := by
  have holdI : ∀ R ∈ I.map old, BijectionRelation R := by
    intro R hR
    rcases List.mem_map.1 hR with ⟨i, hi, rfl⟩
    exact hold i
  have hnewI : ∀ R ∈ I.map new, BijectionRelation R := by
    intro R hR
    rcases List.mem_map.1 hR with ⟨i, hi, rfl⟩
    exact hnew i
  have haffected :
      composeList (I.map old) = composeList (I.map new) :=
    composeList_eq_of_cyclicSatisfiable_iff_bijections holdI hnewI hcyc
  have hphysical :
      composeList (List.ofFn old) = composeList (List.ofFn new) :=
    composeList_ofFn_eq_of_index_replacement old new I hI hold hnew hout haffected
  have horbit :
      composeList (relationCycleList N h hN old) =
        composeList (relationCycleList N h hN new) :=
    compose_relationCycleList_eq_of_compose_ofFn_eq
      hN hcop old new hold hnew hphysical
  unfold PairRelationOrientable CyclicSatisfiable
  rw [horbit]

end PairCycleObstruction
end HigherRankKUM