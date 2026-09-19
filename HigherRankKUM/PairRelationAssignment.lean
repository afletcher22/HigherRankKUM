import HigherRankKUM.PairCycleObstruction
import Mathlib.Data.List.OfFn

namespace HigherRankKUM

namespace BinaryRelationCycle

/-- A witness for a composed finite list of relations can be expanded into
states on all vertices of the corresponding relation chain. -/
theorem exists_chain_of_composeList_ofFn
    {n : ℕ} (R : Fin n → Relation) {x z : Bool}
    (h : composeList (List.ofFn R) x z) :
    ∃ v : Fin (n + 1) → Bool,
      v 0 = x ∧
      v (Fin.last n) = z ∧
      ∀ j : Fin n, R j (v j.castSucc) (v j.succ) := by
  induction n generalizing R x z with
  | zero =>
      have hxz : x = z := by
        simpa [composeList, idRel] using h
      subst z
      refine ⟨fun _ => x, rfl, rfl, ?_⟩
      intro j
      exact Fin.elim0 j
  | succ n ih =>
      have hcomp :
          comp (R 0)
            (composeList (List.ofFn fun j : Fin n => R j.succ)) x z := by
        simpa [List.ofFn_succ, composeList] using h
      obtain ⟨y, hxy, hyz⟩ := hcomp
      obtain ⟨w, hw0, hwlast, hwrel⟩ :=
        ih (R := fun j : Fin n => R j.succ) (x := y) (z := z) hyz
      let v : Fin (n + 2) → Bool := Fin.cases x w
      refine ⟨v, ?_, ?_, ?_⟩
      · simp [v]
      · simpa [v] using hwlast
      · intro j
        refine Fin.cases ?_ (fun k => ?_) j
        · simpa [v, hw0] using hxy
        · simpa [v] using hwrel k

/-- A cyclically satisfiable List.ofFn relation cycle has a Boolean state at
every cyclic vertex satisfying every local relation. -/
theorem exists_cyclic_assignment_of_cyclicSatisfiable_ofFn
    {n : ℕ} (hn : 0 < n) (R : Fin n → Relation)
    (hcyc : CyclicSatisfiable (List.ofFn R)) :
    ∃ s : Fin n → Bool,
      ∀ j : Fin n, R j (s j) (s (cyclicIndex n hn j 1)) := by
  obtain ⟨x, hx⟩ := hcyc
  obtain ⟨v, hv0, hvlast, hvrel⟩ :=
    exists_chain_of_composeList_ofFn R hx
  have hclose : v (Fin.last n) = v 0 := hvlast.trans hv0.symm
  let s : Fin n → Bool := fun j => v j.castSucc
  refine ⟨s, ?_⟩
  intro j
  have hnext :
      v j.succ = v (cyclicIndex n hn j 1).castSucc := by
    by_cases hlt : j.val + 1 < n
    · have hidx :
          cyclicIndex n hn j 1 = ⟨j.val + 1, hlt⟩ := by
        apply Fin.ext
        simp only [cyclicIndex_val]
        rw [Nat.mod_eq_of_lt hlt]
      rw [hidx]
      apply congrArg v
      apply Fin.ext
      rfl
    · have hsum : j.val + 1 = n := by omega
      have hsucc : j.succ = Fin.last n := by
        apply Fin.ext
        exact hsum
      have hzero :
          cyclicIndex n hn j 1 = (⟨0, hn⟩ : Fin n) := by
        apply Fin.ext
        simp only [cyclicIndex_val]
        rw [hsum]
        simp
      rw [hsucc, hzero]
      simpa using hclose
  have hj := hvrel j
  rw [hnext] at hj
  simpa [s] using hj

end BinaryRelationCycle

namespace PairCycleObstruction

open BinaryRelationCycle

/-- Successor in the abstract orbit index corresponds to adding h in the
physical pair index. -/
theorem stepIndex_cyclicIndex_one
    {N h : ℕ} (hN : 0 < N) (j : Fin N) :
    stepIndex N h hN (cyclicIndex N hN j 1) =
      cyclicIndex N hN (stepIndex N h hN j) h := by
  apply Fin.ext
  simp only [stepIndex_val, cyclicIndex_val]
  have hm :
      ((j.val + 1) % N) * h ≡ (j.val * h) % N + h [MOD N] := by
    calc
      ((j.val + 1) % N) * h ≡ (j.val + 1) * h [MOD N] :=
        (Nat.mod_modEq (j.val + 1) N).mul_right h
      _ = j.val * h + h := by simp [Nat.add_mul]
      _ ≡ (j.val * h) % N + h [MOD N] :=
        ((Nat.mod_modEq (j.val * h) N).add_right h).symm
  exact hm

@[simp] theorem stepEquiv_apply
    {N h : ℕ} (hN : 0 < N) (hcop : Nat.gcd N h = 1)
    (j : Fin N) :
    stepEquiv N h hN hcop j = stepIndex N h hN j := rfl

/-- Relation-level cyclic satisfiability on the +h orbit gives an explicit
Boolean orientation on the physical pair indices. -/
theorem exists_orientation_of_pairRelationOrientable
    {N h : ℕ} (hN : 0 < N) (hcop : Nat.gcd N h = 1)
    {R : Fin N → Relation}
    (hor : PairRelationOrientable N h hN R) :
    ∃ o : Fin N → Bool,
      ∀ i : Fin N, R i (o i) (o (cyclicIndex N hN i h)) := by
  change CyclicSatisfiable
    (List.ofFn fun j : Fin N => R (stepIndex N h hN j)) at hor
  obtain ⟨s, hs⟩ :=
    exists_cyclic_assignment_of_cyclicSatisfiable_ofFn
      hN (fun j : Fin N => R (stepIndex N h hN j)) hor
  let E : Fin N ≃ Fin N := stepEquiv N h hN hcop
  let o : Fin N → Bool := fun i => s (E.symm i)
  refine ⟨o, ?_⟩
  intro i
  let j : Fin N := E.symm i
  have hstep : stepIndex N h hN j = i := by
    change E j = i
    simpa [j] using E.apply_symm_apply i
  have hnext :
      E.symm (cyclicIndex N hN i h) =
        cyclicIndex N hN j 1 := by
    apply E.injective
    rw [E.apply_symm_apply]
    change stepIndex N h hN (cyclicIndex N hN j 1) =
      cyclicIndex N hN i h
    rw [stepIndex_cyclicIndex_one hN j, hstep]
  have hj := hs j
  rw [hstep] at hj
  have hi : o i = s j := by
    rfl
  have hinext :
      o (cyclicIndex N hN i h) =
        s (cyclicIndex N hN j 1) := by
    dsimp [o]
    rw [hnext]
  rw [hi, hinext]
  exact hj

end PairCycleObstruction

end HigherRankKUM
