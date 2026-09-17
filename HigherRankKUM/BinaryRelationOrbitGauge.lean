import HigherRankKUM.BinaryRelationGauge

namespace HigherRankKUM
namespace BinaryRelationCycle

/-- Applying the same Boolean gauge to both ends of the identity relation does
nothing.  This is the zero-length case of chain gauge cancellation. -/
private theorem gaugeRelation_self_idRel (a : Bool) :
    gaugeRelation a a idRel = idRel := by
  cases a <;>
    funext x y <;>
    apply propext <;>
    cases x <;> cases y <;>
    simp [gaugeRelation, relabelInput, relabelOutput, idRel]

/-- A simultaneous gauge on both ends of a relation preserves existence of a
fixed point. -/
private theorem exists_fixedPoint_gaugeRelation_self_iff
    (a : Bool) (R : Relation) :
    (∃ x, gaugeRelation a a R x x) ↔ ∃ x, R x x := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨if a then Bool.not x else x, (gaugeRelation_apply a a R x x).1 hx⟩
  · rintro ⟨x, hx⟩
    cases a
    · exact ⟨x, by simpa [gaugeRelation, relabelInput, relabelOutput] using hx⟩
    · refine ⟨Bool.not x, ?_⟩
      cases x <;>
        simpa [gaugeRelation, relabelInput, relabelOutput] using hx

/-- In a finite chain of Boolean relations, if the vertex gauges are supplied
as a function on the `n+1` chain vertices, then all interior gauges cancel in
the total composition.  Only the gauge on the first and last vertices remains.

This is the `List.ofFn` form needed for successor-orbit relation lists. -/
theorem composeList_ofFn_gauge
    {n : Nat} (R : Fin n → Relation) (g : Fin (n + 1) → Bool) :
    composeList
        (List.ofFn fun j : Fin n =>
          gaugeRelation (g j.castSucc) (g j.succ) (R j)) =
      gaugeRelation (g 0) (g (Fin.last n))
        (composeList (List.ofFn R)) := by
  induction n with
  | zero =>
      simpa [composeList] using (gaugeRelation_self_idRel (g 0)).symm
  | succ n ih =>
      simp only [List.ofFn_succ, composeList]
      have htail := ih
        (fun i : Fin n => R i.succ)
        (fun k : Fin (n + 1) => g k.succ)
      have htailFn :
          (fun i : Fin n =>
            gaugeRelation (g i.succ.castSucc) (g i.succ.succ) (R i.succ)) =
          (fun i : Fin n =>
            gaugeRelation (g i.castSucc.succ) (g i.succ.succ) (R i.succ)) := by
        funext i
        rw [show i.succ.castSucc = i.castSucc.succ by
          apply Fin.ext
          rfl]
      rw [htailFn, htail]
      rw [show (Fin.last n).succ = Fin.last (n + 1) by
        apply Fin.ext
        rfl]
      simpa using
        comp_gaugeRelation_cancel
          (g 0) (g (Fin.succ 0)) (g (Fin.last (n + 1)))
          (R 0) (composeList (List.ofFn fun i : Fin n => R i.succ))

/-- If the initial and terminal vertex gauges coincide, a finite gauged chain
has exactly the same cyclic satisfiability as the ungauged chain. -/
theorem cyclicSatisfiable_ofFn_gauge_of_closed
    {n : Nat} (R : Fin n → Relation) (g : Fin (n + 1) → Bool)
    (hclose : g (Fin.last n) = g 0) :
    CyclicSatisfiable
        (List.ofFn fun j : Fin n =>
          gaugeRelation (g j.castSucc) (g j.succ) (R j)) ↔
      CyclicSatisfiable (List.ofFn R) := by
  rw [CyclicSatisfiable, CyclicSatisfiable, composeList_ofFn_gauge, hclose]
  exact exists_fixedPoint_gaugeRelation_self_iff
    (g 0) (composeList (List.ofFn R))

end BinaryRelationCycle
end HigherRankKUM
