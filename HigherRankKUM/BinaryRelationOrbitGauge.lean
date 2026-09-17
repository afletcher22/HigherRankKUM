import HigherRankKUM.BinaryRelationGauge

namespace HigherRankKUM
namespace BinaryRelationCycle

/-- In a finite chain of Boolean relations, if the vertex gauges are supplied
as a function on the `n+1` chain vertices, then all interior gauges cancel in
the total composition.  Only the gauge on the first and last vertices remains.

This is the `List.ofFn` form needed for successor-orbit relation lists. -/
theorem composeList_ofFn_gauge
    {n : ℕ} (R : Fin n → Relation) (g : Fin (n + 1) → Bool) :
    composeList
        (List.ofFn fun j : Fin n =>
          gaugeRelation (g j.castSucc) (g j.succ) (R j)) =
      gaugeRelation (g 0) (g (Fin.last n))
        (composeList (List.ofFn R)) := by
  induction n generalizing R g with
  | zero =>
      funext x y
      apply propext
      cases g 0 <;> cases x <;> cases y <;>
        simp [composeList, gaugeRelation, relabelInput, relabelOutput, idRel]
  | succ n ih =>
      simp only [List.ofFn_succ, composeList]
      have htail := ih
        (fun i : Fin n => R i.succ)
        (fun k : Fin (n + 1) => g k.succ)
      rw [htail]
      simpa using
        comp_gaugeRelation_cancel
          (g 0) (g (Fin.succ 0)) (g (Fin.last (n + 1)))
          (R 0) (composeList (List.ofFn fun i : Fin n => R i.succ))

/-- If the initial and terminal vertex gauges coincide, a finite gauged chain
has exactly the same cyclic satisfiability as the ungauged chain. -/
theorem cyclicSatisfiable_ofFn_gauge_of_closed
    {n : ℕ} (R : Fin n → Relation) (g : Fin (n + 1) → Bool)
    (hclose : g (Fin.last n) = g 0) :
    CyclicSatisfiable
        (List.ofFn fun j : Fin n =>
          gaugeRelation (g j.castSucc) (g j.succ) (R j)) ↔
      CyclicSatisfiable (List.ofFn R) := by
  rw [CyclicSatisfiable, CyclicSatisfiable, composeList_ofFn_gauge, hclose]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨if g 0 then Bool.not x else x, ?_⟩
    cases g 0 <;> cases x <;>
      simpa [gaugeRelation, relabelInput, relabelOutput] using hx
  · rintro ⟨x, hx⟩
    refine ⟨if g 0 then Bool.not x else x, ?_⟩
    cases g 0 <;> cases x <;>
      simpa [gaugeRelation, relabelInput, relabelOutput] using hx

end BinaryRelationCycle
end HigherRankKUM
