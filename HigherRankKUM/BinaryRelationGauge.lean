import HigherRankKUM.BinaryRelationRelabel

namespace HigherRankKUM
namespace BinaryRelationCycle

/-- Apply independent Boolean label swaps to the input and output vertices of
a relation. -/
def gaugeRelation (a b : Bool) (R : Relation) : Relation :=
  relabelInput a (relabelOutput b R)

@[simp] theorem gaugeRelation_apply (a b : Bool) (R : Relation) (x y : Bool) :
    gaugeRelation a b R x y ↔
      R (if a then Bool.not x else x) (if b then Bool.not y else y) := by
  cases a <;> cases b <;> simp [gaugeRelation, relabelInput, relabelOutput]

/-- The same vertex gauge on the shared state cancels under relation
composition.  This is the local algebraic reason arbitrary pair labels do not
affect cyclic orientability. -/
theorem comp_gaugeRelation_cancel
    (a b c : Bool) (R S : Relation) :
    comp (gaugeRelation a b R) (gaugeRelation b c S) =
      gaugeRelation a c (comp R S) := by
  funext x z
  apply propext
  cases a <;> cases b <;> cases c <;> cases x <;> cases z <;>
    simp [gaugeRelation, relabelInput, relabelOutput, comp] <;> tauto

/-- Gauging a forced Boolean relation preserves forcedness. -/
theorem gaugeRelation_bijection
    (a b : Bool) {R : Relation} (hR : BijectionRelation R) :
    BijectionRelation (gaugeRelation a b R) := by
  exact relabelInput_bijection a (relabelOutput_bijection b hR)

/-- A chain packages each relation together with the gauge on its output
vertex.  The next relation automatically uses that same gauge on its input. -/
def gaugeChain : Bool → List (Relation × Bool) → List Relation
  | _, [] => []
  | a, (R, b) :: xs => gaugeRelation a b R :: gaugeChain b xs

/-- Forget the gauge labels in a gauged chain. -/
def ungaugedChain : List (Relation × Bool) → List Relation :=
  List.map Prod.fst

/-- The gauge remaining at the far end of a chain. -/
def terminalGauge : Bool → List (Relation × Bool) → Bool
  | a, [] => a
  | _, (_, b) :: xs => terminalGauge b xs

/-- All intermediate gauges in a relation chain cancel.  Only the gauge at
the first and last vertices survives in the composed relation. -/
theorem composeList_gaugeChain
    (a : Bool) (xs : List (Relation × Bool)) :
    composeList (gaugeChain a xs) =
      gaugeRelation a (terminalGauge a xs) (composeList (ungaugedChain xs)) := by
  induction xs generalizing a with
  | nil =>
      funext x y
      apply propext
      cases a <;> cases x <;> cases y <;>
        simp [gaugeChain, ungaugedChain, terminalGauge, gaugeRelation,
          relabelInput, relabelOutput, composeList, idRel]
  | cons p xs ih =>
      rcases p with ⟨R, b⟩
      simp only [gaugeChain, ungaugedChain, List.map_cons, composeList,
        terminalGauge]
      rw [ih]
      exact comp_gaugeRelation_cancel a b (terminalGauge b xs) R
        (composeList (ungaugedChain xs))

/-- A closed chain of vertex relabellings preserves cyclic satisfiability.
No forcedness hypothesis is needed. -/
theorem cyclicSatisfiable_gaugeChain_of_closed
    (a : Bool) (xs : List (Relation × Bool))
    (hclose : terminalGauge a xs = a) :
    CyclicSatisfiable (gaugeChain a xs) ↔
      CyclicSatisfiable (ungaugedChain xs) := by
  rw [CyclicSatisfiable, CyclicSatisfiable, composeList_gaugeChain, hclose]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨if a then Bool.not x else x, ?_⟩
    cases a <;> cases x <;>
      simpa [gaugeRelation, relabelInput, relabelOutput] using hx
  · rintro ⟨x, hx⟩
    refine ⟨if a then Bool.not x else x, ?_⟩
    cases a <;> cases x <;>
      simpa [gaugeRelation, relabelInput, relabelOutput] using hx

end BinaryRelationCycle
end HigherRankKUM
