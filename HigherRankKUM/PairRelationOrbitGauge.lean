import HigherRankKUM.BinaryRelationOrbitGauge
import HigherRankKUM.PairCycleObstruction
import HigherRankKUM.PairCycleIndexing

namespace HigherRankKUM
namespace PairCycleObstruction

open BinaryRelationCycle

/-- Extend the successor-orbit indexing to the `N+1` vertices of the closed
relation chain.  The final vertex lands back at zero modulo `N`. -/
def orbitVertexIndex (N h : ℕ) (hN : 0 < N) (k : Fin (N + 1)) : Fin N :=
  ⟨(k.val * h) % N, Nat.mod_lt _ hN⟩

@[simp] theorem orbitVertexIndex_castSucc
    (N h : ℕ) (hN : 0 < N) (j : Fin N) :
    orbitVertexIndex N h hN j.castSucc = stepIndex N h hN j := by
  rfl

/-- Moving from relation `j` to relation `j+1` in the successor-orbit list
moves the physical pair index forward by exactly `h`. -/
theorem orbitVertexIndex_succ
    (N h : ℕ) (hN : 0 < N) (j : Fin N) :
    orbitVertexIndex N h hN j.succ =
      cyclicIndex N hN (stepIndex N h hN j) h := by
  apply Fin.ext
  change ((j.val + 1) * h) % N = (((j.val * h) % N) + h) % N
  rw [Nat.add_mul]
  simp only [Nat.one_mul]
  exact (Nat.mod_add_mod (j.val * h) N h).symm

/-- The initial successor-orbit vertex is physical pair zero. -/
@[simp] theorem orbitVertexIndex_zero
    (N h : ℕ) (hN : 0 < N) :
    orbitVertexIndex N h hN (0 : Fin (N + 1)) = ⟨0, hN⟩ := by
  apply Fin.ext
  simp [orbitVertexIndex]

/-- After `N` successor steps the orbit vertex is back at zero, independently
of whether `h` is coprime to `N`. -/
@[simp] theorem orbitVertexIndex_last
    (N h : ℕ) (hN : 0 < N) :
    orbitVertexIndex N h hN (Fin.last N) = ⟨0, hN⟩ := by
  apply Fin.ext
  simp [orbitVertexIndex]

/-- `PairRelationOrientable` is invariant under arbitrary Boolean relabelling
of every pair vertex.  A relation leaving pair `i` receives the gauge of `i`
on its input and the gauge of `i+h` on its output; these gauges cancel around
the closed successor orbit.

No coprimality assumption is needed: coprimality is only required elsewhere to
know that the successor orbit visits every physical pair exactly once. -/
theorem pairRelationOrientable_gauge_iff
    {N h : ℕ} (hN : 0 < N)
    (R : Fin N → Relation) (g : Fin N → Bool) :
    PairRelationOrientable N h hN
        (fun i => gaugeRelation (g i) (g (cyclicIndex N hN i h)) (R i)) ↔
      PairRelationOrientable N h hN R := by
  let gv : Fin (N + 1) → Bool := fun k => g (orbitVertexIndex N h hN k)
  have hclose : gv (Fin.last N) = gv 0 := by
    simp [gv]
  have hcyc := cyclicSatisfiable_ofFn_gauge_of_closed
    (R := fun j : Fin N => R (stepIndex N h hN j)) gv hclose
  change
    CyclicSatisfiable
        (List.ofFn fun j : Fin N =>
          gaugeRelation
            (g (stepIndex N h hN j))
            (g (cyclicIndex N hN (stepIndex N h hN j) h))
            (R (stepIndex N h hN j))) ↔
      CyclicSatisfiable
        (List.ofFn fun j : Fin N => R (stepIndex N h hN j))
  simpa [gv, orbitVertexIndex_castSucc, orbitVertexIndex_succ] using hcyc

end PairCycleObstruction
end HigherRankKUM
