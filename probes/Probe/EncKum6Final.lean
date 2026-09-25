import Probe.EncBridge
import Probe.EncKum6Sound

/-!
Rank-4 KUM on 6 elements, end to end: the kernel-checked certificate refutes every rank model on
6 bits (`no_rank_model`), and a counterexample matroid would give one (`rankModel_of_no_cbo`).
-/

namespace Probe.Enc.Kum6

open HigherRankKUM

theorem solves {α : Type*} : SolvesKUMAtRankSize α 4 6 := by
  intro M _ hn hE hRank hEcard hDense
  by_contra hno
  obtain ⟨m⟩ := rankModel_of_no_cbo hn hE hRank hEcard hDense hno
  exact no_rank_model m

#print axioms solves

end Probe.Enc.Kum6
