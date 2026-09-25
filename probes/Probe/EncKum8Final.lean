import Probe.EncBridge
import Probe.EncKum8

/-!
Rank-4 KUM on 8 elements, end to end: the kernel-checked certificate refutes every rank model on
8 bits, and a counterexample matroid would give one.
-/

namespace Probe.Enc.Kum8

open HigherRankKUM

theorem no_rank_model (m : RankModel 8) : False :=
  no_model m cert.fmla cert.refute ws fmla_eq ws_valid

theorem solves {α : Type*} : SolvesKUMAtRankSize α 4 8 := by
  intro M _ hn hE hRank hEcard hDense
  by_contra hno
  obtain ⟨m⟩ := rankModel_of_no_cbo hn hE hRank hEcard hDense hno
  exact no_rank_model m

#print axioms solves

end Probe.Enc.Kum8
