import Probe.Rank4.TheoremD
import Probe.EncKum8Final

/-!
Theorem D with its 8-element input discharged by the kernel-checked certificate: divisible
rank-4 KUM, given only the rank-4 extension theorem.
-/

namespace HigherRankKUM

theorem solvesDivisibleKUMAtRank_four_of_extension {α : Type*}
    (hext : ∀ N, 8 ≤ N → Rank4Extension α N) : SolvesDivisibleKUMAtRank α 4 :=
  solvesDivisibleKUMAtRank_four hext Probe.Enc.Kum8.solves

#print axioms solvesDivisibleKUMAtRank_four_of_extension

end HigherRankKUM
