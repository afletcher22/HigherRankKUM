import Probe.Rank4.TheoremD
import Probe.Rank4.Kum8

/-!
Theorem D with its 8-element input discharged by Kotlar–Ziv (`Probe.Rank4.Kum8`, a human proof,
no certificate): divisible rank-4 KUM, given only the rank-4 extension theorem.
-/

namespace HigherRankKUM

theorem solvesDivisibleKUMAtRank_four_of_extension {α : Type*}
    (hext : ∀ k, 2 ≤ k → Rank4Extension α (4 * k)) : SolvesDivisibleKUMAtRank α 4 :=
  solvesDivisibleKUMAtRank_four hext solvesKUMAtRankSize_four_eight

#print axioms solvesDivisibleKUMAtRank_four_of_extension

end HigherRankKUM
