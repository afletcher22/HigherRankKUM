import Probe.Rank4.TheoremD
import Probe.Rank4.Kum8
import Probe.XP.Insert

/-!
Theorem D with its 8-element input discharged by Kotlar–Ziv (`Probe.Rank4.Kum8`, a human proof,
no certificate): divisible rank-4 KUM, given only the rank-4 extension theorem.

The extension theorem on `4k` elements (`k ≥ 2`) is pair-chain insertion
(`XP.rank4Extension_of_even`, a human proof, no certificate), so divisible rank-4 KUM holds with
no hypotheses (`solvesDivisibleKUMAtRank_four_xp`).
-/

namespace HigherRankKUM

theorem solvesDivisibleKUMAtRank_four_of_extension {α : Type*}
    (hext : ∀ k, 2 ≤ k → Rank4Extension α (4 * k)) : SolvesDivisibleKUMAtRank α 4 :=
  solvesDivisibleKUMAtRank_four hext solvesKUMAtRankSize_four_eight

#print axioms solvesDivisibleKUMAtRank_four_of_extension

/-- **Divisible rank-4 KUM**, with the extension theorem from pair-chain insertion. -/
theorem solvesDivisibleKUMAtRank_four_xp {α : Type*} : SolvesDivisibleKUMAtRank α 4 :=
  solvesDivisibleKUMAtRank_four_of_extension fun k hk =>
    XP.rank4Extension_of_even (by omega) ⟨2 * k, by ring⟩

#print axioms solvesDivisibleKUMAtRank_four_xp

end HigherRankKUM
