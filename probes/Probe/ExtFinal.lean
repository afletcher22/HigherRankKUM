import Probe.ExtBridge
import Probe.ExtCyc8
import Probe.ExtCyc10
import Probe.ExtCyc12
import Probe.ExtLin14
import Probe.Rank4.TheoremDCert

/-!
# The rank-4 extension theorem, and divisible rank-4 KUM

The extension theorem on `N = 8, 10, 12` elements comes from the cyclic certificates, and on
every `N ≥ 14` from the linear certificate of length 14. With the 8-element KUM certificate,
Theorem D then gives rank-4 KUM on `4k` elements with no hypotheses.
-/

namespace HigherRankKUM

theorem rank4Extension_eight {α : Type*} : Rank4Extension α 8 :=
  Probe.Enc.rank4Extension_of_cert (by norm_num) fun m => Probe.Enc.XCyc8.no_model m

theorem rank4Extension_ten {α : Type*} : Rank4Extension α 10 :=
  Probe.Enc.rank4Extension_of_cert (by norm_num) fun m => Probe.Enc.XCyc10.no_model m

theorem rank4Extension_twelve {α : Type*} : Rank4Extension α 12 :=
  Probe.Enc.rank4Extension_of_cert (by norm_num) fun m => Probe.Enc.XCyc12.no_model m

theorem rank4Extension_of_fourteen_le {α : Type*} {N : ℕ} (hN : 14 ≤ N) : Rank4Extension α N :=
  Probe.Enc.rank4Extension_of_linCert (L := 14) (by norm_num) hN
    fun m => Probe.Enc.XLin14.no_model m

/-- **Divisible rank-4 KUM**: every uniformly dense rank-4 matroid on `4k` elements has a cyclic
basis ordering. -/
theorem solvesDivisibleKUMAtRank_four' {α : Type*} : SolvesDivisibleKUMAtRank α 4 :=
  solvesDivisibleKUMAtRank_four_of_extension fun k hk => by
    rcases (show k = 2 ∨ k = 3 ∨ 4 ≤ k by omega) with rfl | rfl | hk4
    · exact rank4Extension_eight
    · exact rank4Extension_twelve
    · exact rank4Extension_of_fourteen_le (by omega)

#print axioms rank4Extension_eight
#print axioms rank4Extension_ten
#print axioms rank4Extension_twelve
#print axioms rank4Extension_of_fourteen_le
#print axioms solvesDivisibleKUMAtRank_four'

end HigherRankKUM
