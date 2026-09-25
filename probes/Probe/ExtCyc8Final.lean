import Probe.ExtBridge
import Probe.ExtCyc8

/-! The rank-4 extension theorem on 8 elements, from its kernel-checked certificate. -/

namespace HigherRankKUM

theorem rank4Extension_eight {α : Type*} : Rank4Extension α 8 :=
  Probe.Enc.rank4Extension_of_cert (by norm_num) fun m => Probe.Enc.XCyc8.no_model m

#print axioms rank4Extension_eight

end HigherRankKUM
