import Probe.ExtBridge
import Probe.ExtCyc8
import Probe.ExtCyc10
import Probe.ExtCyc12

/-! The rank-4 extension theorem on 8, 10 and 12 elements, from kernel-checked certificates. -/

namespace HigherRankKUM

theorem rank4Extension_eight {α : Type*} : Rank4Extension α 8 :=
  Probe.Enc.rank4Extension_of_cert (by norm_num) fun m => Probe.Enc.XCyc8.no_model m

theorem rank4Extension_ten {α : Type*} : Rank4Extension α 10 :=
  Probe.Enc.rank4Extension_of_cert (by norm_num) fun m => Probe.Enc.XCyc10.no_model m

theorem rank4Extension_twelve {α : Type*} : Rank4Extension α 12 :=
  Probe.Enc.rank4Extension_of_cert (by norm_num) fun m => Probe.Enc.XCyc12.no_model m

#print axioms rank4Extension_eight
#print axioms rank4Extension_ten
#print axioms rank4Extension_twelve

end HigherRankKUM
