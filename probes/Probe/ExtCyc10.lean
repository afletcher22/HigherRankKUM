import Probe.ExtEnc

/-!
The cyclic extension certificate for `N = 10` (14 positions): no rank model of a rank-4 matroid
with a basis `S` and a 10-element cyclic ordering of the rest (all 4-windows bases) avoids a
successful interleaving.
-/

namespace Probe.Enc.XCyc10

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option profiler true

lrat_refutation cert (include_str "../data/xcyc10.cnf") (include_str "../data/xcyc10.lrat")

ext_witnesses ws (include_str "../data/xcyc10.wit")

theorem ws_valid : ws.all (validX 14 true (basesCyc 10)) = true := by decide +kernel

theorem fmla_eq : (cert.fmla : List (List Sat.Literal)) = ws.map (genX true) :=
  fmlaBEq_eq (by decide +kernel)

theorem no_model (m : RankModelX 14 true (basesCyc 10)) : False :=
  no_modelX m cert.fmla cert.refute ws fmla_eq ws_valid

#print axioms no_model

end Probe.Enc.XCyc10
