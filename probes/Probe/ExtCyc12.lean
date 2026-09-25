import Probe.ExtEnc

/-!
The cyclic extension certificate for `N = 12` (16 positions): no rank model of a rank-4 matroid
with a basis `S` and a 12-element cyclic ordering of the rest (all 4-windows bases) avoids a
successful interleaving.
-/

namespace Probe.Enc.XCyc12

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option profiler true

lrat_refutation cert (include_str "../data/xcyc12.cnf") (include_str "../data/xcyc12.lrat")

ext_witnesses ws (include_str "../data/xcyc12.wit")

theorem ws_valid : ws.all (validX 16 true (basesCyc 12)) = true := by decide +kernel

theorem fmla_eq : (cert.fmla : List (List Sat.Literal)) = ws.map (genX true) :=
  fmlaBEq_eq (by decide +kernel)

theorem no_model (m : RankModelX 16 true (basesCyc 12)) : False :=
  no_modelX m cert.fmla cert.refute ws fmla_eq ws_valid

#print axioms no_model

end Probe.Enc.XCyc12
