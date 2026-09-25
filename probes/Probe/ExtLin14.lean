import Probe.ExtEnc

/-!
The linear extension certificate for `L = 14` (18 positions): no rank model of a rank-4 matroid
with a basis `S` and 14 elements `e_0, …, e_13` (all linear 4-windows bases) avoids a
successful interleaving that starts with `e_0, e_1, e_2` and ends with `e_11, e_12, e_13`.
-/

namespace Probe.Enc.XLin14

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option profiler true

lrat_refutation cert (include_str "../data/xlin14.cnf") (include_str "../data/xlin14.lrat")

ext_witnesses ws (include_str "../data/xlin14.wit")

theorem ws_valid : ws.all (validX 18 false (basesLin 14)) = true := by decide +kernel

theorem fmla_eq : (cert.fmla : List (List Sat.Literal)) = ws.map (genX false) :=
  fmlaBEq_eq (by decide +kernel)

theorem no_model (m : RankModelX 18 false (basesLin 14)) : False :=
  no_modelX m cert.fmla cert.refute ws fmla_eq ws_valid

#print axioms no_model

end Probe.Enc.XLin14
