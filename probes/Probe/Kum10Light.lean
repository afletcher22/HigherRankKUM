import Probe.Kum10Data
import Probe.LRATChunked

/-! KUM(4,10) in the strict t=0 class with no 6-plane and no 4-line: no rank model with the size
bounds `lightTab10` avoids every cyclic order. -/

namespace Probe.Enc.Light

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option profiler true

lrat_refutation_chunked cert (include_str "../data/kum10l.cnf") (include_str "../data/kum10l.lrat") 150000

f_witnesses ws (include_str "../data/kum10l.wit")

theorem ws_valid : ws.all (validF 10 lightTab10 []) = true := by decide +kernel

theorem fmla_eq : (cert.fmla : List (List Sat.Literal)) = ws.map (genF 10) :=
  fmlaBEq_eq (by decide +kernel)

theorem no_model (m : RankModelF 10 lightTab10 []) : False :=
  no_modelF m cert.fmla cert.refute ws fmla_eq ws_valid

#print axioms no_model

end Probe.Enc.Light
