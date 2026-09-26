import Probe.Cert
import Probe.Kum10Data

/-! KUM(4,10) in the strict t=0 class with no 6-plane and no 4-line: no rank model with the size
bounds `lightTab10` avoids every cyclic order. -/

namespace Probe.Enc.Light

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option profiler true

f_certificate cert (include_str "../data/kum10l.cnf") (include_str "../data/kum10l.lrat")
  (include_str "../data/kum10l.wit") (validF 10 lightTab10 []) (genF 10) 100000 3000

theorem no_model (m : RankModelF 10 lightTab10 []) : False :=
  no_modelF m cert.fmla cert.refute cert.ws cert.fmla_eq cert.ws_valid

#print axioms no_model

end Probe.Enc.Light
