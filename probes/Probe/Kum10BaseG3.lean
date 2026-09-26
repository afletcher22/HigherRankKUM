import Probe.Cert
import Probe.Kum10Data

/-! The base lemma of Theorem G with `r(C) = 3`. -/

namespace Probe.Enc.BaseG3

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option profiler true

f_certificate cert (include_str "../data/baseG3.cnf") (include_str "../data/baseG3.lrat")
  (include_str "../data/baseG3.wit") (validF 10 densTab10 (factsOfRanks (ranksG 3))) (genF 10) 100000 3000

theorem no_model (m : RankModelF 10 densTab10 (factsOfRanks (ranksG 3))) : False :=
  no_modelF m cert.fmla cert.refute cert.ws cert.fmla_eq cert.ws_valid

#print axioms no_model

end Probe.Enc.BaseG3
