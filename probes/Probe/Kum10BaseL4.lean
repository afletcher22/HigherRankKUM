import Probe.Cert
import Probe.Kum10Data

/-! The base lemma of Theorem L4: no rank model of a uniformly dense rank-4 matroid on 10 elements
with the flat line `{0..3}` avoids every site order. -/

namespace Probe.Enc.BaseL4

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option profiler true

f_certificate cert (include_str "../data/baseL4.cnf") (include_str "../data/baseL4.lrat")
  (include_str "../data/baseL4.wit") (validF 10 densTab10 (factsOfRanks ranksL4)) (genF 10) 100000 3000

theorem no_model (m : RankModelF 10 densTab10 (factsOfRanks ranksL4)) : False :=
  no_modelF m cert.fmla cert.refute cert.ws cert.fmla_eq cert.ws_valid

#print axioms no_model

end Probe.Enc.BaseL4
