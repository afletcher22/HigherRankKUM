import Probe.Cert
import Probe.Kum10Data

/-! The base lemma of Theorem G with `r(C) = 2`: no rank model of a uniformly dense rank-4 matroid
on 10 elements with the flat plane `{0..5}` and `r({6..9}) = 2` avoids every site order. -/

namespace Probe.Enc.BaseG2

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option profiler true

f_certificate cert (include_str "../data/baseG2.cnf") (include_str "../data/baseG2.lrat")
  (include_str "../data/baseG2.wit") (validF 10 densTab10 (factsOfRanks (ranksG 2))) (genF 10) 100000 3000

theorem no_model (m : RankModelF 10 densTab10 (factsOfRanks (ranksG 2))) : False :=
  no_modelF m cert.fmla cert.refute cert.ws cert.fmla_eq cert.ws_valid

#print axioms no_model

end Probe.Enc.BaseG2
