import Probe.Cert
import Probe.Kum10Data

/-! The choice lemma of Theorem G at `k = 3`: with a 9-element plane split into the bases `{0,1,2}`,
`{3,4,5}`, `{6,7,8}`, no rank model in which every basis leaves a dense-violating set exists. -/

namespace Probe.Enc.Hit14G

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option profiler true

h_certificate cert (include_str "../data/hit14g.cnf") (include_str "../data/hit14g.lrat")
  (include_str "../data/hit14g.wit") (validH 14 lowG14 (factsOfRanks [(511, 3), (7, 3), (56, 3), (448, 3)])) (genH 14) 100000 3000

theorem no_model (m : RankModelH 14 lowG14 (factsOfRanks [(511, 3), (7, 3), (56, 3), (448, 3)])) : False :=
  no_modelH m cert.fmla cert.refute cert.ws cert.fmla_eq cert.ws_valid

#print axioms no_model

end Probe.Enc.Hit14G
