import Probe.Cert
import Probe.Kum10Data

/-! The hitting lemma at `n = 14` (`k = 3`) with a 6-element set of rank 2 and no 9-element plane:
no rank model in which every basis leaves a dense-violating set exists. -/

namespace Probe.Enc.Hit14Line

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option profiler true

h_certificate cert (include_str "../data/hit14line.cnf") (include_str "../data/hit14line.lrat")
  (include_str "../data/hit14line.wit") (validH 14 low14 (factsOfRanks [(63, 2)])) (genH 14) 100000 3000

theorem no_model (m : RankModelH 14 low14 (factsOfRanks [(63, 2)])) : False :=
  no_modelH m cert.fmla cert.refute cert.ws cert.fmla_eq cert.ws_valid

#print axioms no_model

end Probe.Enc.Hit14Line
