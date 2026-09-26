import Probe.EncH
import Probe.Kum10Data
import Probe.LRATChunked

/-!
The hitting lemma at `n = 14` (`k = 3`) with a 6-element set of rank 2 and no 9-element plane:
no rank model in which every basis leaves a dense-violating set exists.
-/

namespace Probe.Enc.Hit14Line

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option profiler true

lrat_refutation_chunked cert (include_str "../data/hit14line.cnf")
  (include_str "../data/hit14line.lrat") 150000

h_witnesses ws (include_str "../data/hit14line.wit")

theorem ws_valid : ws.all (validH 14 low14 (factsOfRanks [(63, 2)])) = true := by decide +kernel

theorem fmla_eq : (cert.fmla : List (List Sat.Literal)) = ws.map (genH 14) :=
  fmlaBEq_eq (by decide +kernel)

theorem no_model (m : RankModelH 14 low14 (factsOfRanks [(63, 2)])) : False :=
  no_modelH m cert.fmla cert.refute ws fmla_eq ws_valid

#print axioms no_model

end Probe.Enc.Hit14Line
