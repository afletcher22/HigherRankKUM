import Probe.Kum10Data
import Probe.LRATChunked

/-! The base lemma of Theorem G with `r(C) = 2`: no rank model of a uniformly dense rank-4 matroid
on 10 elements with the flat plane `{0..5}` and `r({6..9}) = 2` avoids every site order. -/

namespace Probe.Enc.BaseG2

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option profiler true

lrat_refutation_chunked cert (include_str "../data/baseG2.cnf") (include_str "../data/baseG2.lrat") 150000

f_witnesses ws (include_str "../data/baseG2.wit")

theorem ws_valid : ws.all (validF 10 densTab10 (factsOfRanks (ranksG 2))) = true := by decide +kernel

theorem fmla_eq : (cert.fmla : List (List Sat.Literal)) = ws.map (genF 10) :=
  fmlaBEq_eq (by decide +kernel)

theorem no_model (m : RankModelF 10 densTab10 (factsOfRanks (ranksG 2))) : False :=
  no_modelF m cert.fmla cert.refute ws fmla_eq ws_valid

#print axioms no_model

end Probe.Enc.BaseG2
