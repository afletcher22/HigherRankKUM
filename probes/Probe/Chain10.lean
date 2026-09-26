import Probe.Cert
import Probe.Kum10Data

/-! KUM(4,10) from a pair chain: no rank model on 10 positions in which the five sets
`P_i ∪ P_{i+1}` (`P_i = {2i, 2i+1}`, positions mod 10) are bases avoids every orientation of the
chain and of the chains obtained by re-splitting one window `P_x ∪ P_{x+1}` into two other pairs.
Certificate: `lean_witness_f.py chain10` (14.7k hints). -/

namespace Probe.Enc.Chain10

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option profiler true

/-- The five chain bases `P_i ∪ P_{i+1}` as facts `r(X) ≥ 4`. -/
def chainFacts10 : List (ℕ × ℕ × Bool) :=
  [(15, 4, true), (60, 4, true), (240, 4, true), (960, 4, true), (771, 4, true)]

f_certificate cert (include_str "../data/chain10.cnf") (include_str "../data/chain10.lrat")
  (include_str "../data/chain10.wit") (validF 10 [] chainFacts10) (genF 10) 100000 3000

theorem no_model (m : RankModelF 10 [] chainFacts10) : False :=
  no_modelF m cert.fmla cert.refute cert.ws cert.fmla_eq cert.ws_valid

#print axioms no_model

end Probe.Enc.Chain10
