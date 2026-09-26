import Probe.Split.G4b

/-! Memory split of `Kum10BaseG4`, part 3: the regenerated formula. -/

namespace Probe.Enc.SplitG4

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem fmla_eq : (cert.fmla : List (List Sat.Literal)) = ws.map (genF 10) :=
  fmlaBEq_eq (by decide +kernel)

theorem no_model (m : RankModelF 10 densTab10 (factsOfRanks (ranksG 4))) : False :=
  no_modelF m cert.fmla cert.refute ws fmla_eq ws_valid

#print axioms no_model

end Probe.Enc.SplitG4
