import Probe.Split.G4a

/-! Memory split of `Kum10BaseG4`, part 2: the witnesses and their side conditions. -/

namespace Probe.Enc.SplitG4

set_option maxHeartbeats 0
set_option maxRecDepth 100000

f_witnesses ws (include_str "../../data/baseG4.wit")

theorem ws_valid : ws.all (validF 10 densTab10 (factsOfRanks (ranksG 4))) = true := by
  decide +kernel

end Probe.Enc.SplitG4
