import Probe.Kum10Data
import Probe.LRATChunked

/-! Memory split of `Kum10BaseG4`, part 1: the LRAT refutation only. -/

namespace Probe.Enc.SplitG4

set_option maxHeartbeats 0
set_option maxRecDepth 100000

lrat_refutation_chunked cert (include_str "../../data/baseG4.cnf")
  (include_str "../../data/baseG4.lrat") 150000

end Probe.Enc.SplitG4
