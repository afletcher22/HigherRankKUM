import Probe.Enc

/-!
Round 1 of the encoding probe for the SAT claim `kum6` (rank-4 KUM on 6 elements): store the core
CNF and its kernel-checked refutation, store one witness per clause, and check by kernel
evaluation that the witnesses are side-condition valid and regenerate the CNF exactly.
-/

namespace Probe.Enc.Kum6

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option profiler true

lrat_refutation cert (include_str "../data/kum6.cnf") (include_str "../data/kum6.lrat")

clause_witnesses ws (include_str "../data/kum6.wit")

theorem ws_valid : ws.all (valid 6) = true := by decide +kernel

theorem fmla_eq : (cert.fmla : List (List Sat.Literal)) = ws.map (gen 6) :=
  fmlaBEq_eq (by decide +kernel)

#print axioms cert.refute
#print axioms fmla_eq

end Probe.Enc.Kum6
