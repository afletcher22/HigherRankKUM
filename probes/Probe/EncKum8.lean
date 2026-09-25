import Probe.Enc

/-!
Round 1 of the encoding probe for the SAT claim `kum8` (rank-4 KUM on 8 elements): store the core
CNF and its kernel-checked refutation, store one witness per clause, and check by kernel
evaluation that the witnesses are side-condition valid and regenerate the CNF exactly.
-/

namespace Probe.Enc.Kum8

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option profiler true

lrat_refutation cert (include_str "../data/kum8.cnf") (include_str "../data/kum8.lrat")

clause_witnesses ws (include_str "../data/kum8.wit")

theorem ws_valid : ws.all (valid 8) = true := by decide +kernel

theorem fmla_eq : (cert.fmla : List (List Sat.Literal)) = ws.map (gen 8) :=
  fmlaBEq_eq (by decide +kernel)

#print axioms cert.refute
#print axioms fmla_eq

end Probe.Enc.Kum8
