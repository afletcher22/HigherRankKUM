import Probe.EncSound
import Probe.EncKum6

/-!
Round 2 for `kum6`: combining the kernel-checked refutation with the witness checks and the
semantic soundness of every clause rule, no rank model on 6 elements exists.  The remaining step
(round 3) builds a rank model from any uniformly dense rank-4 matroid on 6 elements that has no
cyclic basis ordering.
-/

namespace Probe.Enc.Kum6

theorem no_rank_model (m : RankModel 6) : False :=
  no_model m cert.fmla cert.refute ws fmla_eq ws_valid

#print axioms no_rank_model

end Probe.Enc.Kum6
