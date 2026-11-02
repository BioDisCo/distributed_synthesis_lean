/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLeaderGroups
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedJointPhaseObjective
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLeaderAlphabet

/-! Assemble the endless-phase compiler from observation-matrix rows and
carried objective states. Group counts and root assignments are generated,
not supplied as separate certificates. -/
namespace Characterisation.EncodedLeaderPhase
open DistributedSynthesis
attribute [local irreducible] Primrec

abbrev Data := EncodedRoundObjectives.Data × EncodedLeaderGroups.Data × List Nat
/-- True selects process one's rows; false selects process two's rows. -/
def headerGroups (header : EncodedLeaderAlphabet.Header) (one : Bool) : EncodedLeaderGroups.Data :=
  (header.1,bif one then header.2.1 else header.2.2.1)
def phaseData (d : Data) : EncodedJointPhaseObjective.Data :=
  (d.1,EncodedLeaderGroups.count d.2.1,d.2.2,EncodedLeaderGroups.assignment d.2.1)
def compile (d : Data) := EncodedJointPhaseObjective.compile (phaseData d)

theorem headerGroups_primrec : Primrec₂ headerGroups := (Primrec.fst.comp Primrec.fst).pair
  (Primrec.cond Primrec.snd (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
theorem phaseData_primrec : Primrec phaseData := Primrec.fst.pair
  ((EncodedLeaderGroups.count_primrec.comp (Primrec.fst.comp Primrec.snd)).pair
    ((Primrec.snd.comp Primrec.snd).pair (EncodedLeaderGroups.assignment_primrec.comp (Primrec.fst.comp Primrec.snd))))
theorem compile_primrec : Primrec compile := EncodedJointPhaseObjective.compile_primrec.comp phaseData_primrec

end Characterisation.EncodedLeaderPhase
