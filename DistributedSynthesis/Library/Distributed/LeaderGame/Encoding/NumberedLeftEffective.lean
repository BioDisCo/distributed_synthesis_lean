/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.NumberedLeftInitialBanks
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedPhysicalObjective

/-! Left-leader legality with generated physical annotation tables and
complete initial-bank search. The remaining uniformity task is the map
from raw numbered headers to this numeric compiler input; this module does
not assume that task solved. -/
noncomputable section
namespace Characterisation.NumberedLeftEffective
open DistributedSynthesis

variable {GQ : Type} {S B D K : Nat} [Fintype GQ] [DecidableEq GQ]
variable (o : EncodedRoundObjectives.Data)
variable (recognizer : Recognizer Graph GQ) [DecidablePred (· ∈ recognizer.accept)]
variable (graphs : GraphRootState GQ D K ≃ Fin S)
variable (header : NumberedLeaderHeader (GQ:=GQ) (d:=D) (K:=K) (B:=B)
  (C:=EncodedLeaderObjective.priorityBound o) (EncodedLeaderObjective.automaton o))
variable (bank : ClosingPlanBank (Fin header.1.val)
  (Fin (EncodedRoundObjectives.inputTwo o)) (Fin (EncodedRoundObjectives.inputOne o))
  (Fin (EncodedRoundObjectives.outputTwo o)) (Fin (EncodedRoundObjectives.outputOne o)) D)
variable (permitted : Finset (NumberedLeaderOutcome (GQ:=GQ) (d:=D) (K:=K) (B:=B)
  (C:=EncodedLeaderObjective.priorityBound o) (EncodedLeaderObjective.automaton o)))

local instance effectiveObjectiveStateDecidable : DecidableEq (EncodedLeaderObjective.automaton o).State :=
  inferInstanceAs (DecidableEq (Fin (EncodedRoundObjectives.stateCount o)))

def compilerInput : EncodedLeaderPhysical.Data :=
  NumberedLeftLocal.compilerData o (EncodedPhysicalObjective.environmentNumber o) (EncodedPhysicalObjective.outputNumber o)
    recognizer graphs (EncodedPhysicalObjective.compile o) header bank permitted

/-- The primitive recursive bank-search solver returns exactly the existing
numbered left-leader legality test. Physical transitions and priorities
are generated from the objective; neither is a correctness hypothesis. -/
theorem solve_eq_legal : EncodedInitialLeftLeaderBanks.solve (compilerInput o recognizer graphs header bank permitted) =
    numberedLeftLegal recognizer (EncodedLeaderObjective.automaton o) (EncodedLeaderObjective.rank o) header permitted :=
  NumberedLeftLocal.solveBanks_eq_legal o (EncodedPhysicalObjective.environmentNumber o) (EncodedPhysicalObjective.outputNumber o)
    recognizer graphs (EncodedPhysicalObjective.compile o) header bank permitted (EncodedLeaderObjective.rank o)
    (EncodedPhysicalObjective.transition o) (EncodedPhysicalObjective.priority o)

/-- The chosen seed bank does not affect the result of initial-bank search. -/
theorem seed_independent (otherBank : ClosingPlanBank (Fin header.1.val)
    (Fin (EncodedRoundObjectives.inputTwo o)) (Fin (EncodedRoundObjectives.inputOne o))
    (Fin (EncodedRoundObjectives.outputTwo o)) (Fin (EncodedRoundObjectives.outputOne o)) D) :
    EncodedInitialLeftLeaderBanks.solve (compilerInput o recognizer graphs header bank permitted) =
      EncodedInitialLeftLeaderBanks.solve (compilerInput o recognizer graphs header otherBank permitted) := by
  rw [solve_eq_legal,solve_eq_legal]

end Characterisation.NumberedLeftEffective
