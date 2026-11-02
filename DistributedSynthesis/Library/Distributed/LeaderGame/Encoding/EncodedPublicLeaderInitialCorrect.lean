/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedPublicLeaderInitial
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedPublicLeaderCorrect

/-! Initialization and solving of the assembled game. Only the finite graph
presentation, leader table, objective, and initial graph index are supplied;
the singleton public family and persistent-thread code are generated. -/
noncomputable section
namespace Characterisation.EncodedPublicLeaderGame
open DistributedSynthesis
variable {GQ : Type} {S B D K : Nat} [Fintype GQ] [DecidableEq GQ]
variable (o : EncodedRoundObjectives.Data)
variable (recognizer : Recognizer Graph GQ) [DecidablePred (· ∈ recognizer.accept)]
variable (graphs : GraphRootState GQ D K ≃ Fin S) (positive : 0 < B) (g : GraphRootState GQ D K)
local notation "M" => EncodedLeaderObjective.automaton o
local notation "rankBound" => EncodedLeaderObjective.priorityBound o
local instance publicInitialCorrectObjectiveEq : DecidableEq (M).State :=
  inferInstanceAs (DecidableEq (Fin (EncodedRoundObjectives.stateCount o)))
local notation "choice" => numberedInitialChoice (C:=rankBound) M positive g

/-- The initialized primitive-recursive solver equals the original public-game test. -/
theorem solveInitial_encode :
    solveInitial (EncodedHeaderCompiler.graphDataEncode (B:=B) recognizer graphs) (leaderTable graphs) o (graphs g).val =
      numberedLeaderGameTest recognizer M (EncodedLeaderObjective.rank o) choice.1
        (numberedGameInitialCode M (EncodedLeaderObjective.rank o) choice) := by
  unfold solveInitial
  rw [initialData_encode]
  exact solve_encode o recognizer graphs choice.1 (numberedGameInitialCode M (EncodedLeaderObjective.rank o) choice)

end Characterisation.EncodedPublicLeaderGame
