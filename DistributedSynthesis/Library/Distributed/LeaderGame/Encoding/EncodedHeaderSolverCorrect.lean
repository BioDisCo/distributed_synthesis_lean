/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedHeaderCompilerCorrect
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedHeaderSolver
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.NumberedRightEffective
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.NumberedLeftEffective

/-! The primitive recursive raw-header test equals each original local
legality predicate. No initial bank or semantic memory tables are inputs. -/
noncomputable section
namespace Characterisation.EncodedHeaderCompiler
open DistributedSynthesis

variable {GQ : Type} {S B D K : Nat} [Fintype GQ] [DecidableEq GQ]
variable (o : EncodedRoundObjectives.Data)
variable (recognizer : Recognizer Graph GQ) [DecidablePred (· ∈ recognizer.accept)]
variable (graphs : GraphRootState GQ D K ≃ Fin S)
variable (h : NumberedLeaderHeader (GQ:=GQ) (d:=D) (K:=K) (B:=B)
  (C:=EncodedLeaderObjective.priorityBound o) (EncodedLeaderObjective.automaton o))
variable (bankCode : EncodedClosingBanks.Bank)
variable (allowed : Finset (NumberedLeaderOutcome (GQ:=GQ) (d:=D) (K:=K) (B:=B)
  (C:=EncodedLeaderObjective.priorityBound o) (EncodedLeaderObjective.automaton o)))
local notation "M" => EncodedLeaderObjective.automaton o
local notation "rankBound" => EncodedLeaderObjective.priorityBound o
local notation "env" => EncodedPhysicalObjective.environmentNumber o
local notation "out" => EncodedPhysicalObjective.outputNumber o
local notation "root" => Equiv.refl (Fin (Fin.val (Sigma.fst h)))
local notation "annNumber" => leaderAnnotationNumber (C:=rankBound) M graphs (Equiv.refl _)
local instance headerSolverCorrectObjectiveDecidable : DecidableEq (M).State :=
  inferInstanceAs (DecidableEq (Fin (EncodedRoundObjectives.stateCount o)))

def questionEncode : Question :=
  (graphDataEncode (B:=B) recognizer graphs,o,EncodedLeaderAlphabet.headerEncode annNumber h,
    EncodedGraphMemory.allowedEncode annNumber allowed)

/-- All tables depending on the specification and header are generated. The
only fixed presentation is the finite graph context of the adversary. -/
theorem test_right_eq_legal : test (questionEncode o recognizer graphs h allowed) true =
    numberedRightLegal recognizer M (EncodedLeaderObjective.rank o) h allowed := by
  let initialBank : ClosingPlanBank (Fin h.1.val)
      (Fin (EncodedRoundObjectives.inputOne o)) (Fin (EncodedRoundObjectives.inputTwo o))
      (Fin (EncodedRoundObjectives.outputOne o)) (Fin (EncodedRoundObjectives.outputTwo o)) D :=
    fun _ _ => (⟨0,Nat.succ_pos _⟩,⟨0,Nat.succ_pos _⟩)
  rw [questionEncode,test_eq_solve _ _ _ _ (EncodedClosingBanks.bankEncode root env out initialBank)]
  change EncodedInitialLeaderBanks.solve
    (compile (dataEncode o recognizer graphs h (EncodedClosingBanks.bankEncode root env out initialBank) allowed) true) = _
  rw [compile_right_encode]
  exact NumberedRightEffective.solve_eq_legal o recognizer graphs h initialBank allowed

theorem test_left_eq_legal : test (questionEncode o recognizer graphs h allowed) false =
    numberedLeftLegal recognizer M (EncodedLeaderObjective.rank o) h allowed := by
  let initialBank : ClosingPlanBank (Fin h.1.val)
      (Fin (EncodedRoundObjectives.inputTwo o)) (Fin (EncodedRoundObjectives.inputOne o))
      (Fin (EncodedRoundObjectives.outputTwo o)) (Fin (EncodedRoundObjectives.outputOne o)) D :=
    fun _ _ => (⟨0,Nat.succ_pos _⟩,⟨0,Nat.succ_pos _⟩)
  rw [questionEncode,test_eq_solve _ _ _ _ (EncodedClosingBanks.bankEncode root
    (EncodedBankRoleExchange.environment env) (EncodedBankRoleExchange.output out) initialBank)]
  change EncodedInitialLeftLeaderBanks.solve
    (compile (dataEncode o recognizer graphs h (EncodedClosingBanks.bankEncode root
      (EncodedBankRoleExchange.environment env) (EncodedBankRoleExchange.output out) initialBank) allowed) false) = _
  rw [compile_left_encode]
  exact NumberedLeftEffective.solve_eq_legal o recognizer graphs h initialBank allowed

end Characterisation.EncodedHeaderCompiler
