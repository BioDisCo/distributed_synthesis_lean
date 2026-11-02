/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedHeaderCompilerFields
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.NumberedRightEffective
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.NumberedLeftEffective

/-! Exact assembly of both original local compiler inputs from raw header codes. -/
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
local instance compilerCorrectObjectiveDecidable : DecidableEq (M).State :=
  inferInstanceAs (DecidableEq (Fin (EncodedRoundObjectives.stateCount o)))

local notation "input" => dataEncode o recognizer graphs h bankCode allowed
local notation "annData" => EncodedLeaderAnnotations.dataEncode (C:=rankBound)
  (N:=EncodedRoundObjectives.stateCount o) (V:=EncodedPhysicalObjective.outputs o)
  recognizer graphs env (EncodedPhysicalObjective.compile o)

variable (bank : ClosingPlanBank (Fin h.1.val)
  (Fin (EncodedRoundObjectives.inputOne o)) (Fin (EncodedRoundObjectives.inputTwo o))
  (Fin (EncodedRoundObjectives.outputOne o)) (Fin (EncodedRoundObjectives.outputTwo o)) D)

theorem scheduled_encode (code : bankCode = EncodedClosingBanks.bankEncode root env out bank) :
    scheduled input =
      (EncodedGraphCollector.dataEncode root env (Equiv.refl _) (Equiv.refl _) out (Equiv.refl _) (Equiv.refl _)
        annNumber h.2.1 bank (fun i => resetLeaderMinimum M (h.2.2 i))
        (EncodedLeaderAnnotations.compile annData (EncodedPhysicalObjective.alphabet o))
        recognizer graphs (fun i => (h.2.2 i).1.1) true (numberedLeaderSlot M h) (fun q => q.2 ())
        (fun _ => true)).1 := by
  have slots : List.range h.1.val = FiniteFunctionCodes.encode root (numberedLeaderSlot M h) := by
    simpa only [List.map_id_fun] using
      (FiniteSearch.tabulate_eq_ofFn id (fun i : Fin h.1.val => i.val) (fun _ => rfl) :
        (List.range h.1.val).map id = FiniteFunctionCodes.encode root (numberedLeaderSlot M h))
  have minima : EncodedLeaderAnnotations.minima annData =
      FiniteFunctionCodes.encode annNumber (fun q => q.2 ()) :=
    EncodedLeaderAnnotations.minima_encode (C:=rankBound) (V:=EncodedPhysicalObjective.outputs o)
      recognizer M graphs (Equiv.refl _) env (EncodedPhysicalObjective.compile o)
  unfold scheduled
  rw [annotations_encode,initial_encode,environmentGraphs_encode,source_encode]
  change ((EncodedHeaderTables.bankData o (EncodedLeaderAlphabet.headerEncode annNumber h) (D+1),
    bankCode,_,_,_),List.range h.1.val,EncodedLeaderAnnotations.minima annData,_,[],true,B) = _
  rw [EncodedHeaderTables.bankData_encode,code,slots,minima]
  rfl

theorem compile_right_encode :
    compile (dataEncode o recognizer graphs h (EncodedClosingBanks.bankEncode root env out bank) allowed) true =
      NumberedRightEffective.compilerInput o recognizer graphs h bank allowed := by
  unfold compile
  rw [phase_encode]
  unfold memory originalMemory
  rw [scheduled_encode o recognizer graphs h _ allowed bank rfl,advance_encode]
  rfl

theorem compile_left_encode (leftBank : ClosingPlanBank (Fin h.1.val)
    (Fin (EncodedRoundObjectives.inputTwo o)) (Fin (EncodedRoundObjectives.inputOne o))
    (Fin (EncodedRoundObjectives.outputTwo o)) (Fin (EncodedRoundObjectives.outputOne o)) D) :
    compile (dataEncode o recognizer graphs h
      (EncodedClosingBanks.bankEncode root (EncodedBankRoleExchange.environment env)
        (EncodedBankRoleExchange.output out) leftBank) allowed) false =
      NumberedLeftEffective.compilerInput o recognizer graphs h leftBank allowed := by
  unfold compile
  rw [phase_encode]
  unfold memory originalMemory
  rw [scheduled_encode o recognizer graphs h _ allowed (fun i => exchangePlan (leftBank i))
    (EncodedBankRoleExchange.bankEncode_unexchange root env out leftBank).symm,advance_encode]
  rfl

end Characterisation.EncodedHeaderCompiler
