/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedHeaderCompiler
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.NumberedRightEffective
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.NumberedLeftEffective

/-! The raw header projections recover exactly the original carried graph
states, objective states, phase minima, and observation matrices. -/
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
local instance fieldsObjectiveDecidable : DecidableEq (M).State :=
  inferInstanceAs (DecidableEq (Fin (EncodedRoundObjectives.stateCount o)))

def graphDataEncode : GraphData :=
  (EncodedClosingScans.rulesEncode recognizer graphs,EncodedLeaderAnnotations.chosenGraphSteps recognizer graphs,
    List.ofFn (fun i => graphRootStop recognizer (graphs.symm i) .right),
    List.ofFn (fun i => graphRootStop recognizer (graphs.symm i) .left),D,B)
def dataEncode : Data :=
  (graphDataEncode (B:=B) recognizer graphs,o,EncodedLeaderAlphabet.headerEncode annNumber h,
    bankCode,EncodedGraphMemory.allowedEncode annNumber allowed)
local notation "input" => dataEncode o recognizer graphs h bankCode allowed
local notation "annData" => EncodedLeaderAnnotations.dataEncode (C:=rankBound)
  (N:=EncodedRoundObjectives.stateCount o) (V:=EncodedPhysicalObjective.outputs o)
  recognizer graphs env (EncodedPhysicalObjective.compile o)

theorem environmentGraphs_encode : environmentGraphs input =
    List.ofFn (fun i => (graphCode ((env).symm i).2.2).val) := by
  unfold environmentGraphs
  rw [EncodedHeaderTables.environments_encode]
  rw [List.map_ofFn]
  rfl

theorem annotations_encode : annotations input = annData := by
  unfold annotations
  rw [environmentGraphs_encode]
  rfl

theorem source_encode : source input =
    FiniteFunctionCodes.encode root (fun i => graphs (h.2.2 i).1.1) := by
  unfold source
  rw [annotations_encode]
  simp only [header,dataEncode,EncodedLeaderAlphabet.headerEncode,FiniteFunctionCodes.encode,
    List.map_ofFn,Function.comp_apply,Equiv.refl_symm,Equiv.refl_apply]
  apply congrArg List.ofFn
  funext i
  exact EncodedLeaderAnnotations.graphState_encode recognizer M graphs (Equiv.refl _) env
    (EncodedPhysicalObjective.compile o) (h.2.2 i)

theorem initial_encode : initial input =
    FiniteFunctionCodes.encode root (fun i => annNumber (resetLeaderMinimum M (h.2.2 i))) := by
  unfold initial
  rw [annotations_encode]
  simp only [header,dataEncode,EncodedLeaderAlphabet.headerEncode,FiniteFunctionCodes.encode,
    List.map_ofFn,Function.comp_apply,Equiv.refl_symm,Equiv.refl_apply]
  apply congrArg List.ofFn
  funext i
  exact EncodedLeaderAnnotations.reset_encode recognizer M graphs (Equiv.refl _) env
    (EncodedPhysicalObjective.compile o) (h.2.2 i)

theorem residuals_encode : residuals input = List.ofFn (fun i => ((h.2.2 i).1.2).val) := by
  unfold residuals
  rw [annotations_encode]
  simp only [header,dataEncode,EncodedLeaderAlphabet.headerEncode,FiniteFunctionCodes.encode,
    List.map_ofFn,Function.comp_apply,Equiv.refl_symm,Equiv.refl_apply]
  apply congrArg List.ofFn
  funext i
  exact EncodedLeaderAnnotations.objectiveState_encode recognizer M graphs (Equiv.refl _) env
    (EncodedPhysicalObjective.compile o) (h.2.2 i)

theorem advance_encode (one : Bool) : advance input one =
    FiniteFunctionCodes.encode graphs
      (fun q => graphs (chooseGraphRootNext recognizer q (bif one then .right else .left))) := by
  unfold advance
  apply FiniteSearch.tabulate_eq_ofFn
  intro i
  have entry := FiniteFunctionCodes.eval_encode
    (FiniteFunctionCodes.prod graphs EncodedClosingScans.graphNumber)
    (fun p => graphs (chooseGraphRootNext recognizer p.1 p.2))
    (graphs.symm i,bif one then .right else .left)
  have index : (FiniteFunctionCodes.prod graphs EncodedClosingScans.graphNumber
      (graphs.symm i,bif one then .right else .left)).val = i.val*3 + (bif one then 0 else 2) := by
    change (graphCode (bif one then .right else .left)).val + 3*(graphs (graphs.symm i)).val = _
    rw [Equiv.apply_symm_apply]
    cases one <;> simp only [cond_false,cond_true,graphCode] <;> omega
  exact (congrArg (fun j => (EncodedLeaderAnnotations.chosenGraphSteps recognizer graphs).getD j 0) index).symm.trans entry

theorem phase_encode (one : Bool) : phase input one =
    ((bif one then o else EncodedRoleExchange.swap o),
      EncodedLeaderGroups.dataEncode root h.2.1 (bif one then .one else .two),
      List.ofFn (fun i => ((h.2.2 i).1.2).val)) := by
  unfold phase
  rw [residuals_encode]
  cases one <;> rfl

end Characterisation.EncodedHeaderCompiler
