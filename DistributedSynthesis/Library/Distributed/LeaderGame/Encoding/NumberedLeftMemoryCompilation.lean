/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLeftGraphMemoryRun
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.NumberedGraphMemoryCompilation
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.NumberedCollectorCompilation

/-! Specialize generated memory tables to the actual numbered left-leader
header. Annotation updates are generated from the supplied physical
objective, with the original reset minima and chosen graph transitions. -/
namespace Characterisation
open DistributedSynthesis
local instance numberedLeftMemoryLetterBEq : BEq EncodedGraphMemory.Letter := instBEqOfDecidableEq

variable {GQ I₁ I₂ O₁ O₂ : Type} {E V N₁ N₂ P₁ P₂ S N B C d K : Nat}
variable [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂] [Fintype GQ]
variable [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂] [DecidableEq GQ]
variable (env : (I₁ × I₂ × Graph) ≃ Fin E)
variable (one : I₁ ≃ Fin N₁) (two : I₂ ≃ Fin N₂)
variable (output : (O₁ × O₂) ≃ Fin V) (outOne : O₁ ≃ Fin P₁) (outTwo : O₂ ≃ Fin P₂)
variable (recognizer : Recognizer Graph GQ) [DecidablePred (· ∈ recognizer.accept)]
variable (objective : DetParityAutomaton (ContinuationLetter I₁ I₂ O₁ O₂)) [DecidableEq objective.State]
variable (graphNumber : GraphRootState GQ d K ≃ Fin S) (objectiveNumber : objective.State ≃ Fin N)
variable (objectiveData : EncodedParityTables.Data) (rank : objective.State → Fin (C+1))
variable (transition : ∀ q r o, EncodedParityTables.next objectiveData (objectiveNumber q).val
  ((env r).val*V+(output o).val) = (objectiveNumber (objective.step q (r,o))).val)
variable (priority : ∀ q, EncodedParityTables.priority objectiveData (objectiveNumber q).val = (rank q).val)

variable (header : NumberedLeaderHeader (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)
variable (bank : ClosingPlanBank (Fin header.1.val) I₂ I₁ O₂ O₁ d)

noncomputable def numberedLeftMemoryData : EncodedGraphMemory.Data :=
  EncodedLeftGraphMemory.dataEncode (Equiv.refl _) env one two output outOne outTwo
    (leaderAnnotationNumber objective graphNumber objectiveNumber) header.2.1 recognizer graphNumber
    (fun q => chooseGraphRootNext recognizer q .left) (fun i => (header.2.2 i).1.1)
    (fun i => resetLeaderMinimum objective (header.2.2 i)) bank
    (EncodedLeaderAnnotations.compile
      (EncodedLeaderAnnotations.dataEncode (C:=C) (N:=N) (V:=V) recognizer graphNumber env objectiveData) (E*V))
    (numberedLeaderSlot objective header) (fun q => q.2 ())

local notation "data" => numberedLeftMemoryData env one two output outOne outTwo recognizer objective graphNumber objectiveNumber objectiveData header bank
local notation "annNumber" => leaderAnnotationNumber (C:=C) objective graphNumber objectiveNumber
local notation "annData" => EncodedLeaderAnnotations.dataEncode (C:=C) (N:=N) (V:=V) recognizer graphNumber env objectiveData
local notation "Memory" => GraphLeaderMemory (Fin (Fin.val (Sigma.fst header))) GQ
  (LeaderAnnotation (GQ:=GQ) (d:=d) (K:=K) (C:=C) objective) I₂ I₁ O₂ O₁ d K
local notation "encode" => EncodedGraphMemory.stateEncode (Equiv.refl (Fin (Fin.val (Sigma.fst header)))) (EncodedBankRoleExchange.environment env) (EncodedBankRoleExchange.output output) annNumber graphNumber
local notation "group" => shapeLeaderGroup (Prod.fst (Sigma.snd header)) Proc.two
local notation "letterCode" => EncodedGraphMemory.letterEncode (Equiv.refl (Fin (Fin.val (Sigma.fst header)))) (EncodedBankRoleExchange.environment env) (EncodedBankRoleExchange.output output) group

omit [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂] [DecidableEq I₁] [DecidableEq I₂]
    [DecidableEq O₁] [DecidableEq O₂] [DecidableEq objective.State] in
theorem numberedLeftMemory_initial : EncodedGraphMemory.initial data =
    encode (((fun i => (header.2.2 i).1.1),(fun _ => true),
      (fun i => resetLeaderMinimum objective (header.2.2 i))),bank,true) :=
  EncodedLeftGraphMemory.initial_encode (Equiv.refl _) env one two output outOne outTwo annNumber header.2.1
    recognizer graphNumber _ _ _ bank _ (numberedLeaderSlot objective header) (fun q => q.2 ())

include transition priority in
/-- The actual numbered guard is the endless physical phase objective
together with the generated checks on the generated memory run. -/
theorem numberedLeftGuard_generated_checks
    (permitted : Finset (NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective))
    (play : Nat → RealizedBlockRound I₁ I₂ (RollingReceiverOutput (Fin header.1.val) I₂ I₁ O₂ O₁ d)
      (ShapeLeaderGroup header.2.1 .two → O₂)) :
    (numberedLeftGuard recognizer objective rank header permitted bank).WinsPlay play ↔
      (jointPhaseObjective (objective.comap exchangeLetter) (fun i => (header.2.2 i).1.2) group).WinsPlay
        (phasePhysicalPlay Prod.fst play) ∧
      ∀ n, EncodedLeftGraphMemory.readCheck data (EncodedGraphMemory.allowedEncode annNumber permitted)
        (phaseMemoryRun (EncodedGraphMemory.start data) (EncodedGraphMemory.readNext data)
          (fun n => letterCode (play n)) n) (letterCode (play n)) = true := by
  apply (numberedLeftGuard_wins_iff_fused recognizer objective rank header permitted bank play).trans
  exact EncodedLeftGraphMemory.guard_wins_iff (Equiv.refl _) env one two output outOne outTwo annNumber header.2.1
    recognizer graphNumber (fun q => chooseGraphRootNext recognizer q .left)
    (fun i => (header.2.2 i).1.1) (fun i => resetLeaderMinimum objective (header.2.2 i))
    bank _ (numberedLeaderSlot objective header) (fun q => q.2 ())
    (numberedAnnotation_size env recognizer objective graphNumber objectiveNumber objectiveData)
    (leaderAnnotationStep recognizer objective rank)
    (EncodedLeaderAnnotations.compile_encode recognizer objective graphNumber objectiveNumber env output objectiveData rank transition priority)
    group permitted _ play

end Characterisation
