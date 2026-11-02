/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLeaderPhysicalAlphabet
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLeaderPhaseCorrect
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.NumberedGraphMemoryCompilation
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.LocalLeaderOutputEquivalence

/-! Assemble the physical compiler input for the existing numbered right
leader. The header supplies the original observation shape and carried
objective states. Its bank, annotations and closing restrictions use the
already checked concrete graph-memory construction. -/
namespace Characterisation.NumberedRightLocal
open DistributedSynthesis

variable {GQ : Type} {E V S B C D K : Nat} [Fintype GQ] [DecidableEq GQ]
variable (o : EncodedRoundObjectives.Data)
local notation "M" => EncodedLeaderObjective.automaton o
local notation "I₁" => Fin (EncodedRoundObjectives.inputOne o)
local notation "I₂" => Fin (EncodedRoundObjectives.inputTwo o)
local notation "O₁" => Fin (EncodedRoundObjectives.outputOne o)
local notation "O₂" => Fin (EncodedRoundObjectives.outputTwo o)
variable (env : ((Fin (EncodedRoundObjectives.inputOne o)) × (Fin (EncodedRoundObjectives.inputTwo o)) × Graph) ≃ Fin E) (output : ((Fin (EncodedRoundObjectives.outputOne o)) × (Fin (EncodedRoundObjectives.outputTwo o))) ≃ Fin V)
variable (recognizer : Recognizer Graph GQ) [DecidablePred (· ∈ recognizer.accept)]
variable (graphs : GraphRootState GQ D K ≃ Fin S) (objectiveData : EncodedParityTables.Data)
variable (header : NumberedLeaderHeader (GQ:=GQ) (d:=D) (K:=K) (B:=B) (C:=C) (EncodedLeaderObjective.automaton o))
variable (bank : ClosingPlanBank (Fin header.1.val) (Fin (EncodedRoundObjectives.inputOne o)) (Fin (EncodedRoundObjectives.inputTwo o)) (Fin (EncodedRoundObjectives.outputOne o)) (Fin (EncodedRoundObjectives.outputTwo o)) D)
variable (permitted : Finset (NumberedLeaderOutcome (GQ:=GQ) (d:=D) (K:=K) (B:=B) (C:=C) (EncodedLeaderObjective.automaton o)))

local notation "root" => Equiv.refl (Fin (Fin.val (Sigma.fst header)))
local notation "shape" => Prod.fst (Sigma.snd header)
local notation "group" => shapeLeaderGroup shape Proc.one
local notation "groupNumber" => EncodedLeaderGroups.number root shape Proc.one
local notation "residuals" => fun i => Prod.snd (Prod.fst ((Prod.snd (Sigma.snd header)) i))
local notation "annNumber" => leaderAnnotationNumber (C:=C) M graphs (Equiv.refl _)

noncomputable def compilerData : EncodedLeaderPhysical.Data :=
  ((o,EncodedLeaderGroups.dataEncode root shape .one,List.ofFn (fun i => (residuals i).val)),
    numberedRightMemoryData env (Equiv.refl _) (Equiv.refl _) output (Equiv.refl _) (Equiv.refl _)
      recognizer M graphs (Equiv.refl _) objectiveData header bank,
    EncodedGraphMemory.allowedEncode annNumber permitted)

local notation "input" => compilerData o env output recognizer graphs objectiveData header bank permitted

theorem phase_eq : EncodedLeaderPhysical.phase input =
    EncodedJointPhaseObjective.dataEncode o root groupNumber residuals group :=
  EncodedLeaderPhase.phaseData_encode o root shape residuals

theorem bank_eq : EncodedGraphMemory.bankData (EncodedLeaderPhysical.memory input) =
    EncodedClosingBanks.dataEncode root env (Equiv.refl _) (Equiv.refl _) output
      (Equiv.refl _) (Equiv.refl _) shape (D+1) := rfl

theorem outputs_eq : EncodedGraphMemory.outputs (EncodedLeaderPhysical.memory input) = V := rfl

/-- The initial name is in the generated memory carrier. This discharges
the normalization hypothesis of the assembled safety compiler. -/
theorem start_lt : EncodedGraphMemory.start (EncodedLeaderPhysical.memory input) <
    (EncodedGraphMemory.states (EncodedLeaderPhysical.memory input)).length := by
  classical
  let initial : GraphLeaderMemory (Fin header.1.val) GQ
      (LeaderAnnotation (GQ:=GQ) (d:=D) (K:=K) (C:=C) M) I₁ I₂ O₁ O₂ D K := (((fun i => (header.2.2 i).1.1),(fun _ => true),
    (fun i => resetLeaderMinimum M (header.2.2 i))),bank,true)
  have bound := (EncodedGraphMemory.stateNumber root env (Equiv.refl _) (Equiv.refl _) output
    (Equiv.refl _) (Equiv.refl _) annNumber shape recognizer graphs
    (fun q => chooseGraphRootNext recognizer q .right) (fun i => (header.2.2 i).1.1)
    (fun i => resetLeaderMinimum M (header.2.2 i)) bank _ (numberedLeaderSlot M header) (fun q => q.2 ())
    (numberedAnnotation_size (V:=V) env recognizer M graphs (Equiv.refl _) objectiveData) initial).isLt
  rw [EncodedGraphMemory.stateNumber_val] at bound
  unfold EncodedGraphMemory.start
  dsimp only [EncodedLeaderPhysical.memory,compilerData]
  rw [numberedRightMemory_initial env (Equiv.refl _) (Equiv.refl _) output (Equiv.refl _) (Equiv.refl _)
    recognizer M graphs (Equiv.refl _) objectiveData header bank]
  exact bound

noncomputable def receiverNumber := EncodedLeaderPhysical.receiverNumber o root groupNumber residuals group
  env output shape input (phase_eq o env output recognizer graphs objectiveData header bank permitted)
    (bank_eq o env output recognizer graphs objectiveData header bank permitted)
    (outputs_eq o env output recognizer graphs objectiveData header bank permitted)
noncomputable def senderNumber := EncodedLeaderPhysical.senderNumber o root groupNumber residuals group
  input (phase_eq o env output recognizer graphs objectiveData header bank permitted)

abbrev OriginalRound := RealizedBlockRound I₂ I₁
  (RollingReceiverOutput (Fin header.1.val) I₁ I₂ O₁ O₂ D) (ShapeLeaderGroup shape .one → O₁)

/-- Input alphabets are unchanged; only outputs are numbered. -/
noncomputable def number (a : OriginalRound o header) : EncodedLeaderPhysical.PhysicalRound input :=
  mapBlockOutputs (receiverNumber o env output recognizer graphs objectiveData header bank permitted)
    (senderNumber o env output recognizer graphs objectiveData header bank permitted) a

theorem number_eq (a : OriginalRound o header) : number o env output recognizer graphs objectiveData header bank permitted a =
    EncodedLeaderPhysical.roundNumber o root groupNumber residuals group env output shape input
      (phase_eq o env output recognizer graphs objectiveData header bank permitted)
      (bank_eq o env output recognizer graphs objectiveData header bank permitted)
      (outputs_eq o env output recognizer graphs objectiveData header bank permitted) a := by
  apply Prod.ext
  · apply Prod.ext <;> apply Fin.ext <;> rfl
  · rfl

theorem phaseLetter_number (a : OriginalRound o header) :
    EncodedLeaderPhysical.phaseLetter input (EncodedLeaderPhysical.roundCode input
      (number o env output recognizer graphs objectiveData header bank permitted a)) =
      EncodedJointPhaseObjective.encode o root groupNumber (a.1,a.2.1.1,a.2.2) := by
  rw [number_eq]
  exact EncodedLeaderPhysical.phaseLetter_number o root groupNumber residuals group env output shape input
    (phase_eq o env output recognizer graphs objectiveData header bank permitted)
    (bank_eq o env output recognizer graphs objectiveData header bank permitted)
    (outputs_eq o env output recognizer graphs objectiveData header bank permitted) a

theorem memoryLetter_number (a : OriginalRound o header) :
    EncodedLeaderPhysical.memoryLetter input (EncodedLeaderPhysical.roundCode input
      (number o env output recognizer graphs objectiveData header bank permitted a)) =
      EncodedGraphMemory.letterEncode root env output group a := by
  rw [number_eq]
  exact EncodedLeaderPhysical.memoryLetter_number o root groupNumber residuals group env output shape input
    (phase_eq o env output recognizer graphs objectiveData header bank permitted)
    (bank_eq o env output recognizer graphs objectiveData header bank permitted)
    (outputs_eq o env output recognizer graphs objectiveData header bank permitted) a

end Characterisation.NumberedRightLocal
