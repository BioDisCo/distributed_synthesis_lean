/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.NumberedRightLocalData

/-! The assembled physical solver decides exactly the original numbered
right-leader guard. This proof uses its carried residual objective and the
full graph-closing collector at every physical round. -/
noncomputable section
namespace Characterisation.NumberedRightLocal
open DistributedSynthesis
local instance rightLocalPhaseBEq : BEq EncodedJointPhaseObjective.Letter := instBEqOfDecidableEq

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


local instance objectiveStateDecidable : DecidableEq (M).State :=
  inferInstanceAs (DecidableEq (Fin (EncodedRoundObjectives.stateCount o)))

local notation "input" => compilerData o env output recognizer graphs objectiveData header bank permitted
local notation "code" => number o env output recognizer graphs objectiveData header bank permitted

theorem phaseNumber_number (a : OriginalRound o header) :
    EncodedLeaderPhysical.phaseNumber input (EncodedLocalLeaderTest.physicalNumber
      (EncodedLeaderPhysical.layout input) (code a)) =
      EncodedJointPhaseObjective.number o root groupNumber residuals group (a.1,a.2.1.1,a.2.2) := by
  apply Fin.ext
  change (EncodedJointPhaseObjective.letters (EncodedLeaderPhysical.phase input)).idxOf
    (EncodedLeaderPhysical.phaseLetter input (EncodedLeaderPhysical.decode input
      (EncodedLocalLeaderTest.physicalNumber (EncodedLeaderPhysical.layout input) (code a)).val)) = _
  rw [EncodedLeaderPhysical.decode_number,phaseLetter_number,EncodedJointPhaseObjective.number_val]
  rw [phase_eq]
  rfl

theorem phase_accepts_iff (play : Nat → OriginalRound o header) :
    (EncodedParityConjunction.read (EncodedLeaderPhase.compile input.1)
      (EncodedJointPhaseObjective.letters (EncodedLeaderPhysical.phase input)).length).Accepts
        (fun n => EncodedLeaderPhysical.phaseNumber input
          (EncodedLocalLeaderTest.physicalNumber (EncodedLeaderPhysical.layout input) (code (play n)))) ↔
      (jointPhaseObjective M residuals group).WinsPlay (phasePhysicalPlay Prod.fst play) := by
  simp only [phaseNumber_number]
  have correct := EncodedLeaderPhase.accepts_iff o root shape residuals (phasePhysicalPlay Prod.fst play)
  rw [EncodedLeaderPhase.automaton,DetParityAutomaton.comap_accepts_iff] at correct
  exact correct

variable (rank : (EncodedLeaderObjective.automaton o).State → Fin (C+1))
variable (transition : ∀ q r a, EncodedParityTables.next objectiveData q.val
  ((env r).val*V+(output a).val) = ((EncodedLeaderObjective.automaton o).step q (r,a)).val)
variable (priority : ∀ q, EncodedParityTables.priority objectiveData q.val = (rank q).val)

include transition priority in
/-- Exact language equality with the existing numbered guard, including
arbitrarily late closings and all compatible target choices. -/
theorem compile_wins_iff (play : Nat → OriginalRound o header) :
    (EncodedLocalLeaderTest.monitor (EncodedLeaderPhysical.compile input)).WinsPlay (fun n => code (play n)) ↔
      (numberedRightGuard recognizer M rank header permitted bank).WinsPlay play := by
  rw [EncodedLeaderPhysical.compile_wins_iff input
    (start_lt o env output recognizer graphs objectiveData header bank permitted),phase_accepts_iff]
  simp only [memoryLetter_number]
  exact (numberedRightGuard_generated_checks env (Equiv.refl _) (Equiv.refl _) output
    (Equiv.refl _) (Equiv.refl _) recognizer M graphs (Equiv.refl _) objectiveData rank
    transition priority header bank permitted play).symm

noncomputable local instance guardStateDecidable :
    DecidableEq (numberedRightGuard recognizer M rank header permitted bank).State := Classical.decEq _

include transition priority in
/-- The executable solver equals the original right-leader test. No
assumption supplying a local solver or its memory tables is used. -/
theorem solve_eq_guardTest : EncodedLeaderPhysical.solve input =
    leaderThreadTest (numberedRightGuard recognizer M rank header permitted bank) := by
  classical
  letI : Inhabited I₁ := ⟨⟨0,Nat.succ_pos _⟩⟩
  letI : Inhabited I₂ := ⟨⟨0,Nat.succ_pos _⟩⟩
  letI : Inhabited (RollingReceiverOutput (Fin header.1.val) I₁ I₂ O₁ O₂ D) :=
    ⟨(fun _ => ⟨0,Nat.succ_pos _⟩,bank)⟩
  letI : Inhabited (Fin (EncodedLocalLeaderTest.receiverInputs (EncodedLeaderPhysical.compile input))) :=
    inferInstanceAs (Inhabited I₂)
  letI : Inhabited (Fin (EncodedLocalLeaderTest.senderInputs (EncodedLeaderPhysical.compile input))) :=
    inferInstanceAs (Inhabited I₁)
  letI : Inhabited (Fin (EncodedLeaderPhysical.receivers input).length) :=
    ⟨receiverNumber o env output recognizer graphs objectiveData header bank permitted default⟩
  letI : Inhabited (Fin (EncodedLocalLeaderTest.receiverOutputs (EncodedLeaderPhysical.compile input))) :=
    inferInstanceAs (Inhabited (Fin (EncodedLeaderPhysical.receivers input).length))
  letI : DecidableEq (EncodedLocalLeaderTest.monitor (EncodedLeaderPhysical.compile input)).State :=
    inferInstanceAs (DecidableEq (Fin (EncodedLocalLeaderTest.states (EncodedLeaderPhysical.compile input))))
  change EncodedLocalLeaderTest.solve (EncodedLeaderPhysical.compile input) = _
  rw [EncodedLocalLeaderTest.solve_eq_leaderThreadTest]
  symm
  apply leaderThreadTest_output_equiv _ _
    (receiverNumber o env output recognizer graphs objectiveData header bank permitted)
    (senderNumber o env output recognizer graphs objectiveData header bank permitted)
  intro play
  exact (compile_wins_iff o env output recognizer graphs objectiveData header bank permitted rank transition priority play).symm

end Characterisation.NumberedRightLocal
