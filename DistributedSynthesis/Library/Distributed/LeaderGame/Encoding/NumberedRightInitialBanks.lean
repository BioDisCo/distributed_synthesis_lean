/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.NumberedRightLocalCorrect
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedInitialLeaderBanks

/-! Complete initial-bank search for the original right-leader legality
test. Every numeric bank decodes to an original closing-plan bank, and the
assembled compiler is independent of the seed bank after replacement. -/
noncomputable section
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


local instance initialBankObjectiveStateDecidable : DecidableEq (M).State :=
  inferInstanceAs (DecidableEq (Fin (EncodedRoundObjectives.stateCount o)))

local notation "input" => compilerData o env output recognizer graphs objectiveData header bank permitted


theorem withBank_data (nextBank : ClosingPlanBank (Fin header.1.val) I₁ I₂ O₁ O₂ D) :
    EncodedInitialLeaderBanks.withBank input (EncodedClosingBanks.bankEncode root env output nextBank) =
      compilerData o env output recognizer graphs objectiveData header nextBank permitted := rfl

variable (rank : (EncodedLeaderObjective.automaton o).State → Fin (C+1))
variable (transition : ∀ q r a, EncodedParityTables.next objectiveData q.val
  ((env r).val*V+(output a).val) = ((EncodedLeaderObjective.automaton o).step q (r,a)).val)
variable (priority : ∀ q, EncodedParityTables.priority objectiveData q.val = (rank q).val)

include transition priority in
/-- Search over the generated complete bank list equals the existing
right-leader legality predicate. The seed bank places no restriction on
the winning initial bank. -/
theorem solveBanks_eq_legal : EncodedInitialLeaderBanks.solve input =
    numberedRightLegal recognizer M rank header permitted := by
  classical
  apply Bool.eq_iff_iff.mpr
  rw [EncodedInitialLeaderBanks.solve_iff,numberedRightLegal_correct]
  constructor
  · rintro ⟨encoded,member,winning⟩
    change encoded ∈ EncodedClosingBanks.banks _ _ at member
    rw [bank_eq,outputs_eq] at member
    obtain ⟨nextBank,encodedEq⟩ := EncodedClosingBanks.bankEncode_sound root env (Equiv.refl _) (Equiv.refl _)
      output (Equiv.refl _) (Equiv.refl _) shape encoded member
    rw [← encodedEq,withBank_data,
      solve_eq_guardTest o env output recognizer graphs objectiveData header nextBank permitted rank transition priority] at winning
    obtain ⟨tree,winning⟩ := (leaderThreadTest_correct _).mp winning
    exact ⟨nextBank,tree,winning⟩
  · rintro ⟨nextBank,tree,winning⟩
    refine ⟨EncodedClosingBanks.bankEncode root env output nextBank,?_,?_⟩
    · change _ ∈ EncodedClosingBanks.banks _ _
      rw [bank_eq,outputs_eq]
      exact EncodedClosingBanks.bankEncode_mem root env (Equiv.refl _) (Equiv.refl _) output
        (Equiv.refl _) (Equiv.refl _) shape nextBank
    · rw [withBank_data,
        solve_eq_guardTest o env output recognizer graphs objectiveData header nextBank permitted rank transition priority]
      exact (leaderThreadTest_correct _).mpr ⟨tree,winning⟩

end Characterisation.NumberedRightLocal
