/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLeaderPhysicalCorrect
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedJointPhaseAlphabet
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingBankIndices

/-! The generated local output alphabets number the original leader tables
and receiver outputs with complete promised banks. No local output is lost
or added by enumeration; the leader's group remains the original one. -/
namespace Characterisation.EncodedLeaderPhysical
open DistributedSynthesis
local instance alphabetReceiverBEq : BEq Receiver := instBEqOfDecidableEq
local instance alphabetEnvBEq : BEq EncodedClosingObservations.Round := instBEqOfDecidableEq
local instance alphabetOutputBEq : BEq (Nat × Nat) := instBEqOfDecidableEq
local instance alphabetPhaseBEq : BEq EncodedJointPhaseObjective.Letter := instBEqOfDecidableEq

variable {H G : Type} {R S E V D : Nat} [Fintype H] [Fintype G] [DecidableEq H] [DecidableEq G]
variable (o : EncodedRoundObjectives.Data) (root : H ≃ Fin R) (groupNumber : G ≃ Fin S)
variable (start : H → (EncodedLeaderObjective.automaton o).State) (group : H → G)
variable (env : (Fin (EncodedRoundObjectives.inputOne o) × Fin (EncodedRoundObjectives.inputTwo o) × Graph) ≃ Fin E)
variable (output : (Fin (EncodedRoundObjectives.outputOne o) × Fin (EncodedRoundObjectives.outputTwo o)) ≃ Fin V)
variable (shape : InputShape H) (d : Data)
variable (phaseEq : phase d = EncodedJointPhaseObjective.dataEncode o root groupNumber start group)
variable (bankEq : EncodedGraphMemory.bankData (memory d) =
  EncodedClosingBanks.dataEncode root env (Equiv.refl _) (Equiv.refl _) output (Equiv.refl _) (Equiv.refl _) shape (D+1))
variable (outputsEq : EncodedGraphMemory.outputs (memory d) = V)

abbrev SenderValue := G → Fin (EncodedRoundObjectives.outputOne o)
abbrev ReceiverValue := (H → Fin (EncodedRoundObjectives.outputTwo o)) ×
  ClosingPlanBank H (Fin (EncodedRoundObjectives.inputOne o)) (Fin (EncodedRoundObjectives.inputTwo o))
    (Fin (EncodedRoundObjectives.outputOne o)) (Fin (EncodedRoundObjectives.outputTwo o)) D

noncomputable def receiverEncode (a : ReceiverValue (H:=H) (D:=D) o) : Receiver :=
  (FiniteFunctionCodes.encode root a.1,EncodedClosingBanks.bankEncode root env output a.2)

include phaseEq in
omit [Fintype H] [Fintype G] [DecidableEq H] [DecidableEq G] in
theorem senders_eq : senders d = FiniteCodeNumbering.unique
    (FiniteSearch.tables (EncodedRoundObjectives.outputOne o) S) := by
  unfold senders
  rw [phaseEq]
  rfl

include phaseEq bankEq outputsEq in
omit [Fintype H] [Fintype G] [DecidableEq H] [DecidableEq G] in
theorem rawReceivers_eq : rawReceivers d =
    (FiniteSearch.tables (EncodedRoundObjectives.outputTwo o) R).product
      (EncodedClosingBanks.banks (EncodedClosingBanks.dataEncode root env (Equiv.refl _) (Equiv.refl _)
        output (Equiv.refl _) (Equiv.refl _) shape (D+1)) V) := by
  unfold rawReceivers
  rw [phaseEq,bankEq,outputsEq,EncodedJointPhaseObjective.roots_encode]
  rfl

include phaseEq bankEq outputsEq in
omit [Fintype H] [Fintype G] [DecidableEq H] [DecidableEq G] in
theorem receiverEncode_mem (a : ReceiverValue (H:=H) (D:=D) o) :
    receiverEncode o root env output a ∈ rawReceivers d := by
  rw [rawReceivers_eq o root groupNumber start group env output shape d phaseEq bankEq outputsEq]
  exact List.mem_product.mpr ⟨FiniteFunctionCodes.encode_mem root a.1,
    EncodedClosingBanks.bankEncode_mem root env (Equiv.refl _) (Equiv.refl _) output (Equiv.refl _) (Equiv.refl _) shape a.2⟩

omit [Fintype H] [DecidableEq H] in
theorem receiverEncode_injective : Function.Injective (receiverEncode (D:=D) o root env output) := by
  intro a b eq
  apply Prod.ext
  · funext h
    apply Fin.ext
    have same := congrArg (fun x : Receiver => x.1.getD (root h).val 0) eq
    simpa only [receiverEncode,FiniteFunctionCodes.eval_encode] using same
  · exact EncodedClosingBanks.bankEncode_injective root env output (congrArg Prod.snd eq)

include phaseEq bankEq outputsEq in
omit [Fintype H] [Fintype G] [DecidableEq H] [DecidableEq G] in
theorem receiverEncode_sound (a : Receiver) (member : a ∈ rawReceivers d) :
    ∃ value : ReceiverValue (H:=H) (D:=D) o, receiverEncode o root env output value = a := by
  rw [rawReceivers_eq o root groupNumber start group env output shape d phaseEq bankEq outputsEq] at member
  obtain ⟨hr,hb⟩ := List.mem_product.mp member
  obtain ⟨rec,heq⟩ := (FiniteSearch.mem_tables_iff_policy a.1).mp hr
  obtain ⟨bank,hbank⟩ := EncodedClosingBanks.bankEncode_sound root env (Equiv.refl _) (Equiv.refl _)
    output (Equiv.refl _) (Equiv.refl _) shape a.2 hb
  refine ⟨(fun h => rec (root h),bank),Prod.ext ?_ hbank⟩
  simpa only [receiverEncode,FiniteFunctionCodes.encode,Equiv.apply_symm_apply] using heq

noncomputable def receiverNumber : ReceiverValue (H:=H) (D:=D) o ≃ Fin (receivers d).length :=
  FiniteCodeNumbering.equiv (rawReceivers d) (receiverEncode o root env output)
    (receiverEncode_injective o root env output)
    (receiverEncode_mem o root groupNumber start group env output shape d phaseEq bankEq outputsEq)
    (receiverEncode_sound o root groupNumber start group env output shape d phaseEq bankEq outputsEq)

noncomputable def senderTablesNumber : SenderValue (G:=G) o ≃ Fin
    (FiniteCodeNumbering.unique (FiniteSearch.tables (EncodedRoundObjectives.outputOne o) S)).length := by
  apply FiniteCodeNumbering.equiv _ (FiniteFunctionCodes.encode groupNumber)
  · intro a b same
    funext g
    apply Fin.ext
    have entries := congrArg (fun xs : List Nat => xs.getD (groupNumber g).val 0) same
    simpa only [FiniteFunctionCodes.eval_encode] using entries
  · exact FiniteFunctionCodes.encode_mem groupNumber
  · intro xs member
    obtain ⟨f,hf⟩ := (FiniteSearch.mem_tables_iff_policy xs).mp member
    refine ⟨fun g => f (groupNumber g),?_⟩
    simpa only [FiniteFunctionCodes.encode,Equiv.apply_symm_apply] using hf

noncomputable def senderNumber : SenderValue (G:=G) o ≃ Fin (senders d).length :=
  (senderTablesNumber o groupNumber).trans
    (finCongr (congrArg List.length (senders_eq o root groupNumber start group d phaseEq)).symm)

section
omit [Fintype H] [Fintype G] [DecidableEq H] [DecidableEq G]

theorem receiverNumber_lookup (a : ReceiverValue (H:=H) (D:=D) o) :
    (receivers d).getD (receiverNumber o root groupNumber start group env output shape d phaseEq bankEq outputsEq a).val
      ([],[]) = receiverEncode o root env output a := by
  change ((FiniteCodeNumbering.unique (rawReceivers d))[
    FiniteCodeNumbering.name (rawReceivers d) (receiverEncode o root env output a)]?).getD _ = _
  rw [FiniteCodeNumbering.get_name (rawReceivers d) (receiverEncode o root env output)
    (receiverEncode_mem o root groupNumber start group env output shape d phaseEq bankEq outputsEq)]
  rfl

theorem senderNumber_val (a : SenderValue (G:=G) o) :
    (senderNumber o root groupNumber start group d phaseEq a).val =
      FiniteCodeNumbering.name (FiniteSearch.tables (EncodedRoundObjectives.outputOne o) S)
        (FiniteFunctionCodes.encode groupNumber a) := rfl

theorem senderNumber_lookup (a : SenderValue (G:=G) o) :
    (senders d).getD (senderNumber o root groupNumber start group d phaseEq a).val [] =
      FiniteFunctionCodes.encode groupNumber a := by
  rw [senderNumber_val,senders_eq o root groupNumber start group d phaseEq]
  change ((FiniteCodeNumbering.unique _)[FiniteCodeNumbering.name _ _]?).getD _ = _
  rw [FiniteCodeNumbering.get_name _ (FiniteFunctionCodes.encode groupNumber)
    (FiniteFunctionCodes.encode_mem groupNumber)]
  rfl

end

noncomputable def roundNumber : RealizedBlockRound
    (Fin (EncodedRoundObjectives.inputTwo o)) (Fin (EncodedRoundObjectives.inputOne o))
    (ReceiverValue (H:=H) (D:=D) o) (SenderValue (G:=G) o) ≃ PhysicalRound d :=
  (Equiv.prodCongr
    (finCongr (show EncodedRoundObjectives.inputTwo o = EncodedLocalLeaderTest.receiverInputs (layout d) by
      change _ = EncodedRoundObjectives.inputTwo (phase d).1
      rw [phaseEq]; rfl))
    (finCongr (show EncodedRoundObjectives.inputOne o = EncodedLocalLeaderTest.senderInputs (layout d) by
      change _ = EncodedRoundObjectives.inputOne (phase d).1
      rw [phaseEq]; rfl))).prodCongr
    ((receiverNumber o root groupNumber start group env output shape d phaseEq bankEq outputsEq).prodCongr
      (senderNumber o root groupNumber start group d phaseEq))

section
omit [Fintype H] [Fintype G] [DecidableEq H] [DecidableEq G]

theorem roundCode_number (a : RealizedBlockRound
    (Fin (EncodedRoundObjectives.inputTwo o)) (Fin (EncodedRoundObjectives.inputOne o))
    (ReceiverValue (H:=H) (D:=D) o) (SenderValue (G:=G) o)) :
    roundCode d (roundNumber o root groupNumber start group env output shape d phaseEq bankEq outputsEq a) =
      ((a.1.1.val,a.1.2.val),
        (receiverNumber o root groupNumber start group env output shape d phaseEq bankEq outputsEq a.2.1).val,
        (senderNumber o root groupNumber start group d phaseEq a.2.2).val) := rfl

theorem phaseLetter_number (a : RealizedBlockRound
    (Fin (EncodedRoundObjectives.inputTwo o)) (Fin (EncodedRoundObjectives.inputOne o))
    (ReceiverValue (H:=H) (D:=D) o) (SenderValue (G:=G) o)) :
    phaseLetter d (roundCode d (roundNumber o root groupNumber start group env output shape d phaseEq bankEq outputsEq a)) =
      EncodedJointPhaseObjective.encode o root groupNumber (a.1,a.2.1.1,a.2.2) := by
  rw [roundCode_number]
  unfold phaseLetter receiver sender
  dsimp only
  rw [receiverNumber_lookup,senderNumber_lookup]
  rfl

theorem memoryLetter_number (a : RealizedBlockRound
    (Fin (EncodedRoundObjectives.inputTwo o)) (Fin (EncodedRoundObjectives.inputOne o))
    (ReceiverValue (H:=H) (D:=D) o) (SenderValue (G:=G) o)) :
    memoryLetter d (roundCode d (roundNumber o root groupNumber start group env output shape d phaseEq bankEq outputsEq a)) =
      EncodedGraphMemory.letterEncode root env output group a := by
  rw [roundCode_number]
  unfold memoryLetter receiver sender
  dsimp only
  rw [receiverNumber_lookup,senderNumber_lookup,bankEq,phaseEq]
  have environment := EncodedClosingBanks.roundTable_index (D:=D+1) root env (Equiv.refl _) (Equiv.refl _)
    output (Equiv.refl _) (Equiv.refl _) shape (a.1.2,a.1.1,Graph.right)
  dsimp only [EncodedGraphMemory.letterEncode,receiverEncode]
  apply Prod.ext environment
  apply Prod.ext
  swap
  · rfl
  rw [EncodedJointPhaseObjective.roots_encode]
  change (List.range R).map _ = List.ofFn _
  apply FiniteSearch.tabulate_eq_ofFn
  intro i
  have assignment := FiniteFunctionCodes.eval_encode root (groupNumber ∘ group) (root.symm i)
  have receiverOutput := FiniteFunctionCodes.eval_encode root a.2.1.1 (root.symm i)
  simp only [Equiv.apply_symm_apply,Function.comp_apply] at assignment receiverOutput
  change (EncodedClosingBanks.outputTable _).idxOf
    ((FiniteFunctionCodes.encode groupNumber a.2.2).getD
      ((FiniteFunctionCodes.encode root (groupNumber ∘ group)).getD i.val 0) 0,
      (FiniteFunctionCodes.encode root a.2.1.1).getD i.val 0) = _
  rw [assignment,receiverOutput,FiniteFunctionCodes.eval_encode]
  exact EncodedClosingBanks.outputTable_index (D:=D+1) root env (Equiv.refl _) (Equiv.refl _)
    output (Equiv.refl _) (Equiv.refl _) shape (a.2.2 (group (root.symm i)),a.2.1.1 (root.symm i))

end

end Characterisation.EncodedLeaderPhysical
