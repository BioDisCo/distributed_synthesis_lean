/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedJointPhaseObjective
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingBanksCorrect

/-! Number the existing joint-phase alphabet using the generated list of
input pairs and whole receiver/leader output vectors. -/
namespace Characterisation.EncodedJointPhaseObjective
open DistributedSynthesis
local instance : BEq Letter := instBEqOfDecidableEq

variable {H G : Type} {R S : Nat} (o : EncodedRoundObjectives.Data)
variable (root : H ≃ Fin R) (groupNumber : G ≃ Fin S)
variable (start : H → (EncodedLeaderObjective.automaton o).State) (group : H → G)

abbrev PhaseLetter := RealizedBlockRound
  (Fin (EncodedRoundObjectives.inputTwo o)) (Fin (EncodedRoundObjectives.inputOne o))
  (H → Fin (EncodedRoundObjectives.outputTwo o)) (G → Fin (EncodedRoundObjectives.outputOne o))

def dataEncode : Data :=
  (o,S,List.ofFn (fun h => (start (root.symm h)).val),
    FiniteFunctionCodes.encode root (groupNumber ∘ group))

def encode (a : PhaseLetter (H:=H) (G:=G) o) : Letter :=
  ((a.1.1.val,a.1.2.val),FiniteFunctionCodes.encode root a.2.1,FiniteFunctionCodes.encode groupNumber a.2.2)

local notation "input" => dataEncode o root groupNumber start group

theorem roots_encode : roots input = R := by simp [roots,initial,dataEncode]

theorem encode_mem (a : PhaseLetter (H:=H) (G:=G) o) :
    encode o root groupNumber a ∈ rawLetters input := by
  unfold rawLetters
  rw [roots_encode]
  exact List.mem_product.mpr ⟨List.mem_product.mpr ⟨List.mem_range.mpr a.1.1.isLt,List.mem_range.mpr a.1.2.isLt⟩,
    List.mem_product.mpr ⟨FiniteFunctionCodes.encode_mem root a.2.1,FiniteFunctionCodes.encode_mem groupNumber a.2.2⟩⟩

theorem encode_injective : Function.Injective (encode o root groupNumber) := by
  intro a b eq
  apply Prod.ext
  · exact Prod.ext (Fin.ext (congrArg (fun x : Letter => x.1.1) eq))
      (Fin.ext (congrArg (fun x : Letter => x.1.2) eq))
  · apply Prod.ext
    · funext h
      apply Fin.ext
      have same := congrArg (fun x : Letter => x.2.1.getD (root h).val 0) eq
      simpa only [encode,FiniteFunctionCodes.eval_encode] using same
    · funext g
      apply Fin.ext
      have same := congrArg (fun x : Letter => x.2.2.getD (groupNumber g).val 0) eq
      simpa only [encode,FiniteFunctionCodes.eval_encode] using same

theorem encode_sound (a : Letter) (member : a ∈ rawLetters input) :
    ∃ letter : PhaseLetter (H:=H) (G:=G) o, encode o root groupNumber letter = a := by
  rcases a with ⟨⟨i2,i1⟩,receivers,leaders⟩
  obtain ⟨inputs,outputs⟩ := List.mem_product.mp member
  obtain ⟨hi2,hi1⟩ := List.mem_product.mp inputs
  obtain ⟨hrec,hlead⟩ := List.mem_product.mp outputs
  rw [roots_encode] at hrec
  obtain ⟨rec,hrec⟩ := (FiniteSearch.mem_tables_iff_policy receivers).mp hrec
  obtain ⟨lead,hlead⟩ := (FiniteSearch.mem_tables_iff_policy leaders).mp hlead
  refine ⟨((⟨i2,List.mem_range.mp hi2⟩,⟨i1,List.mem_range.mp hi1⟩),
    (fun h => rec (root h)),fun g => lead (groupNumber g)),?_⟩
  change ((i2,i1),List.ofFn (fun i => (rec (root (root.symm i))).val),
    List.ofFn (fun i => (lead (groupNumber (groupNumber.symm i))).val)) = _
  simp only [Equiv.apply_symm_apply]
  exact Prod.ext rfl (Prod.ext hrec hlead)

variable [Fintype H] [Fintype G]
noncomputable def number : PhaseLetter (H:=H) (G:=G) o ≃ Fin (letters input).length :=
  FiniteCodeNumbering.equiv (rawLetters input) (encode o root groupNumber)
    (encode_injective o root groupNumber) (encode_mem o root groupNumber start group)
    (encode_sound o root groupNumber start group)

section
omit [Fintype H] [Fintype G]

theorem number_val (a : PhaseLetter (H:=H) (G:=G) o) :
    (number o root groupNumber start group a).val =
      FiniteCodeNumbering.name (rawLetters input) (encode o root groupNumber a) := rfl

theorem letter_encode (a : PhaseLetter (H:=H) (G:=G) o) :
    letter input (number o root groupNumber start group a).val = encode o root groupNumber a := by
  change ((letters input)[(number o root groupNumber start group a).val]?).getD ((0,0),[],[]) = _
  rw [number_val]
  change ((FiniteCodeNumbering.unique (rawLetters input))[FiniteCodeNumbering.name (rawLetters input) (encode o root groupNumber a)]?).getD _ = _
  rw [FiniteCodeNumbering.name,List.getElem?_idxOf
    ((FiniteCodeNumbering.mem_unique _ _).mpr (encode_mem o root groupNumber start group a))]
  rfl

theorem physical_encode (h : H) (a : PhaseLetter (H:=H) (G:=G) o) :
    physical input (root h).val (encode o root groupNumber a) =
      EncodedNoDirect.letterCode (continuationRecord (jointPhaseLetter group a h)) := by
  unfold physical encode
  change (_,_,_,(FiniteFunctionCodes.encode groupNumber a.2.2).getD
    ((FiniteFunctionCodes.encode root (groupNumber ∘ group)).getD (root h).val 0) 0,
    (FiniteFunctionCodes.encode root a.2.1).getD (root h).val 0) = _
  simp only [FiniteFunctionCodes.eval_encode,Function.comp_apply]
  rfl

end

end Characterisation.EncodedJointPhaseObjective
