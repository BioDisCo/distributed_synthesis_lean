/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLeaderProgress
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLeaderAlphabetCorrect
import DistributedSynthesis.Library.Distributed.LeaderPhases.GlobalLeaderProgress

/-! State correspondence for the generated hidden-thread progress system. -/
namespace Characterisation.EncodedLeaderProgress
open DistributedSynthesis
open EncodedLeaderAlphabet (Context)
attribute [local instance] Classical.propDecidable

abbrev SemanticState (B C : Nat) := HiddenCodeContinuityState (handoverPriorityDPA B C)
abbrev PublicLetter (Q : Type) (B C : Nat) := (Proc × Finset (LeaderHandover Q B C)) × LeaderHandover Q B C

noncomputable def offers {Q : Type} {B C : Nat}
    (move : Proc × Finset (LeaderHandover Q B C)) (outcome : LeaderHandover Q B C) := decide (outcome ∈ move.2)
noncomputable def source {Q : Type} {B C : Nat} (initial : HandoverCode B C) :
    FiniteThreadSystem.{0,0,0} (PublicLetter Q B C) :=
  hiddenCodeContinuitySystem (handoverPriorityDPA B C) initial (OfferedHandoverEdge offers)

def encode {B C : Nat} : SemanticState B C → State
  | .dead => none
  | .live code control => some (code.1.val,code.2.val,control.val)

theorem encode_injective {B C : Nat} : Function.Injective (@encode B C) := by
  intro left right equal
  cases left with
  | dead => cases right <;> simp_all [encode]
  | live code control =>
    cases right with
    | dead => simp [encode] at equal
    | live code' control' =>
      simp only [encode,Option.some.injEq,Prod.mk.injEq] at equal
      obtain ⟨hslot,hmin,hcontrol⟩ := equal
      have hcode : code=code' := Prod.ext (Fin.ext hslot) (Fin.ext hmin)
      cases hcode
      cases Fin.ext hcontrol
      rfl

theorem encode_mem (B N C : Nat) (q : SemanticState B C) : encode q ∈ rawStates (B,N,C) := by
  cases q with
  | dead => exact List.mem_cons_self
  | live code control =>
    apply List.mem_cons_of_mem
    apply List.mem_map.mpr
    exact ⟨_,List.mem_product.mpr ⟨List.mem_range.mpr code.1.isLt,List.mem_product.mpr
      ⟨List.mem_range.mpr code.2.isLt,List.mem_range.mpr control.isLt⟩⟩,rfl⟩

theorem codes_sound (B N C : Nat) (q : State) (member : q ∈ rawStates (B,N,C)) :
    ∃ state : SemanticState B C, encode state=q := by
  rcases List.mem_cons.mp member with h | h
  · exact ⟨.dead,h.symm⟩
  · have mapped : ∃ data ∈ (List.range (B+1)).product
        ((List.range (C+1)).product (List.range (C+1))), some data=q := List.mem_map.mp h
    obtain ⟨⟨slot,minimum,control⟩,hd,rfl⟩ := mapped
    obtain ⟨hs,hr⟩ := List.mem_product.mp hd
    obtain ⟨hm,hc⟩ := List.mem_product.mp hr
    exact ⟨.live (⟨slot,List.mem_range.mp hs⟩,⟨minimum,List.mem_range.mp hm⟩)
      ⟨control,List.mem_range.mp hc⟩,rfl⟩

noncomputable def stateNumber (B N C : Nat) : SemanticState B C ≃ Fin (Fintype.card (SemanticState B C)) :=
  FiniteCodeNumbering.number (rawStates (B,N,C)) encode encode_injective (encode_mem B N C) (codes_sound B N C)

theorem stateNumber_val (B N C : Nat) (q : SemanticState B C) :
    (stateNumber B N C q).val = name (B,N,C) (encode q) := rfl

theorem card_eq (B N C : Nat) : Fintype.card (SemanticState B C) = (states (B,N,C)).length := by
  rw [states]
  exact FiniteCodeNumbering.card_eq (rawStates (B,N,C)) encode encode_injective (encode_mem B N C) (codes_sound B N C)

theorem name_lt (B N C : Nat) (q : SemanticState B C) : name (B,N,C) (encode q) < (states (B,N,C)).length := by
  rw [← stateNumber_val,← card_eq]
  exact (stateNumber B N C q).isLt

theorem get_name (B N C : Nat) (q : SemanticState B C) :
    (states (B,N,C))[name (B,N,C) (encode q)]'(name_lt B N C q) = encode q := by
  apply Option.some.inj
  apply (List.getElem?_eq_getElem (name_lt B N C q)).symm.trans
  simpa only [states,name] using FiniteCodeNumbering.get_name (rawStates (B,N,C)) encode (encode_mem B N C) q

variable {Q : Type} {B N C : Nat} (number : Q ≃ Fin N) (initialCode : HandoverCode B C)

noncomputable def letterEncode (a : PublicLetter Q B C) : Letter :=
  (EncodedLeaderAlphabet.moveEncode number a.1,EncodedLeaderAlphabet.outcomeEncode number a.2)

theorem letterEncode_injective : Function.Injective (letterEncode (B:=B) (C:=C) number) := by
  intro left right equal
  exact Prod.ext (EncodedLeaderAlphabet.moveEncode_injective number (congrArg Prod.fst equal))
    (EncodedLeaderAlphabet.outcomeEncode_injective number (congrArg Prod.snd equal))

theorem letterEncode_mem (a : PublicLetter Q B C) : letterEncode number a ∈ letters (B,N,C) := by
  apply List.mem_product.mpr
  constructor
  · rw [EncodedLeaderAlphabet.moves,FiniteCodeNumbering.mem_unique]
    exact EncodedLeaderAlphabet.moveEncode_mem number a.1
  · rw [EncodedLeaderAlphabet.outcomes,FiniteCodeNumbering.mem_unique]
    exact EncodedLeaderAlphabet.outcomeEncode_mem number a.2

theorem letters_sound (a : Letter) (member : a ∈ letters (B,N,C)) :
    ∃ semantic : PublicLetter Q B C, letterEncode number semantic=a := by
  obtain ⟨hm,ho⟩ := List.mem_product.mp member
  rw [EncodedLeaderAlphabet.moves,FiniteCodeNumbering.mem_unique] at hm
  rw [EncodedLeaderAlphabet.outcomes,FiniteCodeNumbering.mem_unique] at ho
  obtain ⟨move,em⟩ := EncodedLeaderAlphabet.moveEncode_sound number a.1 hm
  obtain ⟨outcome,eo⟩ := EncodedLeaderAlphabet.outcomeEncode_sound number a.2 ho
  exact ⟨(move,outcome),Prod.ext em eo⟩

theorem step_encode (q : SemanticState B C) (a : PublicLetter Q B C) (r : HandoverCode B C) :
    step (B,N,C) (encode q) (letterEncode number a) (r.1.val,r.2.val) =
      encode ((source initialCode).step q a r) := by
  cases q with
  | dead => rfl
  | live code control =>
    have test :
        (EncodedLeaderAlphabet.offered (EncodedLeaderAlphabet.moveEncode number a.1)
            (EncodedLeaderAlphabet.outcomeName (B,N,C) (EncodedLeaderAlphabet.outcomeEncode number a.2)) &&
          EncodedLeaderAlphabet.edge (EncodedLeaderAlphabet.outcomeEncode number a.2)
            (code.1.val,code.2.val) (r.1.val,r.2.val)) = true ↔ OfferedHandoverEdge offers code a.1 a.2 r := by
      rw [Bool.and_eq_true,← EncodedLeaderAlphabet.outcomeNumber_val number a.2,
        EncodedLeaderAlphabet.offered_encode,EncodedLeaderAlphabet.edge_encode]
      simp only [OfferedHandoverEdge,offers,decide_eq_true_eq]
    by_cases h : OfferedHandoverEdge offers code a.1 a.2 r
    · have ht := test.mpr h
      change _ = encode ((hiddenCodeContinuitySystem (handoverPriorityDPA B C) initialCode
        (OfferedHandoverEdge offers)).step (.live code control) a r)
      rw [hiddenCodeContinuitySystem_step_live_of _ _ _ _ _ _ _ h]
      change (if _ then some (r.1.val,r.2.val,r.2.val) else none) = _
      exact if_pos ht
    · have ht : ¬ _ = true := fun ht => h (test.mp ht)
      change _ = encode ((hiddenCodeContinuitySystem (handoverPriorityDPA B C) initialCode
        (OfferedHandoverEdge offers)).step (.live code control) a r)
      rw [hiddenCodeContinuitySystem_step_live_dead_of _ _ _ _ _ _ _ h]
      change (if _ then some (r.1.val,r.2.val,r.2.val) else none) = none
      exact if_neg ht

theorem priority_encode (q : SemanticState B C) : priority (encode q) = (source (Q:=Q) initialCode).priority q := by
  cases q <;> rfl

theorem initial_encode : initial ((B,N,C),(initialCode.1.val,initialCode.2.val)) =
    encode (source (Q:=Q) initialCode).initial := by
  simp only [initial,EncodedLeaderAlphabet.width,EncodedLeaderAlphabet.maxPriority,
    Nat.mod_eq_of_lt initialCode.1.isLt,Nat.mod_eq_of_lt initialCode.2.isLt]
  rfl

end Characterisation.EncodedLeaderProgress
