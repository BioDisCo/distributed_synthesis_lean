/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLeaderProgressState
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedFiniteThreads

/-! Correctness of the generated global progress tables. State and letter
numbering are checked against the existing persistent hidden-code system. -/
namespace Characterisation.EncodedLeaderProgress
open DistributedSynthesis
attribute [local instance] Classical.propDecidable

variable {Q : Type} {B N C : Nat} (number : Q ≃ Fin N) (initialCode : HandoverCode B C)
local notation "ctx" => (B,N,C)
local notation "S" => source (Q:=Q) initialCode

theorem priority_lookup (q : SemanticState B C) :
    ((states ctx).map priority).getD (stateNumber B N C q).val 0 = (S).priority q := by
  rw [stateNumber_val,List.getD_eq_getElem _ _ (by simpa only [List.length_map] using name_lt B N C q),
    List.getElem_map,get_name]
  exact priority_encode initialCode q

theorem priority_range (p : Nat) :
    p ∈ (states ctx).map priority ↔ p ∈ (S).priorityRange := by
  simp only [List.mem_map,FiniteThreadSystem.priorityRange,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨code,member,equal⟩
    have raw : code ∈ rawStates ctx := by
      apply (FiniteCodeNumbering.mem_unique _ _).mp
      simpa only [states] using member
    obtain ⟨q,rfl⟩ := codes_sound B N C code raw
    exact ⟨q,(priority_encode initialCode q).symm.trans equal⟩
  · rintro ⟨q,equal⟩
    refine ⟨encode q,?_,(priority_encode initialCode q).trans equal⟩
    rw [states,FiniteCodeNumbering.mem_unique]
    exact encode_mem B N C q

theorem row_correct (q r : SemanticState B C) (a : PublicLetter Q B C) :
    ((stateNumber B N C q).val,(stateNumber B N C r).val) ∈ row ctx (letterEncode number a) ↔
      ∃ resolution : HandoverCode B C, r = (S).step q a resolution := by
  simp only [stateNumber_val,row,List.mem_flatMap,List.mem_map]
  constructor
  · rintro ⟨old,hold,res,hres,equal⟩
    have oldRaw : old ∈ rawStates ctx := by
      apply (FiniteCodeNumbering.mem_unique _ _).mp
      simpa only [states] using hold
    obtain ⟨s,es⟩ := codes_sound B N C old oldRaw
    subst old
    have hs : s=q := encode_injective (FiniteCodeNumbering.name_injective _ (encode_mem B N C s)
      (encode_mem B N C q) (congrArg Prod.fst equal))
    subst s
    obtain ⟨hi,hj⟩ := List.mem_product.mp hres
    let resolution : HandoverCode B C := (⟨res.1,List.mem_range.mp hi⟩,⟨res.2,List.mem_range.mp hj⟩)
    have he := congrArg Prod.snd equal
    change name ctx (step ctx (encode q) (letterEncode number a) (resolution.1.val,resolution.2.val)) =
      name ctx (encode r) at he
    rw [step_encode number initialCode] at he
    have target := encode_injective (FiniteCodeNumbering.name_injective _
      (encode_mem B N C ((S).step q a resolution)) (encode_mem B N C r) he)
    exact ⟨resolution,target.symm⟩
  · rintro ⟨resolution,rfl⟩
    refine ⟨encode q,?_,(resolution.1.val,resolution.2.val),?_,?_⟩
    · rw [states,FiniteCodeNumbering.mem_unique]
      exact encode_mem B N C q
    · exact List.mem_product.mpr ⟨List.mem_range.mpr resolution.1.isLt,List.mem_range.mpr resolution.2.isLt⟩
    · exact Prod.ext rfl (congrArg (name ctx) (step_encode number initialCode q a resolution))

noncomputable def letterDecode (i : Fin (letters ctx).length) : PublicLetter Q B C :=
  (letters_sound number _ (List.getElem_mem i.isLt)).choose

theorem letterEncode_decode (i : Fin (letters ctx).length) :
    letterEncode number (letterDecode number i) = (letters ctx)[i.val] :=
  (letters_sound number _ (List.getElem_mem i.isLt)).choose_spec

noncomputable def letterIndex (a : PublicLetter Q B C) : Fin (letters ctx).length :=
  ⟨(letters ctx).idxOf (letterEncode number a),List.idxOf_lt_length_iff.mpr (letterEncode_mem number a)⟩

theorem letterDecode_index (a : PublicLetter Q B C) : letterDecode number (letterIndex number a) = a := by
  apply letterEncode_injective number
  rw [letterEncode_decode]
  exact List.getElem_idxOf (letterIndex number a).isLt

theorem edgeRows_length : (edgeRows ctx).length = (letters ctx).length := List.length_map _

noncomputable def rowDecode (i : Fin (edgeRows ctx).length) : PublicLetter Q B C :=
  letterDecode number (Fin.cast edgeRows_length i)

noncomputable def rowIndex (a : PublicLetter Q B C) : Fin (edgeRows ctx).length :=
  Fin.cast edgeRows_length.symm (letterIndex number a)

theorem rowDecode_index (a : PublicLetter Q B C) : rowDecode number (rowIndex number a) = a :=
  letterDecode_index number a

theorem rows_correct (q r : SemanticState B C) (a : Fin (edgeRows ctx).length) :
    ((stateNumber B N C q).val,(stateNumber B N C r).val) ∈ (edgeRows ctx)[a.val]?.getD [] ↔
      ∃ resolution : HandoverCode B C, r = (S).step q (rowDecode number a) resolution := by
  rw [List.getElem?_eq_getElem a.isLt]
  change _ ∈ (edgeRows ctx)[a.val] ↔ _
  have lookup : (edgeRows ctx)[a.val] = row ctx (letterEncode number (rowDecode number a)) := by
    change (List.map (row ctx) (letters ctx))[a.val] = _
    rw [List.getElem_map]
    exact (congrArg (row ctx) (letterEncode_decode number (Fin.cast edgeRows_length a))).symm
  rw [lookup]
  exact row_correct number initialCode q r _

/-- Reindex the existing numeric compiler by the checked public-letter code. -/
noncomputable def automaton : DetParityAutomaton (PublicLetter Q B C) :=
  (EncodedThreadCompiler.automaton (data (ctx,(initialCode.1.val,initialCode.2.val)))).comap (rowIndex number)

/-- The generated DPA recognizes exactly the existing global progress objective. -/
theorem accepts_iff (word : OmegaWord (PublicLetter Q B C)) :
    (automaton number initialCode).Accepts word ↔ (S).universalRunDPA.Accepts word := by
  letI : Fintype (S).Resolution := inferInstanceAs (Fintype (HandoverCode B C))
  letI : DecidableEq (S).State := Classical.typeDecidableEq _
  let ps := (states ctx).map priority
  let es := edgeRows ctx
  let numericWord : OmegaWord (Fin es.length) := OmegaWord.map (rowIndex number) word
  have correct := EncodedFiniteThreads.accepts_iff (S) (stateNumber B N C) ps
    (priority_lookup initialCode) (priority_range initialCode) es (rowDecode number)
    (fun q a r => rows_correct number initialCode q r a) numericWord
  have initialName : name ctx (initial (ctx,(initialCode.1.val,initialCode.2.val))) =
      (stateNumber B N C (S).initial).val := by
    rw [initial_encode, stateNumber_val]
  have same := EncodedThreadCompiler.config_accepts_congr ps es (card_eq B N C).symm initialName numericWord
  have decoded : OmegaWord.map (rowDecode number) numericWord = word := by
    funext n
    exact rowDecode_index number (word n)
  rw [decoded] at correct
  rw [automaton,DetParityAutomaton.comap_accepts_iff]
  exact same.trans correct

/-- All compatible threads retain one actual slot throughout; parity is read
from each successive completed phase of that same thread. -/
theorem accepts_threads_iff (word : OmegaWord (PublicLetter Q B C)) :
    (automaton number initialCode).Accepts word ↔
      ∀ thread : HiddenCodeContinuityThread initialCode (OfferedHandoverEdge offers) word,
        NatSeqMinEvenParity (fun n => (thread.code (n+1)).2.val) := by
  rw [accepts_iff]
  change (hiddenCodeContinuitySystem (handoverPriorityDPA B C) initialCode
    (OfferedHandoverEdge offers)).universalRunDPA.Accepts word ↔ _
  rw [hiddenCodeContinuitySystem_universalRunDPA_accepts_iff]
  simp only [handoverPriorityDPA_accepts_iff,HiddenCodeContinuityThread.childCodeWord]

end Characterisation.EncodedLeaderProgress
