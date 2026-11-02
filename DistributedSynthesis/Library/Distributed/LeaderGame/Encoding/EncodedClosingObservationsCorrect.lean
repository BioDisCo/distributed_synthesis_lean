/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingObservations
import DistributedSynthesis.Library.Distributed.LeaderPhases.ClosingBankCoherence

/-! The numeric observation comparison agrees with the existing closing
compiler. Private inputs and the graph-dependent reception ambiguity are
preserved at every depth. -/
namespace Characterisation.EncodedClosingObservations
open DistributedSynthesis

variable {H I₁ I₂ : Type} {N₁ N₂ : Nat}
  (one : I₁ ≃ Fin N₁) (two : I₂ ≃ Fin N₂)

def roundEncode (r : I₁ × I₂ × Graph) : Round :=
  ((one r.1).val,(two r.2.1).val,(graphCode r.2.2).val)

variable [DecidableEq I₁] [DecidableEq I₂]

theorem advance_encode (shape : InputShape H) (h k : H) (r s : I₁ × I₂ × Graph) :
    advance (shape .one h k,shape .two h k) (roundEncode one two r,roundEncode one two s) =
      (advanceInputShape shape .one (h,r) (k,s),advanceInputShape shape .two (h,r) (k,s)) := by
  rcases r with ⟨x,y,g⟩
  rcases s with ⟨x',y',z⟩
  have ho : ((one x).val = (one x').val) ↔ x=x' :=
    Fin.val_injective.eq_iff.trans one.injective.eq_iff
  have ht : ((two y).val = (two y').val) ↔ y=y' :=
    Fin.val_injective.eq_iff.trans two.injective.eq_iff
  cases g <;> cases z <;>
    simp [advance,reception,roundEncode,graphCode,advanceInputShape,ho,ht,Bool.and_assoc]

theorem paired_ofFn {n : Nat} (left right : Fin n → Round) :
    paired (List.ofFn left) (List.ofFn right) = List.ofFn (fun i => (left i,right i)) := by
  unfold paired
  simp only [List.length_ofFn,min_self]
  apply FiniteSearch.tabulate_eq_ofFn
  intro i
  rw [List.getD_eq_getElem _ _ (by simp),
    List.getD_eq_getElem _ _ (by simp)]
  simp

theorem compare_fromWord (shape : InputShape H) (h k : H) (n : Nat)
    (left right : Fin n → I₁ × I₂ × Graph) :
    compare (shape .one h k,shape .two h k)
      (List.ofFn (fun i => (roundEncode one two (left i),roundEncode one two (right i)))) =
      (closingLayerShape shape n .one (closingLayerFromWord h n left) (closingLayerFromWord k n right),
       closingLayerShape shape n .two (closingLayerFromWord h n left) (closingLayerFromWord k n right)) := by
  induction n with
  | zero => simp [compare,closingLayerShape,closingLayerFromWord]
  | succ n ih =>
    rw [List.ofFn_succ',List.concat_eq_append]
    change (List.ofFn (fun i : Fin n =>
      (roundEncode one two (left i.castSucc),roundEncode one two (right i.castSucc))) ++
        [(roundEncode one two (left (Fin.last n)),roundEncode one two (right (Fin.last n)))]).foldl
      advance (shape .one h k,shape .two h k) = _
    rw [List.foldl_append]
    change advance (compare (shape .one h k,shape .two h k) _)
      (roundEncode one two (left (Fin.last n)),roundEncode one two (right (Fin.last n))) = _
    rw [ih,advance_encode]
    rfl

omit [DecidableEq I₁] [DecidableEq I₂] in
theorem layerFromWord_word (n : Nat) (s : ClosingLayer H I₁ I₂ n) :
    closingLayerFromWord (closingLayerRoot n s) n (closingLayerWord n s) = s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (closingLayerFromWord (closingLayerRoot n s.1) n
      (fun i => Fin.lastCases s.2 (closingLayerWord n s.1) i.castSucc),
      Fin.lastCases s.2 (closingLayerWord n s.1) (Fin.last n)) = s
    simp only [Fin.lastCases_castSucc,Fin.lastCases_last,ih]
    rfl

/-- Actual local view equality is computed by replaying the finite matrix
update, without supplying the graph as an extra observation. -/
theorem compareWords_layer (shape : InputShape H) (n : Nat)
    (left right : ClosingLayer H I₁ I₂ n) :
    compareWords (shape .one (closingLayerRoot n left) (closingLayerRoot n right),
      shape .two (closingLayerRoot n left) (closingLayerRoot n right))
      (List.ofFn (fun i => roundEncode one two (closingLayerWord n left i)))
      (List.ofFn (fun i => roundEncode one two (closingLayerWord n right i))) =
      (closingLayerShape shape n .one left right,closingLayerShape shape n .two left right) := by
  rw [compareWords,paired_ofFn,compare_fromWord,layerFromWord_word,layerFromWord_word]

end Characterisation.EncodedClosingObservations
