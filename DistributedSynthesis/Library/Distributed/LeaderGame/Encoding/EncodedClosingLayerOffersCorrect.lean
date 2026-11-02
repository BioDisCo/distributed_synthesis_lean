/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingLayerOffers
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingComponentsCorrect
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLeaderAlphabetCorrect

/-! Exact generation of whole closing outcomes from numbered layer data.
The selected matrix, labels, predecessors, and minima use one common list
of retained descendants. -/
namespace Characterisation.EncodedClosingLayerOffers
open DistributedSynthesis

variable {X Q : Type} {N J B C n : Nat}
  (number : X ≃ Fin N) (labelNumber : Q ≃ Fin J)
  (shape : InputShape X) (alive exits : X → Bool) (label : X → Q)
  (parent : X → Fin (B+1)) (minimum : X → Fin (C+1))

def encode : Data :=
  (EncodedClosingComponents.encode number shape alive,B,List.ofFn (fun i => exits (number.symm i)),
    FiniteFunctionCodes.encode number (labelNumber ∘ label),
    FiniteFunctionCodes.encode number parent,FiniteFunctionCodes.encode number minimum)

def handover (size : Fin (B+1)) (keep : Fin size.val → X) : LeaderHandover Q B C :=
  ⟨⟨size,restrictInputShape shape keep,label ∘ keep⟩,parent ∘ keep,minimum ∘ keep⟩

theorem select_encode {M : Nat} (f : X → Fin M) (keep : Fin n → X) :
    select (FiniteFunctionCodes.encode number f)
      (FiniteFunctionCodes.encode (Equiv.refl _) (number ∘ keep)) =
      FiniteFunctionCodes.encode (Equiv.refl _) (f ∘ keep) := by
  unfold select
  change (List.ofFn (fun i => (number (keep i)).val)).map _ = _
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  exact FiniteFunctionCodes.eval_encode number f (keep i)

theorem selectedMatrix_encode (keep : Fin n → X) (receiver : Bool) :
    selectedMatrix (encode number labelNumber shape alive exits label parent minimum)
      (FiniteFunctionCodes.encode (Equiv.refl _) (number ∘ keep)) receiver =
      EncodedLeaderAlphabet.matrixEncode (fun i j => if receiver then shape .two (keep i) (keep j)
        else shape .one (keep i) (keep j)) := by
  unfold selectedMatrix
  simp only [FiniteFunctionCodes.encode,List.length_ofFn]
  apply FiniteSearch.tabulate_eq_ofFn
  intro index
  let pair : Fin n × Fin n := finProdFinEquiv.symm index
  have first : pair.1.val = index.val / n := rfl
  have second : pair.2.val = index.val % n := rfl
  have left := FiniteFunctionCodes.eval_encode (Equiv.refl (Fin n)) (number ∘ keep) pair.1
  have right := FiniteFunctionCodes.eval_encode (Equiv.refl (Fin n)) (number ∘ keep) pair.2
  simp only [Equiv.refl_apply,Function.comp_apply] at left right
  rw [first] at left
  rw [second] at right
  change (if receiver then
    (EncodedClosingComponents.views (EncodedClosingComponents.encode number shape alive)
      ((FiniteFunctionCodes.encode (Equiv.refl _) (number ∘ keep)).getD (index.val/n) 0)
      ((FiniteFunctionCodes.encode (Equiv.refl _) (number ∘ keep)).getD (index.val%n) 0)).2 else
    (EncodedClosingComponents.views (EncodedClosingComponents.encode number shape alive)
      ((FiniteFunctionCodes.encode (Equiv.refl _) (number ∘ keep)).getD (index.val/n) 0)
      ((FiniteFunctionCodes.encode (Equiv.refl _) (number ∘ keep)).getD (index.val%n) 0)).1).toNat = _
  rw [left,right,EncodedClosingComponents.views_encode]
  change (if receiver then shape .two (keep pair.1) (keep pair.2) else shape .one (keep pair.1) (keep pair.2)).toNat =
    (finTwoEquiv.symm (if receiver then shape .two (keep pair.1) (keep pair.2) else shape .one (keep pair.1) (keep pair.2))).val
  generalize (if receiver then shape .two (keep pair.1) (keep pair.2) else shape .one (keep pair.1) (keep pair.2)) = value
  cases value <;> rfl

theorem candidate_encode (size : Fin (B+1)) (keep : Fin size.val → X) :
    candidate (encode number labelNumber shape alive exits label parent minimum)
      (FiniteFunctionCodes.encode (Equiv.refl _) (number ∘ keep)) =
      EncodedLeaderAlphabet.outcomeEncode labelNumber (handover shape label parent minimum size keep) := by
  unfold candidate
  rw [selectedMatrix_encode,selectedMatrix_encode]
  change ((_,_,_,select (FiniteFunctionCodes.encode number (labelNumber ∘ label)) _),
    select (FiniteFunctionCodes.encode number parent) _,select (FiniteFunctionCodes.encode number minimum) _) = _
  rw [select_encode,select_encode,select_encode]
  simp only [FiniteFunctionCodes.encode,List.length_ofFn,Bool.false_eq_true,↓reduceIte]
  rfl

variable [Fintype X] [DecidableEq X]

theorem accepted_encode (keep : Fin n → X) :
    Accepted (encode number labelNumber shape alive exits label parent minimum)
      (FiniteFunctionCodes.encode (Equiv.refl _) (number ∘ keep)) ↔
      ∃ root, exits root = true ∧ checkClosingEnumeration (closingComponentMask shape alive root) keep = true := by
  constructor
  · rintro ⟨i,hi,exit,enumerated⟩
    let root := number.symm ⟨i,hi⟩
    have hr : (number root).val=i := by simp [root]
    refine ⟨root,?_,?_⟩
    · have h := EncodedClosingBanks.table_eval number exits false root
      rw [hr] at h
      exact h.symm.trans exit
    · exact (EncodedClosingComponents.enumeration_encode number shape alive (Equiv.refl _) keep root).mp
        (by simpa only [hr] using enumerated)
  · rintro ⟨root,exit,enumerated⟩
    refine ⟨(number root).val,(number root).isLt,?_,?_⟩
    · exact (EncodedClosingBanks.table_eval number exits false root).trans exit
    · exact (EncodedClosingComponents.enumeration_encode number shape alive (Equiv.refl _) keep root).mpr enumerated

/-- Every complete numbering is offered, and no partial or inconsistent
target is introduced by the numeric generation. -/
theorem offers_encode (outcome : LeaderHandover Q B C) :
    EncodedLeaderAlphabet.outcomeEncode labelNumber outcome ∈
      offers (encode number labelNumber shape alive exits label parent minimum) ↔
      ∃ (root : X) (size : Fin (B+1)) (keep : Fin size.val → X),
        exits root = true ∧ checkClosingEnumeration (closingComponentMask shape alive root) keep = true ∧
        handover shape label parent minimum size keep = outcome := by
  constructor
  · intro member
    obtain ⟨code,member,equal⟩ := List.mem_map.mp member
    obtain ⟨n,hn,hcode⟩ := List.mem_flatMap.mp member
    obtain ⟨table,accepted⟩ := List.mem_filter.mp hcode
    obtain ⟨policy,hpolicy⟩ := (FiniteSearch.mem_tables_iff_policy code).mp table
    let keep : Fin n → X := fun i => number.symm (policy i)
    have coding : FiniteFunctionCodes.encode (Equiv.refl _) (number ∘ keep) = code := by
      simpa only [FiniteFunctionCodes.encode,Function.comp_apply,Equiv.refl_symm,Equiv.refl_apply,keep,
        Equiv.apply_symm_apply] using hpolicy
    have passed := (accepted_encode number labelNumber shape alive exits label parent minimum keep).mp
      (by rw [coding]; exact of_decide_eq_true accepted)
    obtain ⟨root,exit,complete⟩ := passed
    refine ⟨root,⟨n,List.mem_range.mp hn⟩,keep,exit,complete,?_⟩
    apply EncodedLeaderAlphabet.outcomeEncode_injective labelNumber
    have h := candidate_encode number labelNumber shape alive exits label parent minimum
      ⟨n,List.mem_range.mp hn⟩ keep
    exact h.symm.trans ((congrArg (candidate _) coding).trans equal)
  · rintro ⟨root,size,keep,exit,complete,rfl⟩
    apply List.mem_map.mpr
    refine ⟨FiniteFunctionCodes.encode (Equiv.refl _) (number ∘ keep),?_,
      candidate_encode number labelNumber shape alive exits label parent minimum size keep⟩
    apply List.mem_flatMap.mpr
    refine ⟨size.val,List.mem_range.mpr size.isLt,?_⟩
    apply List.mem_filter.mpr
    exact ⟨FiniteFunctionCodes.encode_mem _ _,decide_eq_true
      ((accepted_encode number labelNumber shape alive exits label parent minimum keep).mpr ⟨root,exit,complete⟩)⟩

end Characterisation.EncodedClosingLayerOffers
