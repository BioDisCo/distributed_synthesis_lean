/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Logic.MSO.NumericAtomsCorrect

/-! # Atomic numeric languages agree with the established MSO automata -/
namespace DistributedSynthesis.MSO.Tree.NumericAtoms
open NumericValuations

private theorem bool_bit_one (v : Bool) : (if v then 1 else 0 : Nat) = 1 ↔ v = true := by
  cases v <;> decide
private theorem bool_bit_zero (v : Bool) : (if v then 1 else 0 : Nat) = 0 ↔ v = false := by
  cases v <;> decide
private theorem bool_bit_eq (v w : Bool) :
    (if v then 1 else 0 : Nat) = (if w then 1 else 0) ↔ v = w := by
  cases v <;> cases w <;> decide

private theorem bool_encode_zero {b : Nat} (v : Fin b → Bool) :
    FiniteFunctionCoding.encode (finTwoEquiv.symm ∘ v) = zeroVector b ↔ ∀ i, v i = false := by
  rw [encode_zero_iff]
  apply forall_congr'
  intro i
  change finTwoEquiv.symm (v i) = 0 ↔ v i = false
  cases v i <;> decide

private theorem bool_encode_edge {b : Nat} (v : Fin b → Bool) (mark : Bool) (dir : Fin b) :
    FiniteFunctionCoding.encode (finTwoEquiv.symm ∘ v) = edgeVector b (if mark then 1 else 0) dir.val ↔
      ∀ i, v i = (mark && decide (i = dir)) := by
  rw [encode_edge_iff]
  exact forall_congr' (fun _ => finTwoEquiv.symm.injective.eq_iff)

private theorem bool_encode_choice {b : Nat} (v : Fin b → Bool) :
    (∃ d < b, FiniteFunctionCoding.encode (finTwoEquiv.symm ∘ v) = edgeVector b 1 d) ↔
      ∃ d : Fin b, ∀ i, v i = decide (i = d) := by
  constructor
  · rintro ⟨d, hd, hv⟩
    exact ⟨⟨d,hd⟩, by simpa only [Bool.true_and] using (bool_encode_edge v true ⟨d,hd⟩).mp hv⟩
  · rintro ⟨d, hd⟩
    exact ⟨d.val, d.isLt, (bool_encode_edge v true d).mpr (by simpa only [Bool.true_and] using hd)⟩

variable {b a n m : Nat}
variable (tree : LabeledTree (Fin b) (ValuationLabel (Fin (a+1)) n m))

theorem false_accepts_iff : ¬ (view (b,(a,n,m),0,0,0,0)).acceptsTree tree := by
  rw [local_accepts_iff _ (by norm_num [tag])]
  simp only [localCondition, tag, ↓reduceIte]
  exact fun h => h []

theorem membership_accepts_iff (i : Fin n) (j : Fin m) :
    (view (b,(a,n,m),1,i.val,j.val,0)).acceptsTree tree ↔
      (membershipAutomaton i j).acceptsTree tree := by
  rw [local_accepts_iff _ (by norm_num [tag]), membershipAutomaton, RunParityTreeAutomaton.localTest_accepts_iff]
  apply forall_congr'
  intro p
  change (node (a,n,m) (equiv (a,n,m) (tree p)).val i.val = 1 →
    set (a,n,m) (equiv (a,n,m) (tree p)).val j.val = 1) ↔ _
  rw [node_encode, set_encode, bool_bit_one, bool_bit_one]

theorem equality_accepts_iff (i j : Fin n) :
    (view (b,(a,n,m),2,i.val,j.val,0)).acceptsTree tree ↔
      (equalityAutomaton i j).acceptsTree tree := by
  rw [local_accepts_iff _ (by norm_num [tag]), equalityAutomaton, RunParityTreeAutomaton.localTest_accepts_iff]
  apply forall_congr'
  intro p
  change node (a,n,m) (equiv (a,n,m) (tree p)).val i.val =
    node (a,n,m) (equiv (a,n,m) (tree p)).val j.val ↔ _
  rw [node_encode, node_encode, bool_bit_eq]

theorem label_accepts_iff (i : Fin n) (label : Fin (a+1)) :
    (view (b,(a,n,m),3,i.val,label.val,0)).acceptsTree tree ↔
      (labelAutomaton label i).acceptsTree tree := by
  rw [local_accepts_iff _ (by norm_num [tag]), labelAutomaton, RunParityTreeAutomaton.localTest_accepts_iff]
  apply forall_congr'
  intro p
  change (node (a,n,m) (equiv (a,n,m) (tree p)).val i.val = 1 →
    base (a,n,m) (equiv (a,n,m) (tree p)).val = label.val) ↔ _
  rw [node_encode, base_encode, bool_bit_one, Fin.val_inj]

theorem root_accepts_iff (i : Fin n) :
    (view (b,(a,n,m),4,i.val,0,0)).acceptsTree tree ↔ (rootAutomaton i).acceptsTree tree := by
  apply RunParityTreeAutomaton.acceptsTree_iff_of_equiv
    (rootAutomaton (Branch := Fin b) (Alphabet := Fin (a+1)) (m := m) i)
    (view (b,(a,n,m),4,i.val,0,0)) finTwoEquiv.symm
  · rfl
  · intro q
    cases q <;> rfl
  · intro q label next
    rw [delta_iff]
    change (((finTwoEquiv.symm q).val = 1 →
        node (a,n,m) (equiv (a,n,m) label).val i.val = 1) ∧
      FiniteFunctionCoding.encode (finTwoEquiv.symm ∘ next) = zeroVector b) ↔ _
    rw [node_encode, bool_bit_one, bool_encode_zero]
    change (((finTwoEquiv.symm q).val = 1 → label.2.1 i = true) ∧ _) ↔
      ((q = true → label.2.1 i = true) ∧ _)
    apply and_congr _ Iff.rfl
    cases q <;> simp [finTwoEquiv]

theorem successor_accepts_iff (i j : Fin n) (d : Fin b) :
    (view (b,(a,n,m),5,i.val,j.val,d.val)).acceptsTree tree ↔
      (RunParityTreeAutomaton.edgeTest (fun v => v.2.1 i) (fun v => v.2.1 j) d).acceptsTree tree := by
  apply RunParityTreeAutomaton.acceptsTree_iff_of_equiv _ _ finTwoEquiv.symm
  · rfl
  · intro q
    cases q <;> rfl
  · intro q label next
    rw [delta_iff]
    change (node (a,n,m) (equiv (a,n,m) label).val j.val = (finTwoEquiv.symm q).val ∧
      FiniteFunctionCoding.encode (finTwoEquiv.symm ∘ next) =
        edgeVector b (node (a,n,m) (equiv (a,n,m) label).val i.val) d.val) ↔ _
    rw [node_encode, node_encode]
    change (_ ∧ _) ↔ (label.2.1 j = q ∧ ∀ b, next b = (label.2.1 i && decide (b = d)))
    apply and_congr
    · cases q <;> cases label.2.1 j <;> decide
    · exact bool_encode_edge (b := b) next (label.2.1 i) d

theorem child_accepts_iff (i j : Fin n) :
    (view (b,(a,n,m),6,i.val,j.val,0)).acceptsTree tree ↔
      (Recognition.childData i j).Accepts tree := by
  apply RunParityTreeAutomaton.acceptsTree_iff_of_equiv _ _ finTwoEquiv.symm
  · rfl
  · intro q
    cases q <;> rfl
  · intro q label next
    rw [delta_iff]
    change (node (a,n,m) (equiv (a,n,m) label).val j.val = (finTwoEquiv.symm q).val ∧
      (if node (a,n,m) (equiv (a,n,m) label).val i.val = 1 then
        ∃ d < b, FiniteFunctionCoding.encode (finTwoEquiv.symm ∘ next) = edgeVector b 1 d
      else FiniteFunctionCoding.encode (finTwoEquiv.symm ∘ next) = zeroVector b)) ↔ _
    rw [node_encode, node_encode]
    change (_ ∧ _) ↔ (label.2.1 j = q ∧
      if label.2.1 i = true then ∃ d : Fin b, ∀ b, next b = decide (b = d) else ∀ b, next b = false)
    apply and_congr
    · cases q <;> cases label.2.1 j <;> decide
    · cases hi : label.2.1 i
      · simp only [hi, Bool.false_eq_true, ↓reduceIte, Nat.zero_ne_one]
        exact bool_encode_zero (b := b) next
      · simp only [hi, ↓reduceIte]
        exact bool_encode_choice (b := b) next

theorem singleton_accepts_iff (i : Fin n) :
    (view (b,(a,n,m),7,i.val,0,0)).acceptsTree tree ↔
      (TreeSingleton.automaton (fun v => v.2.1 i)).acceptsTree tree := by
  apply RunParityTreeAutomaton.acceptsTree_iff_of_equiv _ _ finTwoEquiv.symm
  · rfl
  · intro q
    cases q <;> rfl
  · intro q label next
    rw [delta_iff]
    change (if (finTwoEquiv.symm q).val = 1 then
      if node (a,n,m) (equiv (a,n,m) label).val i.val = 1 then
        FiniteFunctionCoding.encode (finTwoEquiv.symm ∘ next) = zeroVector b
      else ∃ d < b, FiniteFunctionCoding.encode (finTwoEquiv.symm ∘ next) = edgeVector b 1 d
    else node (a,n,m) (equiv (a,n,m) label).val i.val = 0 ∧
      FiniteFunctionCoding.encode (finTwoEquiv.symm ∘ next) = zeroVector b) ↔ _
    rw [node_encode]
    cases q with
    | false =>
      change ((if label.2.1 i = true then 1 else 0 : Nat) = 0 ∧ _) ↔
        (label.2.1 i = false ∧ ∀ b, next b = false)
      exact and_congr (bool_bit_zero _) (bool_encode_zero (b := b) next)
    | true =>
      change (if (if label.2.1 i = true then 1 else 0 : Nat) = 1 then _ else _) ↔
        (if label.2.1 i = true then ∀ b, next b = false else ∃ d : Fin b, ∀ b, next b = decide (b = d))
      cases hi : label.2.1 i
      · simp only [hi, Bool.false_eq_true, ↓reduceIte, Nat.zero_ne_one]
        exact bool_encode_choice (b := b) next
      · simp only [hi, ↓reduceIte]
        exact bool_encode_zero (b := b) next

end DistributedSynthesis.MSO.Tree.NumericAtoms
