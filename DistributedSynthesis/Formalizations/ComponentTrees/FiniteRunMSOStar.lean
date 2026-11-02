/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.FiniteModels

/-! Finite tests on a node and all its children, added to the existing
universal run condition. These tests express coverage and uniqueness of
successor components when their descriptions occur only at the children.
Model extraction retains the complete input letters.
-/
namespace Characterisation.ComponentTrees.FiniteRunMSO.Star
open DistributedSynthesis DistributedSynthesis.MSO DistributedSynthesis.MSO.Tree
open scoped DistributedSynthesis.FiniteOrders
set_option maxHeartbeats 200000
set_option linter.unusedSectionVars false
variable {Branch Alphabet Edge : Type}
variable [Fintype Branch] [Fintype Alphabet] [Fintype Edge]
variable [LinearOrder Branch] [LinearOrder Alphabet] [LinearOrder Edge]
variable (T : Tables Branch Alphabet Edge)
variable (C : Alphabet → (Branch → Alphabet) → Bool)

def StarLocal (tree : LabeledTree Branch Alphabet) : Prop :=
  ∀ node, C (tree node) (fun dir => tree (node ++ [dir])) = true

def Local (tree : LabeledTree Branch Alphabet) : Prop :=
  StarLocal C tree ∧ FiniteRunMSO.Local T tree

def Accepting (tree : LabeledTree Branch Alphabet) : Prop :=
  Local T C tree ∧ ∀ branch edges, Run T tree branch edges →
    NatSeqMinEvenParity (fun n => T.priority (tree (branchNode branch n)) (edges n))

private def enumeration (X : Type) [Fintype X] [LinearOrder X] : List X :=
  Finset.univ.sort (· ≤ ·)

@[simp] private theorem mem_enumeration {X : Type} [Fintype X] [LinearOrder X] (x : X) :
    x ∈ enumeration X := by simp [enumeration]

def starFormula : Sentence (language Branch Alphabet) :=
  .allNode (.anyOf ((enumeration (Alphabet × (Branch → Alphabet))).map (fun config =>
    (label config.1 0).and ((Formula.ofBool (C config.1 config.2)).and
      (.allOf ((enumeration Branch).map (fun dir =>
        .allNode ((successor dir 0 1).imp (label (config.2 dir) 1)))))))))

theorem starFormula_correct (tree : LabeledTree Branch Alphabet) :
    Tree.Satisfies tree (starFormula C) ↔ StarLocal C tree := by
  classical
  simp [Tree.Satisfies,starFormula,Tree.Realize,Fin.snoc,StarLocal]
  constructor
  · intro checked node
    obtain ⟨children,legal,agree⟩ := checked node
    have same : children = fun dir => tree (node ++ [dir]) := by
      funext dir
      exact (agree dir).symm
    simpa only [same] using legal
  · intro checked node
    exact ⟨fun dir => tree (node ++ [dir]),checked node,fun _ => rfl⟩

variable {k : Nat} (index : Edge ≃ Fin k)

def sentence : Sentence (language Branch Alphabet) :=
  (starFormula C).and (acceptanceFormula T index)

variable [Nonempty Branch]

theorem sentence_correct (tree : LabeledTree Branch Alphabet) :
    Tree.Satisfies tree (sentence T C index) ↔ Accepting T C tree := by
  letI := treeStructure Branch Alphabet tree
  unfold sentence Tree.Satisfies Tree.Realize
  rw [Formula.realize_and]
  change (Tree.Satisfies tree (starFormula C) ∧ Tree.Satisfies tree (acceptanceFormula T index)) ↔ _
  rw [starFormula_correct,acceptanceFormula_correct]
  exact and_assoc.symm

variable [Inhabited Branch]
def satisfiable : Bool := Executable.satisfiable (sentence T C index)

theorem satisfiable_correct : satisfiable T C index = true ↔ ∃ tree, Accepting T C tree := by
  rw [satisfiable,Executable.satisfiable_correct]
  exact exists_congr (sentence_correct T C index)

section Rename
variable {Label : Type} [Fintype Label] [LinearOrder Label]
variable (equiv : Alphabet ≃ Label)

def renameCheck : Label → (Branch → Label) → Bool :=
  fun current children => C (equiv.symm current) (equiv.symm ∘ children)

theorem rename_accepting (tree : LabeledTree Branch Label) :
    Accepting (renameAlphabet T equiv) (renameCheck C equiv) tree ↔
      Accepting T C (equiv.symm ∘ tree) := Iff.rfl

theorem rename_nonempty :
    (∃ tree, Accepting (renameAlphabet T equiv) (renameCheck C equiv) tree) ↔
      ∃ tree, Accepting T C tree := by
  constructor
  · rintro ⟨tree,accepted⟩
    exact ⟨equiv.symm ∘ tree,accepted⟩
  · rintro ⟨tree,accepted⟩
    refine ⟨equiv ∘ tree,?_⟩
    apply (rename_accepting T C equiv _).mpr
    have same : equiv.symm ∘ (equiv ∘ tree) = tree := funext (fun node => equiv.symm_apply_apply _)
    simpa only [same] using accepted
end Rename

section Models
variable [Nonempty Alphabet] {b : Nat}
variable (T : Tables (Fin (b+1)) Alphabet Edge)
variable (C : Alphabet → (Fin (b+1) → Alphabet) → Bool)
variable (index : Edge ≃ Fin k)

def numericSentence :=
  sentence (renameAlphabet T (labelIndex (Alphabet:=Alphabet)))
    (renameCheck C (labelIndex (Alphabet:=Alphabet))) index

def finiteGenerator := NumericModel.extract (numericSentence T C index)

def generatedModel (policy : (NumericModel.monitor (numericSentence T C index)).State →
    Fin (EncodedTreeNonemptiness.labels (EncodedProjectedTree.monitorData
      (NumericModel.data (numericSentence T C index))))) : LabeledTree (Fin (b+1)) Alphabet :=
  (labelIndex (Alphabet:=Alphabet)).symm ∘ NumericModel.model (numericSentence T C index) policy

theorem generatedModel_correct (policy) (found : finiteGenerator T C index = some policy) :
    Accepting T C (generatedModel T C index policy) :=
  (sentence_correct (renameAlphabet T (labelIndex (Alphabet:=Alphabet)))
    (renameCheck C (labelIndex (Alphabet:=Alphabet))) index _).mp
      (NumericModel.model_correct _ policy found)

theorem finiteGenerator_complete : (∃ policy, finiteGenerator T C index = some policy) ↔
    ∃ tree, Accepting T C tree := by
  rw [finiteGenerator,NumericModel.extract_complete]
  exact (exists_congr (sentence_correct _ _ index)).trans (rename_nonempty T C _)

def extractModel : Option (LabeledTree (Fin (b+1)) Alphabet) :=
  (finiteGenerator T C index).map (generatedModel T C index)

theorem extractModel_sound (tree : LabeledTree (Fin (b+1)) Alphabet)
    (found : extractModel T C index = some tree) : Accepting T C tree := by
  unfold extractModel at found
  cases h : finiteGenerator T C index with
  | none => simp only [h,Option.map_none] at found; cases found
  | some policy =>
    simp only [h,Option.map_some,Option.some.injEq] at found
    exact found ▸ generatedModel_correct T C index policy h

theorem extractModel_complete : (∃ tree, extractModel T C index = some tree) ↔
    ∃ tree, Accepting T C tree := by
  have found : (∃ tree, extractModel T C index = some tree) ↔
      ∃ policy, finiteGenerator T C index = some policy := by
    unfold extractModel
    cases h : finiteGenerator T C index <;> simp
  exact found.trans (finiteGenerator_complete T C index)

def model {capacity : Nat} (T : Tables (Fin capacity) Alphabet Edge)
    (C : Alphabet → (Fin capacity → Alphabet) → Bool) (positive : 0 < capacity)
    (index : Edge ≃ Fin k) : Option (LabeledTree (Fin capacity) Alphabet) :=
  match capacity with
  | 0 => False.elim (Nat.not_lt_zero _ positive)
  | _+1 => extractModel T C index

theorem model_sound {capacity : Nat} (T : Tables (Fin capacity) Alphabet Edge)
    (C : Alphabet → (Fin capacity → Alphabet) → Bool) (positive : 0 < capacity)
    (index : Edge ≃ Fin k) (tree : LabeledTree (Fin capacity) Alphabet)
    (found : model T C positive index = some tree) : Accepting T C tree := by
  cases capacity with
  | zero => omega
  | succ b => exact extractModel_sound T C index tree found

theorem model_complete {capacity : Nat} (T : Tables (Fin capacity) Alphabet Edge)
    (C : Alphabet → (Fin capacity → Alphabet) → Bool) (positive : 0 < capacity)
    (index : Edge ≃ Fin k) :
    (∃ tree, model T C positive index = some tree) ↔ ∃ tree, Accepting T C tree := by
  cases capacity with
  | zero => omega
  | succ b => exact extractModel_complete T C index
end Models
end Characterisation.ComponentTrees.FiniteRunMSO.Star
