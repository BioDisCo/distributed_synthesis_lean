/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.FiniteRunMSO
import DistributedSynthesis.Library.Logic.MSO.NumericModel

/-! Finite model extraction for the exact finite-table acceptance language.
The existing numeric MSO compiler supplies a finite monitor, and the existing
finite controller search returns its finite generating table. -/
namespace Characterisation.ComponentTrees.FiniteRunMSO
open DistributedSynthesis
open scoped DistributedSynthesis.FiniteOrders
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
variable {Alphabet Edge : Type} [Fintype Alphabet] [LinearOrder Alphabet] [Nonempty Alphabet]
variable [Fintype Edge] [LinearOrder Edge]

/-- Sorted numbering, without changing the finite alphabet or its semantics. -/
def labelIndex : Alphabet ≃ Fin (Fintype.card Alphabet - 1 + 1) :=
  (monoEquivOfFin Alphabet rfl).toEquiv.symm.trans
    (finCongr (by have positive := Fintype.card_pos (α:=Alphabet); omega))

variable {Branch Label : Type}

def renameAlphabet (T : Tables Branch Alphabet Edge) (e : Alphabet ≃ Label) : Tables Branch Label Edge where
  initial := T.initial
  root a := T.root (e.symm a)
  child a d b := T.child (e.symm a) d (e.symm b)
  allowed a h := T.allowed (e.symm a) h
  step a d h k := T.step (e.symm a) d h k
  priority a h := T.priority (e.symm a) h

theorem renameAlphabet_accepting (T : Tables Branch Alphabet Edge) (e : Alphabet ≃ Label)
    (code : LabeledTree Branch Label) :
    Accepting (renameAlphabet T e) code ↔ Accepting T (e.symm ∘ code) := Iff.rfl

theorem renameAlphabet_nonempty (T : Tables Branch Alphabet Edge) (e : Alphabet ≃ Label) :
    (∃ code, Accepting (renameAlphabet T e) code) ↔ ∃ code, Accepting T code := by
  constructor
  · rintro ⟨code,accepting⟩
    exact ⟨e.symm ∘ code,accepting⟩
  · rintro ⟨code,accepting⟩
    refine ⟨e ∘ code,?_⟩
    have same : e.symm ∘ (e ∘ code) = code := funext (fun n => e.symm_apply_apply (code n))
    apply (renameAlphabet_accepting T e _).mpr
    rw [same]
    exact accepting

variable {b : Nat} (T : Tables (Fin (b+1)) Alphabet Edge)
variable (index : Edge ≃ Fin (Fintype.card Edge))

def numericSentence := acceptanceFormula (renameAlphabet T (labelIndex (Alphabet:=Alphabet))) index

def finiteGenerator := MSO.Tree.NumericModel.extract (numericSentence T index)

def generatedModel
    (policy : (MSO.Tree.NumericModel.monitor (numericSentence T index)).State →
      Fin (EncodedTreeNonemptiness.labels (EncodedProjectedTree.monitorData
        (MSO.Tree.NumericModel.data (numericSentence T index))))) : LabeledTree (Fin (b+1)) Alphabet :=
  (labelIndex (Alphabet:=Alphabet)).symm ∘ MSO.Tree.NumericModel.model (numericSentence T index) policy

theorem generatedModel_correct (policy) (found : finiteGenerator T index = some policy) :
    Accepting T (generatedModel T index policy) :=
  (acceptanceFormula_correct (renameAlphabet T (labelIndex (Alphabet:=Alphabet))) index _).mp
    (MSO.Tree.NumericModel.model_correct _ policy found)

theorem finiteGenerator_complete : (∃ policy, finiteGenerator T index = some policy) ↔
    ∃ code, Accepting T code := by
  rw [finiteGenerator,MSO.Tree.NumericModel.extract_complete]
  exact (exists_congr (acceptanceFormula_correct _ index)).trans (renameAlphabet_nonempty T _)

/-- The finite generator is unfolded only on requested finite addresses. -/
def extractModel : Option (LabeledTree (Fin (b+1)) Alphabet) :=
  (finiteGenerator T index).map (generatedModel T index)

theorem extractModel_complete : (∃ code, extractModel T index = some code) ↔
    ∃ code, Accepting T code := by
  have found : (∃ code, extractModel T index = some code) ↔ ∃ policy, finiteGenerator T index = some policy := by
    unfold extractModel
    cases h : finiteGenerator T index <;> simp
  exact found.trans (finiteGenerator_complete T index)

theorem extractModel_sound (code : LabeledTree (Fin (b+1)) Alphabet)
    (found : extractModel T index = some code) : Accepting T code := by
  unfold extractModel at found
  cases h : finiteGenerator T index with
  | none => simp only [h,Option.map_none] at found; cases found
  | some policy =>
    simp only [h,Option.map_some,Option.some.injEq] at found
    exact found ▸ generatedModel_correct T index policy h

/-- Positive arities are normalized to the numeric compiler's successor
convention; no additional child direction is introduced. -/
def model {capacity : Nat} (T : Tables (Fin capacity) Alphabet Edge)
    (positive : 0 < capacity) (index : Edge ≃ Fin (Fintype.card Edge)) :
    Option (LabeledTree (Fin capacity) Alphabet) :=
  match capacity with
  | 0 => False.elim (Nat.not_lt_zero _ positive)
  | _+1 => extractModel T index

theorem model_complete {capacity : Nat} (T : Tables (Fin capacity) Alphabet Edge)
    (positive : 0 < capacity) (index : Edge ≃ Fin (Fintype.card Edge)) :
    (∃ code, model T positive index = some code) ↔ ∃ code, Accepting T code := by
  cases capacity with
  | zero => omega
  | succ b => exact extractModel_complete T index

theorem model_sound {capacity : Nat} (T : Tables (Fin capacity) Alphabet Edge)
    (positive : 0 < capacity) (index : Edge ≃ Fin (Fintype.card Edge))
    (code : LabeledTree (Fin capacity) Alphabet) (found : model T positive index = some code) :
    Accepting T code := by
  cases capacity with
  | zero => omega
  | succ b => exact extractModel_sound T index code found

end Characterisation.ComponentTrees.FiniteRunMSO
