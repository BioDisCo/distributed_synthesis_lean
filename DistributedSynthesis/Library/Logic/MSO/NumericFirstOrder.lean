/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Logic.MSO.NumericTerms
import DistributedSynthesis.Library.Logic.MSO.FirstOrder

/-! # Numeric compilation of embedded Mathlib first-order formulas -/
namespace DistributedSynthesis.MSO.Tree.Numeric
variable {b a n m k : Nat}

private theorem flatten_term_value (tree : LabeledTree (Fin (b+1)) (Fin (a+1)))
    (nodes : Fin (n+k) → TreeNode (Fin (b+1)))
    (t : (language (Fin (b+1)) (Fin (a+1))).Term (Fin n ⊕ Fin k)) :
    termValue tree nodes (t.relabel (Sum.elim (Fin.castAdd k) (Fin.natAdd n))) =
      @FirstOrder.Language.Term.realize _ _ (treeStructure (Fin (b+1)) (Fin (a+1)) tree) _
        (Sum.elim (fun i => nodes (Fin.castAdd k i)) (fun j => nodes (Fin.natAdd n j))) t := by
  letI := treeStructure (Fin (b+1)) (Fin (a+1)) tree
  unfold termValue
  rw [FirstOrder.Language.Term.realize_relabel]
  congr 1
  funext z
  cases z <;> rfl


def bounded_recognition {k : Nat} (φ : (language (Fin (b+1)) (Fin (a+1))).BoundedFormula (Fin n) k) :
    NumericRecognition (m := m) (fun tree nodes _ => boundedValue tree φ
      (fun i => nodes (Fin.castAdd k i)) (fun j => nodes (Fin.natAdd n j))) :=
  match φ with
  | .falsum => NumericRecognition.falsum
  | .equal t s => by
    let index : Fin n ⊕ Fin k → Fin (n+k) := Sum.elim (Fin.castAdd k) (Fin.natAdd n)
    apply (equal_terms_recognition (m := m) (t.relabel index) (s.relabel index)).congr
    intro tree nodes sets
    simp only [index, flatten_term_value]
    rfl
  | .rel r args => by
    let index : Fin n ⊕ Fin k → Fin (n+k) := Sum.elim (Fin.castAdd k) (Fin.natAdd n)
    apply (relation_terms_recognition (m := m) r (fun i => (args i).relabel index)).congr
    intro tree nodes sets
    simp only [index, flatten_term_value]
    rfl
  | .imp φ ψ => (bounded_recognition φ).impl (bounded_recognition ψ)
  | .all φ => by
    apply (bounded_recognition φ).forallNode.congr
    intro tree nodes sets
    rw [← Fin.append_castAdd_natAdd (f := nodes)]
    simp only [← Fin.append_snoc, Fin.append_left, Fin.append_right]
    rfl

/-- No restriction to atomic formulas or to quantifier-free first-order syntax. -/
def firstOrder_recognition (φ : (language (Fin (b+1)) (Fin (a+1))).Formula (Fin n)) :
    NumericRecognition (m := m) (fun tree nodes sets => Realize tree (.firstOrder φ) nodes sets) := by
  apply (bounded_recognition (m := m) φ).congr
  intro tree nodes sets
  letI := treeStructure (Fin (b+1)) (Fin (a+1)) tree
  change boundedValue tree φ (fun i => nodes (Fin.castAdd 0 i))
    (fun j => nodes (Fin.natAdd n j)) ↔ φ.Realize nodes
  simp only [boundedValue, FirstOrder.Language.Formula.Realize, Fin.castAdd_zero]
  have empty : (fun j : Fin 0 => nodes (Fin.natAdd n j)) = (default : Fin 0 → TreeNode (Fin (b+1))) :=
    Subsingleton.elim _ _
  rw [empty]
  simp
  apply Iff.of_eq
  exact congrArg (fun bound : Fin 0 → TreeNode (Fin (b+1)) =>
    FirstOrder.Language.BoundedFormula.Realize φ nodes bound) (Subsingleton.elim _ _)

end DistributedSynthesis.MSO.Tree.Numeric
