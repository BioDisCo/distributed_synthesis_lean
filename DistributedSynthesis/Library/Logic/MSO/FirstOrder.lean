/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Logic.MSO.Terms

/-! # Recognition of arbitrary Mathlib first-order formulas on trees

Free and bound variables are concatenated using Mathlib's finite-tuple
operations. This preserves the existing de Bruijn levels and quantifier
semantics instead of introducing another first-order syntax.
-/
namespace DistributedSynthesis.MSO.Tree

variable {Branch Alphabet : Type*} {n m k : Nat}

def boundedValue (tree : LabeledTree Branch Alphabet)
    (φ : (language Branch Alphabet).BoundedFormula (Fin n) k)
    (free : Fin n → TreeNode Branch) (bound : Fin k → TreeNode Branch) : Prop :=
  @FirstOrder.Language.BoundedFormula.Realize _ _ (treeStructure Branch Alphabet tree) _ _ φ free bound

private theorem flatten_term_value (tree : LabeledTree Branch Alphabet)
    (nodes : Fin (n+k) → TreeNode Branch)
    (t : (language Branch Alphabet).Term (Fin n ⊕ Fin k)) :
    termValue tree nodes (t.relabel (Sum.elim (Fin.castAdd k) (Fin.natAdd n))) =
      @FirstOrder.Language.Term.realize _ _ (treeStructure Branch Alphabet tree) _
        (Sum.elim (fun i => nodes (Fin.castAdd k i)) (fun j => nodes (Fin.natAdd n j))) t := by
  letI := treeStructure Branch Alphabet tree
  unfold termValue
  rw [FirstOrder.Language.Term.realize_relabel]
  congr 1
  funext z
  cases z <;> rfl

variable [Fintype Branch] [Nonempty Branch] [Fintype Alphabet]

theorem bounded_recognizable (φ : (language Branch Alphabet).BoundedFormula (Fin n) k) :
    Recognizable (m := m) (fun tree nodes _ => boundedValue tree φ
      (fun i => nodes (Fin.castAdd k i)) (fun j => nodes (Fin.natAdd n j))) := by
  induction φ with
  | falsum => exact Recognizable.falsum
  | @equal k t s =>
    let index : Fin n ⊕ Fin k → Fin (n+k) := Sum.elim (Fin.castAdd k) (Fin.natAdd n)
    apply (equal_terms_recognizable (m := m) (t.relabel index) (s.relabel index)).congr
    intro tree nodes sets
    simp only [index, flatten_term_value]
    rfl
  | @rel k arity r args =>
    let index : Fin n ⊕ Fin k → Fin (n+k) := Sum.elim (Fin.castAdd k) (Fin.natAdd n)
    apply (relation_terms_recognizable (m := m) r (fun i => (args i).relabel index)).congr
    intro tree nodes sets
    simp only [index, flatten_term_value]
    rfl
  | imp φ ψ hφ hψ => exact hφ.impl hψ
  | all φ ih =>
    apply ih.forallNode.congr
    intro tree nodes sets
    rw [← Fin.append_castAdd_natAdd (f := nodes)]
    simp only [← Fin.append_snoc, Fin.append_left, Fin.append_right]
    rfl

/-- No restriction to atomic formulas or to quantifier-free first-order syntax. -/
theorem firstOrder_recognizable (φ : (language Branch Alphabet).Formula (Fin n)) :
    Recognizable (m := m) (fun tree nodes sets => Realize tree (.firstOrder φ) nodes sets) := by
  apply (bounded_recognizable (m := m) φ).congr
  intro tree nodes sets
  letI := treeStructure Branch Alphabet tree
  change boundedValue tree φ (fun i => nodes (Fin.castAdd 0 i))
    (fun j => nodes (Fin.natAdd n j)) ↔ φ.Realize nodes
  simp only [boundedValue, FirstOrder.Language.Formula.Realize, Fin.castAdd_zero]
  have empty : (fun j : Fin 0 => nodes (Fin.natAdd n j)) = (default : Fin 0 → TreeNode Branch) :=
    Subsingleton.elim _ _
  rw [empty]
  simp
  apply Iff.of_eq
  exact congrArg (fun bound : Fin 0 → TreeNode Branch =>
    FirstOrder.Language.BoundedFormula.Realize φ nodes bound) (Subsingleton.elim _ _)

end DistributedSynthesis.MSO.Tree
