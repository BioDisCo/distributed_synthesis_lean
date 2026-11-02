/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Logic.MSO.FirstOrder

/-! # Full MSO-to-parity-tree-automaton translation

Structural induction covers every constructor of `MSO.Formula`, including
arbitrary Mathlib first-order formulas and both sorts of quantifiers. The
construction is semantic and noncomputable; no finite-table executability
claim is made by this module.
-/
namespace DistributedSynthesis.MSO.Tree

variable {Branch Alphabet : Type*} [Fintype Branch] [Nonempty Branch] [Fintype Alphabet]
variable {n m : Nat}

/-- Every full MSO formula is recognized on its encoded valuations. -/
theorem formula_recognizable (φ : Formula (language Branch Alphabet) n m) :
    Recognizable (fun tree nodes sets => Realize tree φ nodes sets) := by
  induction φ with
  | firstOrder φ => exact firstOrder_recognizable φ
  | mem x X => exact ⟨membershipAutomaton x X, membershipAutomaton_correct x X⟩
  | falsum => exact Recognizable.falsum
  | imp φ ψ hφ hψ => exact hφ.impl hψ
  | allNode φ ih => exact ih.forallNode
  | allSet φ ih => exact ih.forallSet

/-- Semantic translation to the existing run-based parity tree automaton.
No compiler or closure certificate is supplied as a hypothesis. -/
noncomputable def toAutomaton (φ : Formula (language Branch Alphabet) n m) :
    RunParityTreeAutomaton.{_, _, 0} Branch (ValuationLabel Alphabet n m) :=
  (formula_recognizable φ).choose

theorem toAutomaton_correct (φ : Formula (language Branch Alphabet) n m) :
    Represents (toAutomaton φ) φ :=
  (formula_recognizable φ).choose_spec

/-- A sentence needs no input markers. -/
noncomputable def sentenceAutomaton (φ : Sentence (language Branch Alphabet)) :
    RunParityTreeAutomaton.{_, _, 0} Branch Alphabet :=
  (toAutomaton φ).comap (fun a => (a, Fin.elim0, Fin.elim0))

/-- The MSO-to-automata direction for complete infinite trees. -/
theorem sentenceAutomaton_correct (φ : Sentence (language Branch Alphabet))
    (tree : LabeledTree Branch Alphabet) :
    (sentenceAutomaton φ).acceptsTree tree ↔ Satisfies tree φ := by
  rw [sentenceAutomaton, RunParityTreeAutomaton.comap_acceptsTree_iff]
  have labels : (fun a => (a, Fin.elim0, Fin.elim0)) ∘ tree =
      encode tree (Fin.elim0 : Fin 0 → TreeNode Branch)
        (Fin.elim0 : Fin 0 → Set (TreeNode Branch)) := by
    funext node
    exact Prod.ext rfl (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _))
  rw [labels]
  exact toAutomaton_correct φ tree Fin.elim0 Fin.elim0

end DistributedSynthesis.MSO.Tree
