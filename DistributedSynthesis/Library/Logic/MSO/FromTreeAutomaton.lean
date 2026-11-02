/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Logic.MSO.AutomatonParity

/-! # Parity-tree-automaton to MSO translation

Existential state sets encode a run; a universal branch-set quantifier enforces
min-even parity. States are indexed using Mathlib's `Fintype.equivFin`.
-/
namespace DistributedSynthesis.MSO.Tree

variable {Branch Alphabet : Type*} [Fintype Branch] [Nonempty Branch] [Fintype Alphabet]
variable (A : RunParityTreeAutomaton Branch Alphabet)

namespace Automaton

noncomputable def acceptingRunFormula {m : Nat} (stateVars : A.State → Fin m) :
    Formula (language Branch Alphabet) 0 m :=
  (runFormula A stateVars).and (branchParityFormula A stateVars)

theorem acceptingRunFormula_correct {m : Nat} (stateVars : A.State → Fin m)
    (tree : LabeledTree Branch Alphabet) (sets : Fin m → Set (TreeNode Branch)) :
    Realize tree (acceptingRunFormula A stateVars) Fin.elim0 sets ↔
      ∃ run, EncodesRun A stateVars sets run ∧ A.IsAcceptingRun tree run := by
  unfold acceptingRunFormula Realize
  simp only [Formula.realize_and]
  change (Realize tree (runFormula A stateVars) Fin.elim0 sets ∧
    Realize tree (branchParityFormula A stateVars) Fin.elim0 sets) ↔ _
  rw [runFormula_correct]
  constructor
  · rintro ⟨⟨run,encodes,legal⟩,parity⟩
    exact ⟨run,encodes,legal,
      (branchParityFormula_correct A stateVars tree sets run encodes).mp parity⟩
  · rintro ⟨run,encodes,legal,parity⟩
    exact ⟨⟨run,encodes,legal⟩,
      (branchParityFormula_correct A stateVars tree sets run encodes).mpr parity⟩

/-- State sets of an actual run, indexed by the existing finite enumeration. -/
noncomputable def stateSets (run : TreeNode Branch → A.State) :
    Fin (Fintype.card A.State) → Set (TreeNode Branch) :=
  fun i => {node | run node = (Fintype.equivFin A.State).symm i}

omit [Fintype Branch] [Nonempty Branch] [Fintype Alphabet] in
theorem stateSets_encodes (run : TreeNode Branch → A.State) :
    EncodesRun A (Fintype.equivFin A.State) (stateSets A run) run := by
  intro node q
  simp [stateSets]

end Automaton

/-- Full MSO sentence defining the automaton's accepted language. -/
noncomputable def ofAutomaton : Sentence (language Branch Alphabet) :=
  (Automaton.acceptingRunFormula A (Fintype.equivFin A.State)).exAllSets

/-- The automata-to-MSO direction for complete infinite trees. -/
theorem ofAutomaton_correct (tree : LabeledTree Branch Alphabet) :
    Satisfies tree (ofAutomaton A) ↔ A.acceptsTree tree := by
  letI := treeStructure Branch Alphabet tree
  change Formula.Realize (Formula.exAllSets _) Fin.elim0 Fin.elim0 ↔ _
  rw [Formula.realize_exAllSets]
  change (∃ sets, Realize tree (Automaton.acceptingRunFormula A (Fintype.equivFin A.State))
    Fin.elim0 sets) ↔ _
  simp only [Automaton.acceptingRunFormula_correct]
  constructor
  · rintro ⟨sets,run,_,accepting⟩
    exact ⟨run,accepting⟩
  · rintro ⟨run,accepting⟩
    exact ⟨Automaton.stateSets A run,run,Automaton.stateSets_encodes A run,accepting⟩

end DistributedSynthesis.MSO.Tree
