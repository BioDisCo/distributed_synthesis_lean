/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Logic.MSO.Branches
import DistributedSynthesis.Library.Logic.MSO.FiniteQuantification

/-! # MSO encoding of tree-automaton runs

One set variable represents each state. Partition, initial-state, and local
transition formulas characterize a run of the existing tree automaton.
-/
namespace DistributedSynthesis.MSO.Tree.Automaton

variable {Branch Alphabet : Type*} {m : Nat}
variable (A : RunParityTreeAutomaton Branch Alphabet) (stateVars : A.State → Fin m)

/-- The named sets encode the state assigned to every tree node. -/
def EncodesRun (sets : Fin m → Set (TreeNode Branch)) (run : TreeNode Branch → A.State) : Prop :=
  ∀ node q, node ∈ sets (stateVars q) ↔ run node = q

theorem partition_iff_exists_run (sets : Fin m → Set (TreeNode Branch)) :
    (∀ node, ∃! q, node ∈ sets (stateVars q)) ↔ ∃ run, EncodesRun A stateVars sets run := by
  classical
  constructor
  · intro partition
    choose run member unique using partition
    refine ⟨run, fun node q => ⟨?_, ?_⟩⟩
    · intro h
      exact (unique node q h).symm
    · intro h
      simpa only [← h] using member node
  · rintro ⟨run, encodes⟩ node
    exact ⟨run node, (encodes node _).mpr rfl, fun q h => ((encodes node q).mp h).symm⟩

noncomputable def partitionFormula : Formula (language Branch Alphabet) 0 m := by
  classical
  exact .allNode (.anyOf (Finset.univ.toList.map (fun q : A.State =>
    (Formula.mem 0 (stateVars q)).and (.allOf (Finset.univ.toList.map (fun q' : A.State =>
      (Formula.mem 0 (stateVars q')).imp (.ofBool (decide (q' = q)))))))))

def initialFormula : Formula (language Branch Alphabet) 0 m :=
  ((root 0).and (.mem 0 (stateVars A.initial))).exNode

theorem partitionFormula_correct (tree : LabeledTree Branch Alphabet) (sets : Fin m → Set (TreeNode Branch)) :
    Realize tree (partitionFormula A stateVars) Fin.elim0 sets ↔
      ∀ node, ∃! q, node ∈ sets (stateVars q) := by
  classical
  simp [partitionFormula, Realize, Fin.snoc, ExistsUnique]

theorem initialFormula_correct (tree : LabeledTree Branch Alphabet) (sets : Fin m → Set (TreeNode Branch)) :
    Realize tree (initialFormula A stateVars) Fin.elim0 sets ↔ [] ∈ sets (stateVars A.initial) := by
  simp [initialFormula, Realize, Fin.snoc]

variable [Fintype Branch] [Fintype Alphabet]

noncomputable def stepFormula : Formula (language Branch Alphabet) 0 m := by
  classical
  exact .allNode (.anyOf (Finset.univ.toList.map (fun q : A.State =>
    .anyOf (Finset.univ.toList.map (fun a : Alphabet =>
      .anyOf (Finset.univ.toList.map (fun next : Branch → A.State =>
        (Formula.ofBool (decide (A.delta q a next))).and
          ((Formula.mem 0 (stateVars q)).and ((label a 0).and
            (.allOf (Finset.univ.toList.map (fun b : Branch =>
              .allNode ((successor b 0 1).imp (.mem 1 (stateVars (next b))))))))))))))))

theorem stepFormula_correct (tree : LabeledTree Branch Alphabet) (sets : Fin m → Set (TreeNode Branch)) :
    Realize tree (stepFormula A stateVars) Fin.elim0 sets ↔
      ∀ node, ∃ q a next, A.delta q a next ∧ node ∈ sets (stateVars q) ∧ tree node = a ∧
        ∀ b, node ++ [b] ∈ sets (stateVars (next b)) := by
  classical
  simp [stepFormula, Realize, Fin.snoc]

noncomputable def runFormula : Formula (language Branch Alphabet) 0 m :=
  (partitionFormula A stateVars).and ((initialFormula A stateVars).and (stepFormula A stateVars))

theorem runFormula_correct (tree : LabeledTree Branch Alphabet) (sets : Fin m → Set (TreeNode Branch)) :
    Realize tree (runFormula A stateVars) Fin.elim0 sets ↔
      ∃ run, EncodesRun A stateVars sets run ∧ A.IsRun tree run := by
  unfold runFormula Realize
  simp only [Formula.realize_and]
  change (Realize tree (partitionFormula A stateVars) Fin.elim0 sets ∧
    Realize tree (initialFormula A stateVars) Fin.elim0 sets ∧
    Realize tree (stepFormula A stateVars) Fin.elim0 sets) ↔ _
  rw [partitionFormula_correct, initialFormula_correct, stepFormula_correct, partition_iff_exists_run]
  constructor
  · rintro ⟨⟨run,encodes⟩,initial,transitions⟩
    refine ⟨run,encodes,⟨(encodes [] A.initial).mp initial,?_⟩⟩
    intro node
    obtain ⟨q,a,next,legal,member,letter,children⟩ := transitions node
    have state := (encodes node q).mp member
    have values : (fun b => run (node ++ [b])) = next := funext (fun b => (encodes _ _).mp (children b))
    simpa only [state,letter,values] using legal
  · rintro ⟨run,encodes,initial,transitions⟩
    refine ⟨⟨run,encodes⟩,(encodes [] A.initial).mpr initial,?_⟩
    intro node
    exact ⟨run node,tree node,(fun b => run (node ++ [b])),transitions node,
      (encodes node _).mpr rfl,rfl,fun b => (encodes _ _).mpr rfl⟩

end DistributedSynthesis.MSO.Tree.Automaton
