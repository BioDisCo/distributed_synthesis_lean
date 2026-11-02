/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Logic.MSO

/-! Regression checks for full powerset semantics and tree complementation. -/
namespace DistributedSynthesis.Tests.MSO

open DistributedSynthesis.MSO

private instance : FirstOrder.Language.empty.Structure Nat := FirstOrder.Language.emptyStructure

/-- A set containing every individual must include infinitely many elements.
This witness would be unavailable under finite-set (weak MSO) semantics. -/
private def containsAll : Formula FirstOrder.Language.empty 0 1 :=
  .allNode (.mem 0 0)

example : @Formula.Realize _ Nat inferInstance _ _ containsAll.exSet Fin.elim0 Fin.elim0 := by
  rw [Formula.realize_exSet]
  refine ⟨Set.univ, ?_⟩
  change ∀ x : Nat, x ∈ (Set.univ : Set Nat)
  exact fun _ => Set.mem_univ _

example (X : Set Nat)
    (satisfies : containsAll.Realize Fin.elim0 ![X]) : ¬ X.Finite := by
  have all : ∀ x : Nat, x ∈ X := by simpa [containsAll] using satisfies
  have same : X = Set.univ := Set.eq_univ_of_forall all
  rw [same]
  exact Set.infinite_univ

/-- Dropping the new set bit cannot discard the old individual or set markers. -/
example (tree : LabeledTree Bool Bool) (x : Fin 2 → TreeNode Bool)
    (sets : Fin 3 → Set (TreeNode Bool)) (X : Set (TreeNode Bool)) :
    Tree.dropSet ∘ Tree.encode tree x (Fin.snoc sets X) = Tree.encode tree x sets :=
  Tree.dropSet_encode tree x sets X

example (tree : LabeledTree Bool Unit) (x : Fin 2 → TreeNode Bool)
    (sets : Fin 0 → Set (TreeNode Bool)) :
    Tree.Realize tree (Tree.ancestor 0 1) x sets ↔ x 0 <+: x 1 :=
  Tree.realize_ancestor tree 0 1 x sets

/-- States remember the preceding direction. -/
private def branchAutomaton (priority : Bool → Nat) : RunParityTreeAutomaton Bool Unit where
  State := Bool
  stateFinite := inferInstance
  initial := false
  delta _ _ next := next = id
  priority := priority

private theorem rejects_constant_branch (priority : Bool → Nat) (direction : Bool)
    (odd : priority direction = 1) (tree : LabeledTree Bool Unit) :
    ¬ (branchAutomaton priority).acceptsTree tree := by
  rintro ⟨run, ⟨_, transitions⟩, parity⟩
  have atNext (n : Nat) : run (branchNode (fun _ => direction) (n+1)) = direction := by
    exact congrFun (transitions (branchNode (fun _ => direction) n)) direction
  apply not_natSeqMinEvenParity_of_eventually_one _ 1 _ (parity (fun _ => direction))
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simpa only [branchAutomaton, atNext] using odd

/-- Both the original automaton and its naive priority flip reject: branchwise
negation alone does not complement universal quantification over branches. -/
example (tree : LabeledTree Bool Unit) :
    ¬ (branchAutomaton (fun b => if b then 1 else 0)).acceptsTree tree ∧
    ¬ (branchAutomaton (fun b => (if b then 1 else 0) + 1)).acceptsTree tree :=
  ⟨rejects_constant_branch _ true rfl tree, rejects_constant_branch _ false rfl tree⟩

/-- The actual complement does accept the same tree. -/
example (tree : LabeledTree Bool Unit) :
    (TreeComplement.automaton (branchAutomaton (fun b => if b then 1 else 0))).acceptsTree tree :=
  (TreeComplement.accepts_iff _ tree).mpr (rejects_constant_branch _ true rfl tree)

/-- Missing transitions reject even if all priorities are even. -/
example (tree : LabeledTree Bool Unit) :
    (TreeComplement.automaton (RunParityTreeAutomaton.localTest (fun _ : Unit => False))).acceptsTree tree := by
  rw [TreeComplement.accepts_iff, RunParityTreeAutomaton.localTest_accepts_iff]
  simp

/-- Combining negation and set projection agrees with universal set semantics. -/
example (tree : LabeledTree Bool Unit) (nodes : Fin 1 → TreeNode Bool) :
    ¬ (Tree.allSetAutomaton (Tree.membershipAutomaton 0 0)).acceptsTree
      (Tree.encode tree nodes (Fin.elim0 : Fin 0 → Set (TreeNode Bool))) := by
  rw [Tree.allSetAutomaton_correct _ _ (Tree.membershipAutomaton_correct 0 0)]
  change ¬ ∀ X : Set (TreeNode Bool), nodes 0 ∈ X
  exact fun h => h ∅

/-- An empty marker is not an individual valuation. -/
example : ¬ (TreeSingleton.automaton (Branch := Bool) id).acceptsTree
    (fun _ => false) := by
  rw [TreeSingleton.accepts_iff]
  rintro ⟨witness, single⟩
  have impossible := (single witness).mpr rfl
  contradiction

/-- Neither are multiple markers, even though each branch may see markers. -/
example : ¬ (TreeSingleton.automaton (Branch := Bool) id).acceptsTree
    (fun _ => true) := by
  rw [TreeSingleton.accepts_iff]
  rintro ⟨witness, single⟩
  have a := (single []).mp rfl
  have b := (single [true]).mp rfl
  have impossible := a.trans b.symm
  cases impossible

example : (TreeSingleton.automaton (Branch := Bool) id).acceptsTree
    (fun node => decide (node = [true, false])) := by
  apply TreeSingleton.accepts_iff.mpr
  exact ⟨[true,false], fun _ => by simp⟩

/-- Individual projection asks for a node in X, not for an arbitrary marking. -/
example (tree : LabeledTree Bool Unit) (X : Set (TreeNode Bool)) :
    (Tree.exNodeAutomaton (Tree.membershipAutomaton 0 0)).acceptsTree
      (Tree.encode tree (Fin.elim0 : Fin 0 → TreeNode Bool) ![X]) ↔ X.Nonempty := by
  rw [Tree.exNodeAutomaton_correct _ _ (Tree.membershipAutomaton_correct 0 0)]
  change (¬ ∀ x : TreeNode Bool, ¬ x ∈ X) ↔ ∃ x, x ∈ X
  simp

/-- Directional successors go from parent to child, not conversely. -/
example (tree : LabeledTree Bool Unit) :
    (Tree.successorAutomaton true 0 1).acceptsTree
      (Tree.encode tree ![[], [true]] (Fin.elim0 : Fin 0 → Set (TreeNode Bool))) ∧
    ¬ (Tree.successorAutomaton true 1 0).acceptsTree
      (Tree.encode tree ![[], [true]] (Fin.elim0 : Fin 0 → Set (TreeNode Bool))) := by
  rw [Tree.successorAutomaton_correct true 0 1, Tree.successorAutomaton_correct true 1 0]
  simp

/-- The complete translation accepts a sentence needing an infinite set witness. -/
private def treeContainsAll : Formula (Tree.language Bool Unit) 0 1 :=
  .allNode (.mem 0 0)

example (tree : LabeledTree Bool Unit) :
    (Tree.sentenceAutomaton treeContainsAll.exSet).acceptsTree tree := by
  rw [Tree.sentenceAutomaton_correct]
  change Tree.Realize tree treeContainsAll.exSet Fin.elim0 Fin.elim0
  simp only [Tree.Realize, Formula.realize_exSet]
  exact ⟨Set.univ, fun _ => Set.mem_univ _⟩

/-- Alternating sorts does not accidentally exclude the empty set valuation. -/
private def everySetInhabited : Sentence (Tree.language Bool Unit) :=
  .allSet ((Formula.mem 0 0).exNode)

example (tree : LabeledTree Bool Unit) :
    ¬ (Tree.sentenceAutomaton everySetInhabited).acceptsTree tree := by
  rw [Tree.sentenceAutomaton_correct]
  change ¬ ∀ X : Set (TreeNode Bool), ¬ ∀ x : TreeNode Bool, ¬ x ∈ X
  exact fun h => h ∅ (fun _ => id)

/-- Embedded Mathlib quantifiers and successor terms use the correct bound
variable: no directional successor can equal the root. -/
private def rootHasNoParent : Sentence (Tree.language Bool Unit) :=
  .firstOrder (.all (FirstOrder.Language.BoundedFormula.equal
    (.func (L := Tree.language Bool Unit) .root Fin.elim0)
    (.func (.successor false) ![.var (Sum.inr 0)])).not)

example (tree : LabeledTree Bool Unit) :
    (Tree.sentenceAutomaton rootHasNoParent).acceptsTree tree := by
  rw [Tree.sentenceAutomaton_correct]
  change ∀ x : TreeNode Bool, ¬ ([] : TreeNode Bool) = x ++ [false]
  intro x equal
  have lengths := congrArg List.length equal
  simp at lengths

/-- The reverse translation rejects an automaton whose forced branch is odd. -/
example (tree : LabeledTree Bool Unit) :
    ¬ Tree.Satisfies tree (Tree.ofAutomaton (branchAutomaton (fun b => if b then 1 else 0))) := by
  rw [Tree.ofAutomaton_correct]
  exact rejects_constant_branch _ true rfl tree

/-- This branch set is not finite: the MSO branch formula names the full path. -/
example (tree : LabeledTree Bool Unit) (branch : Nat → Bool) :
    Tree.Realize tree (Tree.branchFormula 0) Fin.elim0 ![Set.range (branchNode branch)] := by
  rw [Tree.branchFormula_correct]
  exact Tree.isBranchSet_range branch

end DistributedSynthesis.Tests.MSO
