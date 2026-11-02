/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemStateControlledTreeRationalization

/-!
# Finite labels retained by state-controlled tree rationalization

Operational witnesses sometimes have to be chosen at the exact semantic
tree occurrence, before the Rabin-basis extraction.  This file supplies the
generic construction for run-based parity tree automata.  A finite label is
paired with every old alphabet letter and checked by a local transition
predicate.  The accepting run and its priorities are unchanged, so the
checked state-controlled extraction returns a finite table which retains the
extra label at every controller state.

The construction is deliberately alphabet-level.  In particular, the extra
label is not reconstructed from a quotient state after rationalization.
-/

namespace DistributedSynthesis

universe u v w x

namespace RunParityTreeAutomaton

variable {Branch : Type u} {Alphabet : Type v}

/-- Decorate every alphabet letter by a finite operational witness.  The
automaton state, initial state, and priority map are definitionally the old
ones; `Allowed` is checked in addition to the old transition relation. -/
def finiteLabelDecoration
    (A : RunParityTreeAutomaton.{u, v, w} Branch Alphabet)
    (Extra : Type x)
    (Allowed : A.State → Alphabet → Extra → Prop) :
    RunParityTreeAutomaton.{u, max v x, w} Branch (Alphabet × Extra) where
  State := A.State
  stateFinite := A.stateFinite
  initial := A.initial
  delta := fun state letter children ↦
    A.delta state letter.1 children ∧ Allowed state letter.1 letter.2
  priority := A.priority

@[simp] theorem finiteLabelDecoration_initial
    (A : RunParityTreeAutomaton.{u, v, w} Branch Alphabet)
    (Extra : Type x)
    (Allowed : A.State → Alphabet → Extra → Prop) :
    (A.finiteLabelDecoration Extra Allowed).initial = A.initial :=
  rfl

@[simp] theorem finiteLabelDecoration_priority
    (A : RunParityTreeAutomaton.{u, v, w} Branch Alphabet)
    (Extra : Type x)
    (Allowed : A.State → Alphabet → Extra → Prop)
    (state : A.State) :
    (A.finiteLabelDecoration Extra Allowed).priority state = A.priority state :=
  rfl

/-- An accepting old run remains accepting when every occurrence is supplied
with an allowed finite annotation. -/
theorem isAcceptingRun_finiteLabelDecoration
    (A : RunParityTreeAutomaton.{u, v, w} Branch Alphabet)
    (Extra : Type x)
    (Allowed : A.State → Alphabet → Extra → Prop)
    (tree : LabeledTree Branch Alphabet)
    (run : TreeNode Branch → A.State)
    (extra : TreeNode Branch → Extra)
    (haccepts : A.IsAcceptingRun tree run)
    (hallowed : ∀ node,
      Allowed (run node) (tree node) (extra node)) :
    (A.finiteLabelDecoration Extra Allowed).IsAcceptingRun
      (fun node ↦ (tree node, extra node)) run := by
  refine ⟨⟨haccepts.1.1, ?_⟩, ?_⟩
  · intro node
    exact ⟨haccepts.1.2 node, hallowed node⟩
  · exact haccepts.2

/-- Existential tree acceptance survives an occurrence-sensitive finite
decoration. -/
theorem acceptsTree_finiteLabelDecoration
    (A : RunParityTreeAutomaton.{u, v, w} Branch Alphabet)
    (Extra : Type x)
    (Allowed : A.State → Alphabet → Extra → Prop)
    (tree : LabeledTree Branch Alphabet)
    (run : TreeNode Branch → A.State)
    (extra : TreeNode Branch → Extra)
    (haccepts : A.IsAcceptingRun tree run)
    (hallowed : ∀ node,
      Allowed (run node) (tree node) (extra node)) :
    (A.finiteLabelDecoration Extra Allowed).acceptsTree
      (fun node ↦ (tree node, extra node)) :=
  ⟨run, A.isAcceptingRun_finiteLabelDecoration Extra Allowed tree run extra
    haccepts hallowed⟩

/-- Forgetting the finite decoration maps any accepting decorated tree back
to an accepting old tree. -/
theorem acceptsTree_fst_of_finiteLabelDecoration
    (A : RunParityTreeAutomaton.{u, v, w} Branch Alphabet)
    (Extra : Type x)
    (Allowed : A.State → Alphabet → Extra → Prop)
    (tree : LabeledTree Branch (Alphabet × Extra))
    (haccepts : (A.finiteLabelDecoration Extra Allowed).acceptsTree tree) :
    A.acceptsTree (fun node ↦ (tree node).1) := by
  rcases haccepts with ⟨run, hrun, hparity⟩
  refine ⟨run, ⟨hrun.1, ?_⟩, hparity⟩
  intro node
  exact (hrun.2 node).1

namespace StateControlledTreeTable

/-- Project a decorated finite table to the old alphabet while retaining its
state transition table definitionally. -/
def fstDecoration
    (A : RunParityTreeAutomaton.{u, v, w} Branch Alphabet)
    (Extra : Type x)
    (Allowed : A.State → Alphabet → Extra → Prop)
    (table : StateControlledTreeTable
      (A.finiteLabelDecoration Extra Allowed)) :
    StateControlledTreeTable A where
  step := table.step
  label := fun state ↦ (table.label state).1

@[simp] theorem fstDecoration_step
    (A : RunParityTreeAutomaton.{u, v, w} Branch Alphabet)
    (Extra : Type x)
    (Allowed : A.State → Alphabet → Extra → Prop)
    (table : StateControlledTreeTable
      (A.finiteLabelDecoration Extra Allowed))
    (state : A.State) (branch : Branch) :
    (table.fstDecoration A Extra Allowed).step state branch =
      table.step state branch :=
  rfl

@[simp] theorem fstDecoration_label
    (A : RunParityTreeAutomaton.{u, v, w} Branch Alphabet)
    (Extra : Type x)
    (Allowed : A.State → Alphabet → Extra → Prop)
    (table : StateControlledTreeTable
      (A.finiteLabelDecoration Extra Allowed))
    (state : A.State) :
    (table.fstDecoration A Extra Allowed).label state =
      (table.label state).1 :=
  rfl

@[simp] theorem fstDecoration_labeledTree
    (A : RunParityTreeAutomaton.{u, v, w} Branch Alphabet)
    (Extra : Type x)
    (Allowed : A.State → Alphabet → Extra → Prop)
    (table : StateControlledTreeTable
      (A.finiteLabelDecoration Extra Allowed))
    (node : TreeNode Branch) :
    (table.fstDecoration A Extra Allowed).toTransitionRationalTree.labeledTree
        node =
      (table.toTransitionRationalTree.labeledTree node).1 := by
  rfl

/-- The second coordinate of the table label is the retained finite witness
available at each runtime controller state. -/
def decorationAt
    (A : RunParityTreeAutomaton.{u, v, w} Branch Alphabet)
    (Extra : Type x)
    (Allowed : A.State → Alphabet → Extra → Prop)
    (table : StateControlledTreeTable
      (A.finiteLabelDecoration Extra Allowed)) :
    A.State → Extra :=
  fun state ↦ (table.label state).2

end StateControlledTreeTable

/-- Acceptance of a decorated state-controlled table implies acceptance of
its projection. -/
theorem StateControlledTreeTable.fstDecoration_accepts
    (A : RunParityTreeAutomaton.{u, v, w} Branch Alphabet)
    (Extra : Type x)
    (Allowed : A.State → Alphabet → Extra → Prop)
    (table : StateControlledTreeTable
      (A.finiteLabelDecoration Extra Allowed))
    (haccepts : (A.finiteLabelDecoration Extra Allowed).acceptsTree
      table.toTransitionRationalTree.labeledTree) :
    A.acceptsTree
      (table.fstDecoration A Extra Allowed).toTransitionRationalTree.labeledTree := by
  apply A.acceptsTree_fst_of_finiteLabelDecoration Extra Allowed
    table.toTransitionRationalTree.labeledTree haccepts

/-- Checked state-controlled extraction with an occurrence-sensitive finite
label.  The output controller state type is still definitionally `A.State`;
the finite witness is retained in its label table. -/
theorem exists_stateControlledTreeTable_finiteLabelDecoration
    {Extra : Type x}
    [Fintype Branch] [Fintype Alphabet] [Fintype Extra] [Nonempty Branch]
    (A : RunParityTreeAutomaton.{u, v, w} Branch Alphabet)
    (Allowed : A.State → Alphabet → Extra → Prop)
    (tree : LabeledTree Branch Alphabet)
    (run : TreeNode Branch → A.State)
    (extra : TreeNode Branch → Extra)
    (haccepts : A.IsAcceptingRun tree run)
    (hallowed : ∀ node,
      Allowed (run node) (tree node) (extra node)) :
    ∃ table : StateControlledTreeTable
        (A.finiteLabelDecoration Extra Allowed),
      (A.finiteLabelDecoration Extra Allowed).acceptsTree
        table.toTransitionRationalTree.labeledTree := by
  apply (A.finiteLabelDecoration Extra Allowed
    ).exists_stateControlledTreeTable_accepted
  exact ⟨fun node ↦ (tree node, extra node),
    A.acceptsTree_finiteLabelDecoration Extra Allowed tree run extra haccepts
      hallowed⟩

/-- Strong operational form of the decorated extraction.  Besides acceptance,
it exposes that the retained annotation is allowed at every controller state
which is actually reached by a branch word.  This conclusion uses the
extracted controller itself as the accepting run; it is intentionally
stronger than merely projecting an existential accepting run. -/
theorem exists_stateControlledTreeTable_finiteLabelDecoration_reachable
    {Extra : Type x}
    [Fintype Branch] [Fintype Alphabet] [Fintype Extra] [Nonempty Branch]
    (A : RunParityTreeAutomaton.{u, v, w} Branch Alphabet)
    (Allowed : A.State → Alphabet → Extra → Prop)
    (tree : LabeledTree Branch Alphabet)
    (run : TreeNode Branch → A.State)
    (extra : TreeNode Branch → Extra)
    (haccepts : A.IsAcceptingRun tree run)
    (hallowed : ∀ node,
      Allowed (run node) (tree node) (extra node)) :
    ∃ table : StateControlledTreeTable
        (A.finiteLabelDecoration Extra Allowed),
      (A.finiteLabelDecoration Extra Allowed).acceptsTree
          table.toTransitionRationalTree.labeledTree ∧
        ∀ node : TreeNode Branch,
          Allowed (table.toTransitionRationalTree.controlAt node)
            (table.toTransitionRationalTree.labeledTree node).1
            (table.toTransitionRationalTree.labeledTree node).2 := by
  classical
  let decorated := A.finiteLabelDecoration Extra Allowed
  have hdecorated : ∃ decoratedTree : LabeledTree Branch (Alphabet × Extra),
      decorated.acceptsTree decoratedTree :=
    ⟨fun node ↦ (tree node, extra node),
      A.acceptsTree_finiteLabelDecoration Extra Allowed tree run extra
        haccepts hallowed⟩
  let witness := Classical.choose hdecorated
  let strategy := Classical.choose
    (decorated.exists_evenPositionalStrategy_of_accepts hdecorated)
  have hstrategy := Classical.choose_spec
    (decorated.exists_evenPositionalStrategy_of_accepts hdecorated)
  let table : StateControlledTreeTable decorated :=
    { step := chosenChildren decorated strategy
      label := chosenLabel decorated strategy (witness []) }
  refine ⟨table, acceptsTree_extractedTree decorated strategy (witness [])
    hstrategy, ?_⟩
  intro node
  have hgood := goodState_extractedControl decorated strategy (witness [])
    hstrategy node
  have hdelta :=
    (chosenLabel_children_spec decorated strategy (witness []) hgood).1
  exact hdelta.2

end RunParityTreeAutomaton

end DistributedSynthesis
