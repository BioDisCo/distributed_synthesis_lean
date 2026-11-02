/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmParityTreeEmptinessGame

/-!
# Input-free rational runs with arbitrary directions

This file separates two regularity theorems that had previously been hidden
behind one finite tree-automaton bundle.

* `RunParityTreeAutomaton.exists_transitionRationalRun_accepted` is proved for
  finite directions and finite labels by the checked finite emptiness game.
* The Bérard rational-run lemma has a singleton input alphabet and permits an
  arbitrary nonempty direction type.  Its exact conclusion is
  `RationalRunBasis`: an accepting run can be replaced by one whose complete
  transition depends only on its finite run state.

`InputFreeRationalRunAutomaton` is the reusable arbitrary-direction bundle.  It
does not pretend that the second theorem follows from the first: its
`rationalRunBasis` field is precisely the classical input-free lemma.  Finite
direction automata obtain the field unconditionally through `ofFinite`.
-/

namespace DistributedSynthesis

universe u w

/-- Run-based parity tree automata over the unique input tree.  Directions may
be finite or infinite; the automaton state type is finite by construction. -/
abbrev InputFreeRunParityTreeAutomaton (Branch : Type u) :=
  RunParityTreeAutomaton.{u, 0, w} Branch PUnit

namespace InputFreeRunParityTreeAutomaton

variable {Branch : Type u}

/-- The unique input tree. -/
def uniqueTree : LabeledTree Branch PUnit :=
  fun _ => PUnit.unit

/-- Nonemptiness in the input-free presentation. -/
def NonemptyLanguage
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch) : Prop :=
  ∃ run : TreeNode Branch -> A.State,
    A.IsAcceptingRun uniqueTree run

/-- Existence of an accepting run whose complete transition is determined by
the current finite automaton state.  This is the paper's notion of a rational
run, not merely a tree with finitely many node labels. -/
def HasRationalRun
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch) : Prop :=
  ∃ run : TreeNode Branch -> A.State,
    A.IsTransitionRationalRun uniqueTree run

/-- Exact statement of the input-free rational-run basis theorem. -/
def RationalRunBasis
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch) : Prop :=
  A.NonemptyLanguage -> A.HasRationalRun

/-- On finite direction types, the arbitrary-direction statement specializes
to the already checked finite emptiness-game theorem. -/
theorem rationalRunBasis_of_finite
    [Fintype Branch]
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch) :
    A.RationalRunBasis := by
  intro hnonempty
  have haccepts :
      ∃ tree : LabeledTree Branch PUnit, A.acceptsTree tree := by
    rcases hnonempty with ⟨run, hrun⟩
    exact ⟨uniqueTree, run, hrun⟩
  rcases A.exists_transitionRationalRun_accepted haccepts with
    ⟨tree, run, hrun⟩
  have htree : tree = uniqueTree := by
    funext node
    exact Subsingleton.elim _ _
  subst tree
  exact ⟨run, hrun⟩

/-- A rational run is in particular an accepting run. -/
theorem nonemptyLanguage_of_hasRationalRun
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
    (h : A.HasRationalRun) :
    A.NonemptyLanguage := by
  rcases h with ⟨run, hrun, _⟩
  exact ⟨run, hrun⟩

/-! ## Finite transition table extracted from a rational run -/

/-- Choose the complete successor assignment of one representative node for
each run state.  Unreachable states receive the harmless constant assignment
to the automaton's initial state. -/
noncomputable def rationalSuccessor
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
    (run : TreeNode Branch -> A.State) :
    A.State -> Branch -> A.State := by
  classical
  exact fun state branch =>
    if h : ∃ node, run node = state then
      run (Classical.choose h ++ [branch])
    else
      A.initial

/-- Transition rationality makes the representative-based table agree with
the actual child at every node. -/
theorem rationalSuccessor_at
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
    (run : TreeNode Branch -> A.State)
    (hrational : ∀ u v : TreeNode Branch, run u = run v ->
      (fun b => run (u ++ [b])) = fun b => run (v ++ [b]))
    (node : TreeNode Branch) (branch : Branch) :
    rationalSuccessor A run (run node) branch = run (node ++ [branch]) := by
  classical
  rw [rationalSuccessor, dif_pos ⟨node, rfl⟩]
  let representative := Classical.choose
    (show ∃ candidate, run candidate = run node from ⟨node, rfl⟩)
  have hrepresentative : run representative = run node := by
    exact Classical.choose_spec
      (show ∃ candidate, run candidate = run node from ⟨node, rfl⟩)
  exact congrFun (hrational representative node hrepresentative) branch

/-- A rational accepting run presented as one finite-state transition table.
The table is globally defined; its legality is required exactly at states
that occur in the run. -/
structure RationalTransitionPolicy
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch) where
  run : TreeNode Branch -> A.State
  accepts : A.IsAcceptingRun uniqueTree run
  successor : A.State -> Branch -> A.State
  successor_at : ∀ node branch,
    successor (run node) branch = run (node ++ [branch])
  legal_at : ∀ node,
    A.delta (run node) PUnit.unit (successor (run node))

/-- Every transition-rational run yields a finite transition policy.  The
result is propositional because Lean correctly prevents extracting data from
the existential `HasRationalRun : Prop` into `Type`. -/
theorem nonempty_rationalTransitionPolicy_of_hasRationalRun
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
    (h : A.HasRationalRun) :
    Nonempty (RationalTransitionPolicy A) := by
  classical
  rcases h with ⟨run, haccepts, hrational⟩
  let successor := rationalSuccessor A run
  have hsuccessor : ∀ node branch,
      successor (run node) branch = run (node ++ [branch]) := by
    intro node branch
    exact rationalSuccessor_at A run
      (fun u v huv => (hrational u v huv).2) node branch
  refine ⟨{
    run := run
    accepts := haccepts
    successor := successor
    successor_at := hsuccessor
    legal_at := ?_
  }⟩
  intro node
  rw [show successor (run node) =
      (fun branch => run (node ++ [branch])) by
    funext branch
    exact hsuccessor node branch]
  simpa only [uniqueTree] using haccepts.1.2 node

end InputFreeRunParityTreeAutomaton

/-- An input-free parity tree automaton equipped with the rational-run basis
at its actual direction type.  This is the clean consumer interface for both
finite and infinite branching. -/
structure InputFreeRationalRunAutomaton (Branch : Type u) where
  toRunAutomaton : InputFreeRunParityTreeAutomaton.{u, w} Branch
  rationalRunBasis : toRunAutomaton.RationalRunBasis

namespace InputFreeRationalRunAutomaton

variable {Branch : Type u}

/-- Every finite-direction input-free run automaton has the certified general
interface. -/
def ofFinite [Fintype Branch]
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch) :
    InputFreeRationalRunAutomaton.{u, w} Branch where
  toRunAutomaton := A
  rationalRunBasis := A.rationalRunBasis_of_finite

/-- Apply the bundled basis theorem. -/
theorem exists_rationalRun_of_nonempty
    (A : InputFreeRationalRunAutomaton.{u, w} Branch)
    (h : A.toRunAutomaton.NonemptyLanguage) :
    A.toRunAutomaton.HasRationalRun :=
  A.rationalRunBasis h

end InputFreeRationalRunAutomaton

end DistributedSynthesis
