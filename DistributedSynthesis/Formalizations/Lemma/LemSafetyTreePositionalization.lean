/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Definition.DefTreeAutomata

/-!
# Positionalizing a history-dependent safety tree

This is the safety-only extraction needed by the simultaneous-family route.
A semantic construction may choose a move using its complete proof history.
If every chosen move is safe, the set of states reached in that tree is a
post-fixed safety invariant.  Choosing one witnessing occurrence of each
reachable state therefore gives one positional move whose every successor
remains in the same invariant.

No parity or observation quotient is used here.  In the intended application
the state is the finite pair of fixed-policy family sources, the move is one
simultaneous family table, and parity is carried independently by the fixed
policy's universal hidden-thread monitor.
-/

namespace DistributedSynthesis

universe u v w

section

variable {State : Type u} {Move : Type v} {Branch : Type w}

/-- Prefix and semantic state accumulated while reading a branch word. -/
def safetyTreePrefixState
    (initial : State) (next : State → Move → Branch → State)
    (tree : LabeledTree Branch Move) (node : TreeNode Branch) :
    TreeNode Branch × State :=
  node.foldl
    (fun current branch =>
      (current.1 ++ [branch], next current.2 (tree current.1) branch))
    ([], initial)

/-- State reached below a node of a history-dependent move tree. -/
def safetyTreeStateAt
    (initial : State) (next : State → Move → Branch → State)
    (tree : LabeledTree Branch Move) (node : TreeNode Branch) : State :=
  (safetyTreePrefixState initial next tree node).2

@[simp] theorem safetyTreePrefixState_fst
    (initial : State) (next : State → Move → Branch → State)
    (tree : LabeledTree Branch Move) : ∀ node,
    (safetyTreePrefixState initial next tree node).1 = node := by
  intro node
  induction node using List.reverseRecOn with
  | nil => rfl
  | append_singleton node branch ih =>
      rw [safetyTreePrefixState, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      change
        (safetyTreePrefixState initial next tree node).1 ++ [branch] =
          node ++ [branch]
      rw [ih]

@[simp] theorem safetyTreeStateAt_nil
    (initial : State) (next : State → Move → Branch → State)
    (tree : LabeledTree Branch Move) :
    safetyTreeStateAt initial next tree [] = initial :=
  rfl

theorem safetyTreeStateAt_append
    (initial : State) (next : State → Move → Branch → State)
    (tree : LabeledTree Branch Move) (node : TreeNode Branch)
    (branch : Branch) :
    safetyTreeStateAt initial next tree (node ++ [branch]) =
      next (safetyTreeStateAt initial next tree node) (tree node) branch := by
  change (safetyTreePrefixState initial next tree (node ++ [branch])).2 = _
  rw [safetyTreePrefixState, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  change next (safetyTreePrefixState initial next tree node).2
      (tree (safetyTreePrefixState initial next tree node).1) branch = _
  rw [safetyTreePrefixState_fst]
  rfl

/-- Every node of the semantic tree chooses a move legal at the state reached
there.  The move may still depend on the whole node history. -/
def SafetyTreeValid
    (initial : State) (next : State → Move → Branch → State)
    (Legal : State → Move → Prop)
    (tree : LabeledTree Branch Move) : Prop :=
  ∀ node, Legal (safetyTreeStateAt initial next tree node) (tree node)

/-- States occurring in one semantic safety tree. -/
def SafetyTreeReachable
    (initial : State) (next : State → Move → Branch → State)
    (tree : LabeledTree Branch Move) : Set State :=
  fun state => ∃ node, safetyTreeStateAt initial next tree node = state

theorem safetyTreeReachable_initial
    (initial : State) (next : State → Move → Branch → State)
    (tree : LabeledTree Branch Move) :
    SafetyTreeReachable initial next tree initial := by
  exact ⟨[], rfl⟩

/-- One representative occurrence of a reachable state.  This is proof-side
choice; it is not stored in the extracted controller. -/
noncomputable def safetyTreeRepresentativeNode
    (initial : State) (next : State → Move → Branch → State)
    (tree : LabeledTree Branch Move)
    (state : { state // SafetyTreeReachable initial next tree state }) :
    TreeNode Branch :=
  Classical.choose state.2

theorem safetyTreeRepresentativeNode_state
    (initial : State) (next : State → Move → Branch → State)
    (tree : LabeledTree Branch Move)
    (state : { state // SafetyTreeReachable initial next tree state }) :
    safetyTreeStateAt initial next tree
        (safetyTreeRepresentativeNode initial next tree state) = state.1 :=
  Classical.choose_spec state.2

/-- Positional move obtained by reading the semantic move at one chosen
occurrence of the finite state. -/
noncomputable def safetyTreePositionalMove
    (initial : State) (next : State → Move → Branch → State)
    (tree : LabeledTree Branch Move)
    (state : { state // SafetyTreeReachable initial next tree state }) : Move :=
  tree (safetyTreeRepresentativeNode initial next tree state)

/-- The representative move is legal and all of its environment successors
are again represented in the same reachable-state invariant.  This is the
precise safety-game positionalization step. -/
theorem safetyTreePositionalMove_spec
    (initial : State) (next : State → Move → Branch → State)
    (Legal : State → Move → Prop)
    (tree : LabeledTree Branch Move)
    (hvalid : SafetyTreeValid initial next Legal tree)
    (state : { state // SafetyTreeReachable initial next tree state }) :
    Legal state.1 (safetyTreePositionalMove initial next tree state) ∧
      ∀ branch,
        SafetyTreeReachable initial next tree
          (next state.1 (safetyTreePositionalMove initial next tree state)
            branch) := by
  let node := safetyTreeRepresentativeNode initial next tree state
  have hstate : safetyTreeStateAt initial next tree node = state.1 :=
    safetyTreeRepresentativeNode_state initial next tree state
  constructor
  · simpa [safetyTreePositionalMove, node, hstate] using hvalid node
  · intro branch
    refine ⟨node ++ [branch], ?_⟩
    rw [safetyTreeStateAt_append, hstate]
    rfl

/-- Closed successor on the reachable-state subtype. -/
noncomputable def safetyTreePositionalNext
    (initial : State) (next : State → Move → Branch → State)
    (Legal : State → Move → Prop)
    (tree : LabeledTree Branch Move)
    (hvalid : SafetyTreeValid initial next Legal tree)
    (state : { state // SafetyTreeReachable initial next tree state })
    (branch : Branch) :
    { state // SafetyTreeReachable initial next tree state } :=
  ⟨next state.1 (safetyTreePositionalMove initial next tree state) branch,
    (safetyTreePositionalMove_spec initial next Legal tree hvalid state).2
      branch⟩

/-- Initial reachable-state value. -/
def safetyTreeInitialReachable
    (initial : State) (next : State → Move → Branch → State)
    (tree : LabeledTree Branch Move) :
    { state // SafetyTreeReachable initial next tree state } :=
  ⟨initial, safetyTreeReachable_initial initial next tree⟩

/-- State reached by the positional selector along a branch word. -/
noncomputable def safetyTreePositionalStateAt
    (initial : State) (next : State → Move → Branch → State)
    (Legal : State → Move → Prop)
    (tree : LabeledTree Branch Move)
    (hvalid : SafetyTreeValid initial next Legal tree)
    (node : TreeNode Branch) :
    { state // SafetyTreeReachable initial next tree state } :=
  node.foldl
    (safetyTreePositionalNext initial next Legal tree hvalid)
    (safetyTreeInitialReachable initial next tree)

/-- The actual positional move tree. -/
noncomputable def safetyTreePositionalTree
    (initial : State) (next : State → Move → Branch → State)
    (Legal : State → Move → Prop)
    (tree : LabeledTree Branch Move)
    (hvalid : SafetyTreeValid initial next Legal tree) :
    LabeledTree Branch Move :=
  fun node => safetyTreePositionalMove initial next tree
    (safetyTreePositionalStateAt initial next Legal tree hvalid node)

/-- Every label of the positional tree is legal at its closed invariant
state. -/
theorem safetyTreePositionalTree_valid
    (initial : State) (next : State → Move → Branch → State)
    (Legal : State → Move → Prop)
    (tree : LabeledTree Branch Move)
    (hvalid : SafetyTreeValid initial next Legal tree) :
    ∀ node,
      Legal
        (safetyTreePositionalStateAt initial next Legal tree hvalid node).1
        (safetyTreePositionalTree initial next Legal tree hvalid node) := by
  intro node
  exact (safetyTreePositionalMove_spec initial next Legal tree hvalid
    (safetyTreePositionalStateAt initial next Legal tree hvalid node)).1

/-- When the semantic state type is finite, the closed invariant used by the
positional selector is literally finite as well. -/
noncomputable instance safetyTreeReachableFintype
    [Fintype State]
    (initial : State) (next : State → Move → Branch → State)
    (tree : LabeledTree Branch Move) :
    Fintype { state // SafetyTreeReachable initial next tree state } := by
  classical
  infer_instance

/-! ## Building the semantic tree from a closed proof invariant -/

/-- A proof-side post-fixed safety invariant.  The witness stored in `Good`
may contain exact histories or a selected hidden root; it is erased from the
public state and move.  Closure is universal in the environment branch. -/
structure SafetyKernel
    (initial : State) (next : State → Move → Branch → State)
    (Legal : State → Move → Prop) where
  Good : State → Prop
  initial_good : Good initial
  move : { state // Good state } → Move
  legal : ∀ state, Legal state.1 (move state)
  closed : ∀ state branch, Good (next state.1 (move state) branch)

namespace SafetyKernel

variable {initial : State} {next : State → Move → Branch → State}
variable {Legal : State → Move → Prop}

/-- Closed proof-state transition of a safety kernel. -/
noncomputable def step
    (kernel : SafetyKernel initial next Legal)
    (state : { state // kernel.Good state }) (branch : Branch) :
    { state // kernel.Good state } :=
  ⟨next state.1 (kernel.move state) branch, kernel.closed state branch⟩

/-- Proof state reached along a finite environment history. -/
noncomputable def stateAt
    (kernel : SafetyKernel initial next Legal) (node : TreeNode Branch) :
    { state // kernel.Good state } :=
  node.foldl kernel.step ⟨initial, kernel.initial_good⟩

/-- History-dependent semantic move tree generated by the closed kernel.
Only the finite public move is exposed; `Good` witnesses remain in proofs. -/
noncomputable def tree
    (kernel : SafetyKernel initial next Legal) : LabeledTree Branch Move :=
  fun node => kernel.move (kernel.stateAt node)

@[simp] theorem stateAt_nil
    (kernel : SafetyKernel initial next Legal) :
    kernel.stateAt ([] : TreeNode Branch) =
      ⟨initial, kernel.initial_good⟩ :=
  rfl

theorem stateAt_append
    (kernel : SafetyKernel initial next Legal)
    (node : TreeNode Branch) (branch : Branch) :
    kernel.stateAt (node ++ [branch]) =
      kernel.step (kernel.stateAt node) branch := by
  simp [stateAt]

/-- The operational state obtained by executing the generated tree is the
public projection of its proof state. -/
theorem safetyTreeStateAt_tree
    (kernel : SafetyKernel initial next Legal) : ∀ node,
    safetyTreeStateAt initial next kernel.tree node =
      (kernel.stateAt node).1 := by
  intro node
  induction node using List.reverseRecOn with
  | nil => rfl
  | append_singleton node branch ih =>
      rw [safetyTreeStateAt_append, ih, stateAt_append]
      rfl

/-- Every node of the kernel-generated tree uses a legal move at the state
reached there. -/
theorem tree_valid
    (kernel : SafetyKernel initial next Legal) :
    SafetyTreeValid initial next Legal kernel.tree := by
  intro node
  rw [safetyTreeStateAt_tree]
  exact kernel.legal (kernel.stateAt node)

/-- A closed proof invariant supplies the semantic safety tree required by
positionalization. -/
theorem exists_validTree
    (kernel : SafetyKernel initial next Legal) :
    ∃ tree : LabeledTree Branch Move,
      SafetyTreeValid initial next Legal tree :=
  ⟨kernel.tree, kernel.tree_valid⟩

end SafetyKernel

end

end DistributedSynthesis
