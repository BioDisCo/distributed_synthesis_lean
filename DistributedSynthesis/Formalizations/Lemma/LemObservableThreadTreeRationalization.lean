/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemStateControlledTreeRationalization
import DistributedSynthesis.Formalizations.Theorem.ThmBundleDeterminization

/-!
# Rational trees with coherent hidden threads

This is the global counterpart of finite root-family narrowing.  A node of
the strategy tree sees only the current observation and chooses one finite
move.  Hidden actual roots are runs of a `FiniteThreadSystem`; they are not
part of the tree node and hence cannot influence the chosen move.  The
universal-run DPA checks every coherent hidden thread along every observation
branch.

The sticky Boolean rejects a move that is invalid for the current observable
class.  Consequently ordinary state-controlled Rabin extraction preserves
both the shared-move discipline and universal hidden-thread parity.
-/

namespace DistributedSynthesis

universe u v w x

section

variable {Observation : Type u} {Move : Type v}
variable [Fintype Observation] [Fintype Move]
variable [Inhabited Observation]

/-- Finite control of the observable tree monitor. -/
abbrev ObservableThreadTreeState
    (S : FiniteThreadSystem.{max u v, w, x} (Move × Observation)) :=
  Observation × S.universalRunDPA.State × Bool

/--
The deterministic tree monitor for observable moves and coherent hidden
threads.  At a node the move is checked against the observation stored in the
state.  Descending through `nextObservation` advances the universal thread
DPA by the public letter `(move, nextObservation)`.
-/
noncomputable def observableThreadTreeMonitor
    (S : FiniteThreadSystem.{max u v, w, x} (Move × Observation))
    (initialObservation : Observation)
    (Valid : Observation → Move → Prop) [DecidableRel Valid] :
    DeterministicBlockMonitor.{u, v, max u w}
      Observation Move := by
  classical
  let D := S.universalRunDPA
  exact {
    branchFinite := inferInstance
    alphabetFinite := inferInstance
    State := ObservableThreadTreeState S
    stateFinite := inferInstance
    initial := (initialObservation, D.initial, true)
    step := fun state move nextObservation =>
      (nextObservation, D.step state.2.1 (move, nextObservation),
        state.2.2 && decide (Valid state.1 move))
    priority := fun state =>
      if state.2.2 then D.priority state.2.1 + 2 else 1
  }

omit [Inhabited Observation] in
/-- The observable component at a child is exactly its incoming direction. -/
theorem observableThreadTreeMonitor_control_observation_append
    (S : FiniteThreadSystem.{max u v, w, x} (Move × Observation))
    (initialObservation : Observation)
    (Valid : Observation → Move → Prop) [DecidableRel Valid]
    (tree : LabeledTree Observation Move)
    (node : TreeNode Observation) (nextObservation : Observation) :
    ((observableThreadTreeMonitor S initialObservation Valid).control tree
      (node ++ [nextObservation])).1 = nextObservation := by
  rw [(observableThreadTreeMonitor S initialObservation Valid).control_append]
  rfl

/-- The current observation is the initial one at the root and the last
branch direction at every non-root node. -/
def observableAt (initialObservation : Observation)
    (node : TreeNode Observation) : Observation :=
  node.getLast?.getD initialObservation

omit [Inhabited Observation] in
theorem observableThreadTreeMonitor_control_observation
    (S : FiniteThreadSystem.{max u v, w, x} (Move × Observation))
    (initialObservation : Observation)
    (Valid : Observation → Move → Prop) [DecidableRel Valid]
    (tree : LabeledTree Observation Move) :
    ∀ node,
      ((observableThreadTreeMonitor S initialObservation Valid).control tree
        node).1 = observableAt initialObservation node := by
  intro node
  cases node using List.reverseRecOn with
  | nil => rfl
  | append_singleton node observation =>
      rw [observableThreadTreeMonitor_control_observation_append]
      simp [observableAt]

/-- Node-local validity in the observable strategy tree. -/
def ObservableMovesValid
    (initialObservation : Observation)
    (Valid : Observation → Move → Prop)
    (tree : LabeledTree Observation Move) : Prop :=
  ∀ node, Valid (observableAt initialObservation node) (tree node)

omit [Inhabited Observation] in
/-- Validity keeps the sticky component true everywhere. -/
theorem observableThreadTreeMonitor_control_safe_of_valid
    (S : FiniteThreadSystem.{max u v, w, x} (Move × Observation))
    (initialObservation : Observation)
    (Valid : Observation → Move → Prop) [DecidableRel Valid]
    (tree : LabeledTree Observation Move)
    (hvalid : ObservableMovesValid initialObservation Valid tree) :
    ∀ node,
      ((observableThreadTreeMonitor S initialObservation Valid).control tree
        node).2.2 = true := by
  intro node
  induction node using List.reverseRecOn with
  | nil => rfl
  | append_singleton node observation ih =>
      rw [(observableThreadTreeMonitor S initialObservation Valid).control_append]
      change Bool.and _ (decide (Valid _ (tree node))) = true
      rw [ih,
        observableThreadTreeMonitor_control_observation S initialObservation
          Valid tree node,
        decide_eq_true (hvalid node)]
      rfl

omit [Inhabited Observation] in
/-- Once invalid, the sticky component remains false below the node. -/
theorem observableThreadTreeMonitor_control_false_persists
    (S : FiniteThreadSystem.{max u v, w, x} (Move × Observation))
    (initialObservation : Observation)
    (Valid : Observation → Move → Prop) [DecidableRel Valid]
    (tree : LabeledTree Observation Move)
    (node : TreeNode Observation)
    (hfalse :
      ((observableThreadTreeMonitor S initialObservation Valid).control tree
        node).2.2 = false) :
    ∀ suffix,
      ((observableThreadTreeMonitor S initialObservation Valid).control tree
        (node ++ suffix)).2.2 = false := by
  intro suffix
  induction suffix using List.reverseRecOn with
  | nil => simpa using hfalse
  | append_singleton suffix observation ih =>
      rw [← List.append_assoc,
        (observableThreadTreeMonitor S initialObservation Valid).control_append]
      change Bool.and _ _ = false
      rw [ih]
      rfl

private def observableBranchExtending (node : TreeNode Observation) :
    Nat → Observation := fun n => node.getD n default

omit [Fintype Observation] in
private theorem observableBranchPrefix_getD
    (node : TreeNode Observation) : ∀ n, n ≤ node.length →
    branchNode (observableBranchExtending node) n = node.take n := by
  intro n hn
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show branchNode (observableBranchExtending node) (n + 1) =
          branchNode (observableBranchExtending node) n ++
            [node.getD n default] from rfl,
        ih (by omega), List.getD_eq_getElem node default (by omega),
        List.take_add_one, List.getElem?_eq_getElem (by omega)]
      rfl

omit [Fintype Observation] in
private theorem observableBranchPrefix_length
    (node : TreeNode Observation) :
    branchNode (observableBranchExtending node) node.length = node := by
  rw [observableBranchPrefix_getD node node.length (Nat.le_refl _),
    List.take_length]

/-- Winning the sticky monitor implies that every node chose a valid move. -/
theorem observableThreadTreeMonitor_valid_of_winning
    (S : FiniteThreadSystem.{max u v, w, x} (Move × Observation))
    (initialObservation : Observation)
    (Valid : Observation → Move → Prop) [DecidableRel Valid]
    (tree : LabeledTree Observation Move)
    (hwin : (observableThreadTreeMonitor S initialObservation Valid).WinningTree
      tree) :
    ObservableMovesValid initialObservation Valid tree := by
  intro node
  by_contra hnot
  let child := node ++ [(default : Observation)]
  have hfalse :
      ((observableThreadTreeMonitor S initialObservation Valid).control tree
        child).2.2 = false := by
    rw [(observableThreadTreeMonitor S initialObservation Valid).control_append]
    change Bool.and _ (decide (Valid _ (tree node))) = false
    rw [observableThreadTreeMonitor_control_observation S initialObservation
      Valid tree node]
    rw [decide_eq_false hnot]
    exact Bool.and_false _
  let branch := observableBranchExtending child
  have hprefix : branchNode branch child.length = child :=
    observableBranchPrefix_length child
  have hpersist : ∀ k,
      ((observableThreadTreeMonitor S initialObservation Valid).control tree
        (branchNode branch (child.length + k))).2.2 = false := by
    intro k
    induction k with
    | zero => simpa [hprefix] using hfalse
    | succ k ih =>
        rw [Nat.add_succ]
        change
          ((observableThreadTreeMonitor S initialObservation Valid).control tree
            (branchNode branch (child.length + k) ++
              [branch (child.length + k)])).2.2 = false
        rw [(observableThreadTreeMonitor S initialObservation Valid).control_append]
        change Bool.and _ _ = false
        rw [ih]
        rfl
  have heventual : ∀ n, child.length ≤ n →
      (observableThreadTreeMonitor S initialObservation Valid).priority
        ((observableThreadTreeMonitor S initialObservation Valid).control tree
          (branchNode branch n)) = 1 := by
    intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    change (if _ then _ else 1) = 1
    rw [hpersist k]
    rfl
  exact not_natSeqMinEvenParity_of_eventually_one _ child.length heventual
    (hwin branch)

/-- Public word read along an observation branch. -/
def observableThreadWord
    (tree : LabeledTree Observation Move)
    (branch : Nat → Observation) : OmegaWord (Move × Observation) :=
  fun n => (tree (branchNode branch n), branch n)

omit [Inhabited Observation] in
/-- The bundle component of the tree monitor is the DPA run on the public
move/observation word. -/
theorem observableThreadTreeMonitor_control_bundle
    (S : FiniteThreadSystem.{max u v, w, x} (Move × Observation))
    (initialObservation : Observation)
    (Valid : Observation → Move → Prop) [DecidableRel Valid]
    (tree : LabeledTree Observation Move)
    (branch : Nat → Observation) : ∀ n,
    ((observableThreadTreeMonitor S initialObservation Valid).control tree
      (branchNode branch n)).2.1 =
        S.universalRunDPA.run (observableThreadWord tree branch) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show branchNode branch (n + 1) =
          branchNode branch n ++ [branch n] from rfl,
        (observableThreadTreeMonitor S initialObservation Valid).control_append]
      change S.universalRunDPA.step _ _ = _
      rw [ih]
      rfl

omit [Inhabited Observation] in
/-- If all node moves are valid and the universal bundle accepts on every
observation branch, the observable strategy tree wins. -/
theorem observableThreadTreeMonitor_winning_of
    (S : FiniteThreadSystem.{max u v, w, x} (Move × Observation))
    (initialObservation : Observation)
    (Valid : Observation → Move → Prop) [DecidableRel Valid]
    (tree : LabeledTree Observation Move)
    (hvalid : ObservableMovesValid initialObservation Valid tree)
    (hbundle : ∀ branch : Nat → Observation,
      S.universalRunDPA.Accepts (observableThreadWord tree branch)) :
    (observableThreadTreeMonitor S initialObservation Valid).WinningTree tree := by
  intro branch
  have hsafe := observableThreadTreeMonitor_control_safe_of_valid
    S initialObservation Valid tree hvalid
  have heq :
      (fun n =>
        (observableThreadTreeMonitor S initialObservation Valid).priority
          ((observableThreadTreeMonitor S initialObservation Valid).control tree
            (branchNode branch n))) =
      fun n => S.universalRunDPA.priority
        (S.universalRunDPA.run (observableThreadWord tree branch) n) + 2 := by
    funext n
    change (if _ then _ else 1) = _
    rw [hsafe, if_pos rfl,
      observableThreadTreeMonitor_control_bundle S initialObservation Valid
        tree branch n]
  rw [heq]
  exact (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mpr
    (hbundle branch)

/-- Conversely, winning supplies universal coherent-thread parity on every
observation branch. -/
theorem observableThreadTreeMonitor_bundle_of_winning
    (S : FiniteThreadSystem.{max u v, w, x} (Move × Observation))
    (initialObservation : Observation)
    (Valid : Observation → Move → Prop) [DecidableRel Valid]
    (tree : LabeledTree Observation Move)
    (hwin : (observableThreadTreeMonitor S initialObservation Valid).WinningTree
      tree) :
    ∀ branch : Nat → Observation,
      S.universalRunDPA.Accepts (observableThreadWord tree branch) := by
  intro branch
  have hvalid := observableThreadTreeMonitor_valid_of_winning
    S initialObservation Valid tree hwin
  have hsafe := observableThreadTreeMonitor_control_safe_of_valid
    S initialObservation Valid tree hvalid
  have h := hwin branch
  have heq :
      (fun n =>
        (observableThreadTreeMonitor S initialObservation Valid).priority
          ((observableThreadTreeMonitor S initialObservation Valid).control tree
            (branchNode branch n))) =
      fun n => S.universalRunDPA.priority
        (S.universalRunDPA.run (observableThreadWord tree branch) n) + 2 := by
    funext n
    change (if _ then _ else 1) = _
    rw [hsafe, if_pos rfl,
      observableThreadTreeMonitor_control_bundle S initialObservation Valid
        tree branch n]
  rw [heq] at h
  exact (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mp h

/-- Exact semantic characterization of the coupled observable monitor. -/
theorem observableThreadTreeMonitor_winning_iff
    (S : FiniteThreadSystem.{max u v, w, x} (Move × Observation))
    (initialObservation : Observation)
    (Valid : Observation → Move → Prop) [DecidableRel Valid]
    (tree : LabeledTree Observation Move) :
    (observableThreadTreeMonitor S initialObservation Valid).WinningTree tree ↔
      ObservableMovesValid initialObservation Valid tree ∧
        ∀ branch : Nat → Observation,
          S.universalRunDPA.Accepts (observableThreadWord tree branch) := by
  constructor
  · intro hwin
    exact ⟨observableThreadTreeMonitor_valid_of_winning
        S initialObservation Valid tree hwin,
      observableThreadTreeMonitor_bundle_of_winning
        S initialObservation Valid tree hwin⟩
  · rintro ⟨hvalid, hbundle⟩
    exact observableThreadTreeMonitor_winning_of
      S initialObservation Valid tree hvalid hbundle

/-- State-controlled Rabin extraction for the coherent observable-thread
tree.  The extracted table is a literal finite type and still chooses moves
only from observation history. -/
theorem exists_stateControlled_observableThreadTree_of_winning
    (S : FiniteThreadSystem.{max u v, w, x} (Move × Observation))
    (initialObservation : Observation)
    (Valid : Observation → Move → Prop) [DecidableRel Valid]
    (tree : LabeledTree Observation Move)
    (hwin : (observableThreadTreeMonitor S initialObservation Valid).WinningTree
      tree) :
    ∃ table : RunParityTreeAutomaton.StateControlledTreeTable
        (observableThreadTreeMonitor S initialObservation Valid).toRunAutomaton,
      (observableThreadTreeMonitor S initialObservation Valid).WinningTree
        table.toTransitionRationalTree.labeledTree := by
  let M := observableThreadTreeMonitor S initialObservation Valid
  have haccepts : M.toRunAutomaton.acceptsTree tree :=
    (M.acceptsTree_iff_winningTree tree).mpr hwin
  rcases M.toRunAutomaton.exists_stateControlledTreeTable_accepted
      ⟨tree, haccepts⟩ with ⟨table, htable⟩
  exact ⟨table,
    (M.acceptsTree_iff_winningTree
      table.toTransitionRationalTree.labeledTree).mp htable⟩

end

end DistributedSynthesis
