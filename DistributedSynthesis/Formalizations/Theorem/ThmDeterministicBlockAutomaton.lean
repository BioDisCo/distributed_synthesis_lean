/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmParityTreeEmptinessGame
import DistributedSynthesis.Formalizations.Theorem.ThmBerardfinitememory
import Mathlib.Data.List.GetD

/-!
# Deterministic block monitors and their tree automata

This file constructs the one-directional block tree automata concretely.

A `DeterministicBlockMonitor` is the finite deterministic observer of a
one-directional block: its state tracks the objective monitors (in the paper:
the Bérard summary, the saturated test basis, the raw epoch state, the DPA
state, and the receipt/order fringe), its input is the node label chosen by
the block strategy together with the environment branch, and its priority map
carries the parity objective.  A block strategy tree is winning if the
monitor satisfies min-even parity along every infinite branch.

`toRunAutomaton` presents the monitor as a deterministic run-based parity
tree automaton; `acceptsTree_iff_winningTree` identifies its accepted trees
with the winning strategy trees.  `toBlockProblem` then yields a fully proved
`OneDirectionalFiniteMemoryProblem`: `accepts_iff_realizable`,
`rational_iff_finiteSummary`, and `finiteSummary_sound` are theorems, and the
`rationality` interface is discharged by `RunParityTreeAutomaton.toInputFree`.
The headline consequence is
`deterministicBlockMonitor_realizable_iff_finiteSummary`: for
deterministic-monitor blocks, a winning strategy tree exists if and only if a
finite-state (transition-rational) winning controller exists.  This is the
first end-to-end unconditional instance of Theorem `thm:berardfinitememory`.
-/

namespace DistributedSynthesis

universe u v w x

/--
The finite deterministic objective monitor of a one-directional block.
`step` consumes the label placed by the block strategy at the current node
and the environment branch taken from it.
-/
structure DeterministicBlockMonitor (Branch : Type u) (Alphabet : Type v) where
  branchFinite : Fintype Branch
  alphabetFinite : Fintype Alphabet
  State : Type w
  stateFinite : Fintype State
  initial : State
  step : State -> Alphabet -> Branch -> State
  priority : State -> Nat

attribute [instance] DeterministicBlockMonitor.branchFinite
attribute [instance] DeterministicBlockMonitor.alphabetFinite
attribute [instance] DeterministicBlockMonitor.stateFinite

namespace DeterministicBlockMonitor

variable {Branch : Type u} {Alphabet : Type v}

/--
The monitor state reached from `q` by descending a node inside `tree`.
The recursion consumes the node from the root: each step reads the label at
the current node and follows the chosen branch into the subtree.
-/
def controlIn (M : DeterministicBlockMonitor.{u, v, w} Branch Alphabet) :
    LabeledTree Branch Alphabet -> M.State -> TreeNode Branch -> M.State
  | _, q, [] => q
  | tree, q, b :: rest =>
      M.controlIn (fun node => tree (b :: node)) (M.step q (tree []) b) rest

/-- The monitor state at a node of a strategy tree. -/
def control (M : DeterministicBlockMonitor.{u, v, w} Branch Alphabet)
    (tree : LabeledTree Branch Alphabet) (node : TreeNode Branch) : M.State :=
  M.controlIn tree M.initial node

theorem controlIn_append (M : DeterministicBlockMonitor.{u, v, w} Branch Alphabet) :
    ∀ (node : TreeNode Branch) (tree : LabeledTree Branch Alphabet)
      (q : M.State) (b : Branch),
      M.controlIn tree q (node ++ [b]) =
        M.step (M.controlIn tree q node) (tree node) b
  | [], _, _, _ => rfl
  | c :: rest, tree, q, b => by
      show M.controlIn (fun node => tree (c :: node)) (M.step q (tree []) c)
          (rest ++ [b]) = _
      rw [M.controlIn_append rest]
      rfl

/-- One-step law of the monitor state at a node. -/
theorem control_append (M : DeterministicBlockMonitor.{u, v, w} Branch Alphabet)
    (tree : LabeledTree Branch Alphabet) (node : TreeNode Branch) (b : Branch) :
    M.control tree (node ++ [b]) =
      M.step (M.control tree node) (tree node) b :=
  M.controlIn_append node tree M.initial b

/--
A strategy tree wins the block objective if the monitor satisfies min-even
parity along every infinite branch.
-/
def WinningTree (M : DeterministicBlockMonitor.{u, v, w} Branch Alphabet)
    (tree : LabeledTree Branch Alphabet) : Prop :=
  ∀ branch : Nat -> Branch,
    NatSeqMinEvenParity
      (fun n => M.priority (M.control tree (branchNode branch n)))

/-- The deterministic run-based tree automaton of a block monitor. -/
def toRunAutomaton (M : DeterministicBlockMonitor.{u, v, w} Branch Alphabet) :
    RunParityTreeAutomaton.{u, v, w} Branch Alphabet where
  State := M.State
  stateFinite := M.stateFinite
  initial := M.initial
  delta := fun q a f => ∀ b : Branch, f b = M.step q a b
  priority := M.priority

/-- Package the monitor through the proved finite-direction rationality
theorem, installing its bundled finiteness witnesses locally. -/
def toInputFreeAutomaton
    (M : DeterministicBlockMonitor.{u, v, w} Branch Alphabet) :
    InputFreeParityTreeAutomaton.{u, v, w} Branch Alphabet := by
  letI := M.branchFinite
  letI := M.alphabetFinite
  exact M.toRunAutomaton.toInputFree

/-- The canonical monitor run is a run of the deterministic automaton. -/
theorem isRun_control (M : DeterministicBlockMonitor.{u, v, w} Branch Alphabet)
    (tree : LabeledTree Branch Alphabet) :
    M.toRunAutomaton.IsRun tree (M.control tree) := by
  refine ⟨rfl, ?_⟩
  intro node b
  exact M.control_append tree node b

/-- Runs of the deterministic automaton are unique: they are the monitor run. -/
theorem run_eq_control (M : DeterministicBlockMonitor.{u, v, w} Branch Alphabet)
    {tree : LabeledTree Branch Alphabet}
    {run : TreeNode Branch -> M.State}
    (hrun : M.toRunAutomaton.IsRun tree run) :
    ∀ node : TreeNode Branch, run node = M.control tree node := by
  intro node
  induction node using List.reverseRecOn with
  | nil => exact hrun.1
  | append_singleton node b ih =>
      have hdelta : ∀ b' : Branch,
          run (node ++ [b']) = M.step (run node) (tree node) b' :=
        hrun.2 node
      rw [hdelta b, ih]
      exact (M.control_append tree node b).symm

/-- Accepted trees of the block automaton are exactly the winning trees. -/
theorem acceptsTree_iff_winningTree
    (M : DeterministicBlockMonitor.{u, v, w} Branch Alphabet)
    (tree : LabeledTree Branch Alphabet) :
    M.toRunAutomaton.acceptsTree tree ↔ M.WinningTree tree := by
  constructor
  · rintro ⟨run, hrun, hbranch⟩
    intro branch
    have h := hbranch branch
    have heq :
        (fun n => M.toRunAutomaton.priority (run (branchNode branch n))) =
          fun n => M.priority (M.control tree (branchNode branch n)) := by
      funext n
      rw [M.run_eq_control hrun (branchNode branch n)]
      rfl
    rw [heq] at h
    exact h
  · intro hwin
    exact ⟨M.control tree, M.isRun_control tree, hwin⟩

/-! ## A reusable local label restriction -/

/--
Add a sticky, node-local safety condition to a deterministic block monitor.
This is the tree-automaton form of the local-consistency side condition used
when one finite label represents a contingent action table: the table is
chosen once at the node, before the environment selects a branch.
-/
noncomputable def restrictLabels
    (M : DeterministicBlockMonitor.{u, v, w} Branch Alphabet)
    (Allowed : Alphabet -> Prop) [DecidablePred Allowed] :
    DeterministicBlockMonitor.{u, v, w} Branch Alphabet := by
  classical
  exact {
    branchFinite := M.branchFinite
    alphabetFinite := M.alphabetFinite
    State := M.State × Bool
    stateFinite := inferInstance
    initial := (M.initial, true)
    step := fun state label branch =>
      (M.step state.1 label branch, state.2 && decide (Allowed label))
    priority := fun state => if state.2 then M.priority state.1 + 2 else 1
  }

theorem restrictLabels_control_fst
    (M : DeterministicBlockMonitor.{u, v, w} Branch Alphabet)
    (Allowed : Alphabet -> Prop) [DecidablePred Allowed]
    (tree : LabeledTree Branch Alphabet) (node : TreeNode Branch) :
    ((M.restrictLabels Allowed).control tree node).1 = M.control tree node := by
  induction node using List.reverseRecOn with
  | nil => rfl
  | append_singleton node branch ih =>
      rw [(M.restrictLabels Allowed).control_append, M.control_append]
      exact congrArg (fun state => M.step state (tree node) branch) ih

theorem restrictLabels_control_safe_of_all
    (M : DeterministicBlockMonitor.{u, v, w} Branch Alphabet)
    (Allowed : Alphabet -> Prop) [DecidablePred Allowed]
    (tree : LabeledTree Branch Alphabet)
    (hall : ∀ node, Allowed (tree node)) :
    ∀ node, ((M.restrictLabels Allowed).control tree node).2 = true := by
  intro node
  induction node using List.reverseRecOn with
  | nil => rfl
  | append_singleton node branch ih =>
      rw [(M.restrictLabels Allowed).control_append]
      change
        Bool.and ((M.restrictLabels Allowed).control tree node).2
          (decide (Allowed (tree node))) = true
      rw [ih, decide_eq_true (hall node)]
      rfl

theorem restrictLabels_control_safe_false_persists
    (M : DeterministicBlockMonitor.{u, v, w} Branch Alphabet)
    (Allowed : Alphabet -> Prop) [DecidablePred Allowed]
    (tree : LabeledTree Branch Alphabet)
    (node : TreeNode Branch)
    (hfalse : ((M.restrictLabels Allowed).control tree node).2 = false) :
    ∀ suffix, ((M.restrictLabels Allowed).control tree (node ++ suffix)).2 = false := by
  intro suffix
  induction suffix using List.reverseRecOn with
  | nil => simpa using hfalse
  | append_singleton suffix branch ih =>
      rw [← List.append_assoc, (M.restrictLabels Allowed).control_append]
      change Bool.and
        ((M.restrictLabels Allowed).control tree (node ++ suffix)).2
        (decide (Allowed (tree (node ++ suffix)))) = false
      rw [ih]
      rfl

/-- A base-winning tree satisfying the node predicate wins the restriction. -/
theorem restrictLabels_winningTree_of
    (M : DeterministicBlockMonitor.{u, v, w} Branch Alphabet)
    (Allowed : Alphabet -> Prop) [DecidablePred Allowed]
    (tree : LabeledTree Branch Alphabet)
    (hwin : M.WinningTree tree)
    (hall : ∀ node, Allowed (tree node)) :
    (M.restrictLabels Allowed).WinningTree tree := by
  intro branch
  have hsafe := M.restrictLabels_control_safe_of_all Allowed tree hall
  have hbase := hwin branch
  have heq :
      (fun n => (M.restrictLabels Allowed).priority
        ((M.restrictLabels Allowed).control tree (branchNode branch n))) =
      fun n => M.priority (M.control tree (branchNode branch n)) + 2 := by
    funext n
    change
      (if ((M.restrictLabels Allowed).control tree
            (branchNode branch n)).2 then
          M.priority ((M.restrictLabels Allowed).control tree
            (branchNode branch n)).1 + 2
        else 1) = _
    rw [hsafe, if_pos rfl, M.restrictLabels_control_fst Allowed]
  rw [heq]
  exact (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mpr hbase

private def branchExtending [Inhabited Branch]
    (node : TreeNode Branch) : Nat -> Branch :=
  fun n => node.getD n default

private theorem branchNode_getD_basic [Inhabited Branch]
    (node : TreeNode Branch) : ∀ n, n ≤ node.length ->
    branchNode (branchExtending node) n = node.take n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
      intro hn
      rw [show branchNode (branchExtending node) (n + 1) =
          branchNode (branchExtending node) n ++ [node.getD n default] from rfl,
        ih (by omega), List.getD_eq_getElem node default (by omega),
        List.take_add_one, List.getElem?_eq_getElem (by omega)]
      rfl

private theorem branchNode_branchExtending_length [Inhabited Branch]
    (node : TreeNode Branch) :
    branchNode (branchExtending node) node.length = node := by
  rw [branchNode_getD_basic node node.length (Nat.le_refl _), List.take_length]

/-- Winning the restricted monitor is exactly base winning plus the node law. -/
theorem restrictLabels_winningTree_iff
    [Inhabited Branch]
    (M : DeterministicBlockMonitor.{u, v, w} Branch Alphabet)
    (Allowed : Alphabet -> Prop) [DecidablePred Allowed]
    (tree : LabeledTree Branch Alphabet) :
    (M.restrictLabels Allowed).WinningTree tree ↔
      M.WinningTree tree ∧ ∀ node, Allowed (tree node) := by
  constructor
  · intro hrestricted
    have hall : ∀ node, Allowed (tree node) := by
      intro node
      by_contra hnot
      let child := node ++ [(default : Branch)]
      have hfalse :
          ((M.restrictLabels Allowed).control tree child).2 = false := by
        rw [(M.restrictLabels Allowed).control_append]
        change Bool.and _ (decide (Allowed (tree node))) = false
        rw [decide_eq_false hnot]
        simp
      let branch := branchExtending child
      have hprefix : branchNode branch child.length = child :=
        branchNode_branchExtending_length child
      have hpersist : ∀ k,
          ((M.restrictLabels Allowed).control tree
            (branchNode branch (child.length + k))).2 = false := by
        intro k
        induction k with
        | zero => simpa [hprefix] using hfalse
        | succ k ih =>
            rw [Nat.add_succ]
            change
              ((M.restrictLabels Allowed).control tree
                (branchNode branch (child.length + k) ++
                  [branch (child.length + k)])).2 = false
            rw [(M.restrictLabels Allowed).control_append]
            change Bool.and _ (decide (Allowed _)) = false
            rw [ih]
            rfl
      have heventual : ∀ n, child.length ≤ n ->
          (M.restrictLabels Allowed).priority
            ((M.restrictLabels Allowed).control tree
              (branchNode branch n)) = 1 := by
        intro n hn
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
        change (if _ then _ else 1) = 1
        rw [hpersist k]
        rfl
      exact not_natSeqMinEvenParity_of_eventually_one _ child.length heventual
        (hrestricted branch)
    refine ⟨?_, hall⟩
    intro branch
    have hr := hrestricted branch
    have hsafe := M.restrictLabels_control_safe_of_all Allowed tree hall
    have heq :
        (fun n => (M.restrictLabels Allowed).priority
          ((M.restrictLabels Allowed).control tree (branchNode branch n))) =
        fun n => M.priority (M.control tree (branchNode branch n)) + 2 := by
      funext n
      change (if _ then _ else 1) = _
      rw [hsafe, if_pos rfl, M.restrictLabels_control_fst Allowed]
    rw [heq] at hr
    exact (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mp hr
  · rintro ⟨hwin, hall⟩
    exact M.restrictLabels_winningTree_of Allowed tree hwin hall

end DeterministicBlockMonitor

/--
The fully proved one-directional block problem of a deterministic monitor
family.  Realizability is the semantic winning-strategy-tree notion, and all
interface fields are theorems: acceptance is identified with realizability,
rational acceptance with finite-summary realizability, and the rational-run
interface of the tree automata is discharged by
`RunParityTreeAutomaton.toInputFree`.
-/
def DeterministicBlockMonitor.toBlockProblem
    {Boundary : Type u} {Branch : Type v} {Alphabet : Type w}
    [boundaryFinite : Fintype Boundary]
    (M : Boundary -> DeterministicBlockMonitor.{v, w, x} Branch Alphabet) :
    OneDirectionalFiniteMemoryProblem.{u, v, w, x} Boundary Branch Alphabet where
  boundaryFinite := boundaryFinite
  treeAutomaton := fun boundary => (M boundary).toInputFreeAutomaton
  realizable := fun boundary =>
    ∃ tree : LabeledTree Branch Alphabet, (M boundary).WinningTree tree
  finiteSummaryRealizable := fun boundary =>
    ∃ controller : TransitionRationalTree.{v, w, x} Branch Alphabet,
      (M boundary).WinningTree controller.labeledTree
  accepts_iff_realizable := by
    intro boundary
    constructor
    · rintro ⟨tree, htree⟩
      exact ⟨tree, ((M boundary).acceptsTree_iff_winningTree tree).mp htree⟩
    · rintro ⟨tree, htree⟩
      exact ⟨tree, ((M boundary).acceptsTree_iff_winningTree tree).mpr htree⟩
  rational_iff_finiteSummary := by
    intro boundary
    constructor
    · rintro ⟨rationalTree, controller, _, haccepts⟩
      exact ⟨controller,
        ((M boundary).acceptsTree_iff_winningTree _).mp haccepts⟩
    · rintro ⟨controller, hwin⟩
      exact ⟨controller.toRationalTree, controller, rfl,
        ((M boundary).acceptsTree_iff_winningTree _).mpr hwin⟩
  finiteSummary_sound := by
    intro boundary hfinite
    rcases hfinite with ⟨controller, hwin⟩
    exact ⟨controller.labeledTree,
      ((M boundary).acceptsTree_iff_winningTree _).mpr hwin⟩

/--
Nonemptiness transfer for the endpoint hypotheses: a realizable block
objective yields a nonempty accepted tree language for the packaged interface
automaton.  Instantiating the `target`/`targetNonempty` hypotheses of the
epoch-game endpoints therefore reduces to exhibiting a winning strategy tree
of the deterministic block monitor; the rationality demanded downstream is
supplied by the emptiness-game construction.
-/
theorem DeterministicBlockMonitor.toInputFree_acceptsTree_nonempty
    {Branch : Type u} {Alphabet : Type v}
    (M : DeterministicBlockMonitor.{u, v, w} Branch Alphabet)
    (hrealizable : ∃ tree : LabeledTree Branch Alphabet, M.WinningTree tree) :
    ∃ tree : LabeledTree Branch Alphabet,
      M.toInputFreeAutomaton.acceptsTree tree := by
  rcases hrealizable with ⟨tree, hwin⟩
  exact ⟨tree, (M.acceptsTree_iff_winningTree tree).mpr hwin⟩

/--
The one-directional finite-memory theorem, unconditional for
deterministic-monitor blocks: a winning block strategy tree exists at a
boundary if and only if a finite-state winning controller exists.  This is
`thm:berardfinitememory` applied to `toBlockProblem`, with the rational-run
interface discharged by the emptiness-game construction.
-/
theorem deterministicBlockMonitor_realizable_iff_finiteSummary
    {Boundary : Type u} {Branch : Type v} {Alphabet : Type w}
    [Fintype Boundary]
    (M : Boundary -> DeterministicBlockMonitor.{v, w, x} Branch Alphabet)
    (boundary : Boundary) :
    (∃ tree : LabeledTree Branch Alphabet, (M boundary).WinningTree tree) ↔
      ∃ controller : TransitionRationalTree.{v, w, x} Branch Alphabet,
        (M boundary).WinningTree controller.labeledTree :=
  berard_finite_memory (DeterministicBlockMonitor.toBlockProblem M) boundary

/--
Controller extraction form: from any winning strategy tree, a finite-memory
controller with an explicit finite control set, transition map, and output
table.
-/
theorem deterministicBlockMonitor_exists_finite_controller
    {Boundary : Type u} {Branch : Type v} {Alphabet : Type w}
    [Fintype Boundary]
    (M : Boundary -> DeterministicBlockMonitor.{v, w, x} Branch Alphabet)
    (boundary : Boundary)
    (hrealizable :
      ∃ tree : LabeledTree Branch Alphabet, (M boundary).WinningTree tree) :
    ∃ controller : TransitionRationalTree.{v, w, x} Branch Alphabet,
      (M boundary).WinningTree controller.labeledTree :=
  (deterministicBlockMonitor_realizable_iff_finiteSummary M boundary).mp
    hrealizable

end DistributedSynthesis
