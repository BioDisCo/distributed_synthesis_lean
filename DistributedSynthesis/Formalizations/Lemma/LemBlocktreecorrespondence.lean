/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Proposition.PropJournalgivesuniform

/-!
# Block strategy trees and local implementability

This file formalizes Lemma `lem:blocktreecorrespondence` from `paper.tex`:
the semantic identification between realizable one-directional block
strategies and sender-oblivious winning strategy trees.

The information sets are the ones established by Lemma `lem:syncblockinfo`:
inside a one-directional block the receiver observes the full move history
including the current move, while the sender observes only its own input
history including its own current input.  A local block strategy pair is
therefore a receiver map on full histories and a sender map on sender
words.

Strategy trees branch over the full environment move and carry round-aware
lambda labels: a receiver response to the full current move and a sender
response to the sender's current input.  The sender component of a
*sender-oblivious* tree depends only on the sender projection of the node.

The main theorem `block_realizable_iff_senderOblivious_winningTree` states:
a block objective given by a deterministic record-reading monitor is
realizable by a local pair if and only if some sender-oblivious tree is a
winning tree of the lifted `DeterministicBlockMonitor`.  Both translations
preserve the played round sequence against every environment word
(`pairPlay` is definitionally the play of the induced tree).

Consequently the tree language the one-directional block automaton must
recognize is exactly: sender-oblivious and winning.  The Rabin extraction
of `ThmParityTreeEmptinessGame` applied to the lifted monitor yields a
finite-state winning controller from realizability
(`exists_finite_controller_of_block_realizable`); that controller need not
be sender-oblivious, and making the finite route complete is the sender-side
narrowing construction, which is the remaining automaton-theoretic step.
-/

namespace DistributedSynthesis

universe u v x y w

section BlockTreeCorrespondence

variable {RIn : Type u} {SIn : Type v} {ROut : Type x} {SOut : Type y}

/--
A round-aware lambda label of a one-directional block: the receiver responds
to the full current environment move, the sender responds to its own current
input.
-/
abbrev BlockLambdaLabel (RIn : Type u) (SIn : Type v)
    (ROut : Type x) (SOut : Type y) :=
  (RIn × SIn -> ROut) × (SIn -> SOut)

/-- A realized block round: the environment move and the two outputs. -/
abbrev RealizedBlockRound (RIn : Type u) (SIn : Type v)
    (ROut : Type x) (SOut : Type y) :=
  (RIn × SIn) × ROut × SOut

/-- Apply a lambda label to the current environment move. -/
def blockLabelApply (label : BlockLambdaLabel RIn SIn ROut SOut)
    (move : RIn × SIn) : RealizedBlockRound RIn SIn ROut SOut :=
  (move, label.1 move, label.2 move.2)

/-- The sender-visible projection of a block node. -/
def senderWord (node : TreeNode (RIn × SIn)) : List SIn :=
  node.map Prod.snd

/--
A strategy tree is sender-oblivious if its sender component at a node
depends only on the sender-visible word of the node.  This is the exact
tree-level form of local implementability for the sender.
-/
def SenderOblivious
    (tree : LabeledTree (RIn × SIn) (BlockLambdaLabel RIn SIn ROut SOut)) :
    Prop :=
  ∀ left right : TreeNode (RIn × SIn),
    senderWord left = senderWord right ->
      (tree left).2 = (tree right).2

/--
A receiver block strategy: a function of the past move history and the full
current move.  By Lemma `lem:syncblockinfo` this is the information in the
receiver's view at each interior block round.
-/
abbrev ReceiverBlockStrategy (RIn : Type u) (SIn : Type v) (ROut : Type x) :=
  TreeNode (RIn × SIn) -> RIn × SIn -> ROut

/--
A sender block strategy: a function of the sender's own past input word and
its own current input.  By Lemma `lem:syncblockinfo` this is the information
in the sender's view at each interior block round.
-/
abbrev SenderBlockStrategy (SIn : Type v) (SOut : Type y) :=
  List SIn -> SIn -> SOut

/-- The strategy tree induced by a local block strategy pair. -/
def treeOfPair (receiver : ReceiverBlockStrategy RIn SIn ROut)
    (sender : SenderBlockStrategy SIn SOut) :
    LabeledTree (RIn × SIn) (BlockLambdaLabel RIn SIn ROut SOut) :=
  fun node => (receiver node, sender (senderWord node))

/-- Induced trees are sender-oblivious. -/
theorem senderOblivious_treeOfPair
    (receiver : ReceiverBlockStrategy RIn SIn ROut)
    (sender : SenderBlockStrategy SIn SOut) :
    SenderOblivious (treeOfPair (SOut := SOut) receiver sender) := by
  intro left right h
  simp [treeOfPair, h]

/-- The receiver strategy read off a strategy tree. -/
def receiverOfTree
    (tree : LabeledTree (RIn × SIn) (BlockLambdaLabel RIn SIn ROut SOut)) :
    ReceiverBlockStrategy RIn SIn ROut :=
  fun node move => (tree node).1 move

/--
The sender strategy read off a strategy tree, evaluated on an arbitrary
receiver-input completion of the sender word.  For sender-oblivious trees
the choice of completion is irrelevant.
-/
def senderOfTree [Inhabited RIn]
    (tree : LabeledTree (RIn × SIn) (BlockLambdaLabel RIn SIn ROut SOut)) :
    SenderBlockStrategy SIn SOut :=
  fun word input =>
    (tree (word.map (fun sIn => ((default : RIn), sIn)))).2 input

theorem senderWord_completion [Inhabited RIn] (word : List SIn) :
    senderWord (word.map (fun sIn => ((default : RIn), sIn))) = word := by
  simp [senderWord, List.map_map, Function.comp_def]

/-- Reading a pair off a sender-oblivious tree reproduces the tree. -/
theorem treeOfPair_ofTree [Inhabited RIn]
    {tree : LabeledTree (RIn × SIn) (BlockLambdaLabel RIn SIn ROut SOut)}
    (hoblivious : SenderOblivious tree) :
    treeOfPair (receiverOfTree tree) (senderOfTree tree) = tree := by
  funext node
  refine Prod.ext ?_ ?_
  · rfl
  · exact hoblivious _ _ (senderWord_completion (senderWord node))

/-- The play of a strategy tree against an environment word. -/
def treePlay
    (tree : LabeledTree (RIn × SIn) (BlockLambdaLabel RIn SIn ROut SOut))
    (env : Nat -> RIn × SIn) (t : Nat) : RealizedBlockRound RIn SIn ROut SOut :=
  blockLabelApply (tree (branchNode env t)) (env t)

/-- The play of a local block strategy pair against an environment word. -/
def pairPlay (receiver : ReceiverBlockStrategy RIn SIn ROut)
    (sender : SenderBlockStrategy SIn SOut)
    (env : Nat -> RIn × SIn) : Nat -> RealizedBlockRound RIn SIn ROut SOut :=
  treePlay (treeOfPair receiver sender) env

/--
Objective-agnostic correspondence: a block objective is realizable by a
local strategy pair if and only if it is realized by a sender-oblivious
strategy tree.  The two translations preserve the played round sequence.
-/
theorem block_pair_realizable_iff_senderOblivious_tree [Inhabited RIn]
    (Objective : (Nat -> RealizedBlockRound RIn SIn ROut SOut) -> Prop) :
    (∃ receiver : ReceiverBlockStrategy RIn SIn ROut,
      ∃ sender : SenderBlockStrategy SIn SOut,
        ∀ env : Nat -> RIn × SIn, Objective (pairPlay receiver sender env)) ↔
      ∃ tree : LabeledTree (RIn × SIn) (BlockLambdaLabel RIn SIn ROut SOut),
        SenderOblivious tree ∧
          ∀ env : Nat -> RIn × SIn, Objective (treePlay tree env) := by
  constructor
  · rintro ⟨receiver, sender, hwin⟩
    exact ⟨treeOfPair receiver sender,
      senderOblivious_treeOfPair receiver sender, hwin⟩
  · rintro ⟨tree, hoblivious, hwin⟩
    refine ⟨receiverOfTree tree, senderOfTree tree, ?_⟩
    intro env
    have hplay :
        pairPlay (receiverOfTree tree) (senderOfTree tree) env =
          treePlay tree env := by
      rw [pairPlay, treeOfPair_ofTree hoblivious]
    rw [hplay]
    exact hwin env

/--
A deterministic finite monitor reading realized block rounds.  This is the
objective shape of the block problem: the specification automaton, priority
summary, and regular tests all read the realized round records.
-/
structure BlockRecordMonitor (RIn : Type u) (SIn : Type v)
    (ROut : Type x) (SOut : Type y) where
  State : Type w
  stateFinite : Fintype State
  initial : State
  step : State -> RealizedBlockRound RIn SIn ROut SOut -> State
  priority : State -> Nat

attribute [instance] BlockRecordMonitor.stateFinite

namespace BlockRecordMonitor

variable (M : BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut)

/-- The monitor run on a play. -/
def run (play : Nat -> RealizedBlockRound RIn SIn ROut SOut) : Nat -> M.State
  | 0 => M.initial
  | n + 1 => M.step (run play n) (play n)

/-- The parity objective of the monitor on plays. -/
def WinsPlay (play : Nat -> RealizedBlockRound RIn SIn ROut SOut) : Prop :=
  NatSeqMinEvenParity (fun n => M.priority (M.run play n))

/--
Lift a record-reading monitor to a lambda-label block monitor: the lifted
step applies the label to the branch move and reads the realized record.
-/
def lift [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut]
    [DecidableEq RIn] [DecidableEq SIn] :
    DeterministicBlockMonitor.{max u v, max u v x y, w}
      (RIn × SIn) (BlockLambdaLabel RIn SIn ROut SOut) where
  branchFinite := inferInstance
  alphabetFinite := inferInstance
  State := M.State
  stateFinite := M.stateFinite
  initial := M.initial
  step := fun state label move => M.step state (blockLabelApply label move)
  priority := M.priority

variable [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut]
variable [DecidableEq RIn] [DecidableEq SIn]

/-- The lifted monitor control along a branch is the record run of the play. -/
theorem lift_control_branchNode
    (tree : LabeledTree (RIn × SIn) (BlockLambdaLabel RIn SIn ROut SOut))
    (env : Nat -> RIn × SIn) :
    ∀ n : Nat,
      M.lift.control tree (branchNode env n) = M.run (treePlay tree env) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      show M.lift.control tree (branchNode env n ++ [env n]) = _
      rw [M.lift.control_append tree (branchNode env n) (env n), ih]
      simp [BlockRecordMonitor.run, BlockRecordMonitor.lift, treePlay]

/-- Winning trees of the lifted monitor are the trees whose plays all win. -/
theorem lift_winningTree_iff
    (tree : LabeledTree (RIn × SIn) (BlockLambdaLabel RIn SIn ROut SOut)) :
    M.lift.WinningTree tree ↔
      ∀ env : Nat -> RIn × SIn, M.WinsPlay (treePlay tree env) := by
  constructor
  · intro hwin env
    have h := hwin env
    have heq :
        (fun n => M.lift.priority (M.lift.control tree (branchNode env n))) =
          fun n => M.priority (M.run (treePlay tree env) n) := by
      funext n
      rw [M.lift_control_branchNode tree env n]
      rfl
    rw [heq] at h
    exact h
  · intro hwin env
    have h := hwin env
    have heq :
        (fun n => M.lift.priority (M.lift.control tree (branchNode env n))) =
          fun n => M.priority (M.run (treePlay tree env) n) := by
      funext n
      rw [M.lift_control_branchNode tree env n]
      rfl
    rw [heq]
    exact h

end BlockRecordMonitor

/--
Lemma `lem:blocktreecorrespondence`: the block synthesis problem for a
record-reading monitor objective is realizable by a local strategy pair if
and only if some sender-oblivious strategy tree is a winning tree of the
lifted block monitor.
-/
theorem block_realizable_iff_senderOblivious_winningTree
    [Inhabited RIn]
    [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut]
    [DecidableEq RIn] [DecidableEq SIn]
    (M : BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut) :
    (∃ receiver : ReceiverBlockStrategy RIn SIn ROut,
      ∃ sender : SenderBlockStrategy SIn SOut,
        ∀ env : Nat -> RIn × SIn,
          M.WinsPlay (pairPlay receiver sender env)) ↔
      ∃ tree : LabeledTree (RIn × SIn) (BlockLambdaLabel RIn SIn ROut SOut),
        SenderOblivious tree ∧ M.lift.WinningTree tree := by
  rw [block_pair_realizable_iff_senderOblivious_tree
    (Objective := fun play => M.WinsPlay play)]
  constructor
  · rintro ⟨tree, hoblivious, hwin⟩
    exact ⟨tree, hoblivious, (M.lift_winningTree_iff tree).mpr hwin⟩
  · rintro ⟨tree, hoblivious, hwin⟩
    exact ⟨tree, hoblivious, (M.lift_winningTree_iff tree).mp hwin⟩

/--
Sound finite-controller direction: block realizability by a local pair
yields a finite-state winning controller of the lifted monitor, through the
sender-oblivious tree and the emptiness-game extraction.  The extracted
controller need not itself be sender-oblivious; recovering an oblivious
finite controller is the sender-side narrowing construction.
-/
theorem exists_finite_controller_of_block_realizable
    [Inhabited RIn]
    [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut]
    [DecidableEq RIn] [DecidableEq SIn]
    (M : BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut)
    (hrealizable :
      ∃ receiver : ReceiverBlockStrategy RIn SIn ROut,
        ∃ sender : SenderBlockStrategy SIn SOut,
          ∀ env : Nat -> RIn × SIn,
            M.WinsPlay (pairPlay receiver sender env)) :
    ∃ controller :
        TransitionRationalTree.{max u v, max u v x y, w}
          (RIn × SIn) (BlockLambdaLabel RIn SIn ROut SOut),
      M.lift.WinningTree controller.labeledTree := by
  rcases (block_realizable_iff_senderOblivious_winningTree M).mp hrealizable with
    ⟨tree, _, hwin⟩
  rcases M.lift.toRunAutomaton.exists_transitionRational_accepted
      ⟨tree, (M.lift.acceptsTree_iff_winningTree tree).mpr hwin⟩ with
    ⟨controller, haccepts⟩
  exact ⟨controller,
    (M.lift.acceptsTree_iff_winningTree controller.labeledTree).mp haccepts⟩

end BlockTreeCorrespondence

end DistributedSynthesis
