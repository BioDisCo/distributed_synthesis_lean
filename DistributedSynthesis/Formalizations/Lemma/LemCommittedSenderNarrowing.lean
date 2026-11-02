/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemEdgeRestrictedTreeRationalization
import DistributedSynthesis.Formalizations.Lemma.LemLocallyConsistentSenderNarrowing

/-!
# Sender narrowing with a one-step commitment

An informed process may choose a finite handoff source after seeing the full
current move.  The process that is blind in the current homogeneous block
must nevertheless use one finite controller tree.  We represent this timing
by enriching every narrowed label with a complete commitment table indexed
by the objective state and current full move.

The child label contains the old block's next contingent action table.  A
depth-one edge law verifies that the handoff source committed at the parent
agrees with that next table at the monitor state reached by the current move.
Rabin extraction preserves the law by
`exists_transitionRational_of_winning_of_edgesAllowed`.
-/

namespace DistributedSynthesis

universe u v x y w z

namespace DeterministicBlockMonitor

variable {Branch : Type u} {Alphabet : Type v} {Alphabet' : Type x}

/-- Read a richer finite alphabet through a projection. -/
noncomputable def comapAlphabet
    (M : DeterministicBlockMonitor.{u, v, w} Branch Alphabet)
    [Fintype Alphabet'] (project : Alphabet' -> Alphabet) :
    DeterministicBlockMonitor.{u, x, w} Branch Alphabet' where
  branchFinite := M.branchFinite
  alphabetFinite := inferInstance
  State := M.State
  stateFinite := M.stateFinite
  initial := M.initial
  step state label branch := M.step state (project label) branch
  priority := M.priority

theorem comapAlphabet_control
    (M : DeterministicBlockMonitor.{u, v, w} Branch Alphabet)
    [Fintype Alphabet'] (project : Alphabet' -> Alphabet)
    (tree : LabeledTree Branch Alphabet') (node : TreeNode Branch) :
    (M.comapAlphabet project).control tree node =
      M.control (fun word => project (tree word)) node := by
  induction node using List.reverseRecOn with
  | nil => rfl
  | append_singleton node branch ih =>
      rw [(M.comapAlphabet project).control_append, M.control_append, ih]
      rfl

theorem comapAlphabet_winningTree_iff
    (M : DeterministicBlockMonitor.{u, v, w} Branch Alphabet)
    [Fintype Alphabet'] (project : Alphabet' -> Alphabet)
    (tree : LabeledTree Branch Alphabet') :
    (M.comapAlphabet project).WinningTree tree ↔
      M.WinningTree (fun word => project (tree word)) := by
  simp only [WinningTree]
  constructor <;> intro h branch
  · simpa [M.comapAlphabet_control project] using h branch
  · simpa [M.comapAlphabet_control project] using h branch

end DeterministicBlockMonitor

section CommittedSenderNarrowing

variable {RIn : Type u} {SIn : Type v} {ROut : Type x} {SOut : Type y}
variable {Key : Type z}

/-- A narrowed action label plus the handoff key selected for every possible
current objective state and full move. -/
abbrev CommittedNarrowedBlockLabel
    (RIn : Type u) (SIn : Type v) (ROut : Type x) (SOut : Type y)
    (Q : Type w) (Key : Type z) :=
  NarrowedBlockLabel RIn SIn ROut SOut Q × (Q -> RIn × SIn -> Key)

variable (M : BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut)

/-- Forget the finite handoff commitment. -/
def forgetCommittedNarrowedTree
    (tree : LabeledTree SIn
      (CommittedNarrowedBlockLabel RIn SIn ROut SOut M.State Key)) :
    LabeledTree SIn (NarrowedBlockLabel RIn SIn ROut SOut M.State) :=
  fun word => (tree word).1

/--
The parent-to-child law induced by a semantic realization predicate.  For
every possible receiver input, it computes the actual next objective state
and asks the child label to realize the key selected by the parent's complete
commitment table.
-/
def CommittedNarrowedEdgeAllowed
    (Realizes : M.State -> (RIn × SIn) ->
      NarrowedBlockLabel RIn SIn ROut SOut M.State -> Key -> M.State ->
      NarrowedBlockLabel RIn SIn ROut SOut M.State -> Prop)
    (edge :
      CommittedNarrowedBlockLabel RIn SIn ROut SOut M.State Key × SIn ×
        CommittedNarrowedBlockLabel RIn SIn ROut SOut M.State Key) : Prop :=
  ∀ q receiverInput,
    let move : RIn × SIn := (receiverInput, edge.2.1)
    let next := M.step q (narrowedRecord M edge.1.1 q move)
    Realizes q move edge.1.1 (edge.1.2 q move) next edge.2.2.1

/-- The complete one-step commitment law on an enriched narrowed tree. -/
def CommittedNarrowedEdgesRealized
    (Realizes : M.State -> (RIn × SIn) ->
      NarrowedBlockLabel RIn SIn ROut SOut M.State -> Key -> M.State ->
      NarrowedBlockLabel RIn SIn ROut SOut M.State -> Prop)
    (tree : LabeledTree SIn
      (CommittedNarrowedBlockLabel RIn SIn ROut SOut M.State Key)) : Prop :=
  DeterministicBlockMonitor.TreeEdgesAllowed
    (CommittedNarrowedEdgeAllowed M Realizes) tree

/--
Rationalize an enriched narrowed tree while preserving both universal thread
acceptance and the depth-one handoff law.
-/
theorem exists_transitionRational_committedNarrowed
    [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut]
    [Fintype Key] [DecidableEq SIn] [Inhabited SIn]
    (Realizes : M.State -> (RIn × SIn) ->
      NarrowedBlockLabel RIn SIn ROut SOut M.State -> Key -> M.State ->
      NarrowedBlockLabel RIn SIn ROut SOut M.State -> Prop)
    [DecidablePred (CommittedNarrowedEdgeAllowed M Realizes)]
    (tree : LabeledTree SIn
      (CommittedNarrowedBlockLabel RIn SIn ROut SOut M.State Key))
    (hthreads : NarrowedAllThreadsWin M (forgetCommittedNarrowedTree M tree))
    (hedges : CommittedNarrowedEdgesRealized M Realizes tree) :
    ∃ controller : TransitionRationalTree.{v,
        max (max (max (max (max u v) w) x) y) z,
        max v (max (max (max (max (max u v) w) x) y) z) w} SIn
        (CommittedNarrowedBlockLabel RIn SIn ROut SOut M.State Key),
      NarrowedAllThreadsWin M
          (forgetCommittedNarrowedTree M controller.labeledTree) ∧
        CommittedNarrowedEdgesRealized M Realizes controller.labeledTree := by
  classical
  let base := BlockRecordMonitor.threadBlockMonitor M
  let enriched := base.comapAlphabet
    (fun label : CommittedNarrowedBlockLabel RIn SIn ROut SOut M.State Key =>
      label.1)
  have hbase : base.WinningTree (forgetCommittedNarrowedTree M tree) :=
    (BlockRecordMonitor.threadBlockMonitor_winningTree_iff M _).mpr hthreads
  have henriched : enriched.WinningTree tree :=
    (base.comapAlphabet_winningTree_iff
      (fun label : CommittedNarrowedBlockLabel
        RIn SIn ROut SOut M.State Key => label.1) tree).mpr hbase
  rcases enriched.exists_transitionRational_of_winning_of_edgesAllowed
      (CommittedNarrowedEdgeAllowed M Realizes) tree henriched hedges with
    ⟨controller, hwin, hedge⟩
  have hbase' : base.WinningTree
      (forgetCommittedNarrowedTree M controller.labeledTree) :=
    (base.comapAlphabet_winningTree_iff
      (fun label : CommittedNarrowedBlockLabel
        RIn SIn ROut SOut M.State Key => label.1)
      controller.labeledTree).mp hwin
  exact ⟨controller,
    (BlockRecordMonitor.threadBlockMonitor_winningTree_iff M _).mp hbase',
    hedge⟩

end CommittedSenderNarrowing

end DistributedSynthesis
