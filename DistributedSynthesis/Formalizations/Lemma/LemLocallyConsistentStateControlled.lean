/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemLocallyConsistentSenderNarrowing
import DistributedSynthesis.Formalizations.Lemma.LemStateControlledTreeRationalization

/-!
# Fixed finite tables for locally consistent narrowing

`exists_transitionRational_narrowed_of_tablesAllowed` preserves a decidable
law on complete receiver tables, but its controller type is existential.  An
outer parity automaton needs a fixed finite move alphabet.  This file applies
state-controlled Rabin extraction to the label-restricted universal-thread
automaton and packages the result in its literal finite state type.
-/

namespace DistributedSynthesis

universe u v x y w

section

variable {RIn : Type u} {SIn : Type v} {ROut : Type x} {SOut : Type y}
variable [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut]
variable [DecidableEq RIn] [DecidableEq SIn]
variable [Inhabited RIn] [Inhabited SIn] [Inhabited ROut]
variable (M : BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut)
variable (Allowed : (RIn × SIn → ROut) → Prop)
variable [DecidablePred Allowed]

noncomputable local instance narrowedLabelAllowedDecidable :
    DecidablePred (NarrowedLabelAllowed M Allowed) :=
  fun _ => Classical.propDecidable _

/-- The fixed finite table type of the label-restricted thread automaton. -/
noncomputable abbrev LocallyConsistentNarrowedTable :=
  RunParityTreeAutomaton.StateControlledTreeTable
    ((BlockRecordMonitor.threadBlockMonitor M).restrictLabels
      (NarrowedLabelAllowed M Allowed)).toRunAutomaton

noncomputable instance : Fintype (LocallyConsistentNarrowedTable M Allowed) := by
  classical
  infer_instance

/-! ## Forgetting a stronger complete-table law

The state type and alphabet of `restrictLabels` do not depend on the
predicate used to reject labels.  Consequently a table extracted with a
strong semantic provenance law can be reused *literally* under a weaker
finite outer-interface law.  This operation is important: running Rabin
extraction a second time would preserve the weaker language but could choose
different labels and lose the provenance needed for global parity pasting.
-/

/-- Reinterpret the same controller and labels under a weaker table law. -/
noncomputable def LocallyConsistentNarrowedTable.weaken
    (Strong Weak : (RIn × SIn → ROut) → Prop)
    [DecidablePred Strong] [DecidablePred Weak]
    (table : LocallyConsistentNarrowedTable M Strong) :
    LocallyConsistentNarrowedTable M Weak :=
  { step := table.step
    label := table.label }

section
omit [DecidableEq RIn] [Inhabited RIn] [Inhabited SIn] [Inhabited ROut]

@[simp] theorem LocallyConsistentNarrowedTable.weaken_labeledTree
    (Strong Weak : (RIn × SIn → ROut) → Prop)
    [DecidablePred Strong] [DecidablePred Weak]
    (table : LocallyConsistentNarrowedTable M Strong) :
    (table.weaken M Strong Weak).toTransitionRationalTree.labeledTree =
      table.toTransitionRationalTree.labeledTree := by
  rfl

/-- Universal-thread acceptance is unchanged by forgetting a label law. -/
theorem LocallyConsistentNarrowedTable.weaken_wins
    (Strong Weak : (RIn × SIn → ROut) → Prop)
    [DecidablePred Strong] [DecidablePred Weak]
    (table : LocallyConsistentNarrowedTable M Strong)
    (hwins : NarrowedAllThreadsWin M
      table.toTransitionRationalTree.labeledTree) :
    NarrowedAllThreadsWin M
      (table.weaken M Strong Weak).toTransitionRationalTree.labeledTree := by
  simpa using hwins

/-- Any pointwise consequence of the strong table law is retained by the
same literal controller after weakening. -/
theorem LocallyConsistentNarrowedTable.weaken_allowed
    (Strong Weak : (RIn × SIn → ROut) → Prop)
    [DecidablePred Strong] [DecidablePred Weak]
    (himp : ∀ responses, Strong responses → Weak responses)
    (table : LocallyConsistentNarrowedTable M Strong)
    (hallowed : NarrowedTablesAllowed M Strong
      table.toTransitionRationalTree.labeledTree) :
    NarrowedTablesAllowed M Weak
      (table.weaken M Strong Weak).toTransitionRationalTree.labeledTree := by
  intro node q
  rw [LocallyConsistentNarrowedTable.weaken_labeledTree]
  exact himp _ (hallowed node q)

end

/-- Canonical fixed-state extraction from any winning narrowed tree satisfying
the complete-table law. -/
noncomputable def locallyConsistentNarrowedTable
    (narrowed :
      LabeledTree SIn (NarrowedBlockLabel RIn SIn ROut SOut M.State))
    (hthreads : NarrowedAllThreadsWin M narrowed)
    (hallowed : NarrowedTablesAllowed M Allowed narrowed) :
    LocallyConsistentNarrowedTable M Allowed := by
  classical
  let base := BlockRecordMonitor.threadBlockMonitor M
  let P := NarrowedLabelAllowed M Allowed
  let restricted := base.restrictLabels P
  have hbase : base.WinningTree narrowed :=
    (BlockRecordMonitor.threadBlockMonitor_winningTree_iff M narrowed).mpr
      hthreads
  have hrestricted : restricted.WinningTree narrowed :=
    base.restrictLabels_winningTree_of P narrowed hbase hallowed
  have haccepts : restricted.toRunAutomaton.acceptsTree narrowed :=
    (restricted.acceptsTree_iff_winningTree narrowed).mpr hrestricted
  exact Classical.choose
    (restricted.toRunAutomaton.exists_stateControlledTreeTable_accepted
      ⟨narrowed, haccepts⟩)

section
omit [Inhabited RIn] [Inhabited ROut] [DecidablePred Allowed]

private theorem locallyConsistentNarrowedTable_restricted_wins
    (narrowed :
      LabeledTree SIn (NarrowedBlockLabel RIn SIn ROut SOut M.State))
    (hthreads : NarrowedAllThreadsWin M narrowed)
    (hallowed : NarrowedTablesAllowed M Allowed narrowed) :
    let base := BlockRecordMonitor.threadBlockMonitor M
    let P := NarrowedLabelAllowed M Allowed
    (base.restrictLabels P).WinningTree
      (locallyConsistentNarrowedTable M Allowed narrowed hthreads hallowed).toTransitionRationalTree.labeledTree := by
  classical
  dsimp only
  let base := BlockRecordMonitor.threadBlockMonitor M
  let P := NarrowedLabelAllowed M Allowed
  let restricted := base.restrictLabels P
  have hbase : base.WinningTree narrowed :=
    (BlockRecordMonitor.threadBlockMonitor_winningTree_iff M narrowed).mpr
      hthreads
  have hrestricted : restricted.WinningTree narrowed :=
    base.restrictLabels_winningTree_of P narrowed hbase hallowed
  have haccepts : restricted.toRunAutomaton.acceptsTree narrowed :=
    (restricted.acceptsTree_iff_winningTree narrowed).mpr hrestricted
  have hchosen := Classical.choose_spec
    (restricted.toRunAutomaton.exists_stateControlledTreeTable_accepted
      ⟨narrowed, haccepts⟩)
  exact (restricted.acceptsTree_iff_winningTree _).mp hchosen

/-- The canonical fixed table retains universal-thread parity. -/
theorem locallyConsistentNarrowedTable_wins
    (narrowed :
      LabeledTree SIn (NarrowedBlockLabel RIn SIn ROut SOut M.State))
    (hthreads : NarrowedAllThreadsWin M narrowed)
    (hallowed : NarrowedTablesAllowed M Allowed narrowed) :
    NarrowedAllThreadsWin M
      (locallyConsistentNarrowedTable M Allowed narrowed hthreads hallowed).toTransitionRationalTree.labeledTree := by
  let base := BlockRecordMonitor.threadBlockMonitor M
  let P := NarrowedLabelAllowed M Allowed
  have hrestricted := locallyConsistentNarrowedTable_restricted_wins
    M Allowed narrowed hthreads hallowed
  have hsplit := (base.restrictLabels_winningTree_iff P _).mp hrestricted
  exact (BlockRecordMonitor.threadBlockMonitor_winningTree_iff M _).mp hsplit.1

/-- The complete receiver-table law is preserved by the same extraction. -/
theorem locallyConsistentNarrowedTable_allowed
    (narrowed :
      LabeledTree SIn (NarrowedBlockLabel RIn SIn ROut SOut M.State))
    (hthreads : NarrowedAllThreadsWin M narrowed)
    (hallowed : NarrowedTablesAllowed M Allowed narrowed) :
    NarrowedTablesAllowed M Allowed
      (locallyConsistentNarrowedTable M Allowed narrowed hthreads hallowed).toTransitionRationalTree.labeledTree := by
  let base := BlockRecordMonitor.threadBlockMonitor M
  let P := NarrowedLabelAllowed M Allowed
  have hrestricted := locallyConsistentNarrowedTable_restricted_wins
    M Allowed narrowed hthreads hallowed
  exact ((base.restrictLabels_winningTree_iff P _).mp hrestricted).2

end

/-! ## End-to-end fixed extraction from semantic strategies -/

/-- The constrained narrowed tree obtained before rational extraction. -/
noncomputable def locallyConsistentNarrowedTreeOfStrategies
    (defaultTable : RIn × SIn → ROut)
    (hdefault : Allowed defaultTable)
    (receiver : ReceiverBlockStrategy RIn SIn ROut)
    (sender : SenderBlockStrategy SIn SOut)
    (hwin : ∀ env, M.WinsPlay (pairPlay receiver sender env))
    (hallowed : ∀ past, Allowed (receiver past)) :
    { narrowed :
        LabeledTree SIn (NarrowedBlockLabel RIn SIn ROut SOut M.State) //
      NarrowedAllThreadsWin M narrowed ∧
        NarrowedTablesAllowed M Allowed narrowed } := by
  classical
  let tree := treeOfPair (SOut := SOut) receiver sender
  have hoblivious : SenderOblivious tree :=
    senderOblivious_treeOfPair receiver sender
  have htree : M.lift.WinningTree tree := by
    apply (M.lift_winningTree_iff tree).mpr
    simpa [tree, pairPlay] using hwin
  have htreeAllowed : ∀ node, Allowed (tree node).1 := by
    intro node
    exact hallowed node
  have hex := exists_narrowed_tablesAllowed_of_senderOblivious_winningTree M Allowed
    defaultTable hdefault hoblivious htreeAllowed htree
  exact ⟨hex.choose, hex.choose_spec⟩

/-- End-to-end canonical fixed finite table from semantic receiver/sender
strategies satisfying a complete-table law. -/
noncomputable def locallyConsistentTableOfStrategies
    (defaultTable : RIn × SIn → ROut)
    (hdefault : Allowed defaultTable)
    (receiver : ReceiverBlockStrategy RIn SIn ROut)
    (sender : SenderBlockStrategy SIn SOut)
    (hwin : ∀ env, M.WinsPlay (pairPlay receiver sender env))
    (hallowed : ∀ past, Allowed (receiver past)) :
    LocallyConsistentNarrowedTable M Allowed := by
  let constrained := locallyConsistentNarrowedTreeOfStrategies M Allowed
    defaultTable hdefault receiver sender hwin hallowed
  exact locallyConsistentNarrowedTable M Allowed constrained.1
    constrained.2.1 constrained.2.2

omit [DecidablePred Allowed] [Inhabited ROut] in
theorem locallyConsistentTableOfStrategies_wins
    (defaultTable : RIn × SIn → ROut)
    (hdefault : Allowed defaultTable)
    (receiver : ReceiverBlockStrategy RIn SIn ROut)
    (sender : SenderBlockStrategy SIn SOut)
    (hwin : ∀ env, M.WinsPlay (pairPlay receiver sender env))
    (hallowed : ∀ past, Allowed (receiver past)) :
    NarrowedAllThreadsWin M
      (locallyConsistentTableOfStrategies M Allowed defaultTable hdefault
        receiver sender hwin hallowed).toTransitionRationalTree.labeledTree := by
  let constrained := locallyConsistentNarrowedTreeOfStrategies M Allowed
    defaultTable hdefault receiver sender hwin hallowed
  simpa [locallyConsistentTableOfStrategies] using
    (locallyConsistentNarrowedTable_wins M Allowed constrained.1
      constrained.2.1 constrained.2.2)

omit [DecidablePred Allowed] [Inhabited ROut] in
theorem locallyConsistentTableOfStrategies_allowed
    (defaultTable : RIn × SIn → ROut)
    (hdefault : Allowed defaultTable)
    (receiver : ReceiverBlockStrategy RIn SIn ROut)
    (sender : SenderBlockStrategy SIn SOut)
    (hwin : ∀ env, M.WinsPlay (pairPlay receiver sender env))
    (hallowed : ∀ past, Allowed (receiver past)) :
    NarrowedTablesAllowed M Allowed
      (locallyConsistentTableOfStrategies M Allowed defaultTable hdefault
        receiver sender hwin hallowed).toTransitionRationalTree.labeledTree := by
  let constrained := locallyConsistentNarrowedTreeOfStrategies M Allowed
    defaultTable hdefault receiver sender hwin hallowed
  simpa [locallyConsistentTableOfStrategies] using
    (locallyConsistentNarrowedTable_allowed M Allowed constrained.1
      constrained.2.1 constrained.2.2)

end


end DistributedSynthesis
