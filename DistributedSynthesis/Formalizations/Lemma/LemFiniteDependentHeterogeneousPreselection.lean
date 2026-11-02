/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteCrossAnchorHeterogeneousPreselection

/-!
# Simultaneous preselection for a finite dependent receiver family

The two-member heterogeneous cross-anchor construction is enough for one
pending bit.  Before a delayed finite key has been delivered, however, a
blind endpoint carries one candidate for every possible key.  Rationalizing
those candidates independently would leave exactly the wrong residual
premise: their blind outputs need not agree.

This file performs the preselection before rationalization for an arbitrary
finite dependent family.  Receiver outputs are embedded in the dependent
product `forall key, ROut key`; the monitor at `key` observes only its own
coordinate.  All members are then projections of one finite root-family
table, so their sender controls, transitions, and output functions agree
definitionally at every depth.

The model-facing constructor uses only equality of the blind process's local
views.  It supplies no graph, orientation, hierarchy side, leader bit,
strict-leader bit, history, or candidate key to the executable sender.
-/

namespace DistributedSynthesis

universe k u v x y w

noncomputable section

variable {Key : Type k} {RIn : Type u} {SIn : Type v}
variable {ROut : Key → Type x} {SOut : Type y}
variable [Inhabited Key] [Fintype Key] [DecidableEq Key]
variable [Inhabited RIn] [Inhabited SIn] [Fintype RIn] [Fintype SIn]
variable [DecidableEq RIn] [DecidableEq SIn]
variable [(key : Key) → Inhabited (ROut key)]
variable [(key : Key) → Fintype (ROut key)] [Fintype SOut]

private abbrev DependentReceiverOutput (Key : Type k)
    (ROut : Key → Type x) :=
  (key : Key) → ROut key

/-! ## Dependent monitor and receiver embeddings -/

/-- Let member `key` observe only its coordinate of a dependent receiver
output tuple. -/
noncomputable def finiteDependentHeterogeneousMonitor
    (base : (key : Key) →
      BlockRecordMonitor.{u, v, x, y, w} RIn SIn (ROut key) SOut)
    (key : Key) :
    BlockRecordMonitor RIn SIn (DependentReceiverOutput Key ROut) SOut :=
  (base key).comapReceiverOutput (fun output ↦ output key)

/-- The dependent restart states are unchanged by receiver-output comapping. -/
noncomputable def finiteDependentHeterogeneousStart
    (base : (key : Key) →
      BlockRecordMonitor.{u, v, x, y, w} RIn SIn (ROut key) SOut)
    (start : (key : Key) → (base key).State) :
    (key : Key) →
      (finiteDependentHeterogeneousMonitor base key).State :=
  fun key ↦ start key

/-- Put one semantic receiver in its own coordinate and fill every unused
coordinate by the local default.  The monitor projection erases those
defaults. -/
noncomputable def finiteDependentHeterogeneousReceiver
    (receiver : (key : Key) →
      ReceiverBlockStrategy RIn SIn (ROut key)) :
    (key : Key) →
      ReceiverBlockStrategy RIn SIn (DependentReceiverOutput Key ROut) :=
  fun selected past input candidate ↦
    if h : selected = candidate then
      h ▸ receiver selected past input
    else default

omit [Inhabited Key] [Fintype Key] [Inhabited RIn] [Inhabited SIn] [Fintype RIn] [Fintype SIn]
    [DecidableEq RIn] [DecidableEq SIn] [(key : Key) → Fintype (ROut key)] in
@[simp] theorem finiteDependentHeterogeneousReceiver_self
    (receiver : (key : Key) →
      ReceiverBlockStrategy RIn SIn (ROut key))
    (key : Key) (past : TreeNode (RIn × SIn)) (input : RIn × SIn) :
    finiteDependentHeterogeneousReceiver receiver key past input key =
      receiver key past input := by
  simp [finiteDependentHeterogeneousReceiver]

/-- The restarted dependent family seen by the root-family narrowing. -/
noncomputable abbrev finiteDependentHeterogeneousRestartFamily
    (base : (key : Key) →
      BlockRecordMonitor.{u, v, x, y, w} RIn SIn (ROut key) SOut)
    (start : (key : Key) → (base key).State) (key : Key) :=
  (finiteDependentHeterogeneousMonitor base key).restartAt
    (finiteDependentHeterogeneousStart base start key)

/-! ## One finite table shared by every key -/

/-- A finite table simultaneously satisfying every dependent restarted
monitor.  Its sender transition system is stored only once. -/
noncomputable abbrev FiniteDependentHeterogeneousTable
    (base : (key : Key) →
      BlockRecordMonitor.{u, v, x, y, w} RIn SIn (ROut key) SOut)
    (start : (key : Key) → (base key).State) :=
  { table : FiniteRootFamilyTable
      (finiteDependentHeterogeneousRestartFamily base start) //
    NarrowedAllThreadsWin
      (finiteRootFamilyMonitor
        (finiteDependentHeterogeneousRestartFamily base start))
      table.toTransitionRationalTree.labeledTree }

noncomputable instance finiteDependentHeterogeneousTableFintype
    (base : (key : Key) →
      BlockRecordMonitor.{u, v, x, y, w} RIn SIn (ROut key) SOut)
    (start : (key : Key) → (base key).State) :
    Fintype (FiniteDependentHeterogeneousTable base start) := by
  classical infer_instance

/-- Simultaneously narrow all dependent obligations realized by one sender. -/
noncomputable def finiteDependentHeterogeneousTable
    (base : (key : Key) →
      BlockRecordMonitor.{u, v, x, y, w} RIn SIn (ROut key) SOut)
    (start : (key : Key) → (base key).State)
    (receiver : (key : Key) →
      ReceiverBlockStrategy RIn SIn (ROut key))
    (sender : SenderBlockStrategy SIn SOut)
    (hwin : ∀ key env,
      ((base key).restartAt (start key)).WinsPlay
        (pairPlay (receiver key) sender env)) :
    FiniteDependentHeterogeneousTable base start := by
  classical
  let lifted := finiteDependentHeterogeneousReceiver receiver
  let table := finiteRootFamilyTable
    (finiteDependentHeterogeneousRestartFamily base start) lifted sender (by
      intro key env
      change (((base key).restartAt (start key)).comapReceiverOutput
        (fun output : DependentReceiverOutput Key ROut => output key)).WinsPlay
          (pairPlay (lifted key) sender env)
      apply (BlockRecordMonitor.comapReceiverOutput_wins_iff
        ((base key).restartAt (start key))
        (fun output : DependentReceiverOutput Key ROut ↦ output key)
        (pairPlay (lifted key) sender env)).mpr
      have hproject :
          BlockRecordMonitor.projectReceiverPlay
              (fun output : DependentReceiverOutput Key ROut ↦ output key)
              (pairPlay (lifted key) sender env) =
            pairPlay (receiver key) sender env := by
        funext n
        simp [BlockRecordMonitor.projectReceiverPlay, pairPlay, treePlay,
          treeOfPair, blockLabelApply, lifted,
          finiteDependentHeterogeneousReceiver]
      rw [hproject]
      exact hwin key env)
  exact ⟨table,
    finiteRootFamilyTable_wins
      (finiteDependentHeterogeneousRestartFamily base start) lifted sender (by
        intro key env
        change (((base key).restartAt (start key)).comapReceiverOutput
          (fun output : DependentReceiverOutput Key ROut => output key)).WinsPlay
            (pairPlay (lifted key) sender env)
        apply (BlockRecordMonitor.comapReceiverOutput_wins_iff
          ((base key).restartAt (start key))
          (fun output : DependentReceiverOutput Key ROut ↦ output key)
          (pairPlay (lifted key) sender env)).mpr
        have hproject :
            BlockRecordMonitor.projectReceiverPlay
                (fun output : DependentReceiverOutput Key ROut ↦ output key)
                (pairPlay (lifted key) sender env) =
              pairPlay (receiver key) sender env := by
          funext n
          simp [BlockRecordMonitor.projectReceiverPlay, pairPlay, treePlay,
            treeOfPair, blockLabelApply, lifted,
            finiteDependentHeterogeneousReceiver]
        rw [hproject]
        exact hwin key env)⟩

/-- Project one receiver obligation from the shared table. -/
noncomputable def FiniteDependentHeterogeneousTable.memberController
    {base : (key : Key) →
      BlockRecordMonitor.{u, v, x, y, w} RIn SIn (ROut key) SOut}
    {start : (key : Key) → (base key).State}
    (table : FiniteDependentHeterogeneousTable base start) (key : Key) :=
  finiteRootMemberController
    (finiteDependentHeterogeneousRestartFamily base start)
    table.1.toTransitionRationalTree key

section
omit [Inhabited Key] [Inhabited RIn] [Inhabited SIn] [(key : Key) → Inhabited (ROut key)]

/-- Every member projection wins its own restarted monitor. -/
theorem FiniteDependentHeterogeneousTable.memberController_wins
    {base : (key : Key) →
      BlockRecordMonitor.{u, v, x, y, w} RIn SIn (ROut key) SOut}
    {start : (key : Key) → (base key).State}
    (table : FiniteDependentHeterogeneousTable base start) (key : Key) :
    NarrowedAllThreadsWin
      (finiteDependentHeterogeneousRestartFamily base start key)
      (table.memberController key).labeledTree := by
  exact finiteRootMemberController_allThreadsWin
    (finiteDependentHeterogeneousRestartFamily base start)
    table.1.toTransitionRationalTree table.2 key

/-- All member projections have literally the same sender label at every
shared finite control. -/
theorem FiniteDependentHeterogeneousTable.memberController_senderLabel_eq
    {base : (key : Key) →
      BlockRecordMonitor.{u, v, x, y, w} RIn SIn (ROut key) SOut}
    {start : (key : Key) → (base key).State}
    (table : FiniteDependentHeterogeneousTable base start)
    (left right : Key) (control : (table.memberController left).Control) :
    ((table.memberController left).labelOf control).1 =
      ((table.memberController right).labelOf control).1 := by
  rfl

/-- Hence every candidate emits the same blind output on every input. -/
theorem FiniteDependentHeterogeneousTable.memberController_senderOutput_eq
    {base : (key : Key) →
      BlockRecordMonitor.{u, v, x, y, w} RIn SIn (ROut key) SOut}
    {start : (key : Key) → (base key).State}
    (table : FiniteDependentHeterogeneousTable base start)
    (left right : Key) (control : (table.memberController left).Control)
    (input : SIn) :
    ((table.memberController left).labelOf control).1 input =
      ((table.memberController right).labelOf control).1 input := by
  exact congrFun (table.memberController_senderLabel_eq left right control)
    input

/-- Sender-state updates are independent of the receiver key as well. -/
theorem FiniteDependentHeterogeneousTable.memberController_step_eq
    {base : (key : Key) →
      BlockRecordMonitor.{u, v, x, y, w} RIn SIn (ROut key) SOut}
    {start : (key : Key) → (base key).State}
    (table : FiniteDependentHeterogeneousTable base start)
    (left right : Key) (control : (table.memberController left).Control)
    (input : SIn) :
    (table.memberController left).step control input =
      (table.memberController right).step control input := by
  rfl

end

end

end DistributedSynthesis
