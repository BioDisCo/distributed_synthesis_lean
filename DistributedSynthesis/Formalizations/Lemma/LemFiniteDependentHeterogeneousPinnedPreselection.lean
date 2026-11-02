/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteDependentHeterogeneousPreselection
import DistributedSynthesis.Formalizations.Theorem.ThmRootPinnedBlockNarrowing

/-!
# Root-pinned simultaneous preselection for a dependent receiver family

Sharing the sender table of several hidden candidates is not enough at an
orientation switch: the required equation compares that sender coordinate
with a receiver coordinate of another candidate.  This file pins the complete
first record of every member *before* the single finite-family narrowing.

All members are still projections of one sender controller.  In addition,
each projected member has exactly its semantic first record.  Consequently a
semantic sender/receiver equality is transported through rationalization as a
literal cross-member output equality.  It is never reconstructed from two
independently selected finite tables.

The member key and the dependent output tuple occur only on the receiver and
monitor side.  The executable sender receives no key, graph, orientation,
hierarchy side, leader bit, strict-leader bit, history, or semantic view.
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

abbrev FiniteDependentReceiverOutput (Key : Type k)
    (ROut : Key → Type x) :=
  (key : Key) → ROut key

/-! ## The semantic records pinned before narrowing -/

/-- The literal first record of member `key`, using the common semantic
sender and the receiver embedded at that member's dependent coordinate. -/
noncomputable def finiteDependentHeterogeneousSemanticRootRecord
    (receiver : (key : Key) → ReceiverBlockStrategy RIn SIn (ROut key))
    (sender : SenderBlockStrategy SIn SOut) (key : Key)
    (input : RIn × SIn) :
    RealizedBlockRound RIn SIn (FiniteDependentReceiverOutput Key ROut) SOut :=
  pairPlay (finiteDependentHeterogeneousReceiver receiver key) sender
    (fun _ ↦ input) 0

/-- Restarted member monitor with its complete semantic first record pinned. -/
noncomputable abbrev finiteDependentHeterogeneousPinnedRestartFamily
    (base : (key : Key) →
      BlockRecordMonitor.{u, v, x, y, w} RIn SIn (ROut key) SOut)
    (start : (key : Key) → (base key).State)
    (receiver : (key : Key) → ReceiverBlockStrategy RIn SIn (ROut key))
    (sender : SenderBlockStrategy SIn SOut) (key : Key) :=
  (finiteDependentHeterogeneousRestartFamily base start key).rootPinned
    (finiteDependentHeterogeneousSemanticRootRecord receiver sender key)

/-! ## One shared finite table -/

/-- A single finite sender table satisfying all restarted dependent monitors
and all of their semantic root pins. -/
noncomputable abbrev FiniteDependentHeterogeneousPinnedTable
    (base : (key : Key) →
      BlockRecordMonitor.{u, v, x, y, w} RIn SIn (ROut key) SOut)
    (start : (key : Key) → (base key).State)
    (receiver : (key : Key) → ReceiverBlockStrategy RIn SIn (ROut key))
    (sender : SenderBlockStrategy SIn SOut) :=
  { table : FiniteRootFamilyTable
      (finiteDependentHeterogeneousPinnedRestartFamily base start receiver
        sender) //
    NarrowedAllThreadsWin
      (finiteRootFamilyMonitor
        (finiteDependentHeterogeneousPinnedRestartFamily base start receiver
          sender))
      table.toTransitionRationalTree.labeledTree }

noncomputable instance finiteDependentHeterogeneousPinnedTableFintype
    (base : (key : Key) →
      BlockRecordMonitor.{u, v, x, y, w} RIn SIn (ROut key) SOut)
    (start : (key : Key) → (base key).State)
    (receiver : (key : Key) → ReceiverBlockStrategy RIn SIn (ROut key))
    (sender : SenderBlockStrategy SIn SOut) :
    Fintype
      (FiniteDependentHeterogeneousPinnedTable base start receiver sender) := by
  classical infer_instance

/-- Narrow once, after placing every dependent obligation and every root pin
in the same finite family monitor. -/
noncomputable def finiteDependentHeterogeneousPinnedTable
    (base : (key : Key) →
      BlockRecordMonitor.{u, v, x, y, w} RIn SIn (ROut key) SOut)
    (start : (key : Key) → (base key).State)
    (receiver : (key : Key) → ReceiverBlockStrategy RIn SIn (ROut key))
    (sender : SenderBlockStrategy SIn SOut)
    (hwin : ∀ key env,
      ((base key).restartAt (start key)).WinsPlay
        (pairPlay (receiver key) sender env)) :
    FiniteDependentHeterogeneousPinnedTable base start receiver sender := by
  classical
  let lifted := finiteDependentHeterogeneousReceiver receiver
  have hdependent : ∀ key env,
      (finiteDependentHeterogeneousRestartFamily base start key).WinsPlay
        (pairPlay (lifted key) sender env) := by
    intro key env
    change (((base key).restartAt (start key)).comapReceiverOutput
      (fun output : FiniteDependentReceiverOutput Key ROut ↦ output key)
      ).WinsPlay (pairPlay (lifted key) sender env)
    apply (BlockRecordMonitor.comapReceiverOutput_wins_iff
      ((base key).restartAt (start key))
      (fun output : FiniteDependentReceiverOutput Key ROut ↦ output key)
      (pairPlay (lifted key) sender env)).mpr
    have hproject :
        BlockRecordMonitor.projectReceiverPlay
            (fun output : FiniteDependentReceiverOutput Key ROut ↦ output key)
            (pairPlay (lifted key) sender env) =
          pairPlay (receiver key) sender env := by
      funext n
      simp [BlockRecordMonitor.projectReceiverPlay, pairPlay, treePlay,
        treeOfPair, blockLabelApply, lifted,
        finiteDependentHeterogeneousReceiver]
    rw [hproject]
    exact hwin key env
  have hpinned : ∀ key env,
      (finiteDependentHeterogeneousPinnedRestartFamily base start receiver
        sender key).WinsPlay (pairPlay (lifted key) sender env) := by
    intro key
    apply (finiteDependentHeterogeneousRestartFamily base start key
      ).rootPinned_realizable
      (finiteDependentHeterogeneousSemanticRootRecord receiver sender key)
      (lifted key) sender (hdependent key)
    intro input
    rfl
  let table := finiteRootFamilyTable
    (finiteDependentHeterogeneousPinnedRestartFamily base start receiver sender)
    lifted sender hpinned
  exact ⟨table, finiteRootFamilyTable_wins
    (finiteDependentHeterogeneousPinnedRestartFamily base start receiver sender)
    lifted sender hpinned⟩

/-! ## Member readback and cross-coordinate preservation -/

noncomputable def FiniteDependentHeterogeneousPinnedTable.memberController
    {base : (key : Key) →
      BlockRecordMonitor.{u, v, x, y, w} RIn SIn (ROut key) SOut}
    {start : (key : Key) → (base key).State}
    {receiver : (key : Key) → ReceiverBlockStrategy RIn SIn (ROut key)}
    {sender : SenderBlockStrategy SIn SOut}
    (table : FiniteDependentHeterogeneousPinnedTable base start receiver sender)
    (key : Key) :=
  finiteRootMemberController
    (finiteDependentHeterogeneousPinnedRestartFamily base start receiver sender)
    table.1.toTransitionRationalTree key

omit [Inhabited Key] [Inhabited RIn] [Inhabited SIn] in
theorem FiniteDependentHeterogeneousPinnedTable.member_wins
    {base : (key : Key) →
      BlockRecordMonitor.{u, v, x, y, w} RIn SIn (ROut key) SOut}
    {start : (key : Key) → (base key).State}
    {receiver : (key : Key) → ReceiverBlockStrategy RIn SIn (ROut key)}
    {sender : SenderBlockStrategy SIn SOut}
    (table : FiniteDependentHeterogeneousPinnedTable base start receiver sender)
    (key : Key) :
    NarrowedAllThreadsWin
      (finiteDependentHeterogeneousPinnedRestartFamily base start receiver
        sender key)
      (table.memberController key).labeledTree := by
  exact finiteRootMemberController_allThreadsWin
    (finiteDependentHeterogeneousPinnedRestartFamily base start receiver sender)
    table.1.toTransitionRationalTree table.2 key

section
omit [Inhabited Key]

/-- Each member projection retains its complete prescribed first record. -/
theorem FiniteDependentHeterogeneousPinnedTable.member_root_record
    {base : (key : Key) →
      BlockRecordMonitor.{u, v, x, y, w} RIn SIn (ROut key) SOut}
    {start : (key : Key) → (base key).State}
    {receiver : (key : Key) → ReceiverBlockStrategy RIn SIn (ROut key)}
    {sender : SenderBlockStrategy SIn SOut}
    (table : FiniteDependentHeterogeneousPinnedTable base start receiver sender)
    (key : Key) (input : RIn × SIn) :
    narrowedRecord
        (finiteDependentHeterogeneousPinnedRestartFamily base start receiver
          sender key)
        ((table.memberController key).labeledTree [])
        (finiteDependentHeterogeneousPinnedRestartFamily base start receiver
          sender key).initial input =
      finiteDependentHeterogeneousSemanticRootRecord receiver sender key
        input := by
  apply (finiteDependentHeterogeneousRestartFamily base start key
    ).rootPinned_root_record
  exact table.member_wins key

/-- The pinned receiver coordinate is the original semantic member output. -/
theorem FiniteDependentHeterogeneousPinnedTable.member_root_receiver
    {base : (key : Key) →
      BlockRecordMonitor.{u, v, x, y, w} RIn SIn (ROut key) SOut}
    {start : (key : Key) → (base key).State}
    {receiver : (key : Key) → ReceiverBlockStrategy RIn SIn (ROut key)}
    {sender : SenderBlockStrategy SIn SOut}
    (table : FiniteDependentHeterogeneousPinnedTable base start receiver sender)
    (key : Key) (input : RIn × SIn) :
    (narrowedRecord
        (finiteDependentHeterogeneousPinnedRestartFamily base start receiver
          sender key)
        ((table.memberController key).labeledTree [])
        (finiteDependentHeterogeneousPinnedRestartFamily base start receiver
          sender key).initial input).2.1 key =
      receiver key [] input := by
  rw [table.member_root_record key input]
  simp [finiteDependentHeterogeneousSemanticRootRecord, pairPlay, treePlay,
    treeOfPair, branchNode, blockLabelApply,
    finiteDependentHeterogeneousReceiver]

/-- The pinned sender coordinate is the common semantic sender output. -/
theorem FiniteDependentHeterogeneousPinnedTable.member_root_sender
    {base : (key : Key) →
      BlockRecordMonitor.{u, v, x, y, w} RIn SIn (ROut key) SOut}
    {start : (key : Key) → (base key).State}
    {receiver : (key : Key) → ReceiverBlockStrategy RIn SIn (ROut key)}
    {sender : SenderBlockStrategy SIn SOut}
    (table : FiniteDependentHeterogeneousPinnedTable base start receiver sender)
    (key : Key) (input : RIn × SIn) :
    (narrowedRecord
        (finiteDependentHeterogeneousPinnedRestartFamily base start receiver
          sender key)
        ((table.memberController key).labeledTree [])
        (finiteDependentHeterogeneousPinnedRestartFamily base start receiver
          sender key).initial input).2.2 =
      sender [] input.2 := by
  rw [table.member_root_record key input]
  rfl

/-- A semantic equality between the common sender and another member's
receiver is preserved as a literal equality between their narrowed root
records.  This is the generic sender/receiver anti-mosaic bridge. -/
theorem FiniteDependentHeterogeneousPinnedTable.root_sender_eq_receiver
    {base : (key : Key) →
      BlockRecordMonitor.{u, v, x, y, w} RIn SIn (ROut key) SOut}
    {start : (key : Key) → (base key).State}
    {receiver : (key : Key) → ReceiverBlockStrategy RIn SIn (ROut key)}
    {sender : SenderBlockStrategy SIn SOut}
    (table : FiniteDependentHeterogeneousPinnedTable base start receiver sender)
    (senderMember receiverMember : Key) (input : RIn × SIn)
    (project : ROut receiverMember → SOut)
    (hsemantic :
      sender [] input.2 = project (receiver receiverMember [] input)) :
    (narrowedRecord
        (finiteDependentHeterogeneousPinnedRestartFamily base start receiver
          sender senderMember)
        ((table.memberController senderMember).labeledTree [])
        (finiteDependentHeterogeneousPinnedRestartFamily base start receiver
          sender senderMember).initial input).2.2 =
      project
        ((narrowedRecord
          (finiteDependentHeterogeneousPinnedRestartFamily base start receiver
            sender receiverMember)
          ((table.memberController receiverMember).labeledTree [])
          (finiteDependentHeterogeneousPinnedRestartFamily base start receiver
            sender receiverMember).initial input).2.1 receiverMember) := by
  rw [table.member_root_sender senderMember input,
    table.member_root_receiver receiverMember input]
  exact hsemantic

end

/-! ## Constructing one table over a genuine blind-view fibre -/

/-- It is enough that every candidate's semantic sender is equal to the
sender at one pivot.  In the model this premise is discharged by equality of
the corresponding process-local views.  The family should therefore be
indexed only by candidates inside one such view fibre, never by all global
tags indiscriminately. -/
noncomputable def finiteDependentHeterogeneousPinnedTableOfSenderEq
    (base : (key : Key) →
      BlockRecordMonitor.{u, v, x, y, w} RIn SIn (ROut key) SOut)
    (start : (key : Key) → (base key).State)
    (receiver : (key : Key) → ReceiverBlockStrategy RIn SIn (ROut key))
    (senderAt : Key → SenderBlockStrategy SIn SOut)
    (pivot : Key) (hsender : ∀ key, senderAt key = senderAt pivot)
    (hwin : ∀ key env,
      ((base key).restartAt (start key)).WinsPlay
        (pairPlay (receiver key) (senderAt key) env)) :
    FiniteDependentHeterogeneousPinnedTable base start receiver
      (senderAt pivot) := by
  apply finiteDependentHeterogeneousPinnedTable base start receiver
    (senderAt pivot)
  intro key env
  rw [← hsender key]
  exact hwin key env

end

end DistributedSynthesis
