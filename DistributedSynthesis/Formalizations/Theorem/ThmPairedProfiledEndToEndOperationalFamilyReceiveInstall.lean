/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndOperationalFamilySourceRefresh
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndOperationalFamilySourceSelection
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndOperationalFamilyReceiveSynchronization

/-!
# Total receive-side installation of the next alternating families

The receiver banks expose the exact next mixed roots as `Option`s: the
continued member is always present, while the opposite member is present once
the just-finished block has staged its recurrent macro.  This file supplies
the executable boundary around that proof fact.

First, missing staging is totalized by duplicating the continued root.  Then
the proof-free family selectors choose finite tables, and both sender overlays
and both dual receiver banks are installed at their initial states.  The
fallback has no correctness claim.  The theorems below recover the exact
mixed roots under the two staging equations, and recover winning tables only
from explicit `SourceRealizable` hypotheses.

The receive table is a joint function of the two delivered finite summaries
and the two inputs.  It never receives a graph, orientation, family member, or
strict-leader bit.  Its common Boolean is the already stored historical
anchor.  Both receiver projections use the same joint function, so a strict
receive and the corresponding side of a simultaneous receive remain locally
indistinguishable.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

open PairedStrategyMemory
open PairedStrategyMemory.PairedInitialProfiledRationalPackage

variable (package : PairedInitialProfiledRationalPackage A)

/-! ## Total root refresh -/

/-- Totalize the optional right-family refresh.  The fallback duplicates the
continued current root and is used only when the staged macro is absent. -/
noncomputable def endToEndTotalNextRightFamilyRoots
    (pastAnchor : Bool)
    (rightMove : EndToEndRightFamilyPairMove A package)
    (rightBank : EndToEndRightFamilyReceiverBank A package rightMove)
    (leftMove : EndToEndLeftFamilyPairMove A package)
    (leftBank : EndToEndLeftFamilyReceiverBank A package leftMove) :
    Bool → EndToEndRightRestartRoot A package :=
  fun member =>
    (endToEndNextRightFamilyRoots? A package pastAnchor rightMove rightBank
      leftMove leftBank member).getD
        (endToEndRightFamilyBankCurrentRoot A package rightMove rightBank
          pastAnchor)

/-- Left-oriented mirror. -/
noncomputable def endToEndTotalNextLeftFamilyRoots
    (pastAnchor : Bool)
    (rightMove : EndToEndRightFamilyPairMove A package)
    (rightBank : EndToEndRightFamilyReceiverBank A package rightMove)
    (leftMove : EndToEndLeftFamilyPairMove A package)
    (leftBank : EndToEndLeftFamilyReceiverBank A package leftMove) :
    Bool → EndToEndLeftRestartRoot A package :=
  fun member =>
    (endToEndNextLeftFamilyRoots? A package pastAnchor rightMove rightBank
      leftMove leftBank member).getD
        (endToEndLeftFamilyBankCurrentRoot A package leftMove leftBank
          (!pastAnchor))

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem endToEndTotalNextRightFamilyRoots_false
    (pastAnchor : Bool)
    (rightMove : EndToEndRightFamilyPairMove A package)
    (rightBank : EndToEndRightFamilyReceiverBank A package rightMove)
    (leftMove : EndToEndLeftFamilyPairMove A package)
    (leftBank : EndToEndLeftFamilyReceiverBank A package leftMove) :
    endToEndTotalNextRightFamilyRoots A package pastAnchor rightMove rightBank
        leftMove leftBank false =
      endToEndRightFamilyBankCurrentRoot A package rightMove rightBank
        pastAnchor := by
  rfl

@[simp] theorem endToEndTotalNextLeftFamilyRoots_false
    (pastAnchor : Bool)
    (rightMove : EndToEndRightFamilyPairMove A package)
    (rightBank : EndToEndRightFamilyReceiverBank A package rightMove)
    (leftMove : EndToEndLeftFamilyPairMove A package)
    (leftBank : EndToEndLeftFamilyReceiverBank A package leftMove) :
    endToEndTotalNextLeftFamilyRoots A package pastAnchor rightMove rightBank
        leftMove leftBank false =
      endToEndLeftFamilyBankCurrentRoot A package leftMove leftBank
        (!pastAnchor) := by
  rfl

theorem endToEndTotalNextRightFamilyRoots_true_of_pending
    (pastAnchor : Bool)
    (rightMove : EndToEndRightFamilyPairMove A package)
    (rightBank : EndToEndRightFamilyReceiverBank A package rightMove)
    (leftMove : EndToEndLeftFamilyPairMove A package)
    (leftBank : EndToEndLeftFamilyReceiverBank A package leftMove)
    (source : EndToEndRecurrentRightMacro A package)
    (hpending : (leftBank (!pastAnchor)).2.2 = some source) :
    endToEndTotalNextRightFamilyRoots A package pastAnchor rightMove rightBank
        leftMove leftBank true =
      endToEndRightRestartRootOfPending A package source := by
  simp [endToEndTotalNextRightFamilyRoots,
    endToEndNextRightFamilyRoots?_true_of_pending A package pastAnchor
      rightMove rightBank leftMove leftBank source hpending]

theorem endToEndTotalNextLeftFamilyRoots_true_of_pending
    (pastAnchor : Bool)
    (rightMove : EndToEndRightFamilyPairMove A package)
    (rightBank : EndToEndRightFamilyReceiverBank A package rightMove)
    (leftMove : EndToEndLeftFamilyPairMove A package)
    (leftBank : EndToEndLeftFamilyReceiverBank A package leftMove)
    (source : EndToEndRecurrentLeftMacro A package)
    (hpending : (rightBank pastAnchor).2.2 = some source) :
    endToEndTotalNextLeftFamilyRoots A package pastAnchor rightMove rightBank
        leftMove leftBank true =
      endToEndLeftRestartRootOfPending A package source := by
  simp [endToEndTotalNextLeftFamilyRoots,
    endToEndNextLeftFamilyRoots?_true_of_pending A package pastAnchor
      rightMove rightBank leftMove leftBank source hpending]

end

/-! ## Rows for the freshly installed receiver banks -/

/-- The continued right member retains its exact old entry row.  The staged
member is entered on a receive, hence its preceding-receipt row is `both`.
For a strict receive the process-two component is not installed; for a
simultaneous receive process two really did receive. -/
def endToEndNextRightFamilyRows
    (pastAnchor : Bool)
    (rightMove : EndToEndRightFamilyPairMove A package)
    (rightBank : EndToEndRightFamilyReceiverBank A package rightMove) :
    Bool → PairedEntryRow
  | false => (rightBank pastAnchor).1
  | true => guardedEntryRowOfReceived true

/-- Left-oriented mirror. -/
def endToEndNextLeftFamilyRows
    (pastAnchor : Bool)
    (leftMove : EndToEndLeftFamilyPairMove A package)
    (leftBank : EndToEndLeftFamilyReceiverBank A package leftMove) :
    Bool → PairedEntryRow
  | false => (leftBank (!pastAnchor)).1
  | true => guardedEntryRowOfReceived true

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem endToEndNextRightFamilyRows_false
    (pastAnchor : Bool)
    (rightMove : EndToEndRightFamilyPairMove A package)
    (rightBank : EndToEndRightFamilyReceiverBank A package rightMove) :
    endToEndNextRightFamilyRows A package pastAnchor rightMove rightBank false =
      (rightBank pastAnchor).1 := rfl

@[simp] theorem endToEndNextRightFamilyRows_true
    (pastAnchor : Bool)
    (rightMove : EndToEndRightFamilyPairMove A package)
    (rightBank : EndToEndRightFamilyReceiverBank A package rightMove) :
    endToEndNextRightFamilyRows A package pastAnchor rightMove rightBank true =
      guardedEntryRowOfReceived true := rfl

@[simp] theorem endToEndNextLeftFamilyRows_false
    (pastAnchor : Bool)
    (leftMove : EndToEndLeftFamilyPairMove A package)
    (leftBank : EndToEndLeftFamilyReceiverBank A package leftMove) :
    endToEndNextLeftFamilyRows A package pastAnchor leftMove leftBank false =
      (leftBank (!pastAnchor)).1 := rfl

@[simp] theorem endToEndNextLeftFamilyRows_true
    (pastAnchor : Bool)
    (leftMove : EndToEndLeftFamilyPairMove A package)
    (leftBank : EndToEndLeftFamilyReceiverBank A package leftMove) :
    endToEndNextLeftFamilyRows A package pastAnchor leftMove leftBank true =
      guardedEntryRowOfReceived true := rfl

end

/-! ## Select and install both next families -/

/-- Joint post-block data consumed by the installer.  It is assembled from
the two synchronized bank steps below. -/
structure EndToEndFamilyPostBlockBanks where
  pastAnchor : Bool
  rightMove : EndToEndRightFamilyPairMove A package
  rightBank : EndToEndRightFamilyReceiverBank A package rightMove
  leftMove : EndToEndLeftFamilyPairMove A package
  leftBank : EndToEndLeftFamilyReceiverBank A package leftMove
  outputOne : Out₁
  outputTwo : Out₂

namespace EndToEndFamilyPostBlockBanks

noncomputable def rightSource
    (post : EndToEndFamilyPostBlockBanks A package) :
    Bool → EndToEndRightRestartRoot A package :=
  endToEndTotalNextRightFamilyRoots A package post.pastAnchor post.rightMove
    post.rightBank post.leftMove post.leftBank

noncomputable def leftSource
    (post : EndToEndFamilyPostBlockBanks A package) :
    Bool → EndToEndLeftRestartRoot A package :=
  endToEndTotalNextLeftFamilyRoots A package post.pastAnchor post.rightMove
    post.rightBank post.leftMove post.leftBank

noncomputable def rightMoveSelected
    (post : EndToEndFamilyPostBlockBanks A package) :
    EndToEndRightFamilyPairMove A package :=
  endToEndRightFamilyMoveSelector A package (post.rightSource A package)

noncomputable def leftMoveSelected
    (post : EndToEndFamilyPostBlockBanks A package) :
    EndToEndLeftFamilyPairMove A package :=
  endToEndLeftFamilyMoveSelector A package (post.leftSource A package)

/-- Install both selected moves, both shared sender overlays, and both
two-member receiver banks.  The historical anchor is carried unchanged. -/
noncomputable def installControls
    (post : EndToEndFamilyPostBlockBanks A package) :
    EndToEndFamilyFullOneControl A package ×
      EndToEndFamilyFullTwoControl A package :=
  let right := post.rightMoveSelected A package
  let left := post.leftMoveSelected A package
  ({ rightSender := EndToEndRightFamilyPairOverlay.initial A package right
     leftReceiver :=
       (post.pastAnchor, ⟨left,
        initialEndToEndLeftFamilyReceiverBank A package left
          (endToEndNextLeftFamilyRows A package post.pastAnchor post.leftMove
            post.leftBank)⟩) },
   { rightReceiver :=
       (post.pastAnchor, ⟨right,
        initialEndToEndRightFamilyReceiverBank A package right
          (endToEndNextRightFamilyRows A package post.pastAnchor post.rightMove
            post.rightBank)⟩)
     leftSender := EndToEndLeftFamilyPairOverlay.initial A package left })

/-- Install the controls while retaining the outputs emitted by the bank
steps that closed the old block. -/
noncomputable def installSummaries
    (post : EndToEndFamilyPostBlockBanks A package) :
    EndToEndFamilyFullOneSummary A package ×
      EndToEndFamilyFullTwoSummary A package :=
  (((post.installControls A package).1, post.outputOne),
    ((post.installControls A package).2, post.outputTwo))

section
omit [Inhabited In₁] [Inhabited In₂]

@[simp] theorem rightMoveSelected_source
    (post : EndToEndFamilyPostBlockBanks A package) :
    (post.rightMoveSelected A package).1 = post.rightSource A package :=
  rfl

@[simp] theorem leftMoveSelected_source
    (post : EndToEndFamilyPostBlockBanks A package) :
    (post.leftMoveSelected A package).1 = post.leftSource A package :=
  rfl

@[simp] theorem installControls_rightSender_move
    (post : EndToEndFamilyPostBlockBanks A package) :
    (post.installControls A package).1.rightSender.1 =
      post.rightMoveSelected A package := rfl

@[simp] theorem installControls_leftSender_move
    (post : EndToEndFamilyPostBlockBanks A package) :
    (post.installControls A package).2.leftSender.1 =
      post.leftMoveSelected A package := rfl

@[simp] theorem installControls_rightReceiver_move
    (post : EndToEndFamilyPostBlockBanks A package) :
    (post.installControls A package).2.rightReceiver.2.1 =
      post.rightMoveSelected A package := rfl

@[simp] theorem installControls_leftReceiver_move
    (post : EndToEndFamilyPostBlockBanks A package) :
    (post.installControls A package).1.leftReceiver.2.1 =
      post.leftMoveSelected A package := rfl

@[simp] theorem installControls_rightReceiver_anchor
    (post : EndToEndFamilyPostBlockBanks A package) :
    (post.installControls A package).2.rightReceiver.1 = post.pastAnchor := rfl

@[simp] theorem installControls_leftReceiver_anchor
    (post : EndToEndFamilyPostBlockBanks A package) :
    (post.installControls A package).1.leftReceiver.1 = post.pastAnchor := rfl

theorem installControls_rightSender_root
    (post : EndToEndFamilyPostBlockBanks A package) (member : Bool) :
    (post.installControls A package).1.rightSender.1.1 member =
      post.rightSource A package member := by
  rfl

theorem installControls_leftSender_root
    (post : EndToEndFamilyPostBlockBanks A package) (member : Bool) :
    (post.installControls A package).2.leftSender.1.1 member =
      post.leftSource A package member := by
  rfl

theorem installControls_rightReceiver_root
    (post : EndToEndFamilyPostBlockBanks A package) (member : Bool) :
    (post.installControls A package).2.rightReceiver.2.1.1 member =
      post.rightSource A package member := by
  rfl

theorem installControls_leftReceiver_root
    (post : EndToEndFamilyPostBlockBanks A package) (member : Bool) :
    (post.installControls A package).1.leftReceiver.2.1.1 member =
      post.leftSource A package member := by
  rfl

end

section
omit [Inhabited In₁] [Inhabited In₂]

theorem rightMoveSelected_wins
    (post : EndToEndFamilyPostBlockBanks A package)
    (hrealizable : EndToEndRightFamilySourceRealizable A package
      (post.rightSource A package)) :
    EndToEndRightFamilyRootTableWins A package (post.rightSource A package)
      (post.rightMoveSelected A package).2 :=
  endToEndRightFamilyMoveSelector_wins A package _ hrealizable

theorem leftMoveSelected_wins
    (post : EndToEndFamilyPostBlockBanks A package)
    (hrealizable : EndToEndLeftFamilySourceRealizable A package
      (post.leftSource A package)) :
    EndToEndLeftFamilyRootTableWins A package (post.leftSource A package)
      (post.leftMoveSelected A package).2 :=
  endToEndLeftFamilyMoveSelector_wins A package _ hrealizable

@[simp] theorem installSummaries_outputOne
    (post : EndToEndFamilyPostBlockBanks A package) :
    (post.installSummaries A package).1.2 = post.outputOne := rfl

@[simp] theorem installSummaries_outputTwo
    (post : EndToEndFamilyPostBlockBanks A package) :
    (post.installSummaries A package).2.2 = post.outputTwo := rfl

end

end EndToEndFamilyPostBlockBanks

/-! ## Assemble the post-block data from the finite receive synchronizer -/

/-- Run both projections of the graph-free bank synchronizer on the same
delivered pair.  Which projection is subsequently read is decided by the
ordinary local-summary semantics, not by this function. -/
noncomputable def endToEndFamilyFullRecvBankSyncPair
    (one : EndToEndFamilyFullOneSummary A package) (inputOne : In₁)
    (two : EndToEndFamilyFullTwoSummary A package) (inputTwo : In₂) :
    EndToEndFamilyFullOneSummary A package ×
      EndToEndFamilyFullTwoSummary A package :=
  (endToEndFamilyFullRecvOneBankSync A package one inputOne two inputTwo,
    endToEndFamilyFullRecvTwoBankSync A package two inputTwo one inputOne)

/-- Extract the two stepped banks and their outputs.  Process one's stored
anchor is the canonical common historical anchor.  The represented-state
invariant must prove that process two stores the same anchor. -/
noncomputable def endToEndFamilyPostBlockBanksOfReceive
    (one : EndToEndFamilyFullOneSummary A package) (inputOne : In₁)
    (two : EndToEndFamilyFullTwoSummary A package) (inputTwo : In₂) :
    EndToEndFamilyPostBlockBanks A package := by
  let synced := endToEndFamilyFullRecvBankSyncPair A package one inputOne two
    inputTwo
  exact
    { pastAnchor := synced.1.1.leftReceiver.1
      rightMove := synced.2.1.rightReceiver.2.1
      rightBank := synced.2.1.rightReceiver.2.2
      leftMove := synced.1.1.leftReceiver.2.1
      leftBank := synced.1.1.leftReceiver.2.2
      outputOne := synced.1.2
      outputTwo := synced.2.2 }

/-- The total joint receive/install function. -/
noncomputable def endToEndFamilyFullRecvRefreshInstallPair
    (one : EndToEndFamilyFullOneSummary A package) (inputOne : In₁)
    (two : EndToEndFamilyFullTwoSummary A package) (inputTwo : In₂) :
    EndToEndFamilyFullOneSummary A package ×
      EndToEndFamilyFullTwoSummary A package :=
  let post := endToEndFamilyPostBlockBanksOfReceive A package one inputOne two
    inputTwo
  post.installSummaries A package

/-- The concrete finite receive table.  Both projections call the same joint
function with the arguments put in process order. -/
noncomputable def endToEndFamilyFullRefreshReceiveTable :
    EndToEndFamilyFullReceiveTable A package where
  recvOne := fun one inputOne two inputTwo =>
    (endToEndFamilyFullRecvRefreshInstallPair A package one inputOne two
      inputTwo).1
  recvTwo := fun two inputTwo one inputOne =>
    (endToEndFamilyFullRecvRefreshInstallPair A package one inputOne two
      inputTwo).2

/-- The full finite local-summary carrier with the refresh table installed.
Only the two initial summaries remain parameters of this operational brick. -/
noncomputable def endToEndFamilyFullRefreshSummaryAutomaton
    (initialOne : EndToEndFamilyFullOneSummary A package)
    (initialTwo : EndToEndFamilyFullTwoSummary A package) :
    LocalSummaryAutomaton In₁ In₂ :=
  endToEndFamilyFullSummaryAutomaton A package initialOne initialTwo
    (endToEndFamilyFullRefreshReceiveTable A package)

section
omit [Inhabited In₁] [Inhabited In₂]

@[simp] theorem endToEndFamilyFullRefreshReceiveTable_recvOne
    (one : EndToEndFamilyFullOneSummary A package) (inputOne : In₁)
    (two : EndToEndFamilyFullTwoSummary A package) (inputTwo : In₂) :
    (endToEndFamilyFullRefreshReceiveTable A package).recvOne one inputOne two
        inputTwo =
      (endToEndFamilyFullRecvRefreshInstallPair A package one inputOne two
        inputTwo).1 := rfl

@[simp] theorem endToEndFamilyFullRefreshReceiveTable_recvTwo
    (two : EndToEndFamilyFullTwoSummary A package) (inputTwo : In₂)
    (one : EndToEndFamilyFullOneSummary A package) (inputOne : In₁) :
    (endToEndFamilyFullRefreshReceiveTable A package).recvTwo two inputTwo one
        inputOne =
      (endToEndFamilyFullRecvRefreshInstallPair A package one inputOne two
        inputTwo).2 := rfl

@[simp] theorem endToEndFamilyFullRefreshSummaryAutomaton_stepRecv_one
    (initialOne : EndToEndFamilyFullOneSummary A package)
    (initialTwo : EndToEndFamilyFullTwoSummary A package)
    (one : EndToEndFamilyFullOneSummary A package) (inputOne : In₁)
    (two : EndToEndFamilyFullTwoSummary A package) (inputTwo : In₂) :
    (endToEndFamilyFullRefreshSummaryAutomaton A package initialOne
      initialTwo).stepRecv .one one (.inl inputOne) two (.inr inputTwo) =
      (endToEndFamilyFullRecvRefreshInstallPair A package one inputOne two
        inputTwo).1 := rfl

@[simp] theorem endToEndFamilyFullRefreshSummaryAutomaton_stepRecv_two
    (initialOne : EndToEndFamilyFullOneSummary A package)
    (initialTwo : EndToEndFamilyFullTwoSummary A package)
    (two : EndToEndFamilyFullTwoSummary A package) (inputTwo : In₂)
    (one : EndToEndFamilyFullOneSummary A package) (inputOne : In₁) :
    (endToEndFamilyFullRefreshSummaryAutomaton A package initialOne
      initialTwo).stepRecv .two two (.inr inputTwo) one (.inl inputOne) =
      (endToEndFamilyFullRecvRefreshInstallPair A package one inputOne two
        inputTwo).2 := rfl

end

/-! ## Exact synchronized-source equations -/

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem endToEndFamilyPostBlockBanksOfReceive_rightSource_false
    (one : EndToEndFamilyFullOneSummary A package) (inputOne : In₁)
    (two : EndToEndFamilyFullTwoSummary A package) (inputTwo : In₂) :
    let post := endToEndFamilyPostBlockBanksOfReceive A package one inputOne
      two inputTwo
    post.rightSource A package false =
      endToEndRightFamilyBankCurrentRoot A package post.rightMove
        post.rightBank post.pastAnchor := by
  simp [EndToEndFamilyPostBlockBanks.rightSource]

@[simp] theorem endToEndFamilyPostBlockBanksOfReceive_leftSource_false
    (one : EndToEndFamilyFullOneSummary A package) (inputOne : In₁)
    (two : EndToEndFamilyFullTwoSummary A package) (inputTwo : In₂) :
    let post := endToEndFamilyPostBlockBanksOfReceive A package one inputOne
      two inputTwo
    post.leftSource A package false =
      endToEndLeftFamilyBankCurrentRoot A package post.leftMove post.leftBank
        (!post.pastAnchor) := by
  simp [EndToEndFamilyPostBlockBanks.leftSource]

theorem endToEndFamilyPostBlockBanksOfReceive_rightSource_true_of_pending
    (one : EndToEndFamilyFullOneSummary A package) (inputOne : In₁)
    (two : EndToEndFamilyFullTwoSummary A package) (inputTwo : In₂)
    (source : EndToEndRecurrentRightMacro A package)
    (hpending :
      let post := endToEndFamilyPostBlockBanksOfReceive A package one inputOne
        two inputTwo
      (post.leftBank (!post.pastAnchor)).2.2 = some source) :
    let post := endToEndFamilyPostBlockBanksOfReceive A package one inputOne
      two inputTwo
    post.rightSource A package true =
      endToEndRightRestartRootOfPending A package source := by
  dsimp only
  apply endToEndTotalNextRightFamilyRoots_true_of_pending
  exact hpending

theorem endToEndFamilyPostBlockBanksOfReceive_leftSource_true_of_pending
    (one : EndToEndFamilyFullOneSummary A package) (inputOne : In₁)
    (two : EndToEndFamilyFullTwoSummary A package) (inputTwo : In₂)
    (source : EndToEndRecurrentLeftMacro A package)
    (hpending :
      let post := endToEndFamilyPostBlockBanksOfReceive A package one inputOne
        two inputTwo
      (post.rightBank post.pastAnchor).2.2 = some source) :
    let post := endToEndFamilyPostBlockBanksOfReceive A package one inputOne
      two inputTwo
    post.leftSource A package true =
      endToEndLeftRestartRootOfPending A package source := by
  dsimp only
  apply endToEndTotalNextLeftFamilyRoots_true_of_pending
  exact hpending

end

end

end DetParityAutomaton

end DistributedSynthesis
