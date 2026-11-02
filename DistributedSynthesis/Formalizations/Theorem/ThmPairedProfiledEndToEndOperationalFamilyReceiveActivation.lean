/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndOperationalFamilyReceiveInstall

/-!
# Retained receivers and lazy activation of staged family senders

On a strict receive only the receiver can refresh its finite control.  The
other process keeps advancing its already installed sender table.  Therefore
the receiver must retain the matching active receiver bank; replacing that
bank by a freshly selected table would make the very next same-direction
receive take the old mismatch fallback.

The opposite sender table *is* installed at a receive, ready for a possible
reversal.  If that reversal occurs, the newly receiving process sees the
staged table in the delivered summary.  Its retained old bank then has a
different move.  This is not an error: it is the activation signal.  The
receiver initializes the matching bank from the delivered move and its
retained row data, consumes the current input pair, and continues normally.

All choices below are functions of the ordinary receive arguments.  No
function receives the graph, an orientation, a family member, or a
strict-leader bit.
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

/-! ## The one bit of local receipt memory -/

/-- A process-one controller together with the locally observable fact that
process one received in the preceding round.  This bit is not an orientation
or leader tag: it is updated solely from process one's own `recv`/`noRecv`
event. -/
abbrev EndToEndFamilyReceiptOneSummary :=
  EndToEndFamilyFullOneSummary A package × Bool

/-- Process-two mirror. -/
abbrev EndToEndFamilyReceiptTwoSummary :=
  EndToEndFamilyFullTwoSummary A package × Bool

/-! ## Lazy activation on a move mismatch -/

/-- Rows used when a staged left table becomes active.  The continued member
keeps the row stored in the dormant bank; the freshly staged member uses the
new receiver's own previous-round receipt bit. -/
def endToEndActivationNextLeftFamilyRows
    (pastAnchor : Bool)
    (leftMove : EndToEndLeftFamilyPairMove A package)
    (leftBank : EndToEndLeftFamilyReceiverBank A package leftMove)
    (previouslyReceived : Bool) : Bool -> PairedEntryRow
  | false => (leftBank (!pastAnchor)).1
  | true => guardedEntryRowOfReceived previouslyReceived

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem endToEndActivationNextLeftFamilyRows_false
    (pastAnchor : Bool)
    (leftMove : EndToEndLeftFamilyPairMove A package)
    (leftBank : EndToEndLeftFamilyReceiverBank A package leftMove)
    (previouslyReceived : Bool) :
    endToEndActivationNextLeftFamilyRows A package pastAnchor leftMove leftBank
        previouslyReceived false =
      (leftBank (!pastAnchor)).1 :=
  rfl

@[simp] theorem endToEndActivationNextLeftFamilyRows_true
    (pastAnchor : Bool)
    (leftMove : EndToEndLeftFamilyPairMove A package)
    (leftBank : EndToEndLeftFamilyReceiverBank A package leftMove)
    (previouslyReceived : Bool) :
    endToEndActivationNextLeftFamilyRows A package pastAnchor leftMove leftBank
        previouslyReceived true =
      guardedEntryRowOfReceived previouslyReceived :=
  rfl

/-- A staged member activated after a locally strict preceding round uses the
`first` entry row. -/
@[simp] theorem endToEndActivationNextLeftFamilyRows_strict
    (pastAnchor : Bool)
    (leftMove : EndToEndLeftFamilyPairMove A package)
    (leftBank : EndToEndLeftFamilyReceiverBank A package leftMove) :
    endToEndActivationNextLeftFamilyRows A package pastAnchor leftMove leftBank
        false true = .first :=
  rfl

/-- If this same process received in the preceding round, activation uses the
simultaneous (`both`) entry row. -/
@[simp] theorem endToEndActivationNextLeftFamilyRows_both
    (pastAnchor : Bool)
    (leftMove : EndToEndLeftFamilyPairMove A package)
    (leftBank : EndToEndLeftFamilyReceiverBank A package leftMove) :
    endToEndActivationNextLeftFamilyRows A package pastAnchor leftMove leftBank
        true true = .both :=
  rfl

end

/-- Right-family mirror. -/
def endToEndActivationNextRightFamilyRows
    (pastAnchor : Bool)
    (rightMove : EndToEndRightFamilyPairMove A package)
    (rightBank : EndToEndRightFamilyReceiverBank A package rightMove)
    (previouslyReceived : Bool) : Bool -> PairedEntryRow
  | false => (rightBank pastAnchor).1
  | true => guardedEntryRowOfReceived previouslyReceived

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem endToEndActivationNextRightFamilyRows_false
    (pastAnchor : Bool)
    (rightMove : EndToEndRightFamilyPairMove A package)
    (rightBank : EndToEndRightFamilyReceiverBank A package rightMove)
    (previouslyReceived : Bool) :
    endToEndActivationNextRightFamilyRows A package pastAnchor rightMove
        rightBank previouslyReceived false =
      (rightBank pastAnchor).1 :=
  rfl

@[simp] theorem endToEndActivationNextRightFamilyRows_true
    (pastAnchor : Bool)
    (rightMove : EndToEndRightFamilyPairMove A package)
    (rightBank : EndToEndRightFamilyReceiverBank A package rightMove)
    (previouslyReceived : Bool) :
    endToEndActivationNextRightFamilyRows A package pastAnchor rightMove
        rightBank previouslyReceived true =
      guardedEntryRowOfReceived previouslyReceived :=
  rfl

@[simp] theorem endToEndActivationNextRightFamilyRows_strict
    (pastAnchor : Bool)
    (rightMove : EndToEndRightFamilyPairMove A package)
    (rightBank : EndToEndRightFamilyReceiverBank A package rightMove) :
    endToEndActivationNextRightFamilyRows A package pastAnchor rightMove
        rightBank false true = .first :=
  rfl

@[simp] theorem endToEndActivationNextRightFamilyRows_both
    (pastAnchor : Bool)
    (rightMove : EndToEndRightFamilyPairMove A package)
    (rightBank : EndToEndRightFamilyReceiverBank A package rightMove) :
    endToEndActivationNextRightFamilyRows A package pastAnchor rightMove
        rightBank true true = .both :=
  rfl

end

/-- Process one has just received a staged left sender different from its
retained active left bank.  Initialize the new bank from the delivered roots,
using the rows carried by the retained bank, and consume this receive. -/
noncomputable def endToEndFamilyFullRecvOneBankActivate
    (self : EndToEndFamilyFullOneSummary A package) (inputOne : In₁)
    (other : EndToEndFamilyFullTwoSummary A package) (inputTwo : In₂)
    (previouslyReceived : Bool) :
    EndToEndFamilyFullOneSummary A package :=
  let rows := endToEndActivationNextLeftFamilyRows A package
    self.1.leftReceiver.1 self.1.leftReceiver.2.1
    self.1.leftReceiver.2.2 previouslyReceived
  let bank := initialEndToEndLeftFamilyReceiverBank A package
    other.1.leftSender.1 rows
  let next := stepEndToEndLeftFamilyReceiverBankFor A package
    other.1.leftSender bank self.1.leftReceiver.1 (inputOne, inputTwo)
  (⟨self.1.rightSender,
      ⟨self.1.leftReceiver.1, ⟨other.1.leftSender.1, next.2⟩⟩⟩,
    next.1)

/-- Process-two mirror. -/
noncomputable def endToEndFamilyFullRecvTwoBankActivate
    (self : EndToEndFamilyFullTwoSummary A package) (inputTwo : In₂)
    (other : EndToEndFamilyFullOneSummary A package) (inputOne : In₁)
    (previouslyReceived : Bool) :
    EndToEndFamilyFullTwoSummary A package :=
  let rows := endToEndActivationNextRightFamilyRows A package
    self.1.rightReceiver.1 self.1.rightReceiver.2.1
    self.1.rightReceiver.2.2 previouslyReceived
  let bank := initialEndToEndRightFamilyReceiverBank A package
    other.1.rightSender.1 rows
  let next := stepEndToEndRightFamilyReceiverBankFor A package
    other.1.rightSender bank self.1.rightReceiver.1 (inputTwo, inputOne)
  (⟨⟨self.1.rightReceiver.1, ⟨other.1.rightSender.1, next.2⟩⟩,
      self.1.leftSender⟩,
    next.1)

/-- Matched moves continue the active bank; a mismatch activates the newly
delivered staged sender instead of silently doing nothing. -/
noncomputable def endToEndFamilyFullRecvOneBankSyncOrActivate
    (self : EndToEndFamilyFullOneSummary A package) (inputOne : In₁)
    (other : EndToEndFamilyFullTwoSummary A package) (inputTwo : In₂)
    (previouslyReceived : Bool) :
    EndToEndFamilyFullOneSummary A package := by
  classical
  if hmove : self.1.leftReceiver.2.1 = other.1.leftSender.1 then
    exact endToEndFamilyFullRecvOneBankSyncMatched A package self inputOne
      other inputTwo hmove
  else
    exact endToEndFamilyFullRecvOneBankActivate A package self inputOne other
      inputTwo previouslyReceived

noncomputable def endToEndFamilyFullRecvTwoBankSyncOrActivate
    (self : EndToEndFamilyFullTwoSummary A package) (inputTwo : In₂)
    (other : EndToEndFamilyFullOneSummary A package) (inputOne : In₁)
    (previouslyReceived : Bool) :
    EndToEndFamilyFullTwoSummary A package := by
  classical
  if hmove : self.1.rightReceiver.2.1 = other.1.rightSender.1 then
    exact endToEndFamilyFullRecvTwoBankSyncMatched A package self inputTwo
      other inputOne hmove
  else
    exact endToEndFamilyFullRecvTwoBankActivate A package self inputTwo other
      inputOne previouslyReceived

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem endToEndFamilyFullRecvOneBankSyncOrActivate_of_move_eq
    (self : EndToEndFamilyFullOneSummary A package) (inputOne : In₁)
    (other : EndToEndFamilyFullTwoSummary A package) (inputTwo : In₂)
    (previouslyReceived : Bool)
    (hmove : self.1.leftReceiver.2.1 = other.1.leftSender.1) :
    endToEndFamilyFullRecvOneBankSyncOrActivate A package self inputOne other
        inputTwo previouslyReceived =
      endToEndFamilyFullRecvOneBankSyncMatched A package self inputOne other
        inputTwo hmove := by
  classical
  simp only [endToEndFamilyFullRecvOneBankSyncOrActivate, dif_pos hmove]

@[simp] theorem endToEndFamilyFullRecvOneBankSyncOrActivate_of_move_ne
    (self : EndToEndFamilyFullOneSummary A package) (inputOne : In₁)
    (other : EndToEndFamilyFullTwoSummary A package) (inputTwo : In₂)
    (previouslyReceived : Bool)
    (hmove : self.1.leftReceiver.2.1 ≠ other.1.leftSender.1) :
    endToEndFamilyFullRecvOneBankSyncOrActivate A package self inputOne other
        inputTwo previouslyReceived =
      endToEndFamilyFullRecvOneBankActivate A package self inputOne other
        inputTwo previouslyReceived := by
  classical
  simp only [endToEndFamilyFullRecvOneBankSyncOrActivate, dif_neg hmove]

@[simp] theorem endToEndFamilyFullRecvTwoBankSyncOrActivate_of_move_eq
    (self : EndToEndFamilyFullTwoSummary A package) (inputTwo : In₂)
    (other : EndToEndFamilyFullOneSummary A package) (inputOne : In₁)
    (previouslyReceived : Bool)
    (hmove : self.1.rightReceiver.2.1 = other.1.rightSender.1) :
    endToEndFamilyFullRecvTwoBankSyncOrActivate A package self inputTwo other
        inputOne previouslyReceived =
      endToEndFamilyFullRecvTwoBankSyncMatched A package self inputTwo other
        inputOne hmove := by
  classical
  simp only [endToEndFamilyFullRecvTwoBankSyncOrActivate, dif_pos hmove]

@[simp] theorem endToEndFamilyFullRecvTwoBankSyncOrActivate_of_move_ne
    (self : EndToEndFamilyFullTwoSummary A package) (inputTwo : In₂)
    (other : EndToEndFamilyFullOneSummary A package) (inputOne : In₁)
    (previouslyReceived : Bool)
    (hmove : self.1.rightReceiver.2.1 ≠ other.1.rightSender.1) :
    endToEndFamilyFullRecvTwoBankSyncOrActivate A package self inputTwo other
        inputOne previouslyReceived =
      endToEndFamilyFullRecvTwoBankActivate A package self inputTwo other
        inputOne previouslyReceived := by
  classical
  simp only [endToEndFamilyFullRecvTwoBankSyncOrActivate, dif_neg hmove]

end

/-! ## Exact activation equations -/

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem endToEndFamilyFullRecvOneBankActivate_receiverMove
    (self : EndToEndFamilyFullOneSummary A package) (inputOne : In₁)
    (other : EndToEndFamilyFullTwoSummary A package) (inputTwo : In₂)
    (previouslyReceived : Bool) :
    (endToEndFamilyFullRecvOneBankActivate A package self inputOne other
      inputTwo previouslyReceived).1.leftReceiver.2.1 = other.1.leftSender.1 :=
  rfl

@[simp] theorem endToEndFamilyFullRecvTwoBankActivate_receiverMove
    (self : EndToEndFamilyFullTwoSummary A package) (inputTwo : In₂)
    (other : EndToEndFamilyFullOneSummary A package) (inputOne : In₁)
    (previouslyReceived : Bool) :
    (endToEndFamilyFullRecvTwoBankActivate A package self inputTwo other
      inputOne previouslyReceived).1.rightReceiver.2.1 = other.1.rightSender.1 :=
  rfl

@[simp] theorem endToEndFamilyFullRecvOneBankActivate_senderRetained
    (self : EndToEndFamilyFullOneSummary A package) (inputOne : In₁)
    (other : EndToEndFamilyFullTwoSummary A package) (inputTwo : In₂)
    (previouslyReceived : Bool) :
    (endToEndFamilyFullRecvOneBankActivate A package self inputOne other
      inputTwo previouslyReceived).1.rightSender = self.1.rightSender :=
  rfl

@[simp] theorem endToEndFamilyFullRecvTwoBankActivate_senderRetained
    (self : EndToEndFamilyFullTwoSummary A package) (inputTwo : In₂)
    (other : EndToEndFamilyFullOneSummary A package) (inputOne : In₁)
    (previouslyReceived : Bool) :
    (endToEndFamilyFullRecvTwoBankActivate A package self inputTwo other
      inputOne previouslyReceived).1.leftSender = self.1.leftSender :=
  rfl

end

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- After either continuation or activation, the receiver bank is attached
to exactly the move delivered by the current sender. -/
@[simp] theorem endToEndFamilyFullRecvOneBankSyncOrActivate_receiverMove
    (self : EndToEndFamilyFullOneSummary A package) (inputOne : In₁)
    (other : EndToEndFamilyFullTwoSummary A package) (inputTwo : In₂)
    (previouslyReceived : Bool) :
    (endToEndFamilyFullRecvOneBankSyncOrActivate A package self inputOne other
      inputTwo previouslyReceived).1.leftReceiver.2.1 = other.1.leftSender.1 := by
  classical
  by_cases hmove : self.1.leftReceiver.2.1 = other.1.leftSender.1
  · rw [endToEndFamilyFullRecvOneBankSyncOrActivate_of_move_eq A package self
      inputOne other inputTwo previouslyReceived hmove]
    rfl
  · rw [endToEndFamilyFullRecvOneBankSyncOrActivate_of_move_ne A package self
      inputOne other inputTwo previouslyReceived hmove]
    rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem endToEndFamilyFullRecvTwoBankSyncOrActivate_receiverMove
    (self : EndToEndFamilyFullTwoSummary A package) (inputTwo : In₂)
    (other : EndToEndFamilyFullOneSummary A package) (inputOne : In₁)
    (previouslyReceived : Bool) :
    (endToEndFamilyFullRecvTwoBankSyncOrActivate A package self inputTwo other
      inputOne previouslyReceived).1.rightReceiver.2.1 = other.1.rightSender.1 := by
  classical
  by_cases hmove : self.1.rightReceiver.2.1 = other.1.rightSender.1
  · rw [endToEndFamilyFullRecvTwoBankSyncOrActivate_of_move_eq A package self
      inputTwo other inputOne previouslyReceived hmove]
    rfl
  · rw [endToEndFamilyFullRecvTwoBankSyncOrActivate_of_move_ne A package self
      inputTwo other inputOne previouslyReceived hmove]
    rfl

/-! ## Graph-blind synchronized post data -/

noncomputable def endToEndFamilyFullRecvBankSyncOrActivatePair
    (one : EndToEndFamilyFullOneSummary A package) (inputOne : In₁)
    (two : EndToEndFamilyFullTwoSummary A package) (inputTwo : In₂)
    (onePreviouslyReceived twoPreviouslyReceived : Bool) :
    EndToEndFamilyFullOneSummary A package ×
      EndToEndFamilyFullTwoSummary A package :=
  (endToEndFamilyFullRecvOneBankSyncOrActivate A package one inputOne two
      inputTwo onePreviouslyReceived,
    endToEndFamilyFullRecvTwoBankSyncOrActivate A package two inputTwo one
      inputOne twoPreviouslyReceived)

noncomputable def endToEndFamilyPostBlockBanksOfReceiveActivate
    (one : EndToEndFamilyFullOneSummary A package) (inputOne : In₁)
    (two : EndToEndFamilyFullTwoSummary A package) (inputTwo : In₂)
    (onePreviouslyReceived twoPreviouslyReceived : Bool) :
    EndToEndFamilyPostBlockBanks A package := by
  let synced := endToEndFamilyFullRecvBankSyncOrActivatePair A package one
    inputOne two inputTwo onePreviouslyReceived twoPreviouslyReceived
  exact
    { pastAnchor := synced.1.1.leftReceiver.1
      rightMove := synced.2.1.rightReceiver.2.1
      rightBank := synced.2.1.rightReceiver.2.2
      leftMove := synced.1.1.leftReceiver.2.1
      leftBank := synced.1.1.leftReceiver.2.2
      outputOne := synced.1.2
      outputTwo := synced.2.2 }

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem endToEndFamilyPostBlockBanksOfReceiveActivate_leftMove
    (one : EndToEndFamilyFullOneSummary A package) (inputOne : In₁)
    (two : EndToEndFamilyFullTwoSummary A package) (inputTwo : In₂)
    (onePreviouslyReceived twoPreviouslyReceived : Bool) :
    (endToEndFamilyPostBlockBanksOfReceiveActivate A package one inputOne two
      inputTwo onePreviouslyReceived twoPreviouslyReceived).leftMove =
        two.1.leftSender.1 := by
  exact endToEndFamilyFullRecvOneBankSyncOrActivate_receiverMove A package one
    inputOne two inputTwo onePreviouslyReceived

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem endToEndFamilyPostBlockBanksOfReceiveActivate_rightMove
    (one : EndToEndFamilyFullOneSummary A package) (inputOne : In₁)
    (two : EndToEndFamilyFullTwoSummary A package) (inputTwo : In₂)
    (onePreviouslyReceived twoPreviouslyReceived : Bool) :
    (endToEndFamilyPostBlockBanksOfReceiveActivate A package one inputOne two
      inputTwo onePreviouslyReceived twoPreviouslyReceived).rightMove =
        one.1.rightSender.1 := by
  exact endToEndFamilyFullRecvTwoBankSyncOrActivate_receiverMove A package two
    inputTwo one inputOne twoPreviouslyReceived

/-! ## Retain active receiver banks, install only staged senders -/

namespace EndToEndFamilyPostBlockBanks

/-- The right move is staged only in process one's sender slot; the stepped
left receiver remains attached to the active process-two sender.  The mirror
holds for process two. -/
noncomputable def installControlsRetainingWith
    (post : EndToEndFamilyPostBlockBanks A package)
    (right : EndToEndRightFamilyPairMove A package)
    (left : EndToEndLeftFamilyPairMove A package) :
    EndToEndFamilyFullOneControl A package ×
      EndToEndFamilyFullTwoControl A package :=
  ({ rightSender := EndToEndRightFamilyPairOverlay.initial A package right
     leftReceiver :=
       (post.pastAnchor, ⟨post.leftMove, post.leftBank⟩) },
   { rightReceiver :=
       (post.pastAnchor, ⟨post.rightMove, post.rightBank⟩)
     leftSender := EndToEndLeftFamilyPairOverlay.initial A package left })

noncomputable def installSummariesRetainingWith
    (post : EndToEndFamilyPostBlockBanks A package)
    (right : EndToEndRightFamilyPairMove A package)
    (left : EndToEndLeftFamilyPairMove A package) :
    EndToEndFamilyFullOneSummary A package ×
      EndToEndFamilyFullTwoSummary A package :=
  (((post.installControlsRetainingWith A package right left).1,
      post.outputOne),
    ((post.installControlsRetainingWith A package right left).2,
      post.outputTwo))

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem installControlsRetainingWith_leftReceiver_move
    (post : EndToEndFamilyPostBlockBanks A package)
    (right : EndToEndRightFamilyPairMove A package)
    (left : EndToEndLeftFamilyPairMove A package) :
    (post.installControlsRetainingWith A package right left).1.leftReceiver.2.1
      = post.leftMove :=
  rfl

@[simp] theorem installControlsRetainingWith_rightReceiver_move
    (post : EndToEndFamilyPostBlockBanks A package)
    (right : EndToEndRightFamilyPairMove A package)
    (left : EndToEndLeftFamilyPairMove A package) :
    (post.installControlsRetainingWith A package right left).2.rightReceiver.2.1
      = post.rightMove :=
  rfl

@[simp] theorem installControlsRetainingWith_rightSender_move
    (post : EndToEndFamilyPostBlockBanks A package)
    (right : EndToEndRightFamilyPairMove A package)
    (left : EndToEndLeftFamilyPairMove A package) :
    (post.installControlsRetainingWith A package right left).1.rightSender.1 =
      right :=
  rfl

@[simp] theorem installControlsRetainingWith_leftSender_move
    (post : EndToEndFamilyPostBlockBanks A package)
    (right : EndToEndRightFamilyPairMove A package)
    (left : EndToEndLeftFamilyPairMove A package) :
    (post.installControlsRetainingWith A package right left).2.leftSender.1 =
      left :=
  rfl

end

end EndToEndFamilyPostBlockBanks

/-! ## Receipt-tagged local-summary automaton -/

/-- A graph-blind joint receive computation for the payload controllers.
Both old receipt bits are explicit arguments because they are part of the two
delivered local summaries.  The two projections below call this same joint
function, just as `LocalSummaryAutomaton.stepRecv` requires. -/
structure EndToEndFamilyReceiptReceivePairTable where
  recvPair : EndToEndFamilyFullOneSummary A package → In₁ →
    EndToEndFamilyFullTwoSummary A package → In₂ → Bool → Bool →
      EndToEndFamilyFullOneSummary A package ×
        EndToEndFamilyFullTwoSummary A package

/-- The pure synchronization/activation receive computation.  It consumes
the receiver's local previous-receipt bit on either side and never receives a
graph or leader signal. -/
noncomputable def endToEndFamilyReceiptSyncOrActivateReceivePairTable :
    EndToEndFamilyReceiptReceivePairTable A package where
  recvPair := fun one inputOne two inputTwo onePreviouslyReceived
      twoPreviouslyReceived =>
    endToEndFamilyFullRecvBankSyncOrActivatePair A package one inputOne two
      inputTwo onePreviouslyReceived twoPreviouslyReceived

/-- Add the locally observable preceding-round receipt bit to the full family
payload.  A blind step sets the process's own bit to `false`; a receive sets it
to `true`.  On a receive, both old bits are passed to one common joint table.
Thus the carrier is finite and view-measurable without storing an orientation
or a strict-leader flag. -/
noncomputable def endToEndFamilyReceiptSummaryAutomaton
    (initialOne : EndToEndFamilyReceiptOneSummary A package)
    (initialTwo : EndToEndFamilyReceiptTwoSummary A package)
    (receive : EndToEndFamilyReceiptReceivePairTable A package) :
    LocalSummaryAutomaton In₁ In₂ where
  Summary
    | .one => EndToEndFamilyReceiptOneSummary A package
    | .two => EndToEndFamilyReceiptTwoSummary A package
  finite
    | .one => inferInstance
    | .two => inferInstance
  initial
    | .one => initialOne
    | .two => initialTwo
  stepNoRecv
    | .one, summary, .inl input =>
        (endToEndFamilyFullStepNoRecvOne A package summary.1 input, false)
    | .two, summary, .inr input =>
        (endToEndFamilyFullStepNoRecvTwo A package summary.1 input, false)
    | _, summary, _ => summary
  stepRecv
    | .one, self, .inl inputOne, other, .inr inputTwo =>
        ((receive.recvPair self.1 inputOne other.1 inputTwo self.2 other.2).1,
          true)
    | .two, self, .inr inputTwo, other, .inl inputOne =>
        ((receive.recvPair other.1 inputOne self.1 inputTwo other.2 self.2).2,
          true)
    | _, self, _, _, _ => self

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem endToEndFamilyReceiptSummaryAutomaton_stepNoRecv_one
    (initialOne : EndToEndFamilyReceiptOneSummary A package)
    (initialTwo : EndToEndFamilyReceiptTwoSummary A package)
    (receive : EndToEndFamilyReceiptReceivePairTable A package)
    (summary : EndToEndFamilyReceiptOneSummary A package) (input : In₁) :
    (endToEndFamilyReceiptSummaryAutomaton A package initialOne initialTwo
      receive).stepNoRecv .one summary (.inl input) =
        (endToEndFamilyFullStepNoRecvOne A package summary.1 input, false) :=
  rfl

@[simp] theorem endToEndFamilyReceiptSummaryAutomaton_stepNoRecv_two
    (initialOne : EndToEndFamilyReceiptOneSummary A package)
    (initialTwo : EndToEndFamilyReceiptTwoSummary A package)
    (receive : EndToEndFamilyReceiptReceivePairTable A package)
    (summary : EndToEndFamilyReceiptTwoSummary A package) (input : In₂) :
    (endToEndFamilyReceiptSummaryAutomaton A package initialOne initialTwo
      receive).stepNoRecv .two summary (.inr input) =
        (endToEndFamilyFullStepNoRecvTwo A package summary.1 input, false) :=
  rfl

@[simp] theorem endToEndFamilyReceiptSummaryAutomaton_stepRecv_one
    (initialOne : EndToEndFamilyReceiptOneSummary A package)
    (initialTwo : EndToEndFamilyReceiptTwoSummary A package)
    (receive : EndToEndFamilyReceiptReceivePairTable A package)
    (one : EndToEndFamilyReceiptOneSummary A package) (inputOne : In₁)
    (two : EndToEndFamilyReceiptTwoSummary A package) (inputTwo : In₂) :
    (endToEndFamilyReceiptSummaryAutomaton A package initialOne initialTwo
      receive).stepRecv .one one (.inl inputOne) two (.inr inputTwo) =
        ((receive.recvPair one.1 inputOne two.1 inputTwo one.2 two.2).1,
          true) :=
  rfl

@[simp] theorem endToEndFamilyReceiptSummaryAutomaton_stepRecv_two
    (initialOne : EndToEndFamilyReceiptOneSummary A package)
    (initialTwo : EndToEndFamilyReceiptTwoSummary A package)
    (receive : EndToEndFamilyReceiptReceivePairTable A package)
    (two : EndToEndFamilyReceiptTwoSummary A package) (inputTwo : In₂)
    (one : EndToEndFamilyReceiptOneSummary A package) (inputOne : In₁) :
    (endToEndFamilyReceiptSummaryAutomaton A package initialOne initialTwo
      receive).stepRecv .two two (.inr inputTwo) one (.inl inputOne) =
        ((receive.recvPair one.1 inputOne two.1 inputTwo one.2 two.2).2,
          true) :=
  rfl

@[simp] theorem endToEndFamilyReceiptSyncOrActivate_stepRecv_one
    (initialOne : EndToEndFamilyReceiptOneSummary A package)
    (initialTwo : EndToEndFamilyReceiptTwoSummary A package)
    (one : EndToEndFamilyReceiptOneSummary A package) (inputOne : In₁)
    (two : EndToEndFamilyReceiptTwoSummary A package) (inputTwo : In₂) :
    (endToEndFamilyReceiptSummaryAutomaton A package initialOne initialTwo
      (endToEndFamilyReceiptSyncOrActivateReceivePairTable A package)).stepRecv
        .one one (.inl inputOne) two (.inr inputTwo) =
      ((endToEndFamilyFullRecvBankSyncOrActivatePair A package one.1 inputOne
        two.1 inputTwo one.2 two.2).1, true) :=
  rfl

@[simp] theorem endToEndFamilyReceiptSyncOrActivate_stepRecv_two
    (initialOne : EndToEndFamilyReceiptOneSummary A package)
    (initialTwo : EndToEndFamilyReceiptTwoSummary A package)
    (two : EndToEndFamilyReceiptTwoSummary A package) (inputTwo : In₂)
    (one : EndToEndFamilyReceiptOneSummary A package) (inputOne : In₁) :
    (endToEndFamilyReceiptSummaryAutomaton A package initialOne initialTwo
      (endToEndFamilyReceiptSyncOrActivateReceivePairTable A package)).stepRecv
        .two two (.inr inputTwo) one (.inl inputOne) =
      ((endToEndFamilyFullRecvBankSyncOrActivatePair A package one.1 inputOne
        two.1 inputTwo one.2 two.2).2, true) :=
  rfl

end

end


end DetParityAutomaton

end DistributedSynthesis
