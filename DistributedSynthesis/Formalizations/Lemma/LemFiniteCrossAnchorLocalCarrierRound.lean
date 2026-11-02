/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteCrossAnchorLocalCarrier

/-!
# Exact rounds of the local cross-anchor carrier

The two endpoints of a preselected cross-anchor table execute separate local
maps.  This file records the semantic bridge needed by later trace proofs:
when their stored table move and shared control agree, the two physical
outputs form exactly the narrowed monitor record selected by the receiver's
private member state.

No executable definition below receives a graph, orientation, leader bit, or
semantic history.  Those notions occur neither in the state nor in the input
of the local maps.
-/

namespace DistributedSynthesis

universe u v x y w

noncomputable section

variable {RIn : Type u} {SIn : Type v} {ROut : Type x} {SOut : Type y}
variable [Inhabited RIn] [Inhabited SIn] [Inhabited ROut]
variable [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut]
variable [DecidableEq RIn] [DecidableEq SIn]

variable {Descriptor : Type w} [Fintype Descriptor]
variable (monitor : Descriptor →
  BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut)
variable
  (firstAllowed :
    ∀ pair : FiniteCrossAnchorDescriptorPair monitor,
      ∀ anchor, RealizedBlockRound RIn SIn ROut SOut → Bool)
  (secondAllowed :
    ∀ pair : FiniteCrossAnchorDescriptorPair monitor,
      ∀ anchor, RealizedBlockRound RIn SIn ROut SOut →
        RealizedBlockRound RIn SIn ROut SOut → Bool)

private noncomputable abbrev LocalGuard
    (move : FiniteCrossAnchorDescriptorFirstTwoMove monitor firstAllowed
      secondAllowed)
    (anchor : Bool) :=
  finiteCrossAnchorFirstTwoGuardFamily
    (fun member => monitor (move.1.descriptor member)) move.1.start
    (firstAllowed move.1) (secondAllowed move.1) anchor

section
omit [Inhabited RIn] [Inhabited SIn] [Inhabited ROut] [Fintype Descriptor]

/-- The receiver coordinate returned by the local map is literally the
receiver half of the narrowed table label at its private monitor state. -/
theorem finiteCrossAnchorDescriptorFirstTwoReceiverRecv_output_eq_label
    (receiver : FiniteCrossAnchorDescriptorFirstTwoReceiverState monitor
      firstAllowed secondAllowed)
    (own : RIn) (delivered : SIn) :
    (finiteCrossAnchorDescriptorFirstTwoReceiverRecv monitor firstAllowed
      secondAllowed receiver own delivered).1 =
      ((receiver.1.memberController monitor receiver.2.1).labelOf
        receiver.2.2.1).2 receiver.2.2.2 (own, delivered) :=
  rfl

/-- Synchronized endpoint states emit exactly one narrowed monitor round.
This is the local-to-monitor readback equation; the member bit is read only
from the receiver's own finite state. -/
theorem finiteCrossAnchorDescriptorFirstTwo_localRound_eq
    (sender : FiniteCrossAnchorDescriptorFirstTwoSenderState monitor
      firstAllowed secondAllowed)
    (receiver : FiniteCrossAnchorDescriptorFirstTwoReceiverState monitor
      firstAllowed secondAllowed)
    (hmove : sender.1 = receiver.1)
    (hsync : HEq sender.2 receiver.2.2.1)
    (own : RIn) (delivered : SIn) :
    let senderStep :=
      finiteCrossAnchorDescriptorFirstTwoSenderNoRecv monitor firstAllowed
        secondAllowed sender delivered
    let receiverStep :=
      finiteCrossAnchorDescriptorFirstTwoReceiverRecv monitor firstAllowed
        secondAllowed receiver own delivered
    ((own, delivered), receiverStep.1, senderStep.1) =
      narrowedRecord
        (LocalGuard monitor firstAllowed secondAllowed receiver.1 receiver.2.1)
        ((receiver.1.memberController monitor receiver.2.1).labelOf
          receiver.2.2.1)
        receiver.2.2.2 (own, delivered) := by
  rcases sender with ⟨senderMove, senderControl⟩
  rcases receiver with
    ⟨receiverMove, anchor, receiverControl, monitorState⟩
  dsimp only at hmove
  cases hmove
  simp only at hsync
  cases hsync
  cases anchor <;> rfl

/-- One local round simultaneously preserves the selected table move and the
equality of the two copies of its shared controller control. -/
theorem finiteCrossAnchorDescriptorFirstTwo_localRound_preserves
    (sender : FiniteCrossAnchorDescriptorFirstTwoSenderState monitor
      firstAllowed secondAllowed)
    (receiver : FiniteCrossAnchorDescriptorFirstTwoReceiverState monitor
      firstAllowed secondAllowed)
    (hmove : sender.1 = receiver.1)
    (hsync : HEq sender.2 receiver.2.2.1)
    (own : RIn) (delivered : SIn) :
    let senderNext :=
      (finiteCrossAnchorDescriptorFirstTwoSenderNoRecv monitor firstAllowed
        secondAllowed sender delivered).2
    let receiverNext :=
      (finiteCrossAnchorDescriptorFirstTwoReceiverRecv monitor firstAllowed
        secondAllowed receiver own delivered).2
    senderNext.1 = receiverNext.1 ∧
      HEq senderNext.2 receiverNext.2.2.1 := by
  dsimp only
  constructor
  · simpa only [finiteCrossAnchorDescriptorFirstTwoSenderNoRecv_move,
      finiteCrossAnchorDescriptorFirstTwoReceiverRecv_move] using hmove
  · exact finiteCrossAnchorDescriptorFirstTwo_step_controls_eq monitor
      firstAllowed secondAllowed sender receiver hmove hsync own delivered

end

end

end DistributedSynthesis
