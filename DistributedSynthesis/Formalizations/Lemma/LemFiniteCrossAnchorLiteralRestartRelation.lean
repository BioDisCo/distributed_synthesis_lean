/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteCrossAnchorLiteralPrefixDescriptor
import DistributedSynthesis.Formalizations.Lemma.LemFiniteCrossAnchorLocalCarrierRound

/-!
# The exact one-step restart relation of a literal cross table

After an unresolved simultaneous receive, one endpoint can continue the
receiver control of a literal table while its partner restarts the blind
sender control.  The two-record truth tables determine this mixed physical
round exactly:

* the continued receiver coordinate is the literal receiver after the first
  input;
* the restarted blind coordinate is the literal sender at the empty suffix.

Thus the remaining anti-mosaic obligation is one explicit local-view
equality between the sender at the empty suffix and after the one-letter
suffix.  This equality is semantic; it does not follow from the generic
first-two table interface alone.
-/

namespace DistributedSynthesis

universe u v x y w d

noncomputable section

variable {RIn : Type u} {SIn : Type v} {ROut : Type x} {SOut : Type y}
variable [Inhabited RIn] [Inhabited SIn] [Inhabited ROut]
variable [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut]
variable [DecidableEq RIn] [DecidableEq SIn]
variable {Descriptor : Type d} [Fintype Descriptor]

variable (monitor : Descriptor →
  BlockRecordMonitor.{u, v, x, y, max u v x y d}
    RIn SIn ROut SOut)

private noncomputable abbrev LiteralMonitor :=
  finiteCrossAnchorLiteralPrefixMonitor monitor

private abbrev LiteralFirstAllowed :=
  finiteCrossAnchorLiteralPrefixFirstAllowed monitor

private abbrev LiteralSecondAllowed :=
  finiteCrossAnchorLiteralPrefixSecondAllowed monitor

omit [Fintype Descriptor] in
/-- The strongest mixed-round equation supplied by the generic literal
prefix construction.  Notice the deliberately different sender histories
on the two coordinates: the actual restarted sender uses `[]`, whereas the
continued receiver uses the first input as its one-letter past. -/
theorem finiteCrossAnchorLiteralPrefix_restart_mixed_outputs
    (baseDescriptor : Bool → Descriptor)
    (start : ∀ anchor, (monitor (baseDescriptor anchor)).State)
    (receiver : Bool → ReceiverBlockStrategy RIn SIn ROut)
    (sender : SenderBlockStrategy SIn SOut)
    (hwin : ∀ anchor env,
      ((monitor (baseDescriptor anchor)).restartAt (start anchor)).WinsPlay
        (pairPlay (receiver anchor) sender env))
    (anchor : Bool) (first second : RIn × SIn) :
    let move := finiteCrossAnchorLiteralPrefixMove monitor baseDescriptor start
      receiver sender hwin
    let senderRoot :=
      finiteCrossAnchorDescriptorFirstTwoSenderInitial
        (LiteralMonitor monitor) (LiteralFirstAllowed monitor)
        (LiteralSecondAllowed monitor) move
    let receiverRoot :=
      finiteCrossAnchorDescriptorFirstTwoReceiverInitial
        (LiteralMonitor monitor) (LiteralFirstAllowed monitor)
        (LiteralSecondAllowed monitor) move anchor
    let receiverAfterFirst :=
      (finiteCrossAnchorDescriptorFirstTwoReceiverRecv
        (LiteralMonitor monitor) (LiteralFirstAllowed monitor)
        (LiteralSecondAllowed monitor) receiverRoot first.1 first.2).2
    ((finiteCrossAnchorDescriptorFirstTwoReceiverRecv
        (LiteralMonitor monitor) (LiteralFirstAllowed monitor)
        (LiteralSecondAllowed monitor) receiverAfterFirst second.1 second.2).1,
      (finiteCrossAnchorDescriptorFirstTwoSenderNoRecv
        (LiteralMonitor monitor) (LiteralFirstAllowed monitor)
        (LiteralSecondAllowed monitor) senderRoot second.2).1) =
      (receiver anchor [first] second, sender [] second.2) := by
  classical
  let move := finiteCrossAnchorLiteralPrefixMove monitor baseDescriptor start
    receiver sender hwin
  let guard := finiteCrossAnchorFirstTwoGuardFamily
    (fun member ↦ LiteralMonitor monitor (move.1.descriptor member))
    move.1.start (LiteralFirstAllowed monitor move.1)
    (LiteralSecondAllowed monitor move.1) anchor
  let controller := move.memberController (LiteralMonitor monitor) anchor
  let firstRecord := narrowedRecord guard (controller.labeledTree [])
    guard.initial first
  let secondRecord := narrowedRecord guard
    (controller.labeledTree [first.2]) (guard.step guard.initial firstRecord)
    second
  have hallowed :=
    move.memberController_records_allowed (LiteralMonitor monitor) anchor first
      second
  have hsecond : finiteCrossAnchorLiteralSecondAllowed (receiver anchor) sender
      firstRecord secondRecord = true := by
    simpa [move, guard, controller, firstRecord, secondRecord,
      LiteralMonitor, LiteralFirstAllowed, LiteralSecondAllowed,
      finiteCrossAnchorLiteralPrefixMove] using hallowed.2
  have hsecondRecord : secondRecord =
      (second, receiver anchor [first] second, sender [first.2] second.2) := by
    simpa [finiteCrossAnchorLiteralSecondAllowed, firstRecord] using
      (of_decide_eq_true hsecond)
  let rootRecord := narrowedRecord guard (controller.labeledTree [])
    guard.initial second
  have hrootAllowed :=
    move.memberController_records_allowed (LiteralMonitor monitor) anchor
      second first
  have hroot : finiteCrossAnchorLiteralFirstAllowed (receiver anchor) sender
      rootRecord = true := by
    simpa [move, guard, controller, rootRecord,
      LiteralMonitor, LiteralFirstAllowed, LiteralSecondAllowed,
      finiteCrossAnchorLiteralPrefixMove] using hrootAllowed.1
  have hrootRecord : rootRecord =
      (second, receiver anchor [] second, sender [] second.2) := by
    exact of_decide_eq_true hroot
  apply Prod.ext
  · change secondRecord.2.1 = _
    rw [hsecondRecord]
  · change rootRecord.2.2 = _
    rw [hrootRecord]

omit [Fintype Descriptor] in
/-- Once the one remaining sender-history equality is supplied, the mixed
restart round is literally the second record of the semantic block. -/
theorem finiteCrossAnchorLiteralPrefix_restart_mixed_outputs_eq_second
    (baseDescriptor : Bool → Descriptor)
    (start : ∀ anchor, (monitor (baseDescriptor anchor)).State)
    (receiver : Bool → ReceiverBlockStrategy RIn SIn ROut)
    (sender : SenderBlockStrategy SIn SOut)
    (hwin : ∀ anchor env,
      ((monitor (baseDescriptor anchor)).restartAt (start anchor)).WinsPlay
        (pairPlay (receiver anchor) sender env))
    (anchor : Bool) (first second : RIn × SIn)
    (hsender : sender [] second.2 = sender [first.2] second.2) :
    let move := finiteCrossAnchorLiteralPrefixMove monitor baseDescriptor start
      receiver sender hwin
    let senderRoot :=
      finiteCrossAnchorDescriptorFirstTwoSenderInitial
        (LiteralMonitor monitor) (LiteralFirstAllowed monitor)
        (LiteralSecondAllowed monitor) move
    let receiverRoot :=
      finiteCrossAnchorDescriptorFirstTwoReceiverInitial
        (LiteralMonitor monitor) (LiteralFirstAllowed monitor)
        (LiteralSecondAllowed monitor) move anchor
    let receiverAfterFirst :=
      (finiteCrossAnchorDescriptorFirstTwoReceiverRecv
        (LiteralMonitor monitor) (LiteralFirstAllowed monitor)
        (LiteralSecondAllowed monitor) receiverRoot first.1 first.2).2
    ((finiteCrossAnchorDescriptorFirstTwoReceiverRecv
        (LiteralMonitor monitor) (LiteralFirstAllowed monitor)
        (LiteralSecondAllowed monitor) receiverAfterFirst second.1 second.2).1,
      (finiteCrossAnchorDescriptorFirstTwoSenderNoRecv
        (LiteralMonitor monitor) (LiteralFirstAllowed monitor)
        (LiteralSecondAllowed monitor) senderRoot second.2).1) =
      (receiver anchor [first] second, sender [first.2] second.2) := by
  have hmixed := finiteCrossAnchorLiteralPrefix_restart_mixed_outputs monitor
    baseDescriptor start receiver sender hwin anchor first second
  simpa only [hsender] using hmixed

end

end DistributedSynthesis
