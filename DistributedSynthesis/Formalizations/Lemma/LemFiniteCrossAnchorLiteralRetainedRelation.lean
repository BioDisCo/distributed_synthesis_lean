/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteCrossAnchorLiteralRestartRelation

/-!
# The exact retained one-step relation of a literal cross table

`LemFiniteCrossAnchorLiteralRestartRelation` identifies the obstruction met by
the old switch construction: continuing the receiver after the first letter
while restarting the sender asks for the generally false equation
`sender [] = sender [first]`.

The local carrier does not have to restart.  Its sender and receiver share one
preselected finite controller, so both controls may be advanced through the
first letter and retained.  The two-record guard then gives the complete
second semantic record with no extra hypothesis.  This is the reusable
positive counterpart of the restart audit.
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
/-- At installation, the two local endpoints already expose the complete
first literal record of the one preselected table.  This is stated for the
pair (rather than only for the receiver projection) because the switch seam
later consumes the blind coordinate as well. -/
theorem finiteCrossAnchorLiteralPrefix_initial_outputs_eq_first
    (baseDescriptor : Bool → Descriptor)
    (start : ∀ anchor, (monitor (baseDescriptor anchor)).State)
    (receiver : Bool → ReceiverBlockStrategy RIn SIn ROut)
    (sender : SenderBlockStrategy SIn SOut)
    (hwin : ∀ anchor env,
      ((monitor (baseDescriptor anchor)).restartAt (start anchor)).WinsPlay
        (pairPlay (receiver anchor) sender env))
    (anchor : Bool) (first : RIn × SIn) :
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
    ((finiteCrossAnchorDescriptorFirstTwoReceiverRecv
        (LiteralMonitor monitor) (LiteralFirstAllowed monitor)
        (LiteralSecondAllowed monitor) receiverRoot first.1 first.2).1,
      (finiteCrossAnchorDescriptorFirstTwoSenderNoRecv
        (LiteralMonitor monitor) (LiteralFirstAllowed monitor)
        (LiteralSecondAllowed monitor) senderRoot first.2).1) =
      (receiver anchor [] first, sender [] first.2) := by
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
  have hallowed :=
    move.memberController_records_allowed (LiteralMonitor monitor) anchor first
      default
  have hfirst : finiteCrossAnchorLiteralFirstAllowed (receiver anchor) sender
      firstRecord = true := by
    simpa [move, guard, controller, firstRecord,
      LiteralMonitor, LiteralFirstAllowed, LiteralSecondAllowed,
      finiteCrossAnchorLiteralPrefixMove] using hallowed.1
  have hfirstRecord : firstRecord =
      (first, receiver anchor [] first, sender [] first.2) := by
    exact of_decide_eq_true hfirst
  apply Prod.ext
  · change firstRecord.2.1 = _
    rw [hfirstRecord]
  · change firstRecord.2.2 = _
    rw [hfirstRecord]

omit [Fintype Descriptor] in
/-- Advance both copies of the shared controller through the first input.
The following local round is exactly the second record of the semantic play.
Unlike a sender restart, this requires no semantic equality premise. -/
theorem finiteCrossAnchorLiteralPrefix_retained_outputs_eq_second
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
    let senderAfterFirst :=
      (finiteCrossAnchorDescriptorFirstTwoSenderNoRecv
        (LiteralMonitor monitor) (LiteralFirstAllowed monitor)
        (LiteralSecondAllowed monitor) senderRoot first.2).2
    let receiverAfterFirst :=
      (finiteCrossAnchorDescriptorFirstTwoReceiverRecv
        (LiteralMonitor monitor) (LiteralFirstAllowed monitor)
        (LiteralSecondAllowed monitor) receiverRoot first.1 first.2).2
    ((finiteCrossAnchorDescriptorFirstTwoReceiverRecv
        (LiteralMonitor monitor) (LiteralFirstAllowed monitor)
        (LiteralSecondAllowed monitor) receiverAfterFirst second.1 second.2).1,
      (finiteCrossAnchorDescriptorFirstTwoSenderNoRecv
        (LiteralMonitor monitor) (LiteralFirstAllowed monitor)
        (LiteralSecondAllowed monitor) senderAfterFirst second.2).1) =
      (receiver anchor [first] second, sender [first.2] second.2) := by
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
      (second, receiver anchor [first] second,
        sender [first.2] second.2) := by
    simpa [finiteCrossAnchorLiteralSecondAllowed, firstRecord] using
      (of_decide_eq_true hsecond)
  apply Prod.ext
  · change secondRecord.2.1 = _
    rw [hsecondRecord]
  · change secondRecord.2.2 = _
    rw [hsecondRecord]

end

end DistributedSynthesis
