/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteCrossAnchorPairTable

/-!
# A local carrier for a preselected cross-anchor table

`FiniteCrossAnchorFirstTwoTable` performs the mathematically important step:
two different semantic anchors are narrowed before their hidden Boolean is
selected.  This file exposes the resulting table as two ordinary finite local
states.

The blind sender stores only the shared table control.  The informed receiver
stores that same control, its private Boolean member, and that member's
monitor state.  A right-block step uses only the sender's own input and the
receiver's own input plus the delivered sender input.  In particular no map
below accepts a graph, orientation, leader, strict-leader, or semantic-history
argument.
-/

namespace DistributedSynthesis

universe u v x y w d

noncomputable section

variable {RIn : Type u} {SIn : Type v} {ROut : Type x} {SOut : Type y}
variable [Inhabited RIn] [Inhabited SIn] [Inhabited ROut]
variable [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut]
variable [DecidableEq RIn] [DecidableEq SIn]

variable
  (base : Bool → BlockRecordMonitor.{u, v, x, y, w}
    RIn SIn ROut SOut)
  (start : ∀ anchor, (base anchor).State)
  (firstAllowed : ∀ anchor,
    RealizedBlockRound RIn SIn ROut SOut → Bool)
  (secondAllowed : ∀ anchor,
    RealizedBlockRound RIn SIn ROut SOut →
      RealizedBlockRound RIn SIn ROut SOut → Bool)

private abbrev Guard (anchor : Bool) :=
  finiteCrossAnchorFirstTwoGuardFamily base start firstAllowed secondAllowed
    anchor

variable
  (table : FiniteCrossAnchorFirstTwoTable base start firstAllowed
    secondAllowed)

/-- The control type is shared definitionally by the two member projections.
The Boolean flag inside this product is the root-selection phase of
`finiteRootMemberController`, not the hidden semantic member. -/
abbrev FiniteCrossAnchorSharedControl :=
  (table.memberController false).Control

noncomputable instance finiteCrossAnchorSharedControlFintype :
    Fintype
      (FiniteCrossAnchorSharedControl base start firstAllowed secondAllowed
        table) :=
  inferInstance

/-- The blind endpoint carries no hidden member tag. -/
abbrev FiniteCrossAnchorSenderState :=
  FiniteCrossAnchorSharedControl base start firstAllowed secondAllowed table

/-- The receiving endpoint knows which semantic anchor is active and threads
only that member's monitor state. -/
abbrev FiniteCrossAnchorReceiverState :=
  Σ anchor : Bool,
    FiniteCrossAnchorSharedControl base start firstAllowed secondAllowed table ×
      (Guard base start firstAllowed secondAllowed anchor).State

noncomputable instance finiteCrossAnchorReceiverStateFintype :
    Fintype
      (FiniteCrossAnchorReceiverState base start firstAllowed secondAllowed
        table) := by
  classical
  infer_instance

/-- Shared initial sender control. -/
def finiteCrossAnchorSenderInitial :
    FiniteCrossAnchorSenderState base start firstAllowed secondAllowed table :=
  (table.memberController false).initial

/-- Member-specific receiver initialization.  The table control is still the
same shared control for both members. -/
def finiteCrossAnchorReceiverInitial (anchor : Bool) :
    FiniteCrossAnchorReceiverState base start firstAllowed secondAllowed
      table :=
  ⟨anchor, (table.memberController anchor).initial,
    (Guard base start firstAllowed secondAllowed anchor).initial⟩

/-- One graph-blind non-receive of the blind sender. -/
def finiteCrossAnchorSenderNoRecv
    (control :
      FiniteCrossAnchorSenderState base start firstAllowed secondAllowed table)
    (input : SIn) :
    SOut ×
      FiniteCrossAnchorSenderState base start firstAllowed secondAllowed table :=
  let controller := table.memberController false
  ((controller.labelOf control).1 input, controller.step control input)

/-- One receive of the informed endpoint.  Its current member is a component
of its own local state; it is not supplied by the current graph. -/
def finiteCrossAnchorReceiverRecv
    (state :
      FiniteCrossAnchorReceiverState base start firstAllowed secondAllowed
        table)
    (own : RIn) (delivered : SIn) :
    ROut ×
      FiniteCrossAnchorReceiverState base start firstAllowed secondAllowed
        table :=
  let anchor := state.1
  let controller := table.memberController anchor
  let guard := Guard base start firstAllowed secondAllowed anchor
  let control := state.2.1
  let monitorState := state.2.2
  let move := (own, delivered)
  let label := controller.labelOf control
  let output := label.2 monitorState move
  let record := narrowedRecord guard label monitorState move
  (output,
    ⟨anchor, controller.step control delivered,
      guard.step monitorState record⟩)

section
omit [Inhabited RIn] [Inhabited SIn] [Inhabited ROut]

/-- Even at an arbitrary finite table control, both receiver projections have
the same blind sender response table. -/
theorem FiniteCrossAnchorFirstTwoTable.memberController_sender_label_eq
    (left right : Bool)
    (control :
      FiniteCrossAnchorSharedControl base start firstAllowed secondAllowed
        table) :
    ((table.memberController left).labelOf control).1 =
      ((table.memberController right).labelOf control).1 :=
  rfl

/-- The executable sender output may be read through either hidden member. -/
theorem finiteCrossAnchorSenderNoRecv_output_eq_member
    (control :
      FiniteCrossAnchorSenderState base start firstAllowed secondAllowed table)
    (input : SIn) (anchor : Bool) :
    (finiteCrossAnchorSenderNoRecv base start firstAllowed secondAllowed table
        control input).1 =
      ((table.memberController anchor).labelOf control).1 input := by
  cases anchor <;> rfl

/-- Both member projections also advance the same shared finite table
control. -/
theorem FiniteCrossAnchorFirstTwoTable.memberController_step_eq
    (left right : Bool)
    (control :
      FiniteCrossAnchorSharedControl base start firstAllowed secondAllowed
        table)
    (input : SIn) :
    (table.memberController left).step control input =
      (table.memberController right).step control input :=
  rfl

@[simp] theorem finiteCrossAnchorReceiverInitial_anchor (anchor : Bool) :
    (finiteCrossAnchorReceiverInitial base start firstAllowed secondAllowed
      table anchor).1 = anchor :=
  rfl

@[simp] theorem finiteCrossAnchorReceiverRecv_anchor
    (state :
      FiniteCrossAnchorReceiverState base start firstAllowed secondAllowed
        table)
    (own : RIn) (delivered : SIn) :
    (finiteCrossAnchorReceiverRecv base start firstAllowed secondAllowed table
      state own delivered).2.1 = state.1 :=
  rfl

/-- Initially the two endpoints carry the same shared controller control. -/
theorem finiteCrossAnchor_initial_controls_eq (anchor : Bool) :
    finiteCrossAnchorSenderInitial base start firstAllowed secondAllowed table =
      (finiteCrossAnchorReceiverInitial base start firstAllowed secondAllowed
        table anchor).2.1 := by
  cases anchor <;> rfl

/-- A physical block step preserves equality of the two copies of the shared
controller control. -/
theorem finiteCrossAnchor_step_controls_eq
    (sender :
      FiniteCrossAnchorSenderState base start firstAllowed secondAllowed table)
    (receiver :
      FiniteCrossAnchorReceiverState base start firstAllowed secondAllowed
        table)
    (hsync : sender = receiver.2.1)
    (own : RIn) (delivered : SIn) :
    (finiteCrossAnchorSenderNoRecv base start firstAllowed secondAllowed table
        sender delivered).2 =
      (finiteCrossAnchorReceiverRecv base start firstAllowed secondAllowed table
        receiver own delivered).2.2.1 := by
  subst sender
  cases receiver with
  | mk anchor payload =>
      rcases payload with ⟨control, monitorState⟩
      cases anchor <;> rfl

/-- The receiver transition emits exactly the receiver coordinate of the
member's narrowed record. -/
theorem finiteCrossAnchorReceiverRecv_output
    (state :
      FiniteCrossAnchorReceiverState base start firstAllowed secondAllowed
        table)
    (own : RIn) (delivered : SIn) :
    (finiteCrossAnchorReceiverRecv base start firstAllowed secondAllowed table
        state own delivered).1 =
      ((table.memberController state.1).labelOf state.2.1).2 state.2.2
        (own, delivered) :=
  rfl

end

/-! ## Descriptor-indexed unguarded carrier

The post-resolve installation uses a target-safety monitor directly, without
an additional first-two-record guard.  The following carrier keeps the
preselected descriptor move and advances the already selected member's
monitor state through the whole blind prefix. -/

section DescriptorCarrier

variable {Descriptor : Type d} [Fintype Descriptor]
variable (monitor : Descriptor →
  BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut)

private noncomputable abbrev DescriptorRestart
    (move : FiniteCrossAnchorDescriptorMove monitor) (anchor : Bool) :=
  (monitor (move.1.descriptor anchor)).restartAt (move.1.start anchor)

/-- Fixed finite sender state: one preselected move and its shared blind
table control.  The resolved member is absent. -/
noncomputable abbrev FiniteCrossAnchorDescriptorSenderState :=
  FiniteCrossAnchorDescriptorSenderControl monitor

noncomputable instance finiteCrossAnchorDescriptorSenderStateFintype :
    Fintype (FiniteCrossAnchorDescriptorSenderState monitor) := by
  classical
  infer_instance

/-- Fixed finite receiver state.  The informed endpoint stores the resolved
member and that member's current monitor state; it does not store a semantic
history or occurrence. -/
noncomputable abbrev FiniteCrossAnchorDescriptorReceiverState :=
  Sigma fun move : FiniteCrossAnchorDescriptorMove monitor =>
    Sigma fun anchor : Bool =>
      (move.memberController monitor false).Control ×
        (DescriptorRestart monitor move anchor).State

noncomputable instance finiteCrossAnchorDescriptorReceiverStateFintype :
    Fintype (FiniteCrossAnchorDescriptorReceiverState monitor) := by
  classical
  infer_instance

noncomputable def finiteCrossAnchorDescriptorReceiverInitial
    (move : FiniteCrossAnchorDescriptorMove monitor) (anchor : Bool) :
    FiniteCrossAnchorDescriptorReceiverState monitor :=
  ⟨move, anchor, (move.memberController monitor anchor).initial,
    (DescriptorRestart monitor move anchor).initial⟩

/-- One informed receive step.  The stored monitor state is advanced, rather
than being restarted when the member is read. -/
noncomputable def finiteCrossAnchorDescriptorReceiverRecv
    (state : FiniteCrossAnchorDescriptorReceiverState monitor)
    (own : RIn) (delivered : SIn) :
    ROut × FiniteCrossAnchorDescriptorReceiverState monitor :=
  let move := state.1
  let anchor := state.2.1
  let controller := move.memberController monitor anchor
  let restarted := DescriptorRestart monitor move anchor
  let control := state.2.2.1
  let monitorState := state.2.2.2
  let input := (own, delivered)
  let label := controller.labelOf control
  let output := label.2 monitorState input
  let record := narrowedRecord restarted label monitorState input
  (output,
    ⟨move, anchor, controller.step control delivered,
      restarted.step monitorState record⟩)

section
omit [Inhabited RIn] [Inhabited SIn] [Inhabited ROut] [Fintype Descriptor]

@[simp] theorem finiteCrossAnchorDescriptorReceiverRecv_move
    (state : FiniteCrossAnchorDescriptorReceiverState monitor)
    (own : RIn) (delivered : SIn) :
    (finiteCrossAnchorDescriptorReceiverRecv monitor state own delivered).2.1 =
      state.1 :=
  rfl

@[simp] theorem finiteCrossAnchorDescriptorReceiverRecv_anchor
    (state : FiniteCrossAnchorDescriptorReceiverState monitor)
    (own : RIn) (delivered : SIn) :
    (finiteCrossAnchorDescriptorReceiverRecv monitor state own delivered
      ).2.2.1 = state.2.1 :=
  rfl

/-- The two endpoint copies begin at the same finite table control. -/
theorem finiteCrossAnchorDescriptor_initial_controls_eq
    (move : FiniteCrossAnchorDescriptorMove monitor) (anchor : Bool) :
    (finiteCrossAnchorDescriptorSenderInitial monitor move).2 =
      (finiteCrossAnchorDescriptorReceiverInitial monitor move anchor).2.2.1 := by
  cases anchor <;> rfl

/-- Every blind step preserves equality of the two stored table controls.
This is the local, no-restart form of arbitrary-prefix closure. -/
theorem finiteCrossAnchorDescriptor_step_controls_eq
    (sender : FiniteCrossAnchorDescriptorSenderState monitor)
    (receiver : FiniteCrossAnchorDescriptorReceiverState monitor)
    (hmove : sender.1 = receiver.1)
    (hcontrol : HEq sender.2 receiver.2.2.1)
    (own : RIn) (delivered : SIn) :
    HEq (finiteCrossAnchorDescriptorSenderStep monitor sender delivered).2.2
      (finiteCrossAnchorDescriptorReceiverRecv monitor receiver own delivered
        ).2.2.2.1 := by
  cases sender with
  | mk senderMove senderControl =>
      cases receiver with
      | mk receiverMove receiverPayload =>
          cases receiverPayload with
          | mk anchor receiverState =>
              cases hmove
              cases hcontrol
              cases anchor <;> rfl

/-- The informed transition returns exactly the receiver coordinate selected
by the stored member and current monitor state. -/
theorem finiteCrossAnchorDescriptorReceiverRecv_output
    (state : FiniteCrossAnchorDescriptorReceiverState monitor)
    (own : RIn) (delivered : SIn) :
    (finiteCrossAnchorDescriptorReceiverRecv monitor state own delivered).1 =
      ((state.1.memberController monitor state.2.1).labelOf state.2.2.1).2
        state.2.2.2 (own, delivered) :=
  rfl

end

end DescriptorCarrier

/-! ## Descriptor-indexed guarded carrier

The preceding carrier fixes one dependent pair of monitors.  A global finite
machine must also be able to store which pair was preselected.  The outer
sigma below does exactly that.  In particular, the sender state still has no
hidden member bit: it stores the finite guarded move and its one shared table
control. -/

section DescriptorFirstTwoCarrier

variable {Descriptor : Type d} [Fintype Descriptor]
variable (monitor : Descriptor →
  BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut)
variable
  (descriptorFirstAllowed :
    ∀ pair : FiniteCrossAnchorDescriptorPair monitor,
      ∀ anchor, RealizedBlockRound RIn SIn ROut SOut → Bool)
  (descriptorSecondAllowed :
    ∀ pair : FiniteCrossAnchorDescriptorPair monitor,
      ∀ anchor, RealizedBlockRound RIn SIn ROut SOut →
        RealizedBlockRound RIn SIn ROut SOut → Bool)

private noncomputable abbrev DescriptorGuard
    (move : FiniteCrossAnchorDescriptorFirstTwoMove monitor
      descriptorFirstAllowed descriptorSecondAllowed)
    (anchor : Bool) :=
  finiteCrossAnchorFirstTwoGuardFamily
    (fun member => monitor (move.1.descriptor member)) move.1.start
    (descriptorFirstAllowed move.1) (descriptorSecondAllowed move.1) anchor

/-- Fixed finite state type of the graph-blind endpoint, including the
preselected descriptor pair but excluding the hidden member. -/
noncomputable abbrev FiniteCrossAnchorDescriptorFirstTwoSenderState :=
  Sigma fun move : FiniteCrossAnchorDescriptorFirstTwoMove monitor
      descriptorFirstAllowed descriptorSecondAllowed =>
    (move.memberController monitor false).Control

noncomputable instance
    finiteCrossAnchorDescriptorFirstTwoSenderStateFintype :
    Fintype (FiniteCrossAnchorDescriptorFirstTwoSenderState monitor
      descriptorFirstAllowed descriptorSecondAllowed) := by
  classical
  infer_instance

/-- The receiving endpoint owns the resolved member bit and its matching
dependent monitor state. -/
noncomputable abbrev FiniteCrossAnchorDescriptorFirstTwoReceiverState :=
  Sigma fun move : FiniteCrossAnchorDescriptorFirstTwoMove monitor
      descriptorFirstAllowed descriptorSecondAllowed =>
    Sigma fun anchor : Bool =>
      (move.memberController monitor false).Control ×
        (DescriptorGuard monitor descriptorFirstAllowed descriptorSecondAllowed
          move anchor).State

noncomputable instance
    finiteCrossAnchorDescriptorFirstTwoReceiverStateFintype :
    Fintype (FiniteCrossAnchorDescriptorFirstTwoReceiverState monitor
      descriptorFirstAllowed descriptorSecondAllowed) := by
  classical
  infer_instance

/-- Install a preselected guarded move at its one shared sender root. -/
noncomputable def finiteCrossAnchorDescriptorFirstTwoSenderInitial
    (move : FiniteCrossAnchorDescriptorFirstTwoMove monitor
      descriptorFirstAllowed descriptorSecondAllowed) :
    FiniteCrossAnchorDescriptorFirstTwoSenderState monitor
      descriptorFirstAllowed descriptorSecondAllowed :=
  ⟨move, (move.memberController monitor false).initial⟩

/-- Install the matching member-specific receiver root. -/
noncomputable def finiteCrossAnchorDescriptorFirstTwoReceiverInitial
    (move : FiniteCrossAnchorDescriptorFirstTwoMove monitor
      descriptorFirstAllowed descriptorSecondAllowed)
    (anchor : Bool) :
    FiniteCrossAnchorDescriptorFirstTwoReceiverState monitor
      descriptorFirstAllowed descriptorSecondAllowed :=
  ⟨move, anchor, (move.memberController monitor anchor).initial,
    (DescriptorGuard monitor descriptorFirstAllowed descriptorSecondAllowed
      move anchor).initial⟩

/-- One graph-blind step of the descriptor-indexed sender. -/
noncomputable def finiteCrossAnchorDescriptorFirstTwoSenderNoRecv
    (state : FiniteCrossAnchorDescriptorFirstTwoSenderState monitor
      descriptorFirstAllowed descriptorSecondAllowed)
    (input : SIn) :
    SOut × FiniteCrossAnchorDescriptorFirstTwoSenderState monitor
      descriptorFirstAllowed descriptorSecondAllowed :=
  let controller := state.1.memberController monitor false
  ((controller.labelOf state.2).1 input,
    ⟨state.1, controller.step state.2 input⟩)

/-- One receive step of the descriptor-indexed informed endpoint. -/
noncomputable def finiteCrossAnchorDescriptorFirstTwoReceiverRecv
    (state : FiniteCrossAnchorDescriptorFirstTwoReceiverState monitor
      descriptorFirstAllowed descriptorSecondAllowed)
    (own : RIn) (delivered : SIn) :
    ROut × FiniteCrossAnchorDescriptorFirstTwoReceiverState monitor
      descriptorFirstAllowed descriptorSecondAllowed :=
  let move := state.1
  let anchor := state.2.1
  let controller := move.memberController monitor anchor
  let guard := DescriptorGuard monitor descriptorFirstAllowed
    descriptorSecondAllowed move anchor
  let control := state.2.2.1
  let monitorState := state.2.2.2
  let input := (own, delivered)
  let label := controller.labelOf control
  let output := label.2 monitorState input
  let record := narrowedRecord guard label monitorState input
  (output,
    ⟨move, anchor, controller.step control delivered,
      guard.step monitorState record⟩)

section
omit [Inhabited RIn] [Inhabited SIn] [Inhabited ROut] [Fintype Descriptor]

@[simp] theorem finiteCrossAnchorDescriptorFirstTwoSenderNoRecv_move
    (state : FiniteCrossAnchorDescriptorFirstTwoSenderState monitor
      descriptorFirstAllowed descriptorSecondAllowed)
    (input : SIn) :
    (finiteCrossAnchorDescriptorFirstTwoSenderNoRecv monitor
      descriptorFirstAllowed descriptorSecondAllowed state input).2.1 =
      state.1 :=
  rfl

@[simp] theorem finiteCrossAnchorDescriptorFirstTwoReceiverRecv_move
    (state : FiniteCrossAnchorDescriptorFirstTwoReceiverState monitor
      descriptorFirstAllowed descriptorSecondAllowed)
    (own : RIn) (delivered : SIn) :
    (finiteCrossAnchorDescriptorFirstTwoReceiverRecv monitor
      descriptorFirstAllowed descriptorSecondAllowed state own delivered
      ).2.1 = state.1 :=
  rfl

@[simp] theorem finiteCrossAnchorDescriptorFirstTwoReceiverRecv_anchor
    (state : FiniteCrossAnchorDescriptorFirstTwoReceiverState monitor
      descriptorFirstAllowed descriptorSecondAllowed)
    (own : RIn) (delivered : SIn) :
    (finiteCrossAnchorDescriptorFirstTwoReceiverRecv monitor
      descriptorFirstAllowed descriptorSecondAllowed state own delivered
      ).2.2.1 = state.2.1 :=
  rfl

/-- The executable blind output is the sender output of either descriptor
member, even though those members have different monitor types. -/
theorem finiteCrossAnchorDescriptorFirstTwoSenderNoRecv_output_eq_member
    (state : FiniteCrossAnchorDescriptorFirstTwoSenderState monitor
      descriptorFirstAllowed descriptorSecondAllowed)
    (input : SIn) (anchor : Bool) :
    (finiteCrossAnchorDescriptorFirstTwoSenderNoRecv monitor
      descriptorFirstAllowed descriptorSecondAllowed state input).1 =
      ((state.1.memberController monitor anchor).labelOf state.2).1 input := by
  cases anchor <;> rfl

/-- Both endpoints start with identical copies of the one shared table
control. -/
theorem finiteCrossAnchorDescriptorFirstTwo_initial_controls_eq
    (move : FiniteCrossAnchorDescriptorFirstTwoMove monitor
      descriptorFirstAllowed descriptorSecondAllowed)
    (anchor : Bool) :
    (finiteCrossAnchorDescriptorFirstTwoSenderInitial monitor
      descriptorFirstAllowed descriptorSecondAllowed move).2 =
      (finiteCrossAnchorDescriptorFirstTwoReceiverInitial monitor
        descriptorFirstAllowed descriptorSecondAllowed move anchor).2.2.1 := by
  cases anchor <;> rfl

/-- A physical block preserves synchronization of the two stored copies of
the shared table control. -/
theorem finiteCrossAnchorDescriptorFirstTwo_step_controls_eq
    (sender : FiniteCrossAnchorDescriptorFirstTwoSenderState monitor
      descriptorFirstAllowed descriptorSecondAllowed)
    (receiver : FiniteCrossAnchorDescriptorFirstTwoReceiverState monitor
      descriptorFirstAllowed descriptorSecondAllowed)
    (hmove : sender.1 = receiver.1)
    (hsync : HEq sender.2 receiver.2.2.1)
    (own : RIn) (delivered : SIn) :
    HEq
      (finiteCrossAnchorDescriptorFirstTwoSenderNoRecv monitor
        descriptorFirstAllowed descriptorSecondAllowed sender delivered).2.2
      (finiteCrossAnchorDescriptorFirstTwoReceiverRecv monitor
        descriptorFirstAllowed descriptorSecondAllowed receiver own delivered
        ).2.2.2.1 := by
  rcases sender with ⟨senderMove, senderControl⟩
  rcases receiver with ⟨receiverMove, anchor, receiverControl, monitorState⟩
  dsimp only at hmove
  cases hmove
  simp only at hsync
  cases hsync
  cases anchor <;> rfl

end

end DescriptorFirstTwoCarrier

end

end DistributedSynthesis
