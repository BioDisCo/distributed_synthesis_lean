/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteCrossAnchorLocalCarrierRound
import DistributedSynthesis.Formalizations.Lemma.LemFiniteCrossAnchorPairTableSuffix
import DistributedSynthesis.Formalizations.Theorem.ThmPairedEntryControllerSoundness

/-!
# Root reachability of the local cross-anchor carrier

The local sender and receiver maps execute the narrowed table literally.
This file packages the missing prefix witness: synchronized states reached
from a table root are exactly `controlAt` and `narrowedControl` at one common
physical input prefix.  The witness is proof-side only and is never stored by
either executable endpoint.
-/

namespace DistributedSynthesis

universe u v x y w d

noncomputable section

variable {RIn : Type u} {SIn : Type v} {ROut : Type x} {SOut : Type y}
variable [Inhabited RIn] [Inhabited SIn] [Inhabited ROut]
variable [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut]
variable [DecidableEq RIn] [DecidableEq SIn]

variable
  {base : Bool → BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut}
  {start : ∀ anchor, (base anchor).State}
  {firstAllowed : ∀ anchor,
    RealizedBlockRound RIn SIn ROut SOut → Bool}
  {secondAllowed : ∀ anchor,
    RealizedBlockRound RIn SIn ROut SOut →
      RealizedBlockRound RIn SIn ROut SOut → Bool}
  (table : FiniteCrossAnchorFirstTwoTable base start firstAllowed secondAllowed)

private noncomputable abbrev LocalGuard
    (_table : FiniteCrossAnchorFirstTwoTable base start firstAllowed
      secondAllowed) (anchor : Bool) :=
  finiteCrossAnchorFirstTwoGuardFamily base start firstAllowed secondAllowed
    anchor

/-- Shared sender control after one concrete full-input prefix. -/
noncomputable def finiteCrossAnchorSenderAtPrefix
    (past : List (RIn × SIn)) :
    FiniteCrossAnchorSenderState base start firstAllowed secondAllowed table :=
  (table.memberController false).controlAt (senderWord past)

/-- Member-threaded receiver state after the same full-input prefix. -/
noncomputable def finiteCrossAnchorReceiverAtPrefix
    (anchor : Bool) (past : List (RIn × SIn)) :
    FiniteCrossAnchorReceiverState base start firstAllowed secondAllowed table :=
  let guard := LocalGuard table anchor
  let controller := table.memberController anchor
  ⟨anchor, controller.controlAt (senderWord past),
    narrowedControl guard controller.labeledTree past⟩

section
omit [Inhabited RIn] [Inhabited SIn] [Inhabited ROut]

@[simp] theorem finiteCrossAnchorSenderAtPrefix_nil :
    finiteCrossAnchorSenderAtPrefix table [] =
      finiteCrossAnchorSenderInitial base start firstAllowed secondAllowed
        table := by
  rfl

@[simp] theorem finiteCrossAnchorReceiverAtPrefix_nil (anchor : Bool) :
    finiteCrossAnchorReceiverAtPrefix table anchor [] =
      finiteCrossAnchorReceiverInitial base start firstAllowed secondAllowed
        table anchor := by
  rfl

/-- The graph-blind sender step advances the canonical prefix control. -/
theorem finiteCrossAnchorSenderNoRecv_atPrefix
    (past : List (RIn × SIn)) (input : RIn × SIn) :
    (finiteCrossAnchorSenderNoRecv base start firstAllowed secondAllowed table
      (finiteCrossAnchorSenderAtPrefix table past) input.2).2 =
        finiteCrossAnchorSenderAtPrefix table (past ++ [input]) := by
  rw [finiteCrossAnchorSenderAtPrefix, finiteCrossAnchorSenderAtPrefix,
    senderWord_append, TransitionRationalTree.controlAt_append]
  rfl

/-- The member-threaded receiver step advances `controlAt` and
`narrowedControl` at the same prefix. -/
theorem finiteCrossAnchorReceiverRecv_atPrefix
    (anchor : Bool) (past : List (RIn × SIn)) (input : RIn × SIn) :
    (finiteCrossAnchorReceiverRecv base start firstAllowed secondAllowed table
      (finiteCrossAnchorReceiverAtPrefix table anchor past) input.1 input.2
      ).2 =
        finiteCrossAnchorReceiverAtPrefix table anchor (past ++ [input]) := by
  let guard := LocalGuard table anchor
  let controller := table.memberController anchor
  change
    (⟨anchor,
      controller.step (controller.controlAt (senderWord past)) input.2,
      guard.step (narrowedControl guard controller.labeledTree past)
        (narrowedRecord guard
          (controller.labelOf (controller.controlAt (senderWord past)))
          (narrowedControl guard controller.labeledTree past) input)⟩ :
      FiniteCrossAnchorReceiverState base start firstAllowed secondAllowed
        table) =
      ⟨anchor, controller.controlAt (senderWord (past ++ [input])),
        narrowedControl guard controller.labeledTree (past ++ [input])⟩
  rw [senderWord_append, TransitionRationalTree.controlAt_append,
    narrowedControl_append]
  rfl

/-- The two local outputs at a canonical prefix are exactly the next narrowed
table record. -/
theorem finiteCrossAnchor_localRound_atPrefix
    (anchor : Bool) (past : List (RIn × SIn)) (input : RIn × SIn) :
    let guard := LocalGuard table anchor
    let controller := table.memberController anchor
    let sender := finiteCrossAnchorSenderAtPrefix table past
    let receiver := finiteCrossAnchorReceiverAtPrefix table anchor past
    let senderStep := finiteCrossAnchorSenderNoRecv base start firstAllowed
      secondAllowed table sender input.2
    let receiverStep := finiteCrossAnchorReceiverRecv base start firstAllowed
      secondAllowed table receiver input.1 input.2
    (input, receiverStep.1, senderStep.1) =
      narrowedRecord guard
        (controller.labelOf (controller.controlAt (senderWord past)))
        (narrowedControl guard controller.labeledTree past) input := by
  cases anchor <;> rfl

end

omit [Inhabited RIn] [Inhabited SIn] [Inhabited ROut] in
/-- Prefix-local form of the tree-play equation for an arbitrary omega
completion.  Only its finite prefix and current input are relevant. -/
theorem finiteCrossAnchor_localRound_atPrefix_eq_treePlay
    (anchor : Bool) (past : List (RIn × SIn)) (input : RIn × SIn)
    (env : Nat → RIn × SIn)
    (hpast : DetParityAutomaton.omegaPrefix env past.length = past)
    (hinput : env past.length = input) :
    let guard := finiteCrossAnchorFirstTwoGuardFamily base start firstAllowed
      secondAllowed anchor
    let controller := table.memberController anchor
    let sender := finiteCrossAnchorSenderAtPrefix table past
    let receiver := finiteCrossAnchorReceiverAtPrefix table anchor past
    let senderStep := finiteCrossAnchorSenderNoRecv base start firstAllowed
      secondAllowed table sender input.2
    let receiverStep := finiteCrossAnchorReceiverRecv base start firstAllowed
      secondAllowed table receiver input.1 input.2
    (input, receiverStep.1, senderStep.1) =
      treePlay (narrowedInducedTree guard controller.labeledTree) env
        past.length := by
  dsimp only
  rw [finiteCrossAnchor_localRound_atPrefix table anchor past input]
  simp [treePlay, narrowedInducedTree, blockLabelApply, narrowedRecord,
    TransitionRationalTree.labeledTree,
    DetParityAutomaton.branchNode_eq_omegaPrefix, hpast, hinput]

/-- Proof-side reachability relation for synchronized endpoint states. -/
def FiniteCrossAnchorLocallyReachable
    (sender : FiniteCrossAnchorSenderState base start firstAllowed secondAllowed
      table)
    (receiver : FiniteCrossAnchorReceiverState base start firstAllowed
      secondAllowed table) : Prop :=
  ∃ past : List (RIn × SIn),
    sender = finiteCrossAnchorSenderAtPrefix table past ∧
      receiver = finiteCrossAnchorReceiverAtPrefix table receiver.1 past

section
omit [Inhabited RIn] [Inhabited SIn] [Inhabited ROut]

/-- Every member-specific pair of roots is locally reachable. -/
theorem finiteCrossAnchorLocallyReachable_initial (anchor : Bool) :
    FiniteCrossAnchorLocallyReachable table
      (finiteCrossAnchorSenderInitial base start firstAllowed secondAllowed
        table)
      (finiteCrossAnchorReceiverInitial base start firstAllowed secondAllowed
        table anchor) := by
  refine ⟨[], ?_, ?_⟩
  · rfl
  · rfl

/-- One synchronized local round extends the common prefix witness. -/
theorem FiniteCrossAnchorLocallyReachable.step
    {sender : FiniteCrossAnchorSenderState base start firstAllowed secondAllowed
      table}
    {receiver : FiniteCrossAnchorReceiverState base start firstAllowed
      secondAllowed table}
    (hreach : FiniteCrossAnchorLocallyReachable table sender receiver)
    (input : RIn × SIn) :
    FiniteCrossAnchorLocallyReachable table
      (finiteCrossAnchorSenderNoRecv base start firstAllowed secondAllowed table
        sender input.2).2
      (finiteCrossAnchorReceiverRecv base start firstAllowed secondAllowed table
        receiver input.1 input.2).2 := by
  rcases hreach with ⟨past, rfl, hreceiver⟩
  have hanchor :
      (finiteCrossAnchorReceiverAtPrefix table receiver.1 past).1 =
        receiver.1 := by
    rfl
  rw [hreceiver]
  refine ⟨past ++ [input], ?_, ?_⟩
  · exact finiteCrossAnchorSenderNoRecv_atPrefix table past input
  · rw [finiteCrossAnchorReceiverRecv_atPrefix]
    rfl

/-- A reachable local round is an actual record of the selected member's
narrowed table at its witnessed prefix. -/
theorem FiniteCrossAnchorLocallyReachable.exists_localRound_eq
    {sender : FiniteCrossAnchorSenderState base start firstAllowed secondAllowed
      table}
    {receiver : FiniteCrossAnchorReceiverState base start firstAllowed
      secondAllowed table}
    (hreach : FiniteCrossAnchorLocallyReachable table sender receiver)
    (input : RIn × SIn) :
    ∃ past : List (RIn × SIn),
      sender = finiteCrossAnchorSenderAtPrefix table past ∧
      receiver = finiteCrossAnchorReceiverAtPrefix table receiver.1 past ∧
      let guard := LocalGuard table receiver.1
      let controller := table.memberController receiver.1
      let senderStep := finiteCrossAnchorSenderNoRecv base start firstAllowed
        secondAllowed table sender input.2
      let receiverStep := finiteCrossAnchorReceiverRecv base start firstAllowed
        secondAllowed table receiver input.1 input.2
      (input, receiverStep.1, senderStep.1) =
        narrowedRecord guard
          (controller.labelOf (controller.controlAt (senderWord past)))
          (narrowedControl guard controller.labeledTree past) input := by
  rcases hreach with ⟨past, hsender, hreceiver⟩
  refine ⟨past, hsender, hreceiver, ?_⟩
  subst sender
  rw [hreceiver]
  exact finiteCrossAnchor_localRound_atPrefix table receiver.1 past input

end

omit [Inhabited ROut] in
/-- The reachable local round is literally the member controller's
`treePlay` at the witnessed prefix.  `omegaOfList` only completes the finite
prefix to an omega environment; the equality uses no property of that
completion after the current round. -/
theorem FiniteCrossAnchorLocallyReachable.exists_localRound_eq_treePlay
    {sender : FiniteCrossAnchorSenderState base start firstAllowed secondAllowed
      table}
    {receiver : FiniteCrossAnchorReceiverState base start firstAllowed
      secondAllowed table}
    (hreach : FiniteCrossAnchorLocallyReachable table sender receiver)
    (input : RIn × SIn) :
    ∃ past : List (RIn × SIn),
      sender = finiteCrossAnchorSenderAtPrefix table past ∧
      receiver = finiteCrossAnchorReceiverAtPrefix table receiver.1 past ∧
      let guard := finiteCrossAnchorFirstTwoGuardFamily base start firstAllowed
        secondAllowed receiver.1
      let controller := table.memberController receiver.1
      let env : Nat → RIn × SIn :=
        DetParityAutomaton.omegaOfList (past ++ [input])
      let senderStep := finiteCrossAnchorSenderNoRecv base start firstAllowed
        secondAllowed table sender input.2
      let receiverStep := finiteCrossAnchorReceiverRecv base start firstAllowed
        secondAllowed table receiver input.1 input.2
      (input, receiverStep.1, senderStep.1) =
        treePlay (narrowedInducedTree guard controller.labeledTree) env
          past.length := by
  rcases hreach with ⟨past, hsender, hreceiver⟩
  rcases receiver with ⟨anchor, control, monitorState⟩
  dsimp only at hreceiver ⊢
  refine ⟨past, hsender, hreceiver, ?_⟩
  subst sender
  rw [hreceiver]
  let guard := finiteCrossAnchorFirstTwoGuardFamily base start firstAllowed
    secondAllowed anchor
  let controller := table.memberController anchor
  let env : Nat → RIn × SIn :=
    DetParityAutomaton.omegaOfList (past ++ [input])
  have hpast : DetParityAutomaton.omegaPrefix env past.length = past := by
    apply List.ext_get
    · simp [DetParityAutomaton.omegaPrefix]
    · intro n hnLeft hnRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [DetParityAutomaton.omegaPrefix, List.getElem_ofFn]
      have hnPrefix : n < (past ++ [input]).length := by simp; omega
      change DetParityAutomaton.omegaOfList (past ++ [input]) n = past[n]
      rw [DetParityAutomaton.omegaOfList_eq_getElem
        (past ++ [input]) n hnPrefix]
      simp [hnRight]
  have hinput : env past.length = input := by
    have hnPrefix : past.length < (past ++ [input]).length := by simp
    change DetParityAutomaton.omegaOfList (past ++ [input]) past.length = input
    rw [DetParityAutomaton.omegaOfList_eq_getElem
      (past ++ [input]) past.length hnPrefix]
    simp
  rw [finiteCrossAnchor_localRound_atPrefix table anchor past input]
  simp [treePlay, narrowedInducedTree, blockLabelApply, narrowedRecord,
    TransitionRationalTree.labeledTree,
    DetParityAutomaton.branchNode_eq_omegaPrefix,
    hpast, hinput, env, guard, controller]

omit [Inhabited ROut] in
/-- A reachable local round comes with both sides of the semantic handoff:
the concrete endpoint output is the selected member's current tree-play
letter, and the base monitor restarted at that exact cut wins the remaining
member-play suffix.  The completion `omegaOfList` is proof-side only. -/
theorem FiniteCrossAnchorLocallyReachable.exists_localRound_eq_treePlay_and_base_wins_suffix
    {sender : FiniteCrossAnchorSenderState base start firstAllowed secondAllowed
      table}
    {receiver : FiniteCrossAnchorReceiverState base start firstAllowed
      secondAllowed table}
    (hreach : FiniteCrossAnchorLocallyReachable table sender receiver)
    (input : RIn × SIn) :
    ∃ past : List (RIn × SIn),
      sender = finiteCrossAnchorSenderAtPrefix table past ∧
      receiver = finiteCrossAnchorReceiverAtPrefix table receiver.1 past ∧
      let anchor := receiver.1
      let guard := finiteCrossAnchorFirstTwoGuardFamily base start firstAllowed
        secondAllowed anchor
      let controller := table.memberController anchor
      let env : Nat → RIn × SIn :=
        DetParityAutomaton.omegaOfList (past ++ [input])
      let play := treePlay
        (narrowedInducedTree guard controller.labeledTree) env
      let restarted := finiteCrossAnchorRestartFamily base start anchor
      let senderStep := finiteCrossAnchorSenderNoRecv base start firstAllowed
        secondAllowed table sender input.2
      let receiverStep := finiteCrossAnchorReceiverRecv base start firstAllowed
        secondAllowed table receiver input.1 input.2
      (input, receiverStep.1, senderStep.1) = play past.length ∧
        (restarted.restartAt (restarted.run play past.length)).WinsPlay
          (fun k ↦ play (past.length + k)) := by
  rcases hreach.exists_localRound_eq_treePlay table input with
    ⟨past, hsender, hreceiver, hround⟩
  refine ⟨past, hsender, hreceiver, hround, ?_⟩
  exact table.memberController_base_wins_suffix receiver.1
    (DetParityAutomaton.omegaOfList (past ++ [input])) past.length

/-! ## Unguarded descriptor-carrier reachability

The post-resolve carrier has already discharged its finite prefix guard.  Its
receiver therefore runs the selected descriptor monitor directly.  The
following is the unguarded analogue of the preceding reachability interface.
-/

section DescriptorCarrier

variable {Descriptor : Type d} [Fintype Descriptor]
variable (monitor : Descriptor →
  BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut)

private noncomputable abbrev DescriptorRestartAt
    (move : FiniteCrossAnchorDescriptorMove monitor) (anchor : Bool) :=
  (monitor (move.1.descriptor anchor)).restartAt (move.1.start anchor)

/-- Canonical blind-sender state after a concrete full-input prefix. -/
noncomputable def finiteCrossAnchorDescriptorSenderAtPrefix
    (move : FiniteCrossAnchorDescriptorMove monitor)
    (past : List (RIn × SIn)) :
    FiniteCrossAnchorDescriptorSenderState monitor :=
  ⟨move, (move.memberController monitor false).controlAt (senderWord past)⟩

/-- Canonical member-threaded receiver state after the same prefix. -/
noncomputable def finiteCrossAnchorDescriptorReceiverAtPrefix
    (move : FiniteCrossAnchorDescriptorMove monitor) (anchor : Bool)
    (past : List (RIn × SIn)) :
    FiniteCrossAnchorDescriptorReceiverState monitor :=
  let restarted := DescriptorRestartAt monitor move anchor
  let controller := move.memberController monitor anchor
  ⟨move, anchor, controller.controlAt (senderWord past),
    narrowedControl restarted controller.labeledTree past⟩

section
omit [Inhabited RIn] [Inhabited SIn] [Inhabited ROut] [Fintype Descriptor]

@[simp] theorem finiteCrossAnchorDescriptorSenderAtPrefix_nil
    (move : FiniteCrossAnchorDescriptorMove monitor) :
    finiteCrossAnchorDescriptorSenderAtPrefix monitor move [] =
      finiteCrossAnchorDescriptorSenderInitial monitor move :=
  rfl

@[simp] theorem finiteCrossAnchorDescriptorReceiverAtPrefix_nil
    (move : FiniteCrossAnchorDescriptorMove monitor) (anchor : Bool) :
    finiteCrossAnchorDescriptorReceiverAtPrefix monitor move anchor [] =
      finiteCrossAnchorDescriptorReceiverInitial monitor move anchor := by
  cases anchor <;> rfl

/-- The local sender map advances the canonical prefix state. -/
theorem finiteCrossAnchorDescriptorSenderStep_atPrefix
    (move : FiniteCrossAnchorDescriptorMove monitor)
    (past : List (RIn × SIn)) (input : RIn × SIn) :
    (finiteCrossAnchorDescriptorSenderStep monitor
      (finiteCrossAnchorDescriptorSenderAtPrefix monitor move past) input.2
      ).2 =
        finiteCrossAnchorDescriptorSenderAtPrefix monitor move
          (past ++ [input]) := by
  rw [finiteCrossAnchorDescriptorSenderAtPrefix,
    finiteCrossAnchorDescriptorSenderAtPrefix, senderWord_append,
    TransitionRationalTree.controlAt_append]
  rfl

/-- The informed map advances both `controlAt` and the narrowed monitor
state at that same prefix. -/
theorem finiteCrossAnchorDescriptorReceiverRecv_atPrefix
    (move : FiniteCrossAnchorDescriptorMove monitor) (anchor : Bool)
    (past : List (RIn × SIn)) (input : RIn × SIn) :
    (finiteCrossAnchorDescriptorReceiverRecv monitor
      (finiteCrossAnchorDescriptorReceiverAtPrefix monitor move anchor past)
      input.1 input.2).2 =
        finiteCrossAnchorDescriptorReceiverAtPrefix monitor move anchor
          (past ++ [input]) := by
  let restarted := DescriptorRestartAt monitor move anchor
  let controller := move.memberController monitor anchor
  change
    (⟨move, anchor,
      controller.step (controller.controlAt (senderWord past)) input.2,
      restarted.step
        (narrowedControl restarted controller.labeledTree past)
        (narrowedRecord restarted
          (controller.labelOf (controller.controlAt (senderWord past)))
          (narrowedControl restarted controller.labeledTree past) input)⟩ :
      FiniteCrossAnchorDescriptorReceiverState monitor) =
      ⟨move, anchor,
        controller.controlAt (senderWord (past ++ [input])),
        narrowedControl restarted controller.labeledTree
          (past ++ [input])⟩
  rw [senderWord_append, TransitionRationalTree.controlAt_append,
    narrowedControl_append]
  rfl

/-- At a canonical prefix the two endpoint outputs form exactly the next
narrowed record of the stored member. -/
theorem finiteCrossAnchorDescriptor_localRound_atPrefix
    (move : FiniteCrossAnchorDescriptorMove monitor) (anchor : Bool)
    (past : List (RIn × SIn)) (input : RIn × SIn) :
    let restarted := DescriptorRestartAt monitor move anchor
    let controller := move.memberController monitor anchor
    let sender :=
      finiteCrossAnchorDescriptorSenderAtPrefix monitor move past
    let receiver :=
      finiteCrossAnchorDescriptorReceiverAtPrefix monitor move anchor past
    let senderStep := finiteCrossAnchorDescriptorSenderStep monitor sender
      input.2
    let receiverStep := finiteCrossAnchorDescriptorReceiverRecv monitor
      receiver input.1 input.2
    (input, receiverStep.1, senderStep.1) =
      narrowedRecord restarted
        (controller.labelOf (controller.controlAt (senderWord past)))
        (narrowedControl restarted controller.labeledTree past) input := by
  cases anchor <;> rfl

end

omit [Inhabited RIn] [Inhabited SIn] [Inhabited ROut] [Fintype Descriptor] in
/-- Prefix-local equality with the member's actual `treePlay`. -/
theorem finiteCrossAnchorDescriptor_localRound_atPrefix_eq_treePlay
    (move : FiniteCrossAnchorDescriptorMove monitor) (anchor : Bool)
    (past : List (RIn × SIn)) (input : RIn × SIn)
    (env : Nat → RIn × SIn)
    (hpast : DetParityAutomaton.omegaPrefix env past.length = past)
    (hinput : env past.length = input) :
    let restarted := DescriptorRestartAt monitor move anchor
    let controller := move.memberController monitor anchor
    let sender :=
      finiteCrossAnchorDescriptorSenderAtPrefix monitor move past
    let receiver :=
      finiteCrossAnchorDescriptorReceiverAtPrefix monitor move anchor past
    let senderStep := finiteCrossAnchorDescriptorSenderStep monitor sender
      input.2
    let receiverStep := finiteCrossAnchorDescriptorReceiverRecv monitor
      receiver input.1 input.2
    (input, receiverStep.1, senderStep.1) =
      treePlay (narrowedInducedTree restarted controller.labeledTree) env
        past.length := by
  dsimp only
  rw [finiteCrossAnchorDescriptor_localRound_atPrefix monitor move anchor past
    input]
  simp [treePlay, narrowedInducedTree, blockLabelApply, narrowedRecord,
    TransitionRationalTree.labeledTree,
    DetParityAutomaton.branchNode_eq_omegaPrefix, hpast, hinput]

/-- Proof-side reachability of a synchronized unguarded endpoint pair. -/
def FiniteCrossAnchorDescriptorLocallyReachable
    (sender : FiniteCrossAnchorDescriptorSenderState monitor)
    (receiver : FiniteCrossAnchorDescriptorReceiverState monitor) : Prop :=
  ∃ past : List (RIn × SIn),
    sender = finiteCrossAnchorDescriptorSenderAtPrefix monitor receiver.1 past ∧
      receiver = finiteCrossAnchorDescriptorReceiverAtPrefix monitor receiver.1
        receiver.2.1 past

omit [Inhabited RIn] [Inhabited SIn] [Inhabited ROut] [Fintype Descriptor] in
/-- Every installed member root is locally reachable. -/
theorem finiteCrossAnchorDescriptorLocallyReachable_initial
    (move : FiniteCrossAnchorDescriptorMove monitor) (anchor : Bool) :
    FiniteCrossAnchorDescriptorLocallyReachable monitor
      (finiteCrossAnchorDescriptorSenderInitial monitor move)
      (finiteCrossAnchorDescriptorReceiverInitial monitor move anchor) := by
  refine ⟨[], ?_, ?_⟩
  · rfl
  · cases anchor <;> rfl

omit [Inhabited RIn] [Inhabited SIn] [Inhabited ROut] [Fintype Descriptor] in
/-- One local round extends the common prefix witness. -/
theorem FiniteCrossAnchorDescriptorLocallyReachable.step
    {sender : FiniteCrossAnchorDescriptorSenderState monitor}
    {receiver : FiniteCrossAnchorDescriptorReceiverState monitor}
    (hreach : FiniteCrossAnchorDescriptorLocallyReachable monitor sender
      receiver) (input : RIn × SIn) :
    FiniteCrossAnchorDescriptorLocallyReachable monitor
      (finiteCrossAnchorDescriptorSenderStep monitor sender input.2).2
      (finiteCrossAnchorDescriptorReceiverRecv monitor receiver input.1
        input.2).2 := by
  rcases hreach with ⟨past, hsender, hreceiver⟩
  rcases receiver with ⟨move, anchor, control, monitorState⟩
  dsimp only at hsender hreceiver ⊢
  subst sender
  rw [hreceiver]
  refine ⟨past ++ [input], ?_, ?_⟩
  · exact finiteCrossAnchorDescriptorSenderStep_atPrefix monitor move past
      input
  · rw [finiteCrossAnchorDescriptorReceiverRecv_atPrefix]
    rfl

section
omit [Inhabited ROut] [Fintype Descriptor]

/-- A reachable local round is the selected member's tree-play letter at the
witnessed prefix. -/
theorem
    FiniteCrossAnchorDescriptorLocallyReachable.exists_localRound_eq_treePlay
    {sender : FiniteCrossAnchorDescriptorSenderState monitor}
    {receiver : FiniteCrossAnchorDescriptorReceiverState monitor}
    (hreach : FiniteCrossAnchorDescriptorLocallyReachable monitor sender
      receiver) (input : RIn × SIn) :
    ∃ past : List (RIn × SIn),
      sender = finiteCrossAnchorDescriptorSenderAtPrefix monitor receiver.1
        past ∧
      receiver = finiteCrossAnchorDescriptorReceiverAtPrefix monitor receiver.1
        receiver.2.1 past ∧
      let move := receiver.1
      let anchor := receiver.2.1
      let restarted := DescriptorRestartAt monitor move anchor
      let controller := move.memberController monitor anchor
      let env : Nat → RIn × SIn :=
        DetParityAutomaton.omegaOfList (past ++ [input])
      let senderStep := finiteCrossAnchorDescriptorSenderStep monitor sender
        input.2
      let receiverStep := finiteCrossAnchorDescriptorReceiverRecv monitor
        receiver input.1 input.2
      (input, receiverStep.1, senderStep.1) =
        treePlay (narrowedInducedTree restarted controller.labeledTree) env
          past.length := by
  rcases hreach with ⟨past, hsender, hreceiver⟩
  rcases receiver with ⟨move, anchor, control, monitorState⟩
  dsimp only at hsender hreceiver ⊢
  refine ⟨past, hsender, hreceiver, ?_⟩
  subst sender
  rw [hreceiver]
  let env : Nat → RIn × SIn :=
    DetParityAutomaton.omegaOfList (past ++ [input])
  have hpast : DetParityAutomaton.omegaPrefix env past.length = past := by
    apply List.ext_get
    · simp [DetParityAutomaton.omegaPrefix]
    · intro n hnLeft hnRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [DetParityAutomaton.omegaPrefix, List.getElem_ofFn]
      have hnPrefix : n < (past ++ [input]).length := by simp; omega
      change DetParityAutomaton.omegaOfList (past ++ [input]) n = past[n]
      rw [DetParityAutomaton.omegaOfList_eq_getElem
        (past ++ [input]) n hnPrefix]
      simp [hnRight]
  have hinput : env past.length = input := by
    have hnPrefix : past.length < (past ++ [input]).length := by simp
    change DetParityAutomaton.omegaOfList (past ++ [input]) past.length = input
    rw [DetParityAutomaton.omegaOfList_eq_getElem
      (past ++ [input]) past.length hnPrefix]
    simp
  exact finiteCrossAnchorDescriptor_localRound_atPrefix_eq_treePlay monitor
    move anchor past input env hpast hinput

/-- The monitor component stored by a reachable receiver is exactly the
selected member monitor run through the witnessed full-input prefix.  The
extra current input is used only to make `omegaOfList` expose that prefix. -/
theorem
    FiniteCrossAnchorDescriptorLocallyReachable.exists_monitorRun_eq_state
    {sender : FiniteCrossAnchorDescriptorSenderState monitor}
    {receiver : FiniteCrossAnchorDescriptorReceiverState monitor}
    (hreach : FiniteCrossAnchorDescriptorLocallyReachable monitor sender
      receiver) (input : RIn × SIn) :
    ∃ past : List (RIn × SIn),
      let move := receiver.1
      let anchor := receiver.2.1
      let restarted := DescriptorRestartAt monitor move anchor
      let controller := move.memberController monitor anchor
      let env : Nat → RIn × SIn :=
        DetParityAutomaton.omegaOfList (past ++ [input])
      let play := treePlay
        (narrowedInducedTree restarted controller.labeledTree) env
      restarted.run play past.length = receiver.2.2.2 := by
  rcases receiver with ⟨move, anchor, control, monitorState⟩
  rcases hreach with ⟨past, hsender, hreceiver⟩
  dsimp only at hreceiver ⊢
  cases hreceiver
  refine ⟨past, ?_⟩
  let restarted := DescriptorRestartAt monitor move anchor
  let controller := move.memberController monitor anchor
  let env : Nat → RIn × SIn :=
    DetParityAutomaton.omegaOfList (past ++ [input])
  let play := treePlay
    (narrowedInducedTree restarted controller.labeledTree) env
  have hpast : DetParityAutomaton.omegaPrefix env past.length = past := by
    apply List.ext_get
    · simp [DetParityAutomaton.omegaPrefix]
    · intro n hnLeft hnRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [DetParityAutomaton.omegaPrefix, List.getElem_ofFn]
      have hnPrefix : n < (past ++ [input]).length := by simp; omega
      change DetParityAutomaton.omegaOfList (past ++ [input]) n = past[n]
      rw [DetParityAutomaton.omegaOfList_eq_getElem
        (past ++ [input]) n hnPrefix]
      simp [hnRight]
  change restarted.run play past.length =
    narrowedControl restarted controller.labeledTree past
  rw [← restarted.lift_control_branchNode
    (narrowedInducedTree restarted controller.labeledTree) env,
    lift_control_narrowedInducedTree,
    DetParityAutomaton.branchNode_eq_omegaPrefix, hpast]

/-- Joint form of the two preceding readbacks.  Both equalities use the same
prefix witness, which is essential when a closing target certificate mentions
both the emitted letter and the monitor state before that letter. -/
theorem FiniteCrossAnchorDescriptorLocallyReachable.exists_localRound_and_monitorRun
    {sender : FiniteCrossAnchorDescriptorSenderState monitor}
    {receiver : FiniteCrossAnchorDescriptorReceiverState monitor}
    (hreach : FiniteCrossAnchorDescriptorLocallyReachable monitor sender
      receiver) (input : RIn × SIn) :
    ∃ past : List (RIn × SIn),
      let move := receiver.1
      let anchor := receiver.2.1
      let restarted := DescriptorRestartAt monitor move anchor
      let controller := move.memberController monitor anchor
      let env : Nat → RIn × SIn :=
        DetParityAutomaton.omegaOfList (past ++ [input])
      let play := treePlay
        (narrowedInducedTree restarted controller.labeledTree) env
      let senderStep := finiteCrossAnchorDescriptorSenderStep monitor sender
        input.2
      let receiverStep := finiteCrossAnchorDescriptorReceiverRecv monitor
        receiver input.1 input.2
      (input, receiverStep.1, senderStep.1) = play past.length ∧
        restarted.run play past.length = receiver.2.2.2 := by
  rcases receiver with ⟨move, anchor, control, monitorState⟩
  rcases hreach with ⟨past, hsender, hreceiver⟩
  dsimp only at hsender hreceiver ⊢
  cases hreceiver
  subst sender
  refine ⟨past, ?_, ?_⟩
  · let env : Nat → RIn × SIn :=
      DetParityAutomaton.omegaOfList (past ++ [input])
    have hpast : DetParityAutomaton.omegaPrefix env past.length = past := by
      apply List.ext_get
      · simp [DetParityAutomaton.omegaPrefix]
      · intro n hnLeft hnRight
        rw [List.get_eq_getElem, List.get_eq_getElem]
        simp only [DetParityAutomaton.omegaPrefix, List.getElem_ofFn]
        have hnPrefix : n < (past ++ [input]).length := by simp; omega
        change DetParityAutomaton.omegaOfList (past ++ [input]) n = past[n]
        rw [DetParityAutomaton.omegaOfList_eq_getElem
          (past ++ [input]) n hnPrefix]
        simp [hnRight]
    have hinput : env past.length = input := by
      have hnPrefix : past.length < (past ++ [input]).length := by simp
      change DetParityAutomaton.omegaOfList (past ++ [input]) past.length = input
      rw [DetParityAutomaton.omegaOfList_eq_getElem
        (past ++ [input]) past.length hnPrefix]
      simp
    exact finiteCrossAnchorDescriptor_localRound_atPrefix_eq_treePlay monitor
      move anchor past input env hpast hinput
  · let restarted := DescriptorRestartAt monitor move anchor
    let controller := move.memberController monitor anchor
    let env : Nat → RIn × SIn :=
      DetParityAutomaton.omegaOfList (past ++ [input])
    let play := treePlay
      (narrowedInducedTree restarted controller.labeledTree) env
    have hpast : DetParityAutomaton.omegaPrefix env past.length = past := by
      apply List.ext_get
      · simp [DetParityAutomaton.omegaPrefix]
      · intro n hnLeft hnRight
        rw [List.get_eq_getElem, List.get_eq_getElem]
        simp only [DetParityAutomaton.omegaPrefix, List.getElem_ofFn]
        have hnPrefix : n < (past ++ [input]).length := by simp; omega
        change DetParityAutomaton.omegaOfList (past ++ [input]) n = past[n]
        rw [DetParityAutomaton.omegaOfList_eq_getElem
          (past ++ [input]) n hnPrefix]
        simp [hnRight]
    change restarted.run play past.length =
      narrowedControl restarted controller.labeledTree past
    rw [← restarted.lift_control_branchNode
      (narrowedInducedTree restarted controller.labeledTree) env,
      lift_control_narrowedInducedTree,
      DetParityAutomaton.branchNode_eq_omegaPrefix, hpast]

end

end DescriptorCarrier

end

end DistributedSynthesis
