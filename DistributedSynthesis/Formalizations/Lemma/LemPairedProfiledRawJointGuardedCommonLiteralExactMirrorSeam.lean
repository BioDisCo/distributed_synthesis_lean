/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralExactTailHandoff

/-!
# Exact mirror seam at a literal left/`both` ambiguity

This is the process-one/process-two mirror of the exact heterogeneous seam.
The uniform literal right block and the exact root-pinned right block are
rationalized once, before the hidden interpretation is selected.  Their two
proof-side projections therefore have one literal sender transition table.

The exact projection is also read back into the ordinary left-policy bank
after its checked first block.  No executable transition receives the hidden
Boolean, a graph, an orientation, or a leader bit.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

private abbrev MirrorFalseReceiverOutput :=
  ProfiledRawJointTargetRightReceiverOutput
    (Out₁ := Out₁) (Out₂ := Out₂) (ProfiledRawJointUnitTarget A)

private noncomputable abbrev MirrorFalseMonitor
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :=
  profiledRawJointRightPhysicalSiblingMonitor A
    (profiledRawJointHybridExactRightUniformDescriptor A strategy hwin
      installed) false

private noncomputable abbrev MirrorFalseActivation
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :=
  profiledRawJointHybridExactRightUniformActivation A strategy hwin installed

private noncomputable def literalLeftBothMirrorFalseReceiver
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    ReceiverBlockStrategy In₂ In₁
      (MirrorFalseReceiverOutput A (Out₁ := Out₁) (Out₂ := Out₂)) :=
  profiledRawJointTargetRightReceiverStrategy A
    (MirrorFalseActivation A strategy hwin installed)

private noncomputable def literalLeftBothMirrorFalseSender
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    SenderBlockStrategy In₁ Out₁ :=
  pairedRightSenderStrategy
    (MirrorFalseActivation A strategy hwin installed).lambda

private noncomputable def literalLeftBothMirrorFalseFirstAllowed
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :=
  finiteCrossAnchorLiteralFirstAllowed
    (literalLeftBothMirrorFalseReceiver A strategy hwin installed)
    (literalLeftBothMirrorFalseSender A strategy hwin installed)

private noncomputable def literalLeftBothMirrorFalseSecondAllowed
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :=
  finiteCrossAnchorLiteralSecondAllowed
    (literalLeftBothMirrorFalseReceiver A strategy hwin installed)
    (literalLeftBothMirrorFalseSender A strategy hwin installed)

/-! ## Exact root-pinned member -/

noncomputable abbrev ProfiledRawJointLiteralExactRightPackage
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :=
  profiledRawJointHybridExactRightPolicy A hwin installed

abbrev ProfiledRawJointLiteralExactRightReceiverOutput
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :=
  ProfiledRawJointGuardedFirstRightReceiverOutput A strategy
    (installed.world.oneSidedState A .right)
    (profiledRawJointHybridExactRightRootPredicate A installed)
    (ProfiledRawJointLiteralExactRightPackage A strategy hwin installed)

private noncomputable instance
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    Inhabited (ProfiledRawJointLiteralExactRightReceiverOutput A strategy hwin
      installed) :=
  ⟨{
    physical := default
    target := fun row ↦
      profiledRawJointGuardedFirstRightTarget A strategy
        (installed.world.oneSidedState A .right)
        (profiledRawJointHybridExactRightRootPredicate A installed)
        (ProfiledRawJointLiteralExactRightPackage A strategy hwin installed)
        row [] default }⟩

private noncomputable instance :
    Inhabited (ProfiledRawJointUnitTarget A) :=
  ⟨{
    family := {
      right := fun _ ↦ none
      left := fun _ ↦ none
      rightPattern := fun _ _ ↦ false
      leftPattern := fun _ _ ↦ false }
    cross := fun _ _ ↦ false }⟩

private noncomputable abbrev MirrorExactMonitor
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :=
  profiledRawJointHybridExactRightMonitor A installed
    (ProfiledRawJointLiteralExactRightPackage A strategy hwin installed)

private noncomputable def literalLeftBothMirrorExactReceiver
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    ReceiverBlockStrategy In₂ In₁
      (ProfiledRawJointLiteralExactRightReceiverOutput A strategy hwin
        installed) :=
  profiledRawJointGuardedFirstRightReceiverStrategy A
    (profiledRawJointHybridExactRightActivation A hwin installed)

private noncomputable def literalLeftBothMirrorExactSender
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    SenderBlockStrategy In₁ Out₁ :=
  pairedRightSenderStrategy
    (profiledRawJointHybridExactRightActivation A hwin installed).lambda

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
theorem literalLeftBothMirror_uniformSender_eq_exactSender
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    literalLeftBothMirrorFalseSender A strategy hwin installed =
      literalLeftBothMirrorExactSender A strategy hwin installed := by
  rfl

private noncomputable def literalLeftBothMirrorExactFirstAllowed
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :=
  finiteCrossAnchorLiteralFirstAllowed
    (literalLeftBothMirrorExactReceiver A strategy hwin installed)
    (literalLeftBothMirrorExactSender A strategy hwin installed)

private noncomputable def literalLeftBothMirrorExactSecondAllowed
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :=
  finiteCrossAnchorLiteralSecondAllowed
    (literalLeftBothMirrorExactReceiver A strategy hwin installed)
    (literalLeftBothMirrorExactSender A strategy hwin installed)

/-! Short names for the dependent ingredients of the public mirror-table
carrier. -/

private noncomputable abbrev MirrorExactBase
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :=
  finiteCrossAnchorHeterogeneousMonitor
    (MirrorFalseMonitor A strategy hwin installed)
    (MirrorExactMonitor A strategy hwin installed)

private noncomputable abbrev MirrorExactStart
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :=
  finiteCrossAnchorHeterogeneousStart
    (MirrorFalseMonitor A strategy hwin installed)
    (MirrorExactMonitor A strategy hwin installed)
    (MirrorFalseMonitor A strategy hwin installed).initial
    (MirrorExactMonitor A strategy hwin installed).initial

private noncomputable abbrev MirrorExactFirstAllowed
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :=
  finiteCrossAnchorHeterogeneousFirstAllowed
    (literalLeftBothMirrorFalseFirstAllowed A strategy hwin installed)
    (literalLeftBothMirrorExactFirstAllowed A strategy hwin installed)

private noncomputable abbrev MirrorExactSecondAllowed
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :=
  finiteCrossAnchorHeterogeneousSecondAllowed
    (literalLeftBothMirrorFalseSecondAllowed A strategy hwin installed)
    (literalLeftBothMirrorExactSecondAllowed A strategy hwin installed)

/-- Public receiver alphabet of the code-erased mirror member. -/
abbrev ProfiledRawJointLiteralLeftBothExactFalseReceiverOutput :=
  ProfiledRawJointTargetRightReceiverOutput
    (Out₁ := Out₁) (Out₂ := Out₂) (ProfiledRawJointUnitTarget A)

/-- Product receiver alphabet stored by the shared mirror table. -/
abbrev ProfiledRawJointLiteralLeftBothExactProductReceiverOutput
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :=
  ProfiledRawJointLiteralLeftBothExactFalseReceiverOutput A ×
    ProfiledRawJointLiteralExactRightReceiverOutput A strategy hwin installed

/-- Unconditional mirror table for the literal left/`both` seam. -/
noncomputable def profiledRawJointLiteralLeftBothExactHeterogeneousRightTable
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    FiniteCrossAnchorFirstTwoTable
      (MirrorExactBase A strategy hwin installed)
      (MirrorExactStart A strategy hwin installed)
      (MirrorExactFirstAllowed A strategy hwin installed)
      (MirrorExactSecondAllowed A strategy hwin installed) := by
  let falseMonitor := MirrorFalseMonitor A strategy hwin installed
  let trueMonitor := MirrorExactMonitor A strategy hwin installed
  let falseReceiver := literalLeftBothMirrorFalseReceiver A strategy hwin
    installed
  let trueReceiver := literalLeftBothMirrorExactReceiver A strategy hwin
    installed
  let falseSender := literalLeftBothMirrorFalseSender A strategy hwin installed
  let trueSender := literalLeftBothMirrorExactSender A strategy hwin installed
  have hsender : falseSender = trueSender :=
    literalLeftBothMirror_uniformSender_eq_exactSender A strategy hwin
      installed
  apply finiteCrossAnchorHeterogeneousFirstTwoTable
    falseMonitor trueMonitor falseMonitor.initial trueMonitor.initial
    (literalLeftBothMirrorFalseFirstAllowed A strategy hwin installed)
    (literalLeftBothMirrorExactFirstAllowed A strategy hwin installed)
    (literalLeftBothMirrorFalseSecondAllowed A strategy hwin installed)
    (literalLeftBothMirrorExactSecondAllowed A strategy hwin installed)
    falseReceiver trueReceiver falseSender
  · intro env
    simpa [falseMonitor] using
      (profiledRawJointHybridExactRightUniformMonitor_realizable A strategy
        hwin installed env)
  · intro env
    rw [hsender]
    exact profiledRawJointHybridExactRightMonitor_realizable A installed
      (ProfiledRawJointLiteralExactRightPackage A strategy hwin installed)
      (profiledRawJointHybridExactRightActivation A hwin installed) env
  · intro env
    exact finiteCrossAnchorLiteralFirstAllowed_pairPlay falseReceiver
      falseSender env
  · intro env
    rw [hsender]
    exact finiteCrossAnchorLiteralFirstAllowed_pairPlay trueReceiver trueSender
      env
  · intro env
    exact finiteCrossAnchorLiteralSecondAllowed_pairPlay falseReceiver
      falseSender env
  · intro env
    rw [hsender]
    exact finiteCrossAnchorLiteralSecondAllowed_pairPlay trueReceiver trueSender
      env

/-! ## Public finite local carrier at one installed mirror occurrence -/

/-- Process-one blind-sender control of the mirror exact table.  It contains
no hidden member bit. -/
noncomputable abbrev ProfiledRawJointLiteralLeftBothExactSenderState
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :=
  FiniteCrossAnchorSenderState
    (MirrorExactBase A strategy hwin installed)
    (MirrorExactStart A strategy hwin installed)
    (MirrorExactFirstAllowed A strategy hwin installed)
    (MirrorExactSecondAllowed A strategy hwin installed)
    (profiledRawJointLiteralLeftBothExactHeterogeneousRightTable A strategy
      hwin installed)

/-- Process-two receiver control of the same mirror table. -/
noncomputable abbrev ProfiledRawJointLiteralLeftBothExactReceiverState
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :=
  FiniteCrossAnchorReceiverState
    (MirrorExactBase A strategy hwin installed)
    (MirrorExactStart A strategy hwin installed)
    (MirrorExactFirstAllowed A strategy hwin installed)
    (MirrorExactSecondAllowed A strategy hwin installed)
    (profiledRawJointLiteralLeftBothExactHeterogeneousRightTable A strategy
      hwin installed)

noncomputable instance
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    Fintype
      (ProfiledRawJointLiteralLeftBothExactSenderState A strategy hwin
        installed) := by
  infer_instance

noncomputable instance
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    Fintype
      (ProfiledRawJointLiteralLeftBothExactReceiverState A strategy hwin
        installed) := by
  classical
  infer_instance

/-- Shared process-one sender root. -/
noncomputable def profiledRawJointLiteralLeftBothExactSenderInitial
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    ProfiledRawJointLiteralLeftBothExactSenderState A strategy hwin installed :=
  finiteCrossAnchorSenderInitial
    (MirrorExactBase A strategy hwin installed)
    (MirrorExactStart A strategy hwin installed)
    (MirrorExactFirstAllowed A strategy hwin installed)
    (MirrorExactSecondAllowed A strategy hwin installed)
    (profiledRawJointLiteralLeftBothExactHeterogeneousRightTable A strategy
      hwin installed)

/-- Member-specific process-two receiver root. -/
noncomputable def profiledRawJointLiteralLeftBothExactReceiverInitial
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (anchor : Bool) :
    ProfiledRawJointLiteralLeftBothExactReceiverState A strategy hwin
      installed :=
  finiteCrossAnchorReceiverInitial
    (MirrorExactBase A strategy hwin installed)
    (MirrorExactStart A strategy hwin installed)
    (MirrorExactFirstAllowed A strategy hwin installed)
    (MirrorExactSecondAllowed A strategy hwin installed)
    (profiledRawJointLiteralLeftBothExactHeterogeneousRightTable A strategy
      hwin installed) anchor

/-- One arbitrary-depth graph-blind process-one sender step. -/
noncomputable def profiledRawJointLiteralLeftBothExactSenderNoRecv
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (state : ProfiledRawJointLiteralLeftBothExactSenderState A strategy hwin
      installed)
    (input : In₁) : Out₁ ×
      ProfiledRawJointLiteralLeftBothExactSenderState A strategy hwin
        installed :=
  finiteCrossAnchorSenderNoRecv
    (MirrorExactBase A strategy hwin installed)
    (MirrorExactStart A strategy hwin installed)
    (MirrorExactFirstAllowed A strategy hwin installed)
    (MirrorExactSecondAllowed A strategy hwin installed)
    (profiledRawJointLiteralLeftBothExactHeterogeneousRightTable A strategy
      hwin installed) state input

/-- One member-threaded process-two receiver step. -/
noncomputable def profiledRawJointLiteralLeftBothExactReceiverRecv
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (state : ProfiledRawJointLiteralLeftBothExactReceiverState A strategy hwin
      installed)
    (own : In₂) (delivered : In₁) :
    ProfiledRawJointLiteralLeftBothExactProductReceiverOutput A strategy hwin
        installed ×
      ProfiledRawJointLiteralLeftBothExactReceiverState A strategy hwin
        installed :=
  finiteCrossAnchorReceiverRecv
    (MirrorExactBase A strategy hwin installed)
    (MirrorExactStart A strategy hwin installed)
    (MirrorExactFirstAllowed A strategy hwin installed)
    (MirrorExactSecondAllowed A strategy hwin installed)
    (profiledRawJointLiteralLeftBothExactHeterogeneousRightTable A strategy
      hwin installed) state own delivered

@[simp] theorem profiledRawJointLiteralLeftBothExactReceiverInitial_anchor
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (anchor : Bool) :
    (profiledRawJointLiteralLeftBothExactReceiverInitial A strategy hwin
      installed anchor).1 = anchor :=
  rfl

/-- Both mirror endpoints initially store the same finite table control. -/
theorem profiledRawJointLiteralLeftBothExact_initial_controls_eq
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (anchor : Bool) :
    profiledRawJointLiteralLeftBothExactSenderInitial A strategy hwin
        installed =
      (profiledRawJointLiteralLeftBothExactReceiverInitial A strategy hwin
        installed anchor).2.1 := by
  exact finiteCrossAnchor_initial_controls_eq
    (MirrorExactBase A strategy hwin installed)
    (MirrorExactStart A strategy hwin installed)
    (MirrorExactFirstAllowed A strategy hwin installed)
    (MirrorExactSecondAllowed A strategy hwin installed)
    (profiledRawJointLiteralLeftBothExactHeterogeneousRightTable A strategy
      hwin installed) anchor

/-- The executable mirror sender output is the sender coordinate of either
proof-side member. -/
theorem profiledRawJointLiteralLeftBothExactSenderNoRecv_output_eq_member
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (state : ProfiledRawJointLiteralLeftBothExactSenderState A strategy hwin
      installed)
    (input : In₁) (anchor : Bool) :
    (profiledRawJointLiteralLeftBothExactSenderNoRecv A strategy hwin
      installed state input).1 =
      (((profiledRawJointLiteralLeftBothExactHeterogeneousRightTable A strategy
        hwin installed).memberController anchor).labelOf state).1 input := by
  exact finiteCrossAnchorSenderNoRecv_output_eq_member
    (MirrorExactBase A strategy hwin installed)
    (MirrorExactStart A strategy hwin installed)
    (MirrorExactFirstAllowed A strategy hwin installed)
    (MirrorExactSecondAllowed A strategy hwin installed)
    (profiledRawJointLiteralLeftBothExactHeterogeneousRightTable A strategy
      hwin installed) state input anchor

/-- Synchronized mirror sender/receiver controls remain synchronized after
one physical block letter. -/
theorem profiledRawJointLiteralLeftBothExact_step_controls_eq
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (sender : ProfiledRawJointLiteralLeftBothExactSenderState A strategy hwin
      installed)
    (receiver : ProfiledRawJointLiteralLeftBothExactReceiverState A strategy
      hwin installed)
    (hsync : sender = receiver.2.1)
    (own : In₂) (delivered : In₁) :
    (profiledRawJointLiteralLeftBothExactSenderNoRecv A strategy hwin
      installed sender delivered).2 =
      (profiledRawJointLiteralLeftBothExactReceiverRecv A strategy hwin
        installed receiver own delivered).2.2.1 := by
  exact finiteCrossAnchor_step_controls_eq
    (MirrorExactBase A strategy hwin installed)
    (MirrorExactStart A strategy hwin installed)
    (MirrorExactFirstAllowed A strategy hwin installed)
    (MirrorExactSecondAllowed A strategy hwin installed)
    (profiledRawJointLiteralLeftBothExactHeterogeneousRightTable A strategy
      hwin installed) sender receiver hsync own delivered

/-! ## The active false coordinate still carries the exact child code -/

/-- Although the false mirror-table member leaves the unused exact
`Prod.snd` coordinate unconstrained, its active target is the incidence code
of the root-pinned literal child at the same first physical record. -/
theorem profiledRawJointLiteralLeftBothExactReceiverFirst_false_target_code
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (row : PairedEntryRow) (input : In₂ × In₁) :
    (profiledRawJointLiteralLeftBothExactReceiverRecv A strategy hwin
      installed
      (profiledRawJointLiteralLeftBothExactReceiverInitial A strategy hwin
        installed false)
      input.1 input.2).1.1.target row =
      (profiledRawJointGuardedFirstRightTarget A strategy
        (installed.world.oneSidedState A .right)
        (profiledRawJointHybridExactRightRootPredicate A installed)
        (profiledRawJointHybridExactRightPolicy A hwin installed)
        row [] input).1 := by
  classical
  let table :=
    profiledRawJointLiteralLeftBothExactHeterogeneousRightTable A strategy hwin
      installed
  have hfirst := (table.memberController_records_allowed false input input).1
  change decide (_ = _) = true at hfirst
  have hrecord := of_decide_eq_true hfirst
  exact congrArg (fun record ↦ record.2.1.target row) hrecord

theorem
    profiledRawJointLiteralLeftBothExactHeterogeneousRightTable_noRecv_output_eq
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (past : List In₁) (input : In₁) :
    let table :=
      profiledRawJointLiteralLeftBothExactHeterogeneousRightTable A strategy
        hwin installed
    ((table.memberController false).labeledTree past).1 input =
      ((table.memberController true).labeledTree past).1 input := by
  dsimp only
  have h :=
    (profiledRawJointLiteralLeftBothExactHeterogeneousRightTable A strategy
      hwin installed).memberController_sender_eq false true past
  exact congrFun h input

theorem
    profiledRawJointLiteralLeftBothExactHeterogeneousRightTable_noRecv_step_eq
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (control :
      ((profiledRawJointLiteralLeftBothExactHeterogeneousRightTable A strategy
        hwin installed).memberController false).Control)
    (input : In₁) :
    let table :=
      profiledRawJointLiteralLeftBothExactHeterogeneousRightTable A strategy
        hwin installed
    (table.memberController false).step control input =
      (table.memberController true).step control input := by
  dsimp only
  exact
    (profiledRawJointLiteralLeftBothExactHeterogeneousRightTable A strategy
      hwin installed).memberController_step_eq_atControl false true control
        input

/-! ## Model-facing literal child -/

noncomputable def
    profiledRawJointLiteralLeftBothExactHeterogeneousRightTableAtChild
    (point : ProfiledRawJointGuardedCommonSemanticPoint A strategy)
    (blockInput : In₁ × In₂) :=
  let child := point.step A strategy blockInput
  let installed := profiledRawJointGuardedCommonPointInstalled A strategy child
  profiledRawJointLiteralLeftBothExactHeterogeneousRightTable A strategy hwin
    installed

theorem
    profiledRawJointLiteralLeftBothExactHeterogeneousRightTableAtChild_noRecv_output_eq
    (point : ProfiledRawJointGuardedCommonSemanticPoint A strategy)
    (blockInput : In₁ × In₂) (past : List In₁) (input : In₁) :
    let table :=
      profiledRawJointLiteralLeftBothExactHeterogeneousRightTableAtChild A
        strategy hwin point blockInput
    ((table.memberController false).labeledTree past).1 input =
      ((table.memberController true).labeledTree past).1 input := by
  let child := point.step A strategy blockInput
  let installed := profiledRawJointGuardedCommonPointInstalled A strategy child
  simpa [profiledRawJointLiteralLeftBothExactHeterogeneousRightTableAtChild,
    child, installed] using
    (profiledRawJointLiteralLeftBothExactHeterogeneousRightTable_noRecv_output_eq
      A strategy hwin installed past input)

/-- Both hidden interpretations at the literal child advance the same
process-one sender control.  The hidden Boolean remains a proof-side monitor
projection and is not an argument of the executable step. -/
theorem
    profiledRawJointLiteralLeftBothExactHeterogeneousRightTableAtChild_noRecv_step_eq
    (point : ProfiledRawJointGuardedCommonSemanticPoint A strategy)
    (blockInput : In₁ × In₂)
    (control :
      ((profiledRawJointLiteralLeftBothExactHeterogeneousRightTableAtChild A
        strategy hwin point blockInput).memberController false).Control)
    (input : In₁) :
    let table :=
      profiledRawJointLiteralLeftBothExactHeterogeneousRightTableAtChild A
        strategy hwin point blockInput
    (table.memberController false).step control input =
      (table.memberController true).step control input := by
  let child := point.step A strategy blockInput
  let installed := profiledRawJointGuardedCommonPointInstalled A strategy child
  simpa [profiledRawJointLiteralLeftBothExactHeterogeneousRightTableAtChild,
    child, installed] using
    (profiledRawJointLiteralLeftBothExactHeterogeneousRightTable_noRecv_step_eq
      A strategy hwin installed control input)

/-! ## Exact projected play and ordinary-policy handoff -/

noncomputable def profiledRawJointLiteralLeftBothExactTruePlay
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (env : Nat → In₂ × In₁) :
    Nat → RealizedBlockRound In₂ In₁
      (ProfiledRawJointLiteralExactRightReceiverOutput A strategy hwin
        installed) Out₁ :=
  let table :=
    profiledRawJointLiteralLeftBothExactHeterogeneousRightTable A strategy
      hwin installed
  let controller := table.memberController true
  BlockRecordMonitor.projectReceiverPlay Prod.snd
    (treePlay (narrowedInducedTree _ controller.labeledTree) env)

theorem profiledRawJointLiteralLeftBothExactTruePlay_wins
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (env : Nat → In₂ × In₁) :
    (profiledRawJointHybridExactRightMonitor.{u, v, x, y, s, y} A installed
      (ProfiledRawJointLiteralExactRightPackage A strategy hwin installed)
      ).WinsPlay
        (profiledRawJointLiteralLeftBothExactTruePlay A strategy hwin installed
          env) := by
  let table :=
    profiledRawJointLiteralLeftBothExactHeterogeneousRightTable A strategy
      hwin installed
  let controller := table.memberController true
  let productPlay := treePlay
    (narrowedInducedTree _ controller.labeledTree) env
  let exactMonitor := profiledRawJointHybridExactRightMonitor.{u, v, x, y, s,
    y} A installed
    (ProfiledRawJointLiteralExactRightPackage A strategy hwin installed)
  have hproduct := table.memberController_base_wins true env
  have hcomap :
      (exactMonitor.restartAt exactMonitor.initial |>.comapReceiverOutput
        Prod.snd).WinsPlay productPlay := by
    simpa [table, controller, productPlay, exactMonitor, MirrorExactMonitor,
      finiteCrossAnchorRestartFamily,
      finiteCrossAnchorHeterogeneousMonitor,
      finiteCrossAnchorHeterogeneousStart,
      BlockRecordMonitor.restartAt,
      BlockRecordMonitor.comapReceiverOutput] using hproduct
  have hexactRestart :=
    (BlockRecordMonitor.comapReceiverOutput_wins_iff
      (exactMonitor.restartAt exactMonitor.initial) Prod.snd productPlay).mp
      hcomap
  simpa [profiledRawJointLiteralLeftBothExactTruePlay, table, controller,
    productPlay, exactMonitor, BlockRecordMonitor.restartAt] using
    hexactRestart

end


end DetParityAutomaton

end DistributedSynthesis
