/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointUnitPolicyControllerBank

/-!
# Finite local handoff for the singleton raw-joint policy

This is the operational shell around the unconditional raw-joint controller
bank.  An owner stores a reachable finite policy macro and the control of the
controller installed at that macro.  A receiver stores the same macro, its
row, the finite block-monitor state, and an optional opposite macro.

The receiver stages an opposite macro only after checking both the physical
close and the edge of the one fixed finite-code policy.  Owner and receiver
then restart from that very same staged macro.  The executable step functions
take no graph, orientation, side, or strict-leader signal.
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

/-! ## Finite local controls -/

abbrev ProfiledRawJointUnitRightPolicyOwnerControl
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial
      policy) :=
  Σ source : ProfiledRawJointUnitRightPolicyMacro A strategy (initial.code A)
      policy,
    ((bank.right source).1).Control

abbrev ProfiledRawJointUnitLeftPolicyOwnerControl
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial
      policy) :=
  Σ source : ProfiledRawJointUnitLeftPolicyMacro A strategy (initial.code A)
      policy,
    ((bank.left source).1).Control

abbrev ProfiledRawJointUnitRightPolicyReceiverControl
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A)) :=
  Σ source : ProfiledRawJointUnitRightPolicyMacro A strategy (initial.code A)
      policy,
    PairedEntryRow ×
      (profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s,
        max u v x y s} A strategy (initial.code A) policy source.state
          source.slot).State ×
      Option (ProfiledRawJointUnitLeftPolicyMacro A strategy (initial.code A)
        policy)

abbrev ProfiledRawJointUnitLeftPolicyReceiverControl
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A)) :=
  Σ source : ProfiledRawJointUnitLeftPolicyMacro A strategy (initial.code A)
      policy,
    PairedEntryRow ×
      (profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s,
        max u v x y s} A strategy (initial.code A) policy source.state
          source.slot).State ×
      Option (ProfiledRawJointUnitRightPolicyMacro A strategy (initial.code A)
        policy)

noncomputable instance profiledRawJointUnitRightPolicyOwnerControlFintype
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial
      policy) :
    Fintype (ProfiledRawJointUnitRightPolicyOwnerControl A strategy initial
      policy bank) := by
  classical
  infer_instance

noncomputable instance profiledRawJointUnitLeftPolicyOwnerControlFintype
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial
      policy) :
    Fintype (ProfiledRawJointUnitLeftPolicyOwnerControl A strategy initial
      policy bank) := by
  classical
  infer_instance

noncomputable instance profiledRawJointUnitRightPolicyReceiverControlFintype
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A)) :
    Fintype (ProfiledRawJointUnitRightPolicyReceiverControl A strategy initial
      policy) := by
  classical
  infer_instance

noncomputable instance profiledRawJointUnitLeftPolicyReceiverControlFintype
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A)) :
    Fintype (ProfiledRawJointUnitLeftPolicyReceiverControl A strategy initial
      policy) := by
  classical
  infer_instance

/-! ## Initialization and owner steps -/

noncomputable def initialProfiledRawJointUnitRightPolicyOwner
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial
      policy)
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy (initial.code A)
      policy) :
    ProfiledRawJointUnitRightPolicyOwnerControl A strategy initial policy
      bank :=
  ⟨source, ((bank.right source).1).initial⟩

noncomputable def initialProfiledRawJointUnitLeftPolicyOwner
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial
      policy)
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy (initial.code A)
      policy) :
    ProfiledRawJointUnitLeftPolicyOwnerControl A strategy initial policy
      bank :=
  ⟨source, ((bank.left source).1).initial⟩

noncomputable def initialProfiledRawJointUnitRightPolicyReceiver
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy (initial.code A)
      policy) (row : PairedEntryRow) :
    ProfiledRawJointUnitRightPolicyReceiverControl A strategy initial policy :=
  ⟨source, row,
    (profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s,
      max u v x y s} A strategy (initial.code A) policy source.state
        source.slot).initial,
    none⟩

noncomputable def initialProfiledRawJointUnitLeftPolicyReceiver
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy (initial.code A)
      policy) (row : PairedEntryRow) :
    ProfiledRawJointUnitLeftPolicyReceiverControl A strategy initial policy :=
  ⟨source, row,
    (profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s,
      max u v x y s} A strategy (initial.code A) policy source.state
        source.slot).initial,
    none⟩

noncomputable def stepProfiledRawJointUnitRightPolicyOwner
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (owner : ProfiledRawJointUnitRightPolicyOwnerControl A strategy initial
      policy bank) (input : In₁) :
    Out₁ × ProfiledRawJointUnitRightPolicyOwnerControl A strategy initial
      policy bank :=
  let controller := (bank.right owner.1).1
  let label := controller.labelOf owner.2
  (label.1 input, ⟨owner.1, controller.step owner.2 input⟩)

noncomputable def stepProfiledRawJointUnitLeftPolicyOwner
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (owner : ProfiledRawJointUnitLeftPolicyOwnerControl A strategy initial
      policy bank) (input : In₂) :
    Out₂ × ProfiledRawJointUnitLeftPolicyOwnerControl A strategy initial policy
      bank :=
  let controller := (bank.left owner.1).1
  let label := controller.labelOf owner.2
  (label.1 input, ⟨owner.1, controller.step owner.2 input⟩)

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem stepProfiledRawJointUnitRightPolicyOwner_source
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (owner : ProfiledRawJointUnitRightPolicyOwnerControl A strategy initial
      policy bank) (input : In₁) :
    (stepProfiledRawJointUnitRightPolicyOwner A strategy initial policy bank
      owner input).2.1 = owner.1 := rfl

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem stepProfiledRawJointUnitLeftPolicyOwner_source
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (owner : ProfiledRawJointUnitLeftPolicyOwnerControl A strategy initial
      policy bank) (input : In₂) :
    (stepProfiledRawJointUnitLeftPolicyOwner A strategy initial policy bank
      owner input).2.1 = owner.1 := rfl

/-! ## Receiver computation and checked staging -/

abbrev ProfiledRawJointUnitRightPolicyReceiverRoundResult
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy (initial.code A)
      policy) :=
  ProfiledRawJointUnitRightReceiverOutput A strategy (initial.code A) ×
    (profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s,
      max u v x y s} A strategy (initial.code A) policy source.state
        source.slot).State ×
    Option (ProfiledRawJointUnitLeftPolicyMacro A strategy (initial.code A)
      policy)

abbrev ProfiledRawJointUnitLeftPolicyReceiverRoundResult
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy (initial.code A)
      policy) :=
  ProfiledRawJointUnitLeftReceiverOutput A strategy (initial.code A) ×
    (profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s,
      max u v x y s} A strategy (initial.code A) policy source.state
        source.slot).State ×
    Option (ProfiledRawJointUnitRightPolicyMacro A strategy (initial.code A)
      policy)

/-- The local right-receiver check that authorizes an opposite-macro
handoff. -/
abbrev ProfiledRawJointUnitRightPolicyCloseSafe
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy (initial.code A)
      policy)
    (ownerControl : ((bank.right source).1).Control)
    (row : PairedEntryRow)
    (monitorState :
      (profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s,
        max u v x y s} A strategy (initial.code A) policy source.state
          source.slot).State)
    (move : In₂ × In₁) : Prop :=
  let label := (bank.right source).1.labelOf ownerControl
  let output := label.2 monitorState move
  let physical := profiledRawJointUnitRightPhysicalLetter A
    (move, output, label.1 move.2)
  erasePairedProfiledState A
        (profiledRawJointUnitRightTargetProfiledState A (output.target row)) =
      pairedRightCloseTarget A monitorState.2.1 row physical ∧
    ProfiledRawJointOneSidedProvenanceAllowedTarget A strategy
      (initial.code A) policy source.state (output.target row)

/-- Left-to-right mirror of the local closing check. -/
abbrev ProfiledRawJointUnitLeftPolicyCloseSafe
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy (initial.code A)
      policy)
    (ownerControl : ((bank.left source).1).Control)
    (row : PairedEntryRow)
    (monitorState :
      (profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s,
        max u v x y s} A strategy (initial.code A) policy source.state
          source.slot).State)
    (move : In₁ × In₂) : Prop :=
  let label := (bank.left source).1.labelOf ownerControl
  let output := label.2 monitorState move
  let physical := profiledRawJointUnitLeftPhysicalLetter A
    (move, output, label.1 move.2)
  erasePairedProfiledState A
        (profiledRawJointUnitLeftTargetProfiledState A (output.target row)) =
      pairedLeftCloseTarget A monitorState.2.1 row physical ∧
    ProfiledRawJointOneSidedProvenanceAllowedTarget A strategy
      (initial.code A) policy source.state (output.target row)

noncomputable def stepProfiledRawJointUnitRightPolicyReceiverFor
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy (initial.code A)
      policy)
    (ownerControl : ((bank.right source).1).Control)
    (row : PairedEntryRow)
    (monitorState :
      (profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s,
        max u v x y s} A strategy (initial.code A) policy source.state
          source.slot).State)
    (move : In₂ × In₁) :
    ProfiledRawJointUnitRightPolicyReceiverRoundResult A strategy initial policy
      source := by
  classical
  let monitor := profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s,
    max u v x y s} A strategy (initial.code A) policy source.state source.slot
  let controller := (bank.right source).1
  let label := controller.labelOf ownerControl
  let output := label.2 monitorState move
  let physical := profiledRawJointUnitRightPhysicalLetter A
    (move, output, label.1 move.2)
  let nextMonitor := monitor.step monitorState
    (move, output, label.1 move.2)
  if hsafe : ProfiledRawJointUnitRightPolicyCloseSafe A strategy initial
      policy bank source ownerControl row monitorState move then
    let slot := Classical.choose
      (exists_profiledRawJointUnitLeftSlot_of_rightTarget_erases_close A
        (output.target row) monitorState.2.1 row physical hsafe.1)
    let hslot := Classical.choose_spec
      (exists_profiledRawJointUnitLeftSlot_of_rightTarget_erases_close A
        (output.target row) monitorState.2.1 row physical hsafe.1)
    exact (output, nextMonitor,
      some (profiledRawJointUnitStageLeftOfAllowed A strategy (initial.code A)
        policy source (output.target row) slot hsafe.2 hslot))
  else
    exact (output, nextMonitor, none)

noncomputable def stepProfiledRawJointUnitLeftPolicyReceiverFor
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy (initial.code A)
      policy)
    (ownerControl : ((bank.left source).1).Control)
    (row : PairedEntryRow)
    (monitorState :
      (profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s,
        max u v x y s} A strategy (initial.code A) policy source.state
          source.slot).State)
    (move : In₁ × In₂) :
    ProfiledRawJointUnitLeftPolicyReceiverRoundResult A strategy initial policy
      source := by
  classical
  let monitor := profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s,
    max u v x y s} A strategy (initial.code A) policy source.state source.slot
  let controller := (bank.left source).1
  let label := controller.labelOf ownerControl
  let output := label.2 monitorState move
  let physical := profiledRawJointUnitLeftPhysicalLetter A
    (move, output, label.1 move.2)
  let nextMonitor := monitor.step monitorState
    (move, output, label.1 move.2)
  if hsafe : ProfiledRawJointUnitLeftPolicyCloseSafe A strategy initial
      policy bank source ownerControl row monitorState move then
    let slot := Classical.choose
      (exists_profiledRawJointUnitRightSlot_of_leftTarget_erases_close A
        (output.target row) monitorState.2.1 row physical hsafe.1)
    let hslot := Classical.choose_spec
      (exists_profiledRawJointUnitRightSlot_of_leftTarget_erases_close A
        (output.target row) monitorState.2.1 row physical hsafe.1)
    exact (output, nextMonitor,
      some (profiledRawJointUnitStageRightOfAllowed A strategy (initial.code A)
        policy source (output.target row) slot hsafe.2 hslot))
  else
    exact (output, nextMonitor, none)

section
omit [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem stepProfiledRawJointUnitRightPolicyReceiverFor_output
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy (initial.code A)
      policy)
    (ownerControl : ((bank.right source).1).Control)
    (row : PairedEntryRow)
    (monitorState :
      (profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s,
        max u v x y s} A strategy (initial.code A) policy source.state
          source.slot).State)
    (move : In₂ × In₁) :
    (stepProfiledRawJointUnitRightPolicyReceiverFor A strategy initial policy
      bank source ownerControl row monitorState move).1 =
      ((bank.right source).1.labelOf ownerControl).2 monitorState move := by
  classical
  simp only [stepProfiledRawJointUnitRightPolicyReceiverFor]
  split <;> rfl

@[simp] theorem stepProfiledRawJointUnitLeftPolicyReceiverFor_output
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy (initial.code A)
      policy)
    (ownerControl : ((bank.left source).1).Control)
    (row : PairedEntryRow)
    (monitorState :
      (profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s,
        max u v x y s} A strategy (initial.code A) policy source.state
          source.slot).State)
    (move : In₁ × In₂) :
    (stepProfiledRawJointUnitLeftPolicyReceiverFor A strategy initial policy
      bank source ownerControl row monitorState move).1 =
      ((bank.left source).1.labelOf ownerControl).2 monitorState move := by
  classical
  simp only [stepProfiledRawJointUnitLeftPolicyReceiverFor]
  split <;> rfl

@[simp] theorem stepProfiledRawJointUnitRightPolicyReceiverFor_monitor
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy (initial.code A)
      policy)
    (ownerControl : ((bank.right source).1).Control)
    (row : PairedEntryRow)
    (monitorState :
      (profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s,
        max u v x y s} A strategy (initial.code A) policy source.state
          source.slot).State)
    (move : In₂ × In₁) :
    (stepProfiledRawJointUnitRightPolicyReceiverFor A strategy initial policy
      bank source ownerControl row monitorState move).2.1 =
      (profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s,
        max u v x y s} A strategy (initial.code A) policy source.state
          source.slot).step monitorState
        (narrowedRecord
          (profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s,
            max u v x y s} A strategy (initial.code A) policy source.state
              source.slot)
          ((bank.right source).1.labelOf ownerControl) monitorState move) := by
  classical
  simp only [stepProfiledRawJointUnitRightPolicyReceiverFor, narrowedRecord]
  split <;> rfl

@[simp] theorem stepProfiledRawJointUnitLeftPolicyReceiverFor_monitor
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy (initial.code A)
      policy)
    (ownerControl : ((bank.left source).1).Control)
    (row : PairedEntryRow)
    (monitorState :
      (profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s,
        max u v x y s} A strategy (initial.code A) policy source.state
          source.slot).State)
    (move : In₁ × In₂) :
    (stepProfiledRawJointUnitLeftPolicyReceiverFor A strategy initial policy
      bank source ownerControl row monitorState move).2.1 =
      (profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s,
        max u v x y s} A strategy (initial.code A) policy source.state
          source.slot).step monitorState
        (narrowedRecord
          (profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s,
            max u v x y s} A strategy (initial.code A) policy source.state
              source.slot)
          ((bank.left source).1.labelOf ownerControl) monitorState move) := by
  classical
  simp only [stepProfiledRawJointUnitLeftPolicyReceiverFor, narrowedRecord]
  split <;> rfl

end

/-! ## Matched local lookup and interior receiver steps -/

/-- Interpret the current owner control at the receiver's source.  On the
matched-phase invariant this is the literal owner control; the fallback only
totalizes the executable function away from that invariant. -/
noncomputable def profiledRawJointUnitRightPolicyOwnerControlFor
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (receiver : ProfiledRawJointUnitRightPolicyReceiverControl A strategy
      initial policy)
    (owner : ProfiledRawJointUnitRightPolicyOwnerControl A strategy initial
      policy bank) :
    ((bank.right receiver.1).1).Control := by
  classical
  exact if h : owner.1 = receiver.1 then h ▸ owner.2
    else ((bank.right receiver.1).1).initial

noncomputable def profiledRawJointUnitLeftPolicyOwnerControlFor
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (receiver : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy
      initial policy)
    (owner : ProfiledRawJointUnitLeftPolicyOwnerControl A strategy initial
      policy bank) :
    ((bank.left receiver.1).1).Control := by
  classical
  exact if h : owner.1 = receiver.1 then h ▸ owner.2
    else ((bank.left receiver.1).1).initial

/-- Continue a right-oriented block.  The receiver output is selected by its
stored entry row, which remains fixed throughout the block. -/
noncomputable def continueProfiledRawJointUnitRightPolicyReceiver
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (receiver : ProfiledRawJointUnitRightPolicyReceiverControl A strategy
      initial policy)
    (owner : ProfiledRawJointUnitRightPolicyOwnerControl A strategy initial
      policy bank) (move : In₂ × In₁) :
    Out₂ × ProfiledRawJointUnitRightPolicyReceiverControl A strategy initial
      policy :=
  let result := stepProfiledRawJointUnitRightPolicyReceiverFor A strategy
    initial policy bank receiver.1
      (profiledRawJointUnitRightPolicyOwnerControlFor A strategy initial policy
        bank receiver owner)
      receiver.2.1 receiver.2.2.1 move
  (pairedRightInformedForRow receiver.2.1 result.1.physical,
    ⟨receiver.1, receiver.2.1, result.2.1, result.2.2⟩)

/-- Left-oriented mirror of the continuing receiver step. -/
noncomputable def continueProfiledRawJointUnitLeftPolicyReceiver
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (receiver : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy
      initial policy)
    (owner : ProfiledRawJointUnitLeftPolicyOwnerControl A strategy initial
      policy bank) (move : In₁ × In₂) :
    Out₁ × ProfiledRawJointUnitLeftPolicyReceiverControl A strategy initial
      policy :=
  let result := stepProfiledRawJointUnitLeftPolicyReceiverFor A strategy
    initial policy bank receiver.1
      (profiledRawJointUnitLeftPolicyOwnerControlFor A strategy initial policy
        bank receiver owner)
      receiver.2.1 receiver.2.2.1 move
  (pairedLeftInformedForRow receiver.2.1 result.1.physical,
    ⟨receiver.1, receiver.2.1, result.2.1, result.2.2⟩)

section
omit [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem continueProfiledRawJointUnitRightPolicyReceiver_source
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (receiver : ProfiledRawJointUnitRightPolicyReceiverControl A strategy
      initial policy)
    (owner : ProfiledRawJointUnitRightPolicyOwnerControl A strategy initial
      policy bank) (move : In₂ × In₁) :
    (continueProfiledRawJointUnitRightPolicyReceiver A strategy initial policy
      bank receiver owner move).2.1 = receiver.1 :=
  rfl

@[simp] theorem continueProfiledRawJointUnitLeftPolicyReceiver_source
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (receiver : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy
      initial policy)
    (owner : ProfiledRawJointUnitLeftPolicyOwnerControl A strategy initial
      policy bank) (move : In₁ × In₂) :
    (continueProfiledRawJointUnitLeftPolicyReceiver A strategy initial policy
      bank receiver owner move).2.1 = receiver.1 :=
  rfl

/-- A successful local right check stages a reachable left macro whose policy
state is exactly the emitted target, not merely an equivalent projection. -/
theorem stepProfiledRawJointUnitRightPolicyReceiverFor_stages_exact_of_safe
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy (initial.code A)
      policy)
    (ownerControl : ((bank.right source).1).Control)
    (row : PairedEntryRow)
    (monitorState :
      (profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s,
        max u v x y s} A strategy (initial.code A) policy source.state
          source.slot).State)
    (move : In₂ × In₁)
    (hsafe : ProfiledRawJointUnitRightPolicyCloseSafe A strategy initial
      policy bank source ownerControl row monitorState move) :
    ∃ target : ProfiledRawJointUnitLeftPolicyMacro A strategy (initial.code A)
        policy,
      (stepProfiledRawJointUnitRightPolicyReceiverFor A strategy initial policy
        bank source ownerControl row monitorState move).2.2 = some target ∧
      target.state =
        (((bank.right source).1.labelOf ownerControl).2 monitorState move).target
          row := by
  classical
  simp only [stepProfiledRawJointUnitRightPolicyReceiverFor]
  split
  · let slot := Classical.choose
      (exists_profiledRawJointUnitLeftSlot_of_rightTarget_erases_close A
        ((((bank.right source).1.labelOf ownerControl).2 monitorState move).target
          row) monitorState.2.1 row
        (profiledRawJointUnitRightPhysicalLetter A
          (move, ((bank.right source).1.labelOf ownerControl).2 monitorState move,
            ((bank.right source).1.labelOf ownerControl).1 move.2)) hsafe.1)
    let hslot := Classical.choose_spec
      (exists_profiledRawJointUnitLeftSlot_of_rightTarget_erases_close A
        ((((bank.right source).1.labelOf ownerControl).2 monitorState move).target
          row) monitorState.2.1 row
        (profiledRawJointUnitRightPhysicalLetter A
          (move, ((bank.right source).1.labelOf ownerControl).2 monitorState move,
            ((bank.right source).1.labelOf ownerControl).1 move.2)) hsafe.1)
    refine ⟨profiledRawJointUnitStageLeftOfAllowed A strategy (initial.code A)
      policy source
        ((((bank.right source).1.labelOf ownerControl).2 monitorState move).target
          row) slot hsafe.2 hslot, rfl, rfl⟩
  · contradiction

/-- Left-to-right mirror of exact checked staging. -/
theorem stepProfiledRawJointUnitLeftPolicyReceiverFor_stages_exact_of_safe
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy (initial.code A)
      policy)
    (ownerControl : ((bank.left source).1).Control)
    (row : PairedEntryRow)
    (monitorState :
      (profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s,
        max u v x y s} A strategy (initial.code A) policy source.state
          source.slot).State)
    (move : In₁ × In₂)
    (hsafe : ProfiledRawJointUnitLeftPolicyCloseSafe A strategy initial
      policy bank source ownerControl row monitorState move) :
    ∃ target : ProfiledRawJointUnitRightPolicyMacro A strategy (initial.code A)
        policy,
      (stepProfiledRawJointUnitLeftPolicyReceiverFor A strategy initial policy
        bank source ownerControl row monitorState move).2.2 = some target ∧
      target.state =
        (((bank.left source).1.labelOf ownerControl).2 monitorState move).target
          row := by
  classical
  simp only [stepProfiledRawJointUnitLeftPolicyReceiverFor]
  split
  · let slot := Classical.choose
      (exists_profiledRawJointUnitRightSlot_of_leftTarget_erases_close A
        ((((bank.left source).1.labelOf ownerControl).2 monitorState move).target
          row) monitorState.2.1 row
        (profiledRawJointUnitLeftPhysicalLetter A
          (move, ((bank.left source).1.labelOf ownerControl).2 monitorState move,
            ((bank.left source).1.labelOf ownerControl).1 move.2)) hsafe.1)
    let hslot := Classical.choose_spec
      (exists_profiledRawJointUnitRightSlot_of_leftTarget_erases_close A
        ((((bank.left source).1.labelOf ownerControl).2 monitorState move).target
          row) monitorState.2.1 row
        (profiledRawJointUnitLeftPhysicalLetter A
          (move, ((bank.left source).1.labelOf ownerControl).2 monitorState move,
            ((bank.left source).1.labelOf ownerControl).1 move.2)) hsafe.1)
    refine ⟨profiledRawJointUnitStageRightOfAllowed A strategy (initial.code A)
      policy source
        ((((bank.left source).1.labelOf ownerControl).2 monitorState move).target
          row) slot hsafe.2 hslot, rfl, rfl⟩
  · contradiction

end

/-! ## Actual finite-controller prefixes -/

abbrev ProfiledRawJointUnitRightPolicyFiniteState
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy (initial.code A)
      policy) :=
  ((bank.right source).1).Control ×
    (profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s,
      max u v x y s} A strategy (initial.code A) policy source.state
        source.slot).State

noncomputable def stepProfiledRawJointUnitRightPolicyFiniteState
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy (initial.code A)
      policy)
    (state : ProfiledRawJointUnitRightPolicyFiniteState A strategy initial
      policy bank source) (move : In₂ × In₁) :
    ProfiledRawJointUnitRightPolicyFiniteState A strategy initial policy bank
      source :=
  let controller := (bank.right source).1
  let monitor := profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s,
    max u v x y s} A strategy (initial.code A) policy source.state source.slot
  let label := controller.labelOf state.1
  (controller.step state.1 move.2,
    monitor.step state.2 (narrowedRecord monitor label state.2 move))

noncomputable def profiledRawJointUnitRightPolicyFiniteStateAfter
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy (initial.code A)
      policy) (past : List (In₂ × In₁)) :
    ProfiledRawJointUnitRightPolicyFiniteState A strategy initial policy bank
      source :=
  past.foldl
    (stepProfiledRawJointUnitRightPolicyFiniteState A strategy initial policy
      bank source)
    (((bank.right source).1).initial,
      (profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s,
        max u v x y s} A strategy (initial.code A) policy source.state
          source.slot).initial)

section
omit [Inhabited Out₁] [Inhabited Out₂]

theorem profiledRawJointUnitRightPolicyFiniteStateAfter_eq
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy (initial.code A)
      policy) : ∀ past : List (In₂ × In₁),
    profiledRawJointUnitRightPolicyFiniteStateAfter A strategy initial policy
        bank source past =
      (((bank.right source).1).controlAt (senderWord past),
        narrowedControl
          (profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s,
            max u v x y s} A strategy (initial.code A) policy source.state
              source.slot)
          ((bank.right source).1).labeledTree past) := by
  intro past
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past move ih =>
      rw [profiledRawJointUnitRightPolicyFiniteStateAfter, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      change stepProfiledRawJointUnitRightPolicyFiniteState A strategy initial
        policy bank source
          (profiledRawJointUnitRightPolicyFiniteStateAfter A strategy initial
            policy bank source past) move = _
      rw [ih, senderWord_append, TransitionRationalTree.controlAt_append,
        narrowedControl_append]
      rfl

theorem profiledRawJointUnitRightPolicy_treePlay_at_prefix
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy (initial.code A)
      policy) (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    let monitor := profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s,
      max u v x y s} A strategy (initial.code A) policy source.state source.slot
    let controller := (bank.right source).1
    let env := omegaOfList (past ++ [move])
    treePlay (narrowedInducedTree monitor controller.labeledTree) env
        past.length =
      narrowedRecord monitor
        (controller.labelOf (controller.controlAt (senderWord past)))
        (narrowedControl monitor controller.labeledTree past) move := by
  dsimp only
  let finiteWord := past ++ [move]
  let env : Nat → In₂ × In₁ := omegaOfList finiteWord
  have hpast : omegaPrefix env past.length = past := by
    apply List.ext_get
    · simp [omegaPrefix]
    · intro n hnLeft hnRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [omegaPrefix, List.getElem_ofFn]
      have hnPrefix : n < finiteWord.length := by simp [finiteWord]; omega
      change omegaOfList finiteWord n = past[n]
      rw [omegaOfList_eq_getElem finiteWord n hnPrefix]
      simp [finiteWord, hnRight]
  have hmove : env past.length = move := by
    have hnPrefix : past.length < finiteWord.length := by simp [finiteWord]
    change omegaOfList finiteWord past.length = move
    rw [omegaOfList_eq_getElem finiteWord past.length hnPrefix]
    simp [finiteWord]
  simp [treePlay, narrowedInducedTree, blockLabelApply, narrowedRecord,
    TransitionRationalTree.labeledTree, branchNode_eq_omegaPrefix,
    hpast, hmove, senderWord, env, finiteWord]

/-- Every actual right-controller round takes the checked branch and stages
the exact opposite policy state. -/
theorem profiledRawJointUnitRightPolicy_real_close_stages_exact
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy (initial.code A)
      policy) (row : PairedEntryRow)
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    ∃ target : ProfiledRawJointUnitLeftPolicyMacro A strategy (initial.code A)
        policy,
      (stepProfiledRawJointUnitRightPolicyReceiverFor A strategy initial policy
        bank source
          (profiledRawJointUnitRightPolicyFiniteStateAfter A strategy initial
            policy bank source past).1 row
          (profiledRawJointUnitRightPolicyFiniteStateAfter A strategy initial
            policy bank source past).2 move).2.2 = some target ∧
      target.state =
        (((bank.right source).1.labelOf
          (profiledRawJointUnitRightPolicyFiniteStateAfter A strategy initial
            policy bank source past).1).2
          (profiledRawJointUnitRightPolicyFiniteStateAfter A strategy initial
            policy bank source past).2 move).target row := by
  rw [profiledRawJointUnitRightPolicyFiniteStateAfter_eq A strategy initial
    policy bank source]
  let monitor := profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s,
    max u v x y s} A strategy (initial.code A) policy source.state source.slot
  let controller := (bank.right source).1
  let env : Nat → In₂ × In₁ := omegaOfList (past ++ [move])
  let tree := narrowedInducedTree monitor controller.labeledTree
  have htree := narrowedInducedTree_winningTree_of_allThreadsWin monitor
    (bank.right source).2
  have hwin : monitor.WinsPlay (treePlay tree env) :=
    (monitor.lift_winningTree_iff tree).mp htree env
  have hsafe := profiledRawJointUnitRight_targetsSafe_of_wins A strategy
    (initial.code A) policy source (treePlay tree env) hwin past.length row
  have hat := profiledRawJointUnitRightPolicy_treePlay_at_prefix A strategy
    initial policy bank source past move
  change treePlay tree env past.length = _ at hat
  rw [hat] at hsafe
  have hpast : omegaPrefix env past.length = past := by
    apply List.ext_get
    · simp [omegaPrefix]
    · intro n hnLeft hnRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [omegaPrefix, List.getElem_ofFn]
      have hnPrefix : n < (past ++ [move]).length := by simp; omega
      change omegaOfList (past ++ [move]) n = past[n]
      rw [omegaOfList_eq_getElem (past ++ [move]) n hnPrefix]
      simp [hnRight]
  have hrun : monitor.run (treePlay tree env) past.length =
      narrowedControl monitor controller.labeledTree past := by
    rw [← monitor.lift_control_branchNode tree env,
      lift_control_narrowedInducedTree, branchNode_eq_omegaPrefix, hpast]
  rw [hrun] at hsafe
  apply
    stepProfiledRawJointUnitRightPolicyReceiverFor_stages_exact_of_safe A
      strategy initial policy bank source
  simpa [ProfiledRawJointUnitRightPolicyCloseSafe, narrowedRecord] using hsafe

end

abbrev ProfiledRawJointUnitLeftPolicyFiniteState
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy (initial.code A)
      policy) :=
  ((bank.left source).1).Control ×
    (profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s,
      max u v x y s} A strategy (initial.code A) policy source.state
        source.slot).State

noncomputable def stepProfiledRawJointUnitLeftPolicyFiniteState
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy (initial.code A)
      policy)
    (state : ProfiledRawJointUnitLeftPolicyFiniteState A strategy initial policy
      bank source) (move : In₁ × In₂) :
    ProfiledRawJointUnitLeftPolicyFiniteState A strategy initial policy bank
      source :=
  let controller := (bank.left source).1
  let monitor := profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s,
    max u v x y s} A strategy (initial.code A) policy source.state source.slot
  let label := controller.labelOf state.1
  (controller.step state.1 move.2,
    monitor.step state.2 (narrowedRecord monitor label state.2 move))

noncomputable def profiledRawJointUnitLeftPolicyFiniteStateAfter
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy (initial.code A)
      policy) (past : List (In₁ × In₂)) :
    ProfiledRawJointUnitLeftPolicyFiniteState A strategy initial policy bank
      source :=
  past.foldl
    (stepProfiledRawJointUnitLeftPolicyFiniteState A strategy initial policy
      bank source)
    (((bank.left source).1).initial,
      (profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s,
        max u v x y s} A strategy (initial.code A) policy source.state
          source.slot).initial)

section
omit [Inhabited Out₁] [Inhabited Out₂]

theorem profiledRawJointUnitLeftPolicyFiniteStateAfter_eq
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy (initial.code A)
      policy) : ∀ past : List (In₁ × In₂),
    profiledRawJointUnitLeftPolicyFiniteStateAfter A strategy initial policy
        bank source past =
      (((bank.left source).1).controlAt (senderWord past),
        narrowedControl
          (profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s,
            max u v x y s} A strategy (initial.code A) policy source.state
              source.slot)
          ((bank.left source).1).labeledTree past) := by
  intro past
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past move ih =>
      rw [profiledRawJointUnitLeftPolicyFiniteStateAfter, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      change stepProfiledRawJointUnitLeftPolicyFiniteState A strategy initial
        policy bank source
          (profiledRawJointUnitLeftPolicyFiniteStateAfter A strategy initial
            policy bank source past) move = _
      rw [ih, senderWord_append, TransitionRationalTree.controlAt_append,
        narrowedControl_append]
      rfl

theorem profiledRawJointUnitLeftPolicy_treePlay_at_prefix
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy (initial.code A)
      policy) (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    let monitor := profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s,
      max u v x y s} A strategy (initial.code A) policy source.state source.slot
    let controller := (bank.left source).1
    let env := omegaOfList (past ++ [move])
    treePlay (narrowedInducedTree monitor controller.labeledTree) env
        past.length =
      narrowedRecord monitor
        (controller.labelOf (controller.controlAt (senderWord past)))
        (narrowedControl monitor controller.labeledTree past) move := by
  dsimp only
  let finiteWord := past ++ [move]
  let env : Nat → In₁ × In₂ := omegaOfList finiteWord
  have hpast : omegaPrefix env past.length = past := by
    apply List.ext_get
    · simp [omegaPrefix]
    · intro n hnLeft hnRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [omegaPrefix, List.getElem_ofFn]
      have hnPrefix : n < finiteWord.length := by simp [finiteWord]; omega
      change omegaOfList finiteWord n = past[n]
      rw [omegaOfList_eq_getElem finiteWord n hnPrefix]
      simp [finiteWord, hnRight]
  have hmove : env past.length = move := by
    have hnPrefix : past.length < finiteWord.length := by simp [finiteWord]
    change omegaOfList finiteWord past.length = move
    rw [omegaOfList_eq_getElem finiteWord past.length hnPrefix]
    simp [finiteWord]
  simp [treePlay, narrowedInducedTree, blockLabelApply, narrowedRecord,
    TransitionRationalTree.labeledTree, branchNode_eq_omegaPrefix,
    hpast, hmove, senderWord, env, finiteWord]

/-- Every actual left-controller round takes the checked branch and stages
the exact opposite policy state. -/
theorem profiledRawJointUnitLeftPolicy_real_close_stages_exact
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy (initial.code A)
      policy) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    ∃ target : ProfiledRawJointUnitRightPolicyMacro A strategy (initial.code A)
        policy,
      (stepProfiledRawJointUnitLeftPolicyReceiverFor A strategy initial policy
        bank source
          (profiledRawJointUnitLeftPolicyFiniteStateAfter A strategy initial
            policy bank source past).1 row
          (profiledRawJointUnitLeftPolicyFiniteStateAfter A strategy initial
            policy bank source past).2 move).2.2 = some target ∧
      target.state =
        (((bank.left source).1.labelOf
          (profiledRawJointUnitLeftPolicyFiniteStateAfter A strategy initial
            policy bank source past).1).2
          (profiledRawJointUnitLeftPolicyFiniteStateAfter A strategy initial
            policy bank source past).2 move).target row := by
  rw [profiledRawJointUnitLeftPolicyFiniteStateAfter_eq A strategy initial
    policy bank source]
  let monitor := profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s,
    max u v x y s} A strategy (initial.code A) policy source.state source.slot
  let controller := (bank.left source).1
  let env : Nat → In₁ × In₂ := omegaOfList (past ++ [move])
  let tree := narrowedInducedTree monitor controller.labeledTree
  have htree := narrowedInducedTree_winningTree_of_allThreadsWin monitor
    (bank.left source).2
  have hwin : monitor.WinsPlay (treePlay tree env) :=
    (monitor.lift_winningTree_iff tree).mp htree env
  have hsafe := profiledRawJointUnitLeft_targetsSafe_of_wins A strategy
    (initial.code A) policy source (treePlay tree env) hwin past.length row
  have hat := profiledRawJointUnitLeftPolicy_treePlay_at_prefix A strategy
    initial policy bank source past move
  change treePlay tree env past.length = _ at hat
  rw [hat] at hsafe
  have hpast : omegaPrefix env past.length = past := by
    apply List.ext_get
    · simp [omegaPrefix]
    · intro n hnLeft hnRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [omegaPrefix, List.getElem_ofFn]
      have hnPrefix : n < (past ++ [move]).length := by simp; omega
      change omegaOfList (past ++ [move]) n = past[n]
      rw [omegaOfList_eq_getElem (past ++ [move]) n hnPrefix]
      simp [hnRight]
  have hrun : monitor.run (treePlay tree env) past.length =
      narrowedControl monitor controller.labeledTree past := by
    rw [← monitor.lift_control_branchNode tree env,
      lift_control_narrowedInducedTree, branchNode_eq_omegaPrefix, hpast]
  rw [hrun] at hsafe
  apply
    stepProfiledRawJointUnitLeftPolicyReceiverFor_stages_exact_of_safe A
      strategy initial policy bank source
  simpa [ProfiledRawJointUnitLeftPolicyCloseSafe, narrowedRecord] using hsafe

end

/-! ## Definitional common-source restart -/

noncomputable def profiledRawJointUnitRestartLeft
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (target : ProfiledRawJointUnitLeftPolicyMacro A strategy (initial.code A)
      policy) (row : PairedEntryRow) :=
  (initialProfiledRawJointUnitLeftPolicyOwner A strategy initial policy bank
      target,
    initialProfiledRawJointUnitLeftPolicyReceiver A strategy initial policy
      target row)

noncomputable def profiledRawJointUnitRestartRight
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (target : ProfiledRawJointUnitRightPolicyMacro A strategy (initial.code A)
      policy) (row : PairedEntryRow) :=
  (initialProfiledRawJointUnitRightPolicyOwner A strategy initial policy bank
      target,
    initialProfiledRawJointUnitRightPolicyReceiver A strategy initial policy
      target row)

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledRawJointUnitRestartLeft_common_source
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (target : ProfiledRawJointUnitLeftPolicyMacro A strategy (initial.code A)
      policy) (row : PairedEntryRow) :
    (profiledRawJointUnitRestartLeft A strategy initial policy bank target
      row).1.1 =
    (profiledRawJointUnitRestartLeft A strategy initial policy bank target
      row).2.1 :=
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledRawJointUnitRestartRight_common_source
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (target : ProfiledRawJointUnitRightPolicyMacro A strategy (initial.code A)
      policy) (row : PairedEntryRow) :
    (profiledRawJointUnitRestartRight A strategy initial policy bank target
      row).1.1 =
    (profiledRawJointUnitRestartRight A strategy initial policy bank target
      row).2.1 :=
  rfl

end

end DetParityAutomaton

end DistributedSynthesis
