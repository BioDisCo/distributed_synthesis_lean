/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridFullRestartFirstThenBothScan

/-!
# Receiver adapter for the first-then-both scan lane

This is the earliest non-invasive insertion point for the third FullRestart
lane.  A semantic target-block activation is still constructed before any
finite-table rationalization.  Its receiver output is decorated with one
additional target, while projection through `base` recovers the old receiver
strategy and old monitor play definitionally.

Consequently the extra finite field changes neither physical outputs nor the
blind sender interface.  The existing target monitor can be transported by
`BlockRecordMonitor.comapReceiverOutput`; a new mixed-lane checker may later
be conjoined with that transported monitor.
-/

namespace DistributedSynthesis

universe u v x y s t

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

/-! ## Forgetting the third certificate -/

/-- Forget only the additional right mixed-lane target. -/
def profiledRawJointRightFirstThenBothReceiverOutputBase
    {Target : Type t}
    (output : ProfiledRawJointRightFirstThenBothReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂) Target) :
    ProfiledRawJointTargetRightReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂) Target :=
  output.base

/-- Left mirror. -/
def profiledRawJointLeftFirstThenBothReceiverOutputBase
    {Target : Type t}
    (output : ProfiledRawJointLeftFirstThenBothReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂) Target) :
    ProfiledRawJointTargetLeftReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂) Target :=
  output.base

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype Out₁] [Fintype Out₂] in
@[simp] theorem
    profiledRawJointRightFirstThenBothReceiverOutputBase_physical
    {Target : Type t}
    (output : ProfiledRawJointRightFirstThenBothReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂) Target) :
    (profiledRawJointRightFirstThenBothReceiverOutputBase output).physical =
      output.base.physical :=
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype Out₁] [Fintype Out₂] in
@[simp] theorem
    profiledRawJointLeftFirstThenBothReceiverOutputBase_physical
    {Target : Type t}
    (output : ProfiledRawJointLeftFirstThenBothReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂) Target) :
    (profiledRawJointLeftFirstThenBothReceiverOutputBase output).physical =
      output.base.physical :=
  rfl

/-! ## Pre-rationalization semantic receiver lift -/

/-- Decorate an existing semantic right receiver with an arbitrary third
target.  All physical behavior and both old row targets remain unchanged. -/
def profiledRawJointTargetRightFirstThenBothReceiverStrategy
    {Target : Type t}
    {targetState : Target → PairedProfiledTreeState A}
    {Allowed : Target → Prop}
    {source : ProfiledRawRightSlot A}
    (activation : ProfiledRawJointTargetRightBlockActivation A Target
      targetState Allowed source)
    (firstThenBothTarget : List (In₂ × In₁) → In₂ × In₁ → Target) :
    ReceiverBlockStrategy In₂ In₁
      (ProfiledRawJointRightFirstThenBothReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) Target) :=
  fun past input ↦ {
    base := profiledRawJointTargetRightReceiverStrategy A activation past input
    firstThenBothTarget := firstThenBothTarget past input }

/-- Left semantic receiver lift. -/
def profiledRawJointTargetLeftFirstThenBothReceiverStrategy
    {Target : Type t}
    {targetState : Target → PairedProfiledTreeState A}
    {Allowed : Target → Prop}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointTargetLeftBlockActivation A Target
      targetState Allowed source)
    (firstThenBothTarget : List (In₁ × In₂) → In₁ × In₂ → Target) :
    ReceiverBlockStrategy In₁ In₂
      (ProfiledRawJointLeftFirstThenBothReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) Target) :=
  fun past input ↦ {
    base := profiledRawJointTargetLeftReceiverStrategy A activation past input
    firstThenBothTarget := firstThenBothTarget past input }

/-- Canonical right lift supplied by the source-level mixed activation
extension. -/
def profiledRawJointTargetRightFirstThenBothReceiverStrategyOfExtension
    {Target : Type t}
    {targetState : Target → PairedProfiledTreeState A}
    {Allowed : Target → Prop}
    {source : ProfiledRawRightSlot A}
    (activation : ProfiledRawJointTargetRightBlockActivation A Target
      targetState Allowed source)
    (extension :
      ProfiledRawJointTargetRightFirstThenBothActivationExtension A
        activation) :
    ReceiverBlockStrategy In₂ In₁
      (ProfiledRawJointRightFirstThenBothReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) Target) :=
  profiledRawJointTargetRightFirstThenBothReceiverStrategy A activation
    extension.target

/-- Canonical left lift. -/
def profiledRawJointTargetLeftFirstThenBothReceiverStrategyOfExtension
    {Target : Type t}
    {targetState : Target → PairedProfiledTreeState A}
    {Allowed : Target → Prop}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointTargetLeftBlockActivation A Target
      targetState Allowed source)
    (extension :
      ProfiledRawJointTargetLeftFirstThenBothActivationExtension A
        activation) :
    ReceiverBlockStrategy In₁ In₂
      (ProfiledRawJointLeftFirstThenBothReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) Target) :=
  profiledRawJointTargetLeftFirstThenBothReceiverStrategy A activation
    extension.target

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem
    profiledRawJointTargetRightFirstThenBothReceiverStrategyOfExtension_target
    {Target : Type t}
    {targetState : Target → PairedProfiledTreeState A}
    {Allowed : Target → Prop}
    {source : ProfiledRawRightSlot A}
    (activation : ProfiledRawJointTargetRightBlockActivation A Target
      targetState Allowed source)
    (extension :
      ProfiledRawJointTargetRightFirstThenBothActivationExtension A activation)
    (past : List (In₂ × In₁)) (input : In₂ × In₁) :
    (profiledRawJointTargetRightFirstThenBothReceiverStrategyOfExtension A
      activation extension past input).firstThenBothTarget =
        extension.target past input :=
  rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem
    profiledRawJointTargetLeftFirstThenBothReceiverStrategyOfExtension_target
    {Target : Type t}
    {targetState : Target → PairedProfiledTreeState A}
    {Allowed : Target → Prop}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointTargetLeftBlockActivation A Target
      targetState Allowed source)
    (extension :
      ProfiledRawJointTargetLeftFirstThenBothActivationExtension A activation)
    (past : List (In₁ × In₂)) (input : In₁ × In₂) :
    (profiledRawJointTargetLeftFirstThenBothReceiverStrategyOfExtension A
      activation extension past input).firstThenBothTarget =
        extension.target past input :=
  rfl

/-! ## The source extension discharges the finite-lane safety laws -/

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂]

/-- The source-level right extension gives exactly the target-safety law
consumed by the finite lane. -/
theorem
    ProfiledRawJointTargetRightFirstThenBothActivationExtension.monitorLaws
    {Target : Type t}
    {targetState : Target → PairedProfiledTreeState A}
    {Allowed : Target → Prop}
    {source : ProfiledRawRightSlot A}
    {activation : ProfiledRawJointTargetRightBlockActivation A Target
      targetState Allowed source}
    (extension :
      ProfiledRawJointTargetRightFirstThenBothActivationExtension A activation)
    (env : Nat → In₂ × In₁) :
    ProfiledRawJointRightFirstThenBothMonitorLaws A targetState Allowed
      source.1.1 (pairedRightBlockWord activation.lambda env)
      (fun n ↦ extension.target (omegaPrefix env n) (env n)) := by
  constructor
  intro n
  constructor
  · rw [extension.target_state env n]
    simp
  · exact extension.target_allowed (omegaPrefix env n) (env n)

/-- Left law bridge. -/
theorem
    ProfiledRawJointTargetLeftFirstThenBothActivationExtension.monitorLaws
    {Target : Type t}
    {targetState : Target → PairedProfiledTreeState A}
    {Allowed : Target → Prop}
    {source : ProfiledRawLeftSlot A}
    {activation : ProfiledRawJointTargetLeftBlockActivation A Target
      targetState Allowed source}
    (extension :
      ProfiledRawJointTargetLeftFirstThenBothActivationExtension A activation)
    (env : Nat → In₁ × In₂) :
    ProfiledRawJointLeftFirstThenBothMonitorLaws A targetState Allowed
      source.1.1 (pairedLeftBlockWord activation.lambda env)
      (fun n ↦ extension.target (omegaPrefix env n) (env n)) := by
  constructor
  intro n
  constructor
  · rw [extension.target_state env n]
    simp
  · exact extension.target_allowed (omegaPrefix env n) (env n)

@[simp] theorem
    profiledRawJointTargetRightFirstThenBothReceiverStrategy_base
    {Target : Type t}
    {targetState : Target → PairedProfiledTreeState A}
    {Allowed : Target → Prop}
    {source : ProfiledRawRightSlot A}
    (activation : ProfiledRawJointTargetRightBlockActivation A Target
      targetState Allowed source)
    (firstThenBothTarget : List (In₂ × In₁) → In₂ × In₁ → Target)
    (past : List (In₂ × In₁)) (input : In₂ × In₁) :
    profiledRawJointRightFirstThenBothReceiverOutputBase
        (profiledRawJointTargetRightFirstThenBothReceiverStrategy A activation
          firstThenBothTarget past input) =
      profiledRawJointTargetRightReceiverStrategy A activation past input :=
  rfl

@[simp] theorem
    profiledRawJointTargetLeftFirstThenBothReceiverStrategy_base
    {Target : Type t}
    {targetState : Target → PairedProfiledTreeState A}
    {Allowed : Target → Prop}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointTargetLeftBlockActivation A Target
      targetState Allowed source)
    (firstThenBothTarget : List (In₁ × In₂) → In₁ × In₂ → Target)
    (past : List (In₁ × In₂)) (input : In₁ × In₂) :
    profiledRawJointLeftFirstThenBothReceiverOutputBase
        (profiledRawJointTargetLeftFirstThenBothReceiverStrategy A activation
          firstThenBothTarget past input) =
      profiledRawJointTargetLeftReceiverStrategy A activation past input :=
  rfl

end

/-! ## Old monitor transport is exact -/

/-- The old right target monitor, read through the new certificate output. -/
noncomputable abbrev profiledRawJointTargetRightFirstThenBothBaseMonitor
    (Target : Type t) [Fintype Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (source : ProfiledRawRightSlot A) :=
  (profiledRawJointTargetRightBlockMonitor A Target targetState Allowed source
    ).comapReceiverOutput
      (profiledRawJointRightFirstThenBothReceiverOutputBase
        (Out₁ := Out₁) (Out₂ := Out₂))

/-- Left transported base monitor. -/
noncomputable abbrev profiledRawJointTargetLeftFirstThenBothBaseMonitor
    (Target : Type t) [Fintype Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (source : ProfiledRawLeftSlot A) :=
  (profiledRawJointTargetLeftBlockMonitor A Target targetState Allowed source
    ).comapReceiverOutput
      (profiledRawJointLeftFirstThenBothReceiverOutputBase
        (Out₁ := Out₁) (Out₂ := Out₂))

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Projecting a lifted right semantic play recovers the old semantic play
pointwise. -/
theorem
    profiledRawJointTargetRightFirstThenBoth_projectReceiverPlay_pairPlay
    {Target : Type t}
    {targetState : Target → PairedProfiledTreeState A}
    {Allowed : Target → Prop}
    {source : ProfiledRawRightSlot A}
    (activation : ProfiledRawJointTargetRightBlockActivation A Target
      targetState Allowed source)
    (firstThenBothTarget : List (In₂ × In₁) → In₂ × In₁ → Target)
    (env : Nat → In₂ × In₁) :
    BlockRecordMonitor.projectReceiverPlay
        (profiledRawJointRightFirstThenBothReceiverOutputBase
          (Out₁ := Out₁) (Out₂ := Out₂))
        (pairPlay
          (profiledRawJointTargetRightFirstThenBothReceiverStrategy A
            activation firstThenBothTarget)
          (pairedRightSenderStrategy activation.lambda) env) =
      pairPlay (profiledRawJointTargetRightReceiverStrategy A activation)
        (pairedRightSenderStrategy activation.lambda) env := by
  funext n
  rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Left projected-play mirror. -/
theorem
    profiledRawJointTargetLeftFirstThenBoth_projectReceiverPlay_pairPlay
    {Target : Type t}
    {targetState : Target → PairedProfiledTreeState A}
    {Allowed : Target → Prop}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointTargetLeftBlockActivation A Target
      targetState Allowed source)
    (firstThenBothTarget : List (In₁ × In₂) → In₁ × In₂ → Target)
    (env : Nat → In₁ × In₂) :
    BlockRecordMonitor.projectReceiverPlay
        (profiledRawJointLeftFirstThenBothReceiverOutputBase
          (Out₁ := Out₁) (Out₂ := Out₂))
        (pairPlay
          (profiledRawJointTargetLeftFirstThenBothReceiverStrategy A activation
            firstThenBothTarget)
          (pairedLeftSenderStrategy activation.lambda) env) =
      pairPlay (profiledRawJointTargetLeftReceiverStrategy A activation)
        (pairedLeftSenderStrategy activation.lambda) env := by
  funext n
  rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype Out₂] in
/-- The extra right target preserves every old monitor check, for any value
of the new target field. -/
theorem profiledRawJointTargetRightFirstThenBothBaseMonitor_realizable
    {Target : Type t} [Fintype Target]
    {targetState : Target → PairedProfiledTreeState A}
    {Allowed : Target → Prop}
    {source : ProfiledRawRightSlot A}
    (activation : ProfiledRawJointTargetRightBlockActivation A Target
      targetState Allowed source)
    (firstThenBothTarget : List (In₂ × In₁) → In₂ × In₁ → Target)
    (env : Nat → In₂ × In₁) :
    (profiledRawJointTargetRightFirstThenBothBaseMonitor A Target targetState
      Allowed source).WinsPlay
      (pairPlay
        (profiledRawJointTargetRightFirstThenBothReceiverStrategy A activation
          firstThenBothTarget)
        (pairedRightSenderStrategy activation.lambda) env) := by
  apply (BlockRecordMonitor.comapReceiverOutput_wins_iff
    (profiledRawJointTargetRightBlockMonitor A Target targetState Allowed
      source)
    (profiledRawJointRightFirstThenBothReceiverOutputBase
      (Out₁ := Out₁) (Out₂ := Out₂)) _).mpr
  rw [profiledRawJointTargetRightFirstThenBoth_projectReceiverPlay_pairPlay]
  exact profiledRawJointTargetRightBlockMonitor_realizable A targetState
    Allowed source activation env

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype Out₁] in
/-- Left preservation mirror. -/
theorem profiledRawJointTargetLeftFirstThenBothBaseMonitor_realizable
    {Target : Type t} [Fintype Target]
    {targetState : Target → PairedProfiledTreeState A}
    {Allowed : Target → Prop}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointTargetLeftBlockActivation A Target
      targetState Allowed source)
    (firstThenBothTarget : List (In₁ × In₂) → In₁ × In₂ → Target)
    (env : Nat → In₁ × In₂) :
    (profiledRawJointTargetLeftFirstThenBothBaseMonitor A Target targetState
      Allowed source).WinsPlay
      (pairPlay
        (profiledRawJointTargetLeftFirstThenBothReceiverStrategy A activation
          firstThenBothTarget)
        (pairedLeftSenderStrategy activation.lambda) env) := by
  apply (BlockRecordMonitor.comapReceiverOutput_wins_iff
    (profiledRawJointTargetLeftBlockMonitor A Target targetState Allowed source)
    (profiledRawJointLeftFirstThenBothReceiverOutputBase
      (Out₁ := Out₁) (Out₂ := Out₂)) _).mpr
  rw [profiledRawJointTargetLeftFirstThenBoth_projectReceiverPlay_pairPlay]
  exact profiledRawJointTargetLeftBlockMonitor_realizable A targetState Allowed
    source activation env

end

end DetParityAutomaton

end DistributedSynthesis
