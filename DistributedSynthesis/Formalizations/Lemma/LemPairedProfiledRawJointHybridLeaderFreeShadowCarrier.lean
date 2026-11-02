/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridCommonTaggedReplacementFamily
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointHybridExactRootGuard
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointUnitPolicyLocalHandoff

/-!
# The leader-free common/strict shadow

A receive at a common control is locally ambiguous: it may be a genuine
simultaneous round, or it may be the receiver half of the first strict round.
The finite controls in this file retain both honest consequences without a
graph, orientation, or leader bit:

* the common control reached by the hypothetical simultaneous transition;
* the guarded-first receiver-monitor state reached by the strict shadow.

The two receiving processes use mirror controls.  If their delivered controls
are again common shadows, they refresh the common transition.  If a delivered
control is a guarded owner, the receiver continues the strict block.  A local
`noRecv` from a shadow enters the appropriate one-round replacement policy at
its canonical live root.

This is the finite front adapter only.  It proves the exact local transition,
projection, and output equations consumed by the eventual physical carrier;
omega acceptance remains downstream.
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

local notation "CommonControl" =>
  ProfiledRawJointHybridCommonControl A strategy hwin

/-! ## Canonical guarded controllers at one common control -/

local notation "Installed" => fun control : CommonControl ↦
  ProfiledRawJointHybridCommonInstalledMove.toCommonMoveData A
    (profiledRawJointHybridCommonControlInstalled A strategy hwin control)

/-- The root-pinned right policy whose receiver output agrees with the
common move on the locally ambiguous simultaneous row. -/
noncomputable def profiledRawJointHybridShadowRightPinnedPolicy
    (control : CommonControl) :=
  profiledRawJointHybridExactRightPolicy A hwin (Installed control)

/-- Left mirror of `profiledRawJointHybridShadowRightPinnedPolicy`. -/
noncomputable def profiledRawJointHybridShadowLeftPinnedPolicy
    (control : CommonControl) :=
  profiledRawJointHybridExactLeftPolicy A hwin (Installed control)

/-- The right guarded activation at the literal process-one slot of the
installed common world. -/
noncomputable def profiledRawJointHybridShadowRightActivation
    (control : CommonControl) :=
  profiledRawJointHybridExactRightActivation A hwin (Installed control)

/-- The left guarded activation at the literal process-two slot. -/
noncomputable def profiledRawJointHybridShadowLeftActivation
    (control : CommonControl) :=
  profiledRawJointHybridExactLeftActivation A hwin (Installed control)

abbrev ProfiledRawJointHybridShadowRightMonitor
    (control : CommonControl) :=
  profiledRawJointHybridExactRightMonitor.{u, v, x, y, s,
    max u v x y s} A
    (Installed control)
    (profiledRawJointHybridShadowRightPinnedPolicy A strategy hwin control)

abbrev ProfiledRawJointHybridShadowLeftMonitor
    (control : CommonControl) :=
  profiledRawJointHybridExactLeftMonitor.{u, v, x, y, s,
    max u v x y s} A
    (Installed control)
    (profiledRawJointHybridShadowLeftPinnedPolicy A strategy hwin control)

/-- Select the finite right guarded controller once at every finite common
control. -/
noncomputable def profiledRawJointHybridShadowRightController
    (control : CommonControl) :=
  profiledRawJointHybridExactRightController A hwin (Installed control)

/-- Its all-thread certificate. -/
theorem profiledRawJointHybridShadowRightController_wins
    (control : CommonControl) :
    NarrowedAllThreadsWin
      (ProfiledRawJointHybridShadowRightMonitor A strategy hwin control)
      (profiledRawJointHybridShadowRightController A strategy hwin control
        ).labeledTree :=
  profiledRawJointHybridExactRightController_wins A hwin (Installed control)

/-- Select the left mirror controller. -/
noncomputable def profiledRawJointHybridShadowLeftController
    (control : CommonControl) :=
  profiledRawJointHybridExactLeftController A hwin (Installed control)

theorem profiledRawJointHybridShadowLeftController_wins
    (control : CommonControl) :
    NarrowedAllThreadsWin
      (ProfiledRawJointHybridShadowLeftMonitor A strategy hwin control)
      (profiledRawJointHybridShadowLeftController A strategy hwin control
        ).labeledTree :=
  profiledRawJointHybridExactLeftController_wins A hwin (Installed control)

/-! ## The first locally ambiguous receive -/

/-- The complete realized left guarded record at the controller root. -/
noncomputable def profiledRawJointHybridShadowLeftRootRecord
    (control : CommonControl) (input : In₁ × In₂) :=
  let monitor := ProfiledRawJointHybridShadowLeftMonitor A strategy hwin control
  let controller :=
    profiledRawJointHybridShadowLeftController A strategy hwin control
  narrowedRecord monitor (controller.labelOf controller.initial)
    monitor.initial input

/-- Right mirror, whose block input order is process two then process one. -/
noncomputable def profiledRawJointHybridShadowRightRootRecord
    (control : CommonControl) (input : In₁ × In₂) :=
  let monitor := ProfiledRawJointHybridShadowRightMonitor A strategy hwin control
  let controller :=
    profiledRawJointHybridShadowRightController A strategy hwin control
  narrowedRecord monitor (controller.labelOf controller.initial)
    monitor.initial (input.2, input.1)

/-- The guarded left root emits exactly the common process-one output. -/
theorem profiledRawJointHybridShadowLeftRoot_output
    (control : CommonControl) (input : In₁ × In₂) :
    pairedLeftInformedForRow .both
        (profiledRawJointHybridShadowLeftRootRecord A strategy hwin control
          input).2.1.physical =
      (Installed control).bothOutputOne A input := by
  simpa [profiledRawJointHybridShadowLeftRootRecord,
    profiledRawJointHybridShadowLeftController,
    profiledRawJointHybridShadowLeftPinnedPolicy,
    TransitionRationalTree.labeledTree, TransitionRationalTree.controlAt] using
    profiledRawJointHybridExactLeftController_root_output A hwin
      (Installed control) input

/-- Right mirror root-output equality. -/
theorem profiledRawJointHybridShadowRightRoot_output
    (control : CommonControl) (input : In₁ × In₂) :
    pairedRightInformedForRow .both
        (profiledRawJointHybridShadowRightRootRecord A strategy hwin control
          input).2.1.physical =
      (Installed control).bothOutputTwo A input := by
  simpa [profiledRawJointHybridShadowRightRootRecord,
    profiledRawJointHybridShadowRightController,
    profiledRawJointHybridShadowRightPinnedPolicy,
    TransitionRationalTree.labeledTree, TransitionRationalTree.controlAt] using
    profiledRawJointHybridExactRightController_root_output A hwin
      (Installed control) (input.2, input.1)

/-- Process one's ambiguous local state: a hypothetical common successor and
the strict-left receiver continuation are both recoverable from these fields. -/
structure ProfiledRawJointHybridOneShadow where
  origin : CommonControl
  input : In₁ × In₂
  strictReceiver :
    (ProfiledRawJointHybridShadowLeftMonitor A strategy hwin origin).State

/-- Process-two mirror, retaining the strict-right receiver continuation. -/
structure ProfiledRawJointHybridTwoShadow where
  origin : CommonControl
  input : In₁ × In₂
  strictReceiver :
    (ProfiledRawJointHybridShadowRightMonitor A strategy hwin origin).State

noncomputable instance profiledRawJointHybridOneShadowFintype :
    Fintype (ProfiledRawJointHybridOneShadow A strategy hwin) := by
  classical
  let Rep := Σ control : CommonControl, (In₁ × In₂) ×
    (ProfiledRawJointHybridShadowLeftMonitor A strategy hwin control).State
  let equiv : ProfiledRawJointHybridOneShadow A strategy hwin ≃ Rep := {
    toFun := fun state ↦ ⟨state.origin, state.input, state.strictReceiver⟩
    invFun := fun state ↦ ⟨state.1, state.2.1, state.2.2⟩
    left_inv := by intro state; cases state; rfl
    right_inv := by intro state; rcases state with ⟨a, b, c⟩; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

noncomputable instance profiledRawJointHybridTwoShadowFintype :
    Fintype (ProfiledRawJointHybridTwoShadow A strategy hwin) := by
  classical
  let Rep := Σ control : CommonControl, (In₁ × In₂) ×
    (ProfiledRawJointHybridShadowRightMonitor A strategy hwin control).State
  let equiv : ProfiledRawJointHybridTwoShadow A strategy hwin ≃ Rep := {
    toFun := fun state ↦ ⟨state.origin, state.input, state.strictReceiver⟩
    invFun := fun state ↦ ⟨state.1, state.2.1, state.2.2⟩
    left_inv := by intro state; cases state; rfl
    right_inv := by intro state; rcases state with ⟨a, b, c⟩; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

/-- The hypothetical simultaneous successor stored by process one. -/
noncomputable def ProfiledRawJointHybridOneShadow.commonNext
    (state : ProfiledRawJointHybridOneShadow A strategy hwin) : CommonControl :=
  profiledRawJointHybridCommonControlNext A strategy hwin state.origin
    state.input

/-- Process-two mirror projection. -/
noncomputable def ProfiledRawJointHybridTwoShadow.commonNext
    (state : ProfiledRawJointHybridTwoShadow A strategy hwin) : CommonControl :=
  profiledRawJointHybridCommonControlNext A strategy hwin state.origin
    state.input

/-- Execute process one's common receive and retain the strict-left shadow. -/
noncomputable def profiledRawJointHybridCommonToOneShadow
    (control : CommonControl) (own : In₁) (delivered : In₂) :
    Out₁ × ProfiledRawJointHybridOneShadow A strategy hwin :=
  let input := (own, delivered)
  let monitor := ProfiledRawJointHybridShadowLeftMonitor A strategy hwin control
  let record := profiledRawJointHybridShadowLeftRootRecord A strategy hwin
    control input
  ((Installed control).bothOutputOne A input,
    ⟨control, input, monitor.step monitor.initial record⟩)

/-- Process-two common receive mirror. -/
noncomputable def profiledRawJointHybridCommonToTwoShadow
    (control : CommonControl) (own : In₂) (delivered : In₁) :
    Out₂ × ProfiledRawJointHybridTwoShadow A strategy hwin :=
  let input := (delivered, own)
  let monitor := ProfiledRawJointHybridShadowRightMonitor A strategy hwin control
  let record := profiledRawJointHybridShadowRightRootRecord A strategy hwin
    control input
  ((Installed control).bothOutputTwo A input,
    ⟨control, input, monitor.step monitor.initial record⟩)

@[simp] theorem profiledRawJointHybridCommonToOneShadow_origin
    (control : CommonControl) (own : In₁) (delivered : In₂) :
    (profiledRawJointHybridCommonToOneShadow A strategy hwin control own
      delivered).2.origin = control := rfl

@[simp] theorem profiledRawJointHybridCommonToTwoShadow_origin
    (control : CommonControl) (own : In₂) (delivered : In₁) :
    (profiledRawJointHybridCommonToTwoShadow A strategy hwin control own
      delivered).2.origin = control := rfl

@[simp] theorem profiledRawJointHybridCommonToOneShadow_commonNext
    (control : CommonControl) (input : In₁ × In₂) :
    (profiledRawJointHybridCommonToOneShadow A strategy hwin control input.1
      input.2).2.commonNext A strategy hwin =
      profiledRawJointHybridCommonControlNext A strategy hwin control input :=
  rfl

@[simp] theorem profiledRawJointHybridCommonToTwoShadow_commonNext
    (control : CommonControl) (input : In₁ × In₂) :
    (profiledRawJointHybridCommonToTwoShadow A strategy hwin control input.2
      input.1).2.commonNext A strategy hwin =
      profiledRawJointHybridCommonControlNext A strategy hwin control input :=
  rfl

/-- Both local shadows store literally the same hypothetical common control. -/
theorem profiledRawJointHybridCommonToShadows_commonNext_agree
    (control : CommonControl) (input : In₁ × In₂) :
    (profiledRawJointHybridCommonToOneShadow A strategy hwin control input.1
      input.2).2.commonNext A strategy hwin =
    (profiledRawJointHybridCommonToTwoShadow A strategy hwin control input.2
      input.1).2.commonNext A strategy hwin :=
  rfl

/-- The physical output deliberately uses the common table, and the guarded
strict continuation computes the same process-one value. -/
theorem profiledRawJointHybridCommonToOneShadow_strict_output
    (control : CommonControl) (input : In₁ × In₂) :
    pairedLeftInformedForRow .both
        (profiledRawJointHybridShadowLeftRootRecord A strategy hwin control
          input).2.1.physical =
      (profiledRawJointHybridCommonToOneShadow A strategy hwin control input.1
        input.2).1 :=
  profiledRawJointHybridShadowLeftRoot_output A strategy hwin control input

/-- Process-two mirror output coherence. -/
theorem profiledRawJointHybridCommonToTwoShadow_strict_output
    (control : CommonControl) (input : In₁ × In₂) :
    pairedRightInformedForRow .both
        (profiledRawJointHybridShadowRightRootRecord A strategy hwin control
          input).2.1.physical =
      (profiledRawJointHybridCommonToTwoShadow A strategy hwin control input.2
        input.1).1 :=
  profiledRawJointHybridShadowRightRoot_output A strategy hwin control input

/-! ## Common/common refresh -/

/-- Process one sees another common shadow and advances its own stored
hypothetical common control.  The delivered shadow is used only as the honest
local phase witness; no graph value is supplied. -/
noncomputable def profiledRawJointHybridOneShadowRecvCommon
    (own : ProfiledRawJointHybridOneShadow A strategy hwin)
    (_delivered : ProfiledRawJointHybridTwoShadow A strategy hwin)
    (ownInput : In₁) (deliveredInput : In₂) :
    Out₁ × ProfiledRawJointHybridOneShadow A strategy hwin :=
  profiledRawJointHybridCommonToOneShadow A strategy hwin
    (own.commonNext A strategy hwin) ownInput deliveredInput

/-- Process-two mirror common refresh. -/
noncomputable def profiledRawJointHybridTwoShadowRecvCommon
    (own : ProfiledRawJointHybridTwoShadow A strategy hwin)
    (_delivered : ProfiledRawJointHybridOneShadow A strategy hwin)
    (ownInput : In₂) (deliveredInput : In₁) :
    Out₂ × ProfiledRawJointHybridTwoShadow A strategy hwin :=
  profiledRawJointHybridCommonToTwoShadow A strategy hwin
    (own.commonNext A strategy hwin) ownInput deliveredInput

/-- Proof-side agreement predicate for the two independently stored common
projections.  It is not a runtime test. -/
def ProfiledRawJointHybridShadowsCommonAgree
    (one : ProfiledRawJointHybridOneShadow A strategy hwin)
    (two : ProfiledRawJointHybridTwoShadow A strategy hwin) : Prop :=
  one.commonNext A strategy hwin = two.commonNext A strategy hwin

theorem profiledRawJointHybridCommonToShadows_agree
    (control : CommonControl) (input : In₁ × In₂) :
    ProfiledRawJointHybridShadowsCommonAgree A strategy hwin
      (profiledRawJointHybridCommonToOneShadow A strategy hwin control input.1
        input.2).2
      (profiledRawJointHybridCommonToTwoShadow A strategy hwin control input.2
        input.1).2 :=
  rfl

/-- Under the proof-side agreement invariant, the next common/common receive
installs exactly the same origin at both processes. -/
theorem profiledRawJointHybridShadowRecvCommon_origins_agree
    (one : ProfiledRawJointHybridOneShadow A strategy hwin)
    (two : ProfiledRawJointHybridTwoShadow A strategy hwin)
    (hagrees : ProfiledRawJointHybridShadowsCommonAgree A strategy hwin one two)
    (input : In₁ × In₂) :
    (profiledRawJointHybridOneShadowRecvCommon A strategy hwin one two input.1
      input.2).2.origin =
    (profiledRawJointHybridTwoShadowRecvCommon A strategy hwin two one input.2
      input.1).2.origin := by
  simpa [profiledRawJointHybridOneShadowRecvCommon,
    profiledRawJointHybridTwoShadowRecvCommon] using hagrees

/-- The refreshed physical pair is the literal simultaneous output of the
shared next common control. -/
theorem profiledRawJointHybridShadowRecvCommon_outputs
    (one : ProfiledRawJointHybridOneShadow A strategy hwin)
    (two : ProfiledRawJointHybridTwoShadow A strategy hwin)
    (hagrees : ProfiledRawJointHybridShadowsCommonAgree A strategy hwin one two)
    (input : In₁ × In₂) :
    ((profiledRawJointHybridOneShadowRecvCommon A strategy hwin one two input.1
        input.2).1,
      (profiledRawJointHybridTwoShadowRecvCommon A strategy hwin two one input.2
        input.1).1) =
      (profiledRawJointHybridCommonControlInstalled A strategy hwin
        (one.commonNext A strategy hwin)).literalBothOutput A input := by
  rw [profiledRawJointHybridOneShadowRecvCommon,
    profiledRawJointHybridTwoShadowRecvCommon]
  change
    ((profiledRawJointHybridCommonControlInstalled A strategy hwin
        (one.commonNext A strategy hwin)).bothOutputOne A input,
      (profiledRawJointHybridCommonControlInstalled A strategy hwin
        (two.commonNext A strategy hwin)).bothOutputTwo A input) = _
  rw [← hagrees]
  exact (profiledRawJointHybridCommonControlInstalled A strategy hwin
    (one.commonNext A strategy hwin)).bothOutputs_eq_literal A input

/-! ## Guarded strict-owner controls and delivered-owner resolution -/

/-- A process-one guarded owner is indexed by the common control at which it
observed `noRecv`.  Its partner input is intentionally absent. -/
structure ProfiledRawJointHybridRightGuardOwner where
  origin : CommonControl
  owner :
    (profiledRawJointHybridShadowRightController A strategy hwin origin).Control

/-- Process-two mirror. -/
structure ProfiledRawJointHybridLeftGuardOwner where
  origin : CommonControl
  owner :
    (profiledRawJointHybridShadowLeftController A strategy hwin origin).Control

noncomputable instance profiledRawJointHybridRightGuardOwnerFintype :
    Fintype (ProfiledRawJointHybridRightGuardOwner A strategy hwin) := by
  classical
  let Rep := Σ control : CommonControl,
    (profiledRawJointHybridShadowRightController A strategy hwin control).Control
  let equiv : ProfiledRawJointHybridRightGuardOwner A strategy hwin ≃ Rep := {
    toFun := fun state ↦ ⟨state.origin, state.owner⟩
    invFun := fun state ↦ ⟨state.1, state.2⟩
    left_inv := by intro state; cases state; rfl
    right_inv := by intro state; rcases state with ⟨a, b⟩; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

noncomputable instance profiledRawJointHybridLeftGuardOwnerFintype :
    Fintype (ProfiledRawJointHybridLeftGuardOwner A strategy hwin) := by
  classical
  let Rep := Σ control : CommonControl,
    (profiledRawJointHybridShadowLeftController A strategy hwin control).Control
  let equiv : ProfiledRawJointHybridLeftGuardOwner A strategy hwin ≃ Rep := {
    toFun := fun state ↦ ⟨state.origin, state.owner⟩
    invFun := fun state ↦ ⟨state.1, state.2⟩
    left_inv := by intro state; cases state; rfl
    right_inv := by intro state; rcases state with ⟨a, b⟩; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

/-- A common-control `noRecv` at process one starts the guarded strict-right
sender using only the own input. -/
noncomputable def profiledRawJointHybridCommonNoRecvOne
    (control : CommonControl) (input : In₁) :
    Out₁ × ProfiledRawJointHybridRightGuardOwner A strategy hwin :=
  let controller :=
    profiledRawJointHybridShadowRightController A strategy hwin control
  let label := controller.labelOf controller.initial
  (label.1 input, ⟨control, controller.step controller.initial input⟩)

/-- Process-two strict-left owner mirror. -/
noncomputable def profiledRawJointHybridCommonNoRecvTwo
    (control : CommonControl) (input : In₂) :
    Out₂ × ProfiledRawJointHybridLeftGuardOwner A strategy hwin :=
  let controller :=
    profiledRawJointHybridShadowLeftController A strategy hwin control
  let label := controller.labelOf controller.initial
  (label.1 input, ⟨control, controller.step controller.initial input⟩)

@[simp] theorem profiledRawJointHybridCommonNoRecvOne_origin
    (control : CommonControl) (input : In₁) :
    (profiledRawJointHybridCommonNoRecvOne A strategy hwin control input).2.origin
      = control := rfl

@[simp] theorem profiledRawJointHybridCommonNoRecvTwo_origin
    (control : CommonControl) (input : In₂) :
    (profiledRawJointHybridCommonNoRecvTwo A strategy hwin control input).2.origin
      = control := rfl

/-- The strict-right owner output is exactly the sender component used in the
guarded root record computed by the locally indistinguishable receiver. -/
theorem profiledRawJointHybridCommonNoRecvOne_root_sender
    (control : CommonControl) (input : In₁ × In₂) :
    (profiledRawJointHybridCommonNoRecvOne A strategy hwin control input.1).1 =
      (profiledRawJointHybridShadowRightRootRecord A strategy hwin control
        input).2.2 :=
  rfl

/-- Strict-left mirror sender equation. -/
theorem profiledRawJointHybridCommonNoRecvTwo_root_sender
    (control : CommonControl) (input : In₁ × In₂) :
    (profiledRawJointHybridCommonNoRecvTwo A strategy hwin control input.2).1 =
      (profiledRawJointHybridShadowLeftRootRecord A strategy hwin control
        input).2.2 :=
  rfl

/-- At a strict-right first exit, the two independent local transitions are
the two physical projections of one guarded narrowed root record. -/
theorem profiledRawJointHybridCommon_strictRight_root_pair
    (control : CommonControl) (input : In₁ × In₂) :
    ((profiledRawJointHybridCommonNoRecvOne A strategy hwin control input.1).1,
      (profiledRawJointHybridCommonToTwoShadow A strategy hwin control input.2
        input.1).1) =
      ((profiledRawJointHybridShadowRightRootRecord A strategy hwin control
        input).2.2,
        pairedRightInformedForRow .both
          (profiledRawJointHybridShadowRightRootRecord A strategy hwin control
            input).2.1.physical) := by
  rw [profiledRawJointHybridCommonNoRecvOne_root_sender,
    profiledRawJointHybridCommonToTwoShadow_strict_output]

/-- Strict-left mirror pair equation. -/
theorem profiledRawJointHybridCommon_strictLeft_root_pair
    (control : CommonControl) (input : In₁ × In₂) :
    ((profiledRawJointHybridCommonToOneShadow A strategy hwin control input.1
        input.2).1,
      (profiledRawJointHybridCommonNoRecvTwo A strategy hwin control input.2).1)
      =
      (pairedLeftInformedForRow .both
          (profiledRawJointHybridShadowLeftRootRecord A strategy hwin control
            input).2.1.physical,
        (profiledRawJointHybridShadowLeftRootRecord A strategy hwin control
          input).2.2) := by
  rw [profiledRawJointHybridCommonNoRecvTwo_root_sender,
    profiledRawJointHybridCommonToOneShadow_strict_output]

/-- Total local alignment of a delivered left owner with process one's stored
strict shadow.  On unreachable mismatched controls the local table restarts
the selected controller at its root. -/
noncomputable def profiledRawJointHybridLeftGuardOwnerFor
    (shadow : ProfiledRawJointHybridOneShadow A strategy hwin)
    (owner : ProfiledRawJointHybridLeftGuardOwner A strategy hwin) :
    (profiledRawJointHybridShadowLeftController A strategy hwin
      shadow.origin).Control := by
  classical
  exact if h : owner.origin = shadow.origin then h ▸ owner.owner
    else (profiledRawJointHybridShadowLeftController A strategy hwin
      shadow.origin).initial

/-- Process-two/right mirror alignment. -/
noncomputable def profiledRawJointHybridRightGuardOwnerFor
    (shadow : ProfiledRawJointHybridTwoShadow A strategy hwin)
    (owner : ProfiledRawJointHybridRightGuardOwner A strategy hwin) :
    (profiledRawJointHybridShadowRightController A strategy hwin
      shadow.origin).Control := by
  classical
  exact if h : owner.origin = shadow.origin then h ▸ owner.owner
    else (profiledRawJointHybridShadowRightController A strategy hwin
      shadow.origin).initial

/-- Once a delivered owner resolves the ambiguity, process one retains only
the strict-left guarded receiver state. -/
structure ProfiledRawJointHybridLeftStrictReceiver where
  origin : CommonControl
  receiver :
    (ProfiledRawJointHybridShadowLeftMonitor A strategy hwin origin).State

/-- Process-two strict-right mirror. -/
structure ProfiledRawJointHybridRightStrictReceiver where
  origin : CommonControl
  receiver :
    (ProfiledRawJointHybridShadowRightMonitor A strategy hwin origin).State

noncomputable instance profiledRawJointHybridLeftStrictReceiverFintype :
    Fintype (ProfiledRawJointHybridLeftStrictReceiver A strategy hwin) := by
  classical
  let Rep := Σ control : CommonControl,
    (ProfiledRawJointHybridShadowLeftMonitor A strategy hwin control).State
  let equiv : ProfiledRawJointHybridLeftStrictReceiver A strategy hwin ≃ Rep := {
    toFun := fun state ↦ ⟨state.origin, state.receiver⟩
    invFun := fun state ↦ ⟨state.1, state.2⟩
    left_inv := by intro state; cases state; rfl
    right_inv := by intro state; rcases state with ⟨a, b⟩; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

noncomputable instance profiledRawJointHybridRightStrictReceiverFintype :
    Fintype (ProfiledRawJointHybridRightStrictReceiver A strategy hwin) := by
  classical
  let Rep := Σ control : CommonControl,
    (ProfiledRawJointHybridShadowRightMonitor A strategy hwin control).State
  let equiv : ProfiledRawJointHybridRightStrictReceiver A strategy hwin ≃ Rep := {
    toFun := fun state ↦ ⟨state.origin, state.receiver⟩
    invFun := fun state ↦ ⟨state.1, state.2⟩
    left_inv := by intro state; cases state; rfl
    right_inv := by intro state; rcases state with ⟨a, b⟩; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

/-- A delivered left owner resolves process one's shadow and continues the
strict receiver.  The function sees only the two local controls and the two
delivered inputs. -/
noncomputable def profiledRawJointHybridOneShadowRecvLeftOwner
    (shadow : ProfiledRawJointHybridOneShadow A strategy hwin)
    (owner : ProfiledRawJointHybridLeftGuardOwner A strategy hwin)
    (ownInput : In₁) (deliveredInput : In₂) :
    Out₁ × ProfiledRawJointHybridLeftStrictReceiver A strategy hwin :=
  let monitor := ProfiledRawJointHybridShadowLeftMonitor A strategy hwin
    shadow.origin
  let controller := profiledRawJointHybridShadowLeftController A strategy hwin
    shadow.origin
  let ownerControl := profiledRawJointHybridLeftGuardOwnerFor A strategy hwin
    shadow owner
  let label := controller.labelOf ownerControl
  let output := label.2 shadow.strictReceiver (ownInput, deliveredInput)
  (pairedLeftInformedForRow .both output.physical,
    ⟨shadow.origin,
      monitor.step shadow.strictReceiver
        ((ownInput, deliveredInput), output, label.1 deliveredInput)⟩)

/-- Delivered right-owner mirror. -/
noncomputable def profiledRawJointHybridTwoShadowRecvRightOwner
    (shadow : ProfiledRawJointHybridTwoShadow A strategy hwin)
    (owner : ProfiledRawJointHybridRightGuardOwner A strategy hwin)
    (ownInput : In₂) (deliveredInput : In₁) :
    Out₂ × ProfiledRawJointHybridRightStrictReceiver A strategy hwin :=
  let monitor := ProfiledRawJointHybridShadowRightMonitor A strategy hwin
    shadow.origin
  let controller := profiledRawJointHybridShadowRightController A strategy hwin
    shadow.origin
  let ownerControl := profiledRawJointHybridRightGuardOwnerFor A strategy hwin
    shadow owner
  let label := controller.labelOf ownerControl
  let output := label.2 shadow.strictReceiver (ownInput, deliveredInput)
  (pairedRightInformedForRow .both output.physical,
    ⟨shadow.origin,
      monitor.step shadow.strictReceiver
        ((ownInput, deliveredInput), output, label.1 deliveredInput)⟩)

@[simp] theorem profiledRawJointHybridOneShadowRecvLeftOwner_origin
    (shadow : ProfiledRawJointHybridOneShadow A strategy hwin)
    (owner : ProfiledRawJointHybridLeftGuardOwner A strategy hwin)
    (ownInput : In₁) (deliveredInput : In₂) :
    (profiledRawJointHybridOneShadowRecvLeftOwner A strategy hwin shadow owner
      ownInput deliveredInput).2.origin = shadow.origin :=
  rfl

@[simp] theorem profiledRawJointHybridTwoShadowRecvRightOwner_origin
    (shadow : ProfiledRawJointHybridTwoShadow A strategy hwin)
    (owner : ProfiledRawJointHybridRightGuardOwner A strategy hwin)
    (ownInput : In₂) (deliveredInput : In₁) :
    (profiledRawJointHybridTwoShadowRecvRightOwner A strategy hwin shadow owner
      ownInput deliveredInput).2.origin = shadow.origin :=
  rfl

/-! ## A no-receive from a shadow uses the one-round replacement -/

/-- Process one's canonical right-live replacement tag. -/
def ProfiledRawJointHybridOneShadow.rightReplacementTag
    (shadow : ProfiledRawJointHybridOneShadow A strategy hwin) :
    ProfiledRawJointHybridCommonTaggedReplacement A strategy hwin :=
  ⟨shadow.origin, shadow.input, .inl ()⟩

/-- Process-two's canonical left-live replacement tag. -/
def ProfiledRawJointHybridTwoShadow.leftReplacementTag
    (shadow : ProfiledRawJointHybridTwoShadow A strategy hwin) :
    ProfiledRawJointHybridCommonTaggedReplacement A strategy hwin :=
  ⟨shadow.origin, shadow.input, .inr ()⟩

/-- The exact narrowed left root stores the original installed move's
strict-left child, not merely a target with the same active slot. -/
theorem profiledRawJointHybridShadowLeftRoot_strictChild
    (control : CommonControl) (input : In₁ × In₂) :
    ((profiledRawJointHybridShadowLeftRootRecord A strategy hwin control
      input).2.1.target .both).1 =
      profiledRawJointOneSidedNext A control.2.incidenceCode
        (profiledRawJointHybridCommonControlInstalled A strategy hwin control
          ).rawMove
        (profiledRawJointCommonOneRoundStrictLeft input) := by
  simpa [profiledRawJointHybridShadowLeftRootRecord,
    profiledRawJointHybridShadowLeftController,
    profiledRawJointHybridShadowLeftPinnedPolicy,
    TransitionRationalTree.labeledTree, TransitionRationalTree.controlAt] using
    profiledRawJointHybridExactLeftController_root_strictChild A hwin
      (profiledRawJointHybridCommonControlInstalled A strategy hwin control)
      input

/-- Right-root mirror exact child. -/
theorem profiledRawJointHybridShadowRightRoot_strictChild
    (control : CommonControl) (input : In₁ × In₂) :
    ((profiledRawJointHybridShadowRightRootRecord A strategy hwin control
      input).2.1.target .both).1 =
      profiledRawJointOneSidedNext A control.2.incidenceCode
        (profiledRawJointHybridCommonControlInstalled A strategy hwin control
          ).rawMove
        (profiledRawJointCommonOneRoundStrictRight input) := by
  simpa [profiledRawJointHybridShadowRightRootRecord,
    profiledRawJointHybridShadowRightController,
    profiledRawJointHybridShadowRightPinnedPolicy,
    TransitionRationalTree.labeledTree, TransitionRationalTree.controlAt] using
    profiledRawJointHybridExactRightController_root_strictChild A hwin
      (profiledRawJointHybridCommonControlInstalled A strategy hwin control)
      (input.2, input.1)

/-- Cross-paired handoff: process one's stored left strict target is exactly
the code of the canonical right-live replacement used by its next `noRecv`. -/
theorem profiledRawJointHybridShadowLeftRoot_eq_rightReplacement
    (control : CommonControl) (input : In₁ × In₂) :
    ((profiledRawJointHybridShadowLeftRootRecord A strategy hwin control
      input).2.1.target .both).1 =
      (profiledRawJointHybridCommonTaggedReplacementSource A strategy hwin
        ⟨control, input, .inl ()⟩).code A := by
  rw [profiledRawJointHybridShadowLeftRoot_strictChild]
  exact (profiledRawJointHybridCommonRightReplacementSource_code A
    (profiledRawJointHybridCommonControlInstalled A strategy hwin control)
    input).symm

/-- Process-two mirror: the right strict target is the canonical left-live
replacement code. -/
theorem profiledRawJointHybridShadowRightRoot_eq_leftReplacement
    (control : CommonControl) (input : In₁ × In₂) :
    ((profiledRawJointHybridShadowRightRootRecord A strategy hwin control
      input).2.1.target .both).1 =
      (profiledRawJointHybridCommonTaggedReplacementSource A strategy hwin
        ⟨control, input, .inr ()⟩).code A := by
  rw [profiledRawJointHybridShadowRightRoot_strictChild]
  exact (profiledRawJointHybridCommonLeftReplacementSource_code A
    (profiledRawJointHybridCommonControlInstalled A strategy hwin control)
    input).symm

/-- Specialized to the runtime process-one shadow, the controller-emitted
target and the no-receive replacement tag have identical finite codes. -/
theorem profiledRawJointHybridCommonToOneShadow_target_eq_noRecvReplacement
    (control : CommonControl) (input : In₁ × In₂) :
    ((profiledRawJointHybridShadowLeftRootRecord A strategy hwin control
      input).2.1.target .both).1 =
      (profiledRawJointHybridCommonTaggedReplacementSource A strategy hwin
        ((profiledRawJointHybridCommonToOneShadow A strategy hwin control
          input.1 input.2).2.rightReplacementTag A strategy hwin)).code A := by
  simpa [ProfiledRawJointHybridOneShadow.rightReplacementTag] using
    profiledRawJointHybridShadowLeftRoot_eq_rightReplacement A strategy hwin
      control input

/-- Runtime process-two mirror handoff. -/
theorem profiledRawJointHybridCommonToTwoShadow_target_eq_noRecvReplacement
    (control : CommonControl) (input : In₁ × In₂) :
    ((profiledRawJointHybridShadowRightRootRecord A strategy hwin control
      input).2.1.target .both).1 =
      (profiledRawJointHybridCommonTaggedReplacementSource A strategy hwin
        ((profiledRawJointHybridCommonToTwoShadow A strategy hwin control
          input.2 input.1).2.leftReplacementTag A strategy hwin)).code A := by
  simpa [ProfiledRawJointHybridTwoShadow.leftReplacementTag] using
    profiledRawJointHybridShadowRightRoot_eq_leftReplacement A strategy hwin
      control input

abbrev ProfiledRawJointHybridOneReplacementOwnerAt
    (shadow : ProfiledRawJointHybridOneShadow A strategy hwin) :=
  ProfiledRawJointUnitRightPolicyOwnerControl A strategy
    (profiledRawJointHybridCommonTaggedReplacementSource A strategy hwin
      (shadow.rightReplacementTag A strategy hwin))
    (profiledRawJointHybridCommonTaggedReplacementPolicy A strategy hwin
      (shadow.rightReplacementTag A strategy hwin))
    (profiledRawJointHybridCommonTaggedReplacementControllerBank A strategy hwin
      (shadow.rightReplacementTag A strategy hwin))

abbrev ProfiledRawJointHybridTwoReplacementOwnerAt
    (shadow : ProfiledRawJointHybridTwoShadow A strategy hwin) :=
  ProfiledRawJointUnitLeftPolicyOwnerControl A strategy
    (profiledRawJointHybridCommonTaggedReplacementSource A strategy hwin
      (shadow.leftReplacementTag A strategy hwin))
    (profiledRawJointHybridCommonTaggedReplacementPolicy A strategy hwin
      (shadow.leftReplacementTag A strategy hwin))
    (profiledRawJointHybridCommonTaggedReplacementControllerBank A strategy hwin
      (shadow.leftReplacementTag A strategy hwin))

/-- The finite process-one owner installed after a shadow `noRecv`. -/
structure ProfiledRawJointHybridOneReplacementOwner where
  shadow : ProfiledRawJointHybridOneShadow A strategy hwin
  owner : ProfiledRawJointHybridOneReplacementOwnerAt A strategy hwin shadow

/-- Process-two mirror. -/
structure ProfiledRawJointHybridTwoReplacementOwner where
  shadow : ProfiledRawJointHybridTwoShadow A strategy hwin
  owner : ProfiledRawJointHybridTwoReplacementOwnerAt A strategy hwin shadow

noncomputable instance profiledRawJointHybridOneReplacementOwnerFintype :
    Fintype (ProfiledRawJointHybridOneReplacementOwner A strategy hwin) := by
  classical
  let Rep := Σ shadow : ProfiledRawJointHybridOneShadow A strategy hwin,
    ProfiledRawJointHybridOneReplacementOwnerAt A strategy hwin shadow
  let equiv : ProfiledRawJointHybridOneReplacementOwner A strategy hwin ≃
      Rep := {
    toFun := fun state ↦ ⟨state.shadow, state.owner⟩
    invFun := fun state ↦ ⟨state.1, state.2⟩
    left_inv := by intro state; cases state; rfl
    right_inv := by intro state; rcases state with ⟨a, b⟩; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

noncomputable instance profiledRawJointHybridTwoReplacementOwnerFintype :
    Fintype (ProfiledRawJointHybridTwoReplacementOwner A strategy hwin) := by
  classical
  let Rep := Σ shadow : ProfiledRawJointHybridTwoShadow A strategy hwin,
    ProfiledRawJointHybridTwoReplacementOwnerAt A strategy hwin shadow
  let equiv : ProfiledRawJointHybridTwoReplacementOwner A strategy hwin ≃
      Rep := {
    toFun := fun state ↦ ⟨state.shadow, state.owner⟩
    invFun := fun state ↦ ⟨state.1, state.2⟩
    left_inv := by intro state; cases state; rfl
    right_inv := by intro state; rcases state with ⟨a, b⟩; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

/-- Honest `noRecv` at process one discards the false strict shadow and starts
the canonical right-live replacement root. -/
noncomputable def profiledRawJointHybridOneShadowNoRecv
    (shadow : ProfiledRawJointHybridOneShadow A strategy hwin)
    (input : In₁) :
    Out₁ × ProfiledRawJointHybridOneReplacementOwner A strategy hwin :=
  let tag := shadow.rightReplacementTag A strategy hwin
  let source := profiledRawJointHybridCommonTaggedReplacementSource A strategy
    hwin tag
  let policy := profiledRawJointHybridCommonTaggedReplacementPolicy A strategy
    hwin tag
  let bank := profiledRawJointHybridCommonTaggedReplacementControllerBank A
    strategy hwin tag
  let root := profiledRawJointHybridCommonTaggedReplacementRoot A strategy hwin
    tag
  let owner := initialProfiledRawJointUnitRightPolicyOwner A strategy source
    policy bank root
  let next := stepProfiledRawJointUnitRightPolicyOwner A strategy source policy
    bank owner input
  (next.1, ⟨shadow, next.2⟩)

/-- Process-two left-live mirror. -/
noncomputable def profiledRawJointHybridTwoShadowNoRecv
    (shadow : ProfiledRawJointHybridTwoShadow A strategy hwin)
    (input : In₂) :
    Out₂ × ProfiledRawJointHybridTwoReplacementOwner A strategy hwin :=
  let tag := shadow.leftReplacementTag A strategy hwin
  let source := profiledRawJointHybridCommonTaggedReplacementSource A strategy
    hwin tag
  let policy := profiledRawJointHybridCommonTaggedReplacementPolicy A strategy
    hwin tag
  let bank := profiledRawJointHybridCommonTaggedReplacementControllerBank A
    strategy hwin tag
  let root := profiledRawJointHybridCommonTaggedReplacementRoot A strategy hwin
    tag
  let owner := initialProfiledRawJointUnitLeftPolicyOwner A strategy source
    policy bank root
  let next := stepProfiledRawJointUnitLeftPolicyOwner A strategy source policy
    bank owner input
  (next.1, ⟨shadow, next.2⟩)

@[simp] theorem profiledRawJointHybridOneShadowNoRecv_tag
    (shadow : ProfiledRawJointHybridOneShadow A strategy hwin)
    (input : In₁) :
    (ProfiledRawJointHybridOneReplacementOwner.shadow
      (profiledRawJointHybridOneShadowNoRecv A strategy hwin shadow input).2
      ).rightReplacementTag A strategy hwin =
      shadow.rightReplacementTag A strategy hwin :=
  rfl

@[simp] theorem profiledRawJointHybridTwoShadowNoRecv_tag
    (shadow : ProfiledRawJointHybridTwoShadow A strategy hwin)
    (input : In₂) :
    (ProfiledRawJointHybridTwoReplacementOwner.shadow
      (profiledRawJointHybridTwoShadowNoRecv A strategy hwin shadow input).2
      ).leftReplacementTag A strategy hwin =
      shadow.leftReplacementTag A strategy hwin :=
  rfl

/-! ## The thin local front table -/

/--
The complete executable common/first-strict front, collected as one adapter.
Its function types document the locality boundary mechanically: a non-receive
gets only the own input, and a receive gets the two delivered local controls
and inputs.  No field accepts `Graph`, a side, or a leader witness.

The ordinary recurrent transitions below the replacement owner are supplied
by `ProfiledRawJointUnitPolicyControllerBank`; this table stops exactly at
that already-proved interface.
-/
structure ProfiledRawJointHybridLeaderFreeShadowTable where
  commonRecvOne : CommonControl → In₁ → In₂ →
    Out₁ × ProfiledRawJointHybridOneShadow A strategy hwin
  commonRecvTwo : CommonControl → In₂ → In₁ →
    Out₂ × ProfiledRawJointHybridTwoShadow A strategy hwin
  commonNoRecvOne : CommonControl → In₁ →
    Out₁ × ProfiledRawJointHybridRightGuardOwner A strategy hwin
  commonNoRecvTwo : CommonControl → In₂ →
    Out₂ × ProfiledRawJointHybridLeftGuardOwner A strategy hwin
  shadowRecvCommonOne :
    ProfiledRawJointHybridOneShadow A strategy hwin →
    ProfiledRawJointHybridTwoShadow A strategy hwin → In₁ → In₂ →
    Out₁ × ProfiledRawJointHybridOneShadow A strategy hwin
  shadowRecvCommonTwo :
    ProfiledRawJointHybridTwoShadow A strategy hwin →
    ProfiledRawJointHybridOneShadow A strategy hwin → In₂ → In₁ →
    Out₂ × ProfiledRawJointHybridTwoShadow A strategy hwin
  shadowRecvOwnerOne :
    ProfiledRawJointHybridOneShadow A strategy hwin →
    ProfiledRawJointHybridLeftGuardOwner A strategy hwin → In₁ → In₂ →
    Out₁ × ProfiledRawJointHybridLeftStrictReceiver A strategy hwin
  shadowRecvOwnerTwo :
    ProfiledRawJointHybridTwoShadow A strategy hwin →
    ProfiledRawJointHybridRightGuardOwner A strategy hwin → In₂ → In₁ →
    Out₂ × ProfiledRawJointHybridRightStrictReceiver A strategy hwin
  shadowNoRecvOne : ProfiledRawJointHybridOneShadow A strategy hwin → In₁ →
    Out₁ × ProfiledRawJointHybridOneReplacementOwner A strategy hwin
  shadowNoRecvTwo : ProfiledRawJointHybridTwoShadow A strategy hwin → In₂ →
    Out₂ × ProfiledRawJointHybridTwoReplacementOwner A strategy hwin

/-- The canonical table assembled from the exact typed maps above. -/
noncomputable def profiledRawJointHybridLeaderFreeShadowTable :
    ProfiledRawJointHybridLeaderFreeShadowTable A strategy hwin where
  commonRecvOne :=
    profiledRawJointHybridCommonToOneShadow A strategy hwin
  commonRecvTwo :=
    profiledRawJointHybridCommonToTwoShadow A strategy hwin
  commonNoRecvOne :=
    profiledRawJointHybridCommonNoRecvOne A strategy hwin
  commonNoRecvTwo :=
    profiledRawJointHybridCommonNoRecvTwo A strategy hwin
  shadowRecvCommonOne :=
    profiledRawJointHybridOneShadowRecvCommon A strategy hwin
  shadowRecvCommonTwo :=
    profiledRawJointHybridTwoShadowRecvCommon A strategy hwin
  shadowRecvOwnerOne :=
    profiledRawJointHybridOneShadowRecvLeftOwner A strategy hwin
  shadowRecvOwnerTwo :=
    profiledRawJointHybridTwoShadowRecvRightOwner A strategy hwin
  shadowNoRecvOne :=
    profiledRawJointHybridOneShadowNoRecv A strategy hwin
  shadowNoRecvTwo :=
    profiledRawJointHybridTwoShadowNoRecv A strategy hwin

@[simp] theorem profiledRawJointHybridLeaderFreeShadowTable_commonRecvOne
    (control : CommonControl) (own : In₁) (delivered : In₂) :
    (profiledRawJointHybridLeaderFreeShadowTable A strategy hwin).commonRecvOne
        control own delivered =
      profiledRawJointHybridCommonToOneShadow A strategy hwin control own
        delivered :=
  rfl

@[simp] theorem profiledRawJointHybridLeaderFreeShadowTable_shadowNoRecvOne
    (shadow : ProfiledRawJointHybridOneShadow A strategy hwin)
    (input : In₁) :
    (profiledRawJointHybridLeaderFreeShadowTable A strategy hwin).shadowNoRecvOne
        shadow input =
      profiledRawJointHybridOneShadowNoRecv A strategy hwin shadow input :=
  rfl

@[simp] theorem profiledRawJointHybridLeaderFreeShadowTable_shadowNoRecvTwo
    (shadow : ProfiledRawJointHybridTwoShadow A strategy hwin)
    (input : In₂) :
    (profiledRawJointHybridLeaderFreeShadowTable A strategy hwin).shadowNoRecvTwo
        shadow input =
      profiledRawJointHybridTwoShadowNoRecv A strategy hwin shadow input :=
  rfl

end

end DetParityAutomaton

end DistributedSynthesis
