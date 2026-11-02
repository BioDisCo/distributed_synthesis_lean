/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Library.Distributed.Execution

/-! # Finite paired Moore controllers

Local finite-state interfaces and simultaneous round updates, independent of
synthesis or epoch adapters. Outputs are read from post-round controls; a blind
transition sees only its own control and input, and a receive transition sees
both pre-round controls and inputs. No extraction of arbitrary perfect-recall
strategies into finite controllers is asserted.
-/

namespace DistributedSynthesis

universe u v x y b k q p c₁ c₂

/-! ## A genuinely local finite physical controller -/

/-- The executable physical controller interface.  The six transition maps
have exactly the information available in the full-view model.  Outputs are
Moore outputs of the post-round local controls.

This structure contains no graph argument because the local event already
selects `noRecv` or `recv`.  It also contains no branch, bank, epoch side,
leader, or hidden-bit argument. -/
structure FinitePairedPhysicalController
    (In₁ : Type u) (In₂ : Type v) (Out₁ : Type x) (Out₂ : Type y) where
  OneControl : Type c₁
  TwoControl : Type c₂
  oneFinite : Fintype OneControl
  twoFinite : Fintype TwoControl
  initialOne : OneControl
  initialTwo : TwoControl
  noRecvOne : OneControl → In₁ → OneControl
  noRecvTwo : TwoControl → In₂ → TwoControl
  recvOne : OneControl → In₁ → TwoControl → In₂ → OneControl
  recvTwo : TwoControl → In₂ → OneControl → In₁ → TwoControl
  outputOne : OneControl → Out₁
  outputTwo : TwoControl → Out₂

attribute [instance] FinitePairedPhysicalController.oneFinite
  FinitePairedPhysicalController.twoFinite

namespace FinitePairedPhysicalController

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable (controller : FinitePairedPhysicalController.{u, v, x, y, c₁, c₂}
  In₁ In₂ Out₁ Out₂)

/-- Simultaneous physical update.  Both receive maps read the pre-round
controls, exactly as the two delivered full views do. -/
def advanceControls
    (controls : controller.OneControl × controller.TwoControl)
    (round : EnvironmentRound In₁ In₂) :
    controller.OneControl × controller.TwoControl :=
  match round.graph with
  | .left =>
      (controller.recvOne controls.1 round.inputOne controls.2 round.inputTwo,
        controller.noRecvTwo controls.2 round.inputTwo)
  | .right =>
      (controller.noRecvOne controls.1 round.inputOne,
        controller.recvTwo controls.2 round.inputTwo controls.1 round.inputOne)
  | .both =>
      (controller.recvOne controls.1 round.inputOne controls.2 round.inputTwo,
        controller.recvTwo controls.2 round.inputTwo controls.1 round.inputOne)

@[simp] theorem advanceControls_left
    (controls : controller.OneControl × controller.TwoControl)
    (inputOne : In₁) (inputTwo : In₂) :
    controller.advanceControls controls
        { inputOne := inputOne, inputTwo := inputTwo, graph := .left } =
      (controller.recvOne controls.1 inputOne controls.2 inputTwo,
        controller.noRecvTwo controls.2 inputTwo) :=
  rfl

@[simp] theorem advanceControls_right
    (controls : controller.OneControl × controller.TwoControl)
    (inputOne : In₁) (inputTwo : In₂) :
    controller.advanceControls controls
        { inputOne := inputOne, inputTwo := inputTwo, graph := .right } =
      (controller.noRecvOne controls.1 inputOne,
        controller.recvTwo controls.2 inputTwo controls.1 inputOne) :=
  rfl

@[simp] theorem advanceControls_both
    (controls : controller.OneControl × controller.TwoControl)
    (inputOne : In₁) (inputTwo : In₂) :
    controller.advanceControls controls
        { inputOne := inputOne, inputTwo := inputTwo, graph := .both } =
      (controller.recvOne controls.1 inputOne controls.2 inputTwo,
        controller.recvTwo controls.2 inputTwo controls.1 inputOne) :=
  rfl

end FinitePairedPhysicalController

/-! ## The two honest receipt events and the actual epoch clock -/

/-- Process one receives exactly on `left` and `both`. -/
def physicalReceivedOne : Graph → Bool
  | .left => true
  | .right => false
  | .both => true

/-- Process two receives exactly on `right` and `both`. -/
def physicalReceivedTwo : Graph → Bool
  | .left => false
  | .right => true
  | .both => true

@[simp] theorem physicalReceivedOne_left : physicalReceivedOne .left = true :=
  rfl

@[simp] theorem physicalReceivedOne_right :
    physicalReceivedOne .right = false :=
  rfl

@[simp] theorem physicalReceivedOne_both : physicalReceivedOne .both = true :=
  rfl

@[simp] theorem physicalReceivedTwo_left : physicalReceivedTwo .left = false :=
  rfl

@[simp] theorem physicalReceivedTwo_right : physicalReceivedTwo .right = true :=
  rfl

@[simp] theorem physicalReceivedTwo_both : physicalReceivedTwo .both = true :=
  rfl

end DistributedSynthesis
