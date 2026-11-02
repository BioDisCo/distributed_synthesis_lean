/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Library.Distributed.PhysicalControllers

/-!
# Finite paired Mealy controllers as physical Moore controllers

An output-producing local transition is often the most direct executable
presentation of a distributed controller.  The repository's physical adapter
uses Moore outputs of the post-round local controls instead.  This file gives
the exact generic timing bridge: each local Moore control stores the underlying
Mealy control together with that process's last emitted output.

The four transition maps have exactly the information available at their
corresponding local event.  There is no graph, phase, active-side, leader, or
hidden-bit argument.  Mooreization only adds the last local output and never
exposes the other process's stored output to a no-receive transition.
-/

namespace DistributedSynthesis

universe u v x y c₁ c₂

/-- A finite paired local controller whose transitions emit the current
round's output.  Receive transitions read both pre-round controls and inputs;
no-receive transitions read only the process's own control and input. -/
structure FinitePairedMealyController
    (In₁ : Type u) (In₂ : Type v) (Out₁ : Type x) (Out₂ : Type y) where
  OneControl : Type c₁
  TwoControl : Type c₂
  oneFinite : Fintype OneControl
  twoFinite : Fintype TwoControl
  initialOne : OneControl
  initialTwo : TwoControl
  noRecvOne : OneControl → In₁ → OneControl × Out₁
  noRecvTwo : TwoControl → In₂ → TwoControl × Out₂
  recvOne : OneControl → In₁ → TwoControl → In₂ → OneControl × Out₁
  recvTwo : TwoControl → In₂ → OneControl → In₁ → TwoControl × Out₂

attribute [instance] FinitePairedMealyController.oneFinite
  FinitePairedMealyController.twoFinite

namespace FinitePairedMealyController

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable (controller : FinitePairedMealyController.{u, v, x, y, c₁, c₂}
  In₁ In₂ Out₁ Out₂)

/-- Mooreize a paired Mealy controller by retaining each process's last
emitted output in its own finite local control.  The arbitrary initial output
is never used for a physical round: `FinitePairedPhysicalController` reads
outputs after advancing the controls. -/
noncomputable def mooreize
    [Fintype Out₁] [Fintype Out₂] [Inhabited Out₁] [Inhabited Out₂] :
    FinitePairedPhysicalController.{u, v, x, y, max c₁ x, max c₂ y}
      In₁ In₂ Out₁ Out₂ where
  OneControl := controller.OneControl × Out₁
  TwoControl := controller.TwoControl × Out₂
  oneFinite := inferInstance
  twoFinite := inferInstance
  initialOne := (controller.initialOne, default)
  initialTwo := (controller.initialTwo, default)
  noRecvOne := fun state input ↦ controller.noRecvOne state.1 input
  noRecvTwo := fun state input ↦ controller.noRecvTwo state.1 input
  recvOne := fun state input other otherInput ↦
    controller.recvOne state.1 input other.1 otherInput
  recvTwo := fun state input other otherInput ↦
    controller.recvTwo state.1 input other.1 otherInput
  outputOne := Prod.snd
  outputTwo := Prod.snd

@[simp] theorem mooreize_initialOne
    [Fintype Out₁] [Fintype Out₂] [Inhabited Out₁] [Inhabited Out₂] :
    (controller.mooreize).initialOne = (controller.initialOne, default) :=
  rfl

@[simp] theorem mooreize_initialTwo
    [Fintype Out₁] [Fintype Out₂] [Inhabited Out₁] [Inhabited Out₂] :
    (controller.mooreize).initialTwo = (controller.initialTwo, default) :=
  rfl

/-- The post-no-receive process-one Moore output is exactly the Mealy output
emitted by that transition. -/
@[simp] theorem mooreize_noRecvOne_output
    [Fintype Out₁] [Fintype Out₂] [Inhabited Out₁] [Inhabited Out₂]
    (state : (controller.mooreize).OneControl) (input : In₁) :
    (controller.mooreize).outputOne
        ((controller.mooreize).noRecvOne state input) =
      (controller.noRecvOne state.1 input).2 :=
  rfl

/-- Process-two no-receive mirror. -/
@[simp] theorem mooreize_noRecvTwo_output
    [Fintype Out₁] [Fintype Out₂] [Inhabited Out₁] [Inhabited Out₂]
    (state : (controller.mooreize).TwoControl) (input : In₂) :
    (controller.mooreize).outputTwo
        ((controller.mooreize).noRecvTwo state input) =
      (controller.noRecvTwo state.1 input).2 :=
  rfl

/-- The post-receive process-one Moore output is exactly the Mealy output
computed from the two pre-round underlying controls. -/
@[simp] theorem mooreize_recvOne_output
    [Fintype Out₁] [Fintype Out₂] [Inhabited Out₁] [Inhabited Out₂]
    (state : (controller.mooreize).OneControl) (input : In₁)
    (other : (controller.mooreize).TwoControl) (otherInput : In₂) :
    (controller.mooreize).outputOne
        ((controller.mooreize).recvOne state input other otherInput) =
      (controller.recvOne state.1 input other.1 otherInput).2 :=
  rfl

/-- Process-two receive mirror. -/
@[simp] theorem mooreize_recvTwo_output
    [Fintype Out₁] [Fintype Out₂] [Inhabited Out₁] [Inhabited Out₂]
    (state : (controller.mooreize).TwoControl) (input : In₂)
    (other : (controller.mooreize).OneControl) (otherInput : In₁) :
    (controller.mooreize).outputTwo
        ((controller.mooreize).recvTwo state input other otherInput) =
      (controller.recvTwo state.1 input other.1 otherInput).2 :=
  rfl

end FinitePairedMealyController

end DistributedSynthesis
