/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteDependentHeterogeneousPinnedPhysicalAcceptance
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointTargetBlockHandoff

/-!
# Target safety for shared dependent pinned tables

This specializes the generic pin/restart/comap erasure to the profiled right
and left physical target monitors.  A member projection of one shared
dependent table therefore emits only targets legal for that member's original
physical monitor.  No independently rationalized member controller is used.
-/

namespace DistributedSynthesis

universe k u v x y s t

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

variable {Key : Type k} [Inhabited Key] [Fintype Key] [DecidableEq Key]
variable (Target : Key → Type t)
variable [(key : Key) → Inhabited (Target key)]
variable [(key : Key) → Fintype (Target key)]

/-! ## Right member monitors -/

theorem finiteDependentHeterogeneousPinnedRight_targetSafe
    (targetState : (key : Key) → Target key → PairedProfiledTreeState A)
    (Allowed : (key : Key) → Target key → Prop)
    (source : Key → ProfiledRawRightSlot A)
    (start : (key : Key) →
      (profiledRawJointTargetRightBlockMonitor A (Target key)
        (targetState key) (Allowed key) (source key)).State)
    (receiver : (key : Key) → ReceiverBlockStrategy In₂ In₁
      (ProfiledRawJointTargetRightReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) (Target key)))
    (sender : SenderBlockStrategy In₁ Out₁)
    (table : FiniteDependentHeterogeneousPinnedTable
      (fun key ↦ profiledRawJointTargetRightBlockMonitor A (Target key)
        (targetState key) (Allowed key) (source key))
      start receiver sender)
    (key : Key)
    (hstart : start key =
      (profiledRawJointTargetRightBlockMonitor A (Target key)
        (targetState key) (Allowed key) (source key)).initial)
    (env : Nat → In₂ × In₁) (n : Nat) (row : PairedEntryRow) :
    let base := fun key ↦
      profiledRawJointTargetRightBlockMonitor A (Target key)
        (targetState key) (Allowed key) (source key)
    let play := finiteDependentHeterogeneousPinnedMemberPhysicalPlay base start
      receiver sender table key env
    erasePairedProfiledState A
        (targetState key ((play n).2.1.target row)) =
        pairedRightCloseTarget A (((base key).run play n).2.1) row
          (profiledRawJointTargetRightPhysicalLetter A (play n)) ∧
      Allowed key ((play n).2.1.target row) := by
  dsimp only
  let base := fun key ↦
    profiledRawJointTargetRightBlockMonitor A (Target key)
      (targetState key) (Allowed key) (source key)
  let play := finiteDependentHeterogeneousPinnedMemberPhysicalPlay base start
    receiver sender table key env
  have hwins : (base key).WinsPlay play :=
    finiteDependentHeterogeneousPinnedMemberPhysicalPlay_base_wins base start
      receiver sender table key hstart env
  exact profiledRawJointTargetRight_targetsSafe_of_wins A (targetState key)
    (Allowed key) (source key) play hwins n row

/-! ## Left member monitors -/

theorem finiteDependentHeterogeneousPinnedLeft_targetSafe
    (targetState : (key : Key) → Target key → PairedProfiledTreeState A)
    (Allowed : (key : Key) → Target key → Prop)
    (source : Key → ProfiledRawLeftSlot A)
    (start : (key : Key) →
      (profiledRawJointTargetLeftBlockMonitor A (Target key)
        (targetState key) (Allowed key) (source key)).State)
    (receiver : (key : Key) → ReceiverBlockStrategy In₁ In₂
      (ProfiledRawJointTargetLeftReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) (Target key)))
    (sender : SenderBlockStrategy In₂ Out₂)
    (table : FiniteDependentHeterogeneousPinnedTable
      (fun key ↦ profiledRawJointTargetLeftBlockMonitor A (Target key)
        (targetState key) (Allowed key) (source key))
      start receiver sender)
    (key : Key)
    (hstart : start key =
      (profiledRawJointTargetLeftBlockMonitor A (Target key)
        (targetState key) (Allowed key) (source key)).initial)
    (env : Nat → In₁ × In₂) (n : Nat) (row : PairedEntryRow) :
    let base := fun key ↦
      profiledRawJointTargetLeftBlockMonitor A (Target key)
        (targetState key) (Allowed key) (source key)
    let play := finiteDependentHeterogeneousPinnedMemberPhysicalPlay base start
      receiver sender table key env
    erasePairedProfiledState A
        (targetState key ((play n).2.1.target row)) =
        pairedLeftCloseTarget A (((base key).run play n).2.1) row
          (profiledRawJointTargetLeftPhysicalLetter A (play n)) ∧
      Allowed key ((play n).2.1.target row) := by
  dsimp only
  let base := fun key ↦
    profiledRawJointTargetLeftBlockMonitor A (Target key)
      (targetState key) (Allowed key) (source key)
  let play := finiteDependentHeterogeneousPinnedMemberPhysicalPlay base start
    receiver sender table key env
  have hwins : (base key).WinsPlay play :=
    finiteDependentHeterogeneousPinnedMemberPhysicalPlay_base_wins base start
      receiver sender table key hstart env
  exact profiledRawJointTargetLeft_targetsSafe_of_wins A (targetState key)
    (Allowed key) (source key) play hwins n row

end

end DetParityAutomaton

end DistributedSynthesis
