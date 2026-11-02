/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatiblePolicyBankLocalPhaseLiveOwnerFibre

/-!
# Finite local carriers for receiver fibres

The receiver-fibre invariant is useful at a delayed boundary only if the
uninformed endpoint can maintain a witness using finite local data.  This file
packages an installed move, its live owner control, and one receiver-monitor
state from the corresponding fibre.  The initial monitor state is selected
from the owner fibre, so its construction needs neither a history nor the
other endpoint's current input.  On a no-receive round the monitor is advanced
with a fixed filler for that unavailable input.

The resulting step uses only the carrier and the endpoint's own input, emits
exactly the installed owner controller's output, and preserves the fibre.
Consequently its next receiver target is accepted by the physical table and
can be resolved by the recurrent bank.  This establishes local realizability
of the replacement payload; decoder integration remains separate.
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

/-! ## Right-table carrier at process one -/

/-- Finite local data consisting of a right physical move, its current owner
control, and a virtual receiver-monitor state over that owner. -/
noncomputable abbrev ProfiledRawJointRightOwnerFibreControl :=
  Sigma fun move : ProfiledRawJointRightPhysicalSiblingMove A ↦
    (move.memberController A false).Control ×
      (profiledRawJointRightPhysicalSiblingMonitor A move.1 false).State

noncomputable instance :
    Fintype (ProfiledRawJointRightOwnerFibreControl A) := by
  classical
  infer_instance

def ProfiledRawJointRightOwnerFibreValid
    (control : ProfiledRawJointRightOwnerFibreControl A) : Prop :=
  ProfiledRawJointRightPhysicalSiblingReceiverFibre A control.1 control.2.1
    control.2.2

/-- Select a virtual receiver state using only the installed move and current
owner control.  Reachability removes the total fallback in the correctness
theorem below. -/
noncomputable def profiledRawJointRightOwnerFibreControlOfOwner
    (owner : ProfiledRawJointRightPhysicalSiblingExceptional A) :
    ProfiledRawJointRightOwnerFibreControl A :=
  ⟨owner.1, owner.2,
    profiledRawJointRightPhysicalSiblingReceiverFibreChoice A owner.1
      owner.2⟩

omit [Inhabited In₁] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointRightOwnerFibreChoiceControl_valid
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (hreachable :
      ProfiledRawJointRightPhysicalSiblingOwnerReachable A move owner) :
    ProfiledRawJointRightOwnerFibreValid A
      ⟨move, owner,
        profiledRawJointRightPhysicalSiblingReceiverFibreChoice A move
          owner⟩ := by
  simpa only [ProfiledRawJointRightOwnerFibreValid] using
    profiledRawJointRightPhysicalSiblingReceiverFibreChoice_mem A move owner
      hreachable

/-- Advance the owner and virtual receiver together.  The receiver is fed a
fixed filler for process two's unavailable input; its output is not used. -/
noncomputable def profiledRawJointRightOwnerFibreNoRecv
    (control : ProfiledRawJointRightOwnerFibreControl A)
    (input : In₁) :
    ProfiledRawJointRightOwnerFibreControl A × Out₁ :=
  let next :=
    profiledRawJointRightPhysicalSiblingReceiverFibreNoRecv A control.1
      control.2.1 control.2.2 input
  (⟨control.1, next⟩,
    ((control.1.memberController A false).labelOf control.2.1).1 input)

omit [Inhabited In₁] [Inhabited Out₁] [Inhabited Out₂] in
/-- The replacement carrier does not alter the endpoint's observable
no-receive output. -/
@[simp] theorem profiledRawJointRightOwnerFibreNoRecv_output
    (control : ProfiledRawJointRightOwnerFibreControl A)
    (input : In₁) :
    (profiledRawJointRightOwnerFibreNoRecv A control input).2 =
      (profiledRawJointRightPhysicalSiblingMemberNoRecvStep A control.1 false
        control.2.1 input).1 :=
  rfl

omit [Inhabited In₁] [Inhabited Out₁] [Inhabited Out₂] in
theorem ProfiledRawJointRightOwnerFibreValid.noRecv
    (control : ProfiledRawJointRightOwnerFibreControl A)
    (hvalid : ProfiledRawJointRightOwnerFibreValid A control)
    (input : In₁) :
    ProfiledRawJointRightOwnerFibreValid A
      (profiledRawJointRightOwnerFibreNoRecv A control input).1 := by
  exact ProfiledRawJointRightPhysicalSiblingReceiverFibre.noRecv A control.1
    control.2.1 control.2.2 hvalid input

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- A locally maintained valid carrier emits only table-allowed targets on a
later receive, for every delivered input and every row. -/
theorem ProfiledRawJointRightOwnerFibreValid.targetSafe
    (control : ProfiledRawJointRightOwnerFibreControl A)
    (hvalid : ProfiledRawJointRightOwnerFibreValid A control)
    (input : In₂ × In₁) (row : PairedEntryRow) :
    profiledRawJointRightPhysicalSiblingAllowed A control.1.1
      ((((control.1.memberController A false).labelOf control.2.1).2
        control.2.2 input).target row) := by
  exact ProfiledRawJointRightPhysicalSiblingReceiverFibre.targetSafe A
    control.1 control.2.1 control.2.2 hvalid input row

/-- The owner in reachable aligned boundary data is reachable by its own
input projection. -/
theorem ProfiledRawJointRecurrentRightBoundaryInvariant.ownerReachable
    (data : ProfiledRawJointRecurrentRightBoundaryData A strategy hwin)
    (hinvariant : ProfiledRawJointRecurrentRightBoundaryInvariant A strategy
      hwin data) :
    ProfiledRawJointRightPhysicalSiblingOwnerReachable A
      (data.receiver A strategy hwin).1 (data.owner A strategy hwin) := by
  dsimp only [ProfiledRawJointRecurrentRightBoundaryInvariant] at hinvariant
  rcases hinvariant with
    ⟨_currentCode, _root, past, _hreachable, _hcode, _hroot, _hmove,
      howner, _hmonitor⟩
  exact ⟨senderWord past, howner⟩

/-- After its genuine local boundary step, the endpoint can initialize a
valid carrier from the advanced owner alone. -/
theorem ProfiledRawJointRecurrentRightBoundaryInvariant.advancedOwnerFibreControl_valid
    (data : ProfiledRawJointRecurrentRightBoundaryData A strategy hwin)
    (hinvariant : ProfiledRawJointRecurrentRightBoundaryInvariant A strategy
      hwin data)
    (input : In₁) :
    let move := (data.receiver A strategy hwin).1
    let advancedOwner : ProfiledRawJointRightPhysicalSiblingExceptional A :=
      ⟨move, (move.memberController A false).step
        (data.owner A strategy hwin) input⟩
    ProfiledRawJointRightOwnerFibreValid A
      ⟨advancedOwner.1, advancedOwner.2,
        profiledRawJointRightPhysicalSiblingReceiverFibreChoice A
          advancedOwner.1 advancedOwner.2⟩ := by
  dsimp only
  apply profiledRawJointRightOwnerFibreChoiceControl_valid A
  exact (hinvariant.ownerReachable A strategy hwin data).step A _ _ input

/-! ### Reconstruction of decoder-facing aligned data -/

/-- Install a delivered right fibre carrier as ordinary aligned right boundary
data.  The retained opposite receiver is irrelevant to the active right
invariant. -/
noncomputable def ProfiledRawJointRightOwnerFibreControl.boundaryData
    (control : ProfiledRawJointRightOwnerFibreControl A)
    (state :
      ProfiledRawJointOneSidedPhysicalCompatibleBankControl A strategy hwin)
    (row : PairedEntryRow)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A) :
    ProfiledRawJointRecurrentRightBoundaryData A strategy hwin :=
  (state, ⟨⟨control.1, row, control.2.2, none⟩, control.2.1⟩, oldReceiver)

/-- A valid delivered right fibre carrier reconstructs the full existing
matched-prefix invariant.  No equality with the receiver state previously
stored at the other endpoint is required. -/
theorem ProfiledRawJointRightOwnerFibreValid.boundaryInvariant
    (control : ProfiledRawJointRightOwnerFibreControl A)
    (hvalid : ProfiledRawJointRightOwnerFibreValid A control)
    (state :
      ProfiledRawJointOneSidedPhysicalCompatibleBankControl A strategy hwin)
    (hstate :
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcurrentCode : state.2.1.1 = currentCode)
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .right currentCode () =
      some root)
    (hmove : state.2.1.2.1 = some control.1)
    (row : PairedEntryRow)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A) :
    ProfiledRawJointRecurrentRightBoundaryInvariant A strategy hwin
      (control.boundaryData A strategy hwin state row oldReceiver) := by
  rcases hvalid with ⟨past, howner, hreceiver⟩
  refine ⟨currentCode, root, past, hstate, hcurrentCode, hroot, hmove, ?_, ?_⟩
  · exact howner
  · exact hreceiver

/-! ## Left-table carrier at process two -/

noncomputable abbrev ProfiledRawJointLeftOwnerFibreControl :=
  Sigma fun move : ProfiledRawJointLeftPhysicalSiblingMove A ↦
    (move.memberController A false).Control ×
      (profiledRawJointLeftPhysicalSiblingMonitor A move.1 false).State

noncomputable instance :
    Fintype (ProfiledRawJointLeftOwnerFibreControl A) := by
  classical
  infer_instance

def ProfiledRawJointLeftOwnerFibreValid
    (control : ProfiledRawJointLeftOwnerFibreControl A) : Prop :=
  ProfiledRawJointLeftPhysicalSiblingReceiverFibre A control.1 control.2.1
    control.2.2

noncomputable def profiledRawJointLeftOwnerFibreControlOfOwner
    (owner : ProfiledRawJointLeftPhysicalSiblingExceptional A) :
    ProfiledRawJointLeftOwnerFibreControl A :=
  ⟨owner.1, owner.2,
    profiledRawJointLeftPhysicalSiblingReceiverFibreChoice A owner.1
      owner.2⟩

omit [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointLeftOwnerFibreChoiceControl_valid
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (hreachable :
      ProfiledRawJointLeftPhysicalSiblingOwnerReachable A move owner) :
    ProfiledRawJointLeftOwnerFibreValid A
      ⟨move, owner,
        profiledRawJointLeftPhysicalSiblingReceiverFibreChoice A move
          owner⟩ := by
  simpa only [ProfiledRawJointLeftOwnerFibreValid] using
    profiledRawJointLeftPhysicalSiblingReceiverFibreChoice_mem A move owner
      hreachable

noncomputable def profiledRawJointLeftOwnerFibreNoRecv
    (control : ProfiledRawJointLeftOwnerFibreControl A)
    (input : In₂) :
    ProfiledRawJointLeftOwnerFibreControl A × Out₂ :=
  let next :=
    profiledRawJointLeftPhysicalSiblingReceiverFibreNoRecv A control.1
      control.2.1 control.2.2 input
  (⟨control.1, next⟩,
    ((control.1.memberController A false).labelOf control.2.1).1 input)

omit [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledRawJointLeftOwnerFibreNoRecv_output
    (control : ProfiledRawJointLeftOwnerFibreControl A)
    (input : In₂) :
    (profiledRawJointLeftOwnerFibreNoRecv A control input).2 =
      (profiledRawJointLeftPhysicalSiblingMemberNoRecvStep A control.1 false
        control.2.1 input).1 :=
  rfl

omit [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem ProfiledRawJointLeftOwnerFibreValid.noRecv
    (control : ProfiledRawJointLeftOwnerFibreControl A)
    (hvalid : ProfiledRawJointLeftOwnerFibreValid A control)
    (input : In₂) :
    ProfiledRawJointLeftOwnerFibreValid A
      (profiledRawJointLeftOwnerFibreNoRecv A control input).1 := by
  exact ProfiledRawJointLeftPhysicalSiblingReceiverFibre.noRecv A control.1
    control.2.1 control.2.2 hvalid input

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem ProfiledRawJointLeftOwnerFibreValid.targetSafe
    (control : ProfiledRawJointLeftOwnerFibreControl A)
    (hvalid : ProfiledRawJointLeftOwnerFibreValid A control)
    (input : In₁ × In₂) (row : PairedEntryRow) :
    profiledRawJointLeftPhysicalSiblingAllowed A control.1.1
      ((((control.1.memberController A false).labelOf control.2.1).2
        control.2.2 input).target row) := by
  exact ProfiledRawJointLeftPhysicalSiblingReceiverFibre.targetSafe A
    control.1 control.2.1 control.2.2 hvalid input row

theorem ProfiledRawJointRecurrentLeftBoundaryInvariant.ownerReachable
    (data : ProfiledRawJointRecurrentLeftBoundaryData A strategy hwin)
    (hinvariant : ProfiledRawJointRecurrentLeftBoundaryInvariant A strategy
      hwin data) :
    ProfiledRawJointLeftPhysicalSiblingOwnerReachable A
      (data.receiver A strategy hwin).1 (data.owner A strategy hwin) := by
  dsimp only [ProfiledRawJointRecurrentLeftBoundaryInvariant] at hinvariant
  rcases hinvariant with
    ⟨_currentCode, _root, past, _hreachable, _hcode, _hroot, _hmove,
      howner, _hmonitor⟩
  exact ⟨senderWord past, howner⟩

theorem ProfiledRawJointRecurrentLeftBoundaryInvariant.advancedOwnerFibreControl_valid
    (data : ProfiledRawJointRecurrentLeftBoundaryData A strategy hwin)
    (hinvariant : ProfiledRawJointRecurrentLeftBoundaryInvariant A strategy
      hwin data)
    (input : In₂) :
    let move := (data.receiver A strategy hwin).1
    let advancedOwner : ProfiledRawJointLeftPhysicalSiblingExceptional A :=
      ⟨move, (move.memberController A false).step
        (data.owner A strategy hwin) input⟩
    ProfiledRawJointLeftOwnerFibreValid A
      ⟨advancedOwner.1, advancedOwner.2,
        profiledRawJointLeftPhysicalSiblingReceiverFibreChoice A
          advancedOwner.1 advancedOwner.2⟩ := by
  dsimp only
  apply profiledRawJointLeftOwnerFibreChoiceControl_valid A
  exact (hinvariant.ownerReachable A strategy hwin data).step A _ _ input

noncomputable def ProfiledRawJointLeftOwnerFibreControl.boundaryData
    (control : ProfiledRawJointLeftOwnerFibreControl A)
    (state :
      ProfiledRawJointOneSidedPhysicalCompatibleBankControl A strategy hwin)
    (row : PairedEntryRow)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A) :
    ProfiledRawJointRecurrentLeftBoundaryData A strategy hwin :=
  (state, ⟨⟨control.1, row, control.2.2, none⟩, control.2.1⟩, oldReceiver)

theorem ProfiledRawJointLeftOwnerFibreValid.boundaryInvariant
    (control : ProfiledRawJointLeftOwnerFibreControl A)
    (hvalid : ProfiledRawJointLeftOwnerFibreValid A control)
    (state :
      ProfiledRawJointOneSidedPhysicalCompatibleBankControl A strategy hwin)
    (hstate :
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcurrentCode : state.2.1.1 = currentCode)
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .left currentCode () =
      some root)
    (hmove : state.2.1.2.2 = some control.1)
    (row : PairedEntryRow)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A) :
    ProfiledRawJointRecurrentLeftBoundaryInvariant A strategy hwin
      (control.boundaryData A strategy hwin state row oldReceiver) := by
  rcases hvalid with ⟨past, howner, hreceiver⟩
  refine ⟨currentCode, root, past, hstate, hcurrentCode, hroot, hmove, ?_, ?_⟩
  · exact howner
  · exact hreceiver

end

end DetParityAutomaton

end DistributedSynthesis
