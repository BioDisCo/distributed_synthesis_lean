/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatiblePolicyBankLocalPhaseLiveOwnerFork

/-!
# Branch-sensitive owner bisimulation for the recurrent phase-live carrier

The owner-split audit stores the right semantic alternatives but leaves them
dormant while a separate driver advances.  That shape cannot provide an
arbitrary-prefix readback: after one blind input the driver and either
selected owner are at different clock positions.

This file gives the correct finite carrier.  Its two semantic owner
alternatives advance pointwise.  An all-future output-compatibility proof
makes that update graph-blind: the carrier emits the open candidate's output,
which equals the selected candidate's output at every reachable suffix.  The
receiver fork remains dormant, as required by the delayed receive.

The construction is unconditional once compatibility of the two boundary
owners is supplied.  The generic carrier is useful, but the packet-boundary
constructor at the end is diagnostic: its proposed pair is one owner and its
own one-step successor.  Compatibility of that pair forces shift invariance
of all future sender outputs, which is false for finite controllers in
general.  Consequently this constructor must not be used in the recurrent
proof without an independent semantic shift theorem.  The next viable route
has to preserve the actual asynchronous event prefix (or jointly
rationalize the two post-event endpoint states), rather than identify two
consecutive controls of the old physical table.
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

private abbrev BankControl :=
  ProfiledRawJointOneSidedPhysicalCompatibleBankControl A strategy hwin

/-! ## Right owners: finite runs and all-future compatibility -/

noncomputable def profiledRawJointRecurrentRightOwnerNoRecv
    (owner : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (input : In₁) :
    ProfiledRawJointRightPhysicalSiblingExceptional A × Out₁ :=
  let next := profiledRawJointRightPhysicalSiblingMemberNoRecvStep A
    owner.1 false owner.2 input
  (⟨owner.1, next.2⟩, next.1)

noncomputable def profiledRawJointRecurrentRightOwnerRun :
    ProfiledRawJointRightPhysicalSiblingExceptional A → List In₁ →
      ProfiledRawJointRightPhysicalSiblingExceptional A
  | owner, [] => owner
  | owner, input :: rest =>
      profiledRawJointRecurrentRightOwnerRun
        (profiledRawJointRecurrentRightOwnerNoRecv A owner input).1 rest

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledRawJointRecurrentRightOwnerRun_nil
    (owner : ProfiledRawJointRightPhysicalSiblingExceptional A) :
    profiledRawJointRecurrentRightOwnerRun A owner [] = owner :=
  rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledRawJointRecurrentRightOwnerRun_cons
    (owner : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (input : In₁) (rest : List In₁) :
    profiledRawJointRecurrentRightOwnerRun A owner (input :: rest) =
      profiledRawJointRecurrentRightOwnerRun A
        (profiledRawJointRecurrentRightOwnerNoRecv A owner input).1 rest :=
  rfl

/-- Two right-owner states induce the same output after every finite blind
prefix and on every next private input. -/
def ProfiledRawJointRecurrentRightOwnerCompatible
    (fork : FiniteDelayedFork
      (ProfiledRawJointRightPhysicalSiblingExceptional A)) : Prop :=
  ∀ (past : List In₁) (input : In₁),
    (profiledRawJointRecurrentRightOwnerNoRecv A
      (profiledRawJointRecurrentRightOwnerRun A fork.openControl past)
        input).2 =
      (profiledRawJointRecurrentRightOwnerNoRecv A
        (profiledRawJointRecurrentRightOwnerRun A fork.closedControl past)
          input).2

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- In particular, declaring a right owner compatible with its own
one-step successor forces sender-output shift invariance: after any common
future prefix, the output before the boundary step must equal the output
after that step.  This is a genuine semantic requirement; it does not follow
from finiteness or from the member-independence of one physical sibling
table. -/
theorem
    ProfiledRawJointRecurrentRightOwnerCompatible.successor_forces_shift
    (owner : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (boundaryInput : In₁)
    (hcompatible :
      ProfiledRawJointRecurrentRightOwnerCompatible A
        ⟨owner,
          (profiledRawJointRecurrentRightOwnerNoRecv A owner
            boundaryInput).1⟩)
    (past : List In₁) (input : In₁) :
    (profiledRawJointRecurrentRightOwnerNoRecv A
        (profiledRawJointRecurrentRightOwnerRun A owner past) input).2 =
      (profiledRawJointRecurrentRightOwnerNoRecv A
        (profiledRawJointRecurrentRightOwnerRun A
          (profiledRawJointRecurrentRightOwnerNoRecv A owner
            boundaryInput).1 past) input).2 := by
  exact hcompatible past input

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Pointwise owner evolution preserves all-future compatibility. -/
theorem ProfiledRawJointRecurrentRightOwnerCompatible.step
    (fork : FiniteDelayedFork
      (ProfiledRawJointRightPhysicalSiblingExceptional A))
    (hcompatible : ProfiledRawJointRecurrentRightOwnerCompatible A fork)
    (input : In₁) :
    ProfiledRawJointRecurrentRightOwnerCompatible A
      ⟨(profiledRawJointRecurrentRightOwnerNoRecv A fork.openControl input).1,
        (profiledRawJointRecurrentRightOwnerNoRecv A fork.closedControl
          input).1⟩ := by
  intro past nextInput
  exact hcompatible (input :: past) nextInput

/-! ## The process-one bisimulation carrier -/

structure ProfiledRawJointRecurrentRightToLeftOwnerBisimShared where
  ownerFork :
    FiniteDelayedFork (ProfiledRawJointRightPhysicalSiblingExceptional A)
  receiverFork :
    FiniteDelayedFork
      (ProfiledRawJointRecurrentBankedLeftReceiver A strategy hwin)
  compatible :
    ProfiledRawJointRecurrentRightOwnerCompatible A ownerFork

abbrev ProfiledRawJointRecurrentRightToLeftOwnerBisimPending :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (ProfiledRawJointRecurrentRightToLeftOwnerBisimShared A strategy hwin) Unit

noncomputable instance :
    Fintype
      (ProfiledRawJointRecurrentRightToLeftOwnerBisimShared A strategy hwin) := by
  classical
  let encode := fun state :
      ProfiledRawJointRecurrentRightToLeftOwnerBisimShared A strategy hwin ↦
    (state.ownerFork, state.receiverFork)
  exact Fintype.ofInjective encode (by
    intro left right heq
    cases left
    cases right
    cases heq
    rfl)

noncomputable instance :
    Fintype
      (ProfiledRawJointRecurrentRightToLeftOwnerBisimPending A strategy hwin) := by
  classical
  infer_instance

noncomputable def profiledRawJointRecurrentRightToLeftOwnerBisimOwner
    (control :
      ProfiledRawJointRecurrentRightToLeftOwnerBisimPending A strategy hwin) :
    ProfiledRawJointRightPhysicalSiblingExceptional A :=
  if control.1 then control.2.1.ownerFork.closedControl
  else control.2.1.ownerFork.openControl

noncomputable def profiledRawJointRecurrentRightToLeftOwnerBisimReceiver
    (control :
      ProfiledRawJointRecurrentRightToLeftOwnerBisimPending A strategy hwin) :
    ProfiledRawJointRecurrentBankedLeftReceiver A strategy hwin :=
  if control.1 then control.2.1.receiverFork.closedControl
  else control.2.1.receiverFork.openControl

/-- Both owner candidates advance.  Compatibility makes the output chosen
from the open candidate valid for either hidden member. -/
noncomputable def profiledRawJointRecurrentRightToLeftOwnerBisimStep
    (_member : Bool)
    (shared :
      ProfiledRawJointRecurrentRightToLeftOwnerBisimShared A strategy hwin)
    (input : In₁) :
    ProfiledRawJointRecurrentRightToLeftOwnerBisimShared A strategy hwin ×
      Out₁ :=
  let openNext := profiledRawJointRecurrentRightOwnerNoRecv A
    shared.ownerFork.openControl input
  let closedNext := profiledRawJointRecurrentRightOwnerNoRecv A
    shared.ownerFork.closedControl input
  ({ ownerFork := ⟨openNext.1, closedNext.1⟩
     receiverFork := shared.receiverFork
     compatible :=
       ProfiledRawJointRecurrentRightOwnerCompatible.step A
         shared.ownerFork shared.compatible input },
    openNext.2)

theorem profiledRawJointRecurrentRightToLeftOwnerBisimStep_laws :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberStepLaws
      (profiledRawJointRecurrentRightToLeftOwnerBisimStep A strategy hwin) where
  outputEq := by intro shared input; rfl
  stateEq := by intro shared input; rfl

noncomputable def profiledRawJointRecurrentRightToLeftOwnerBisimNoRecv
    (control :
      ProfiledRawJointRecurrentRightToLeftOwnerBisimPending A strategy hwin)
    (input : In₁) :
    ProfiledRawJointRecurrentRightToLeftOwnerBisimPending A strategy hwin ×
      Out₁ :=
  FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
    (profiledRawJointRecurrentRightToLeftOwnerBisimStep A strategy hwin)
      control input

/-- The selected owner advances exactly once; it no longer lags behind a
separate executable driver. -/
@[simp] theorem profiledRawJointRecurrentRightToLeftOwnerBisimNoRecv_owner
    (control :
      ProfiledRawJointRecurrentRightToLeftOwnerBisimPending A strategy hwin)
    (input : In₁) :
    profiledRawJointRecurrentRightToLeftOwnerBisimOwner A strategy hwin
        (profiledRawJointRecurrentRightToLeftOwnerBisimNoRecv A strategy hwin
          control input).1 =
      (profiledRawJointRecurrentRightOwnerNoRecv A
        (profiledRawJointRecurrentRightToLeftOwnerBisimOwner A strategy hwin
          control) input).1 := by
  rcases control with ⟨member, shared, payload⟩
  cases member <;>
    simp [profiledRawJointRecurrentRightToLeftOwnerBisimNoRecv,
      profiledRawJointRecurrentRightToLeftOwnerBisimStep,
      profiledRawJointRecurrentRightToLeftOwnerBisimOwner,
      FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv]

@[simp] theorem profiledRawJointRecurrentRightToLeftOwnerBisimNoRecv_receiver
    (control :
      ProfiledRawJointRecurrentRightToLeftOwnerBisimPending A strategy hwin)
    (input : In₁) :
    profiledRawJointRecurrentRightToLeftOwnerBisimReceiver A strategy hwin
        (profiledRawJointRecurrentRightToLeftOwnerBisimNoRecv A strategy hwin
          control input).1 =
      profiledRawJointRecurrentRightToLeftOwnerBisimReceiver A strategy hwin
        control := by
  rcases control with ⟨member, shared, payload⟩
  cases member <;>
    simp [profiledRawJointRecurrentRightToLeftOwnerBisimNoRecv,
      profiledRawJointRecurrentRightToLeftOwnerBisimStep,
      profiledRawJointRecurrentRightToLeftOwnerBisimReceiver,
      FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv]

/-- The emitted output is exactly the output of the hidden member's selected
semantic owner, including for the closed member. -/
theorem profiledRawJointRecurrentRightToLeftOwnerBisimNoRecv_output
    (control :
      ProfiledRawJointRecurrentRightToLeftOwnerBisimPending A strategy hwin)
    (input : In₁) :
    (profiledRawJointRecurrentRightToLeftOwnerBisimNoRecv A strategy hwin
      control input).2 =
      (profiledRawJointRecurrentRightOwnerNoRecv A
        (profiledRawJointRecurrentRightToLeftOwnerBisimOwner A strategy hwin
          control) input).2 := by
  rcases control with ⟨member, shared, payload⟩
  cases member with
  | false =>
      simp [profiledRawJointRecurrentRightToLeftOwnerBisimNoRecv,
        profiledRawJointRecurrentRightToLeftOwnerBisimStep,
        profiledRawJointRecurrentRightToLeftOwnerBisimOwner,
        FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv]
  | true =>
      simpa [profiledRawJointRecurrentRightToLeftOwnerBisimNoRecv,
        profiledRawJointRecurrentRightToLeftOwnerBisimStep,
        profiledRawJointRecurrentRightToLeftOwnerBisimOwner,
        profiledRawJointRecurrentRightOwnerRun,
        FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv] using
          shared.compatible [] input

/-- The member-independent relation is closed by the pointwise bisimulation
step. -/
theorem profiledRawJointRecurrentRightToLeftOwnerBisim_blind_noRecv
    (left right :
      ProfiledRawJointRecurrentRightToLeftOwnerBisimPending A strategy hwin)
    (input : In₁)
    (hblind : FiniteAcknowledgedDelayedCarrier.DeferredMemberBlind left
      right) :
    (profiledRawJointRecurrentRightToLeftOwnerBisimNoRecv A strategy hwin left
        input).2 =
        (profiledRawJointRecurrentRightToLeftOwnerBisimNoRecv A strategy hwin
          right input).2 ∧
      FiniteAcknowledgedDelayedCarrier.DeferredMemberBlind
        (profiledRawJointRecurrentRightToLeftOwnerBisimNoRecv A strategy hwin
          left input).1
        (profiledRawJointRecurrentRightToLeftOwnerBisimNoRecv A strategy hwin
          right input).1 := by
  exact FiniteAcknowledgedDelayedCarrier.deferredMemberBlind_noRecv
    (profiledRawJointRecurrentRightToLeftOwnerBisimStep A strategy hwin)
    (profiledRawJointRecurrentRightToLeftOwnerBisimStep_laws A strategy hwin)
    left right input hblind

/-! ### Arbitrary-prefix selected-owner readback -/

noncomputable def profiledRawJointRecurrentRightToLeftOwnerBisimRun :
    ProfiledRawJointRecurrentRightToLeftOwnerBisimPending A strategy hwin →
      List In₁ →
        ProfiledRawJointRecurrentRightToLeftOwnerBisimPending A strategy hwin
  | control, [] => control
  | control, input :: rest =>
      profiledRawJointRecurrentRightToLeftOwnerBisimRun
        (profiledRawJointRecurrentRightToLeftOwnerBisimNoRecv A strategy hwin
          control input).1 rest

theorem profiledRawJointRecurrentRightToLeftOwnerBisimRun_owner
    (control :
      ProfiledRawJointRecurrentRightToLeftOwnerBisimPending A strategy hwin)
    (inputs : List In₁) :
    profiledRawJointRecurrentRightToLeftOwnerBisimOwner A strategy hwin
        (profiledRawJointRecurrentRightToLeftOwnerBisimRun A strategy hwin
          control inputs) =
      profiledRawJointRecurrentRightOwnerRun A
        (profiledRawJointRecurrentRightToLeftOwnerBisimOwner A strategy hwin
          control) inputs := by
  induction inputs generalizing control with
  | nil => rfl
  | cons input rest ih =>
      rw [profiledRawJointRecurrentRightToLeftOwnerBisimRun,
        profiledRawJointRecurrentRightOwnerRun, ih]
      rw [profiledRawJointRecurrentRightToLeftOwnerBisimNoRecv_owner]

/-- At an arbitrary blind depth, the executable next output is the selected
semantic owner's next output. -/
theorem profiledRawJointRecurrentRightToLeftOwnerBisimRun_output
    (control :
      ProfiledRawJointRecurrentRightToLeftOwnerBisimPending A strategy hwin)
    (past : List In₁) (input : In₁) :
    (profiledRawJointRecurrentRightToLeftOwnerBisimNoRecv A strategy hwin
      (profiledRawJointRecurrentRightToLeftOwnerBisimRun A strategy hwin
        control past) input).2 =
      (profiledRawJointRecurrentRightOwnerNoRecv A
        (profiledRawJointRecurrentRightOwnerRun A
          (profiledRawJointRecurrentRightToLeftOwnerBisimOwner A strategy hwin
            control) past) input).2 := by
  rw [profiledRawJointRecurrentRightToLeftOwnerBisimNoRecv_output,
    profiledRawJointRecurrentRightToLeftOwnerBisimRun_owner]

/-! ### Diagnostic old/successor boundary constructor

The explicit compatibility argument is intentionally visible.  The
`successor_forces_shift` theorem above shows why it cannot be synthesized
from the current finite-table certificate alone. -/

noncomputable def
    profiledRawJointRecurrentRightToLeftOwnerBisimPacketBoundaryFork
    (sender : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (oldState : BankControl A strategy hwin)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (input : In₁ × In₂)
    (hcompatible :
      ProfiledRawJointRecurrentRightOwnerCompatible A
        ⟨sender,
          (profiledRawJointRecurrentRightOwnerNoRecv A sender input.1).1⟩) :
    FiniteDelayedFork
        (ProfiledRawJointRecurrentRightToLeftOwnerBisimPending A strategy
          hwin) ×
      Out₁ :=
  let advancedReceiver :=
    profiledRawJointRecurrentRightToLeftAdvanceOldReceiver A strategy hwin
      oldState oldReceiver oldOwner input
  let newMove :=
    profiledRawJointRecurrentRightToLeftMove A strategy hwin packet oldReceiver
  let shared :
      ProfiledRawJointRecurrentRightToLeftOwnerBisimShared A strategy hwin :=
    { ownerFork :=
        ⟨sender,
          (profiledRawJointRecurrentRightOwnerNoRecv A sender input.1).1⟩
      receiverFork :=
        ⟨advancedReceiver.1,
          (packet.successor,
            initialProfiledRawJointLeftPhysicalSiblingReceiver A newMove
              .both)⟩
      compatible := hcompatible }
  (FiniteAcknowledgedDelayedCarrier.deferredMemberFork shared (),
    advancedReceiver.2)

@[simp] theorem
    profiledRawJointRecurrentRightToLeftOwnerBisimPacketBoundaryFork_open_owner
    (sender : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (oldState : BankControl A strategy hwin)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (input : In₁ × In₂)
    (hcompatible :
      ProfiledRawJointRecurrentRightOwnerCompatible A
        ⟨sender,
          (profiledRawJointRecurrentRightOwnerNoRecv A sender input.1).1⟩) :
    profiledRawJointRecurrentRightToLeftOwnerBisimOwner A strategy hwin
        (profiledRawJointRecurrentRightToLeftOwnerBisimPacketBoundaryFork A
          strategy hwin sender oldState oldReceiver oldOwner packet input
            hcompatible).1.openControl = sender :=
  rfl

@[simp] theorem
    profiledRawJointRecurrentRightToLeftOwnerBisimPacketBoundaryFork_closed_owner
    (sender : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (oldState : BankControl A strategy hwin)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (input : In₁ × In₂)
    (hcompatible :
      ProfiledRawJointRecurrentRightOwnerCompatible A
        ⟨sender,
          (profiledRawJointRecurrentRightOwnerNoRecv A sender input.1).1⟩) :
    profiledRawJointRecurrentRightToLeftOwnerBisimOwner A strategy hwin
        (profiledRawJointRecurrentRightToLeftOwnerBisimPacketBoundaryFork A
          strategy hwin sender oldState oldReceiver oldOwner packet input
            hcompatible).1.closedControl =
      (profiledRawJointRecurrentRightOwnerNoRecv A sender input.1).1 :=
  rfl

theorem
    profiledRawJointRecurrentRightToLeftOwnerBisimPacketBoundaryFork_blind
    (sender : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (oldState : BankControl A strategy hwin)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (input : In₁ × In₂)
    (hcompatible :
      ProfiledRawJointRecurrentRightOwnerCompatible A
        ⟨sender,
          (profiledRawJointRecurrentRightOwnerNoRecv A sender input.1).1⟩) :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberBlind
      (profiledRawJointRecurrentRightToLeftOwnerBisimPacketBoundaryFork A
        strategy hwin sender oldState oldReceiver oldOwner packet input
          hcompatible).1.openControl
      (profiledRawJointRecurrentRightToLeftOwnerBisimPacketBoundaryFork A
        strategy hwin sender oldState oldReceiver oldOwner packet input
          hcompatible).1.closedControl := by
  apply FiniteAcknowledgedDelayedCarrier.deferredMemberFork_blind

/-! ## Left-owner mirror -/

noncomputable def profiledRawJointRecurrentLeftOwnerNoRecv
    (owner : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (input : In₂) :
    ProfiledRawJointLeftPhysicalSiblingExceptional A × Out₂ :=
  let next := profiledRawJointLeftPhysicalSiblingMemberNoRecvStep A
    owner.1 false owner.2 input
  (⟨owner.1, next.2⟩, next.1)

noncomputable def profiledRawJointRecurrentLeftOwnerRun :
    ProfiledRawJointLeftPhysicalSiblingExceptional A → List In₂ →
      ProfiledRawJointLeftPhysicalSiblingExceptional A
  | owner, [] => owner
  | owner, input :: rest =>
      profiledRawJointRecurrentLeftOwnerRun
        (profiledRawJointRecurrentLeftOwnerNoRecv A owner input).1 rest

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledRawJointRecurrentLeftOwnerRun_nil
    (owner : ProfiledRawJointLeftPhysicalSiblingExceptional A) :
    profiledRawJointRecurrentLeftOwnerRun A owner [] = owner :=
  rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledRawJointRecurrentLeftOwnerRun_cons
    (owner : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (input : In₂) (rest : List In₂) :
    profiledRawJointRecurrentLeftOwnerRun A owner (input :: rest) =
      profiledRawJointRecurrentLeftOwnerRun A
        (profiledRawJointRecurrentLeftOwnerNoRecv A owner input).1 rest :=
  rfl

def ProfiledRawJointRecurrentLeftOwnerCompatible
    (fork : FiniteDelayedFork
      (ProfiledRawJointLeftPhysicalSiblingExceptional A)) : Prop :=
  ∀ (past : List In₂) (input : In₂),
    (profiledRawJointRecurrentLeftOwnerNoRecv A
      (profiledRawJointRecurrentLeftOwnerRun A fork.openControl past)
        input).2 =
      (profiledRawJointRecurrentLeftOwnerNoRecv A
        (profiledRawJointRecurrentLeftOwnerRun A fork.closedControl past)
          input).2

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Mirrored shift-invariance consequence for a left owner paired with its
own successor. -/
theorem
    ProfiledRawJointRecurrentLeftOwnerCompatible.successor_forces_shift
    (owner : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (boundaryInput : In₂)
    (hcompatible :
      ProfiledRawJointRecurrentLeftOwnerCompatible A
        ⟨owner,
          (profiledRawJointRecurrentLeftOwnerNoRecv A owner
            boundaryInput).1⟩)
    (past : List In₂) (input : In₂) :
    (profiledRawJointRecurrentLeftOwnerNoRecv A
        (profiledRawJointRecurrentLeftOwnerRun A owner past) input).2 =
      (profiledRawJointRecurrentLeftOwnerNoRecv A
        (profiledRawJointRecurrentLeftOwnerRun A
          (profiledRawJointRecurrentLeftOwnerNoRecv A owner
            boundaryInput).1 past) input).2 := by
  exact hcompatible past input

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem ProfiledRawJointRecurrentLeftOwnerCompatible.step
    (fork : FiniteDelayedFork
      (ProfiledRawJointLeftPhysicalSiblingExceptional A))
    (hcompatible : ProfiledRawJointRecurrentLeftOwnerCompatible A fork)
    (input : In₂) :
    ProfiledRawJointRecurrentLeftOwnerCompatible A
      ⟨(profiledRawJointRecurrentLeftOwnerNoRecv A fork.openControl input).1,
        (profiledRawJointRecurrentLeftOwnerNoRecv A fork.closedControl
          input).1⟩ := by
  intro past nextInput
  exact hcompatible (input :: past) nextInput

structure ProfiledRawJointRecurrentLeftToRightOwnerBisimShared where
  ownerFork :
    FiniteDelayedFork (ProfiledRawJointLeftPhysicalSiblingExceptional A)
  receiverFork :
    FiniteDelayedFork
      (ProfiledRawJointRecurrentBankedRightReceiver A strategy hwin)
  compatible :
    ProfiledRawJointRecurrentLeftOwnerCompatible A ownerFork

abbrev ProfiledRawJointRecurrentLeftToRightOwnerBisimPending :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (ProfiledRawJointRecurrentLeftToRightOwnerBisimShared A strategy hwin) Unit

noncomputable instance :
    Fintype
      (ProfiledRawJointRecurrentLeftToRightOwnerBisimShared A strategy hwin) := by
  classical
  let encode := fun state :
      ProfiledRawJointRecurrentLeftToRightOwnerBisimShared A strategy hwin ↦
    (state.ownerFork, state.receiverFork)
  exact Fintype.ofInjective encode (by
    intro left right heq
    cases left
    cases right
    cases heq
    rfl)

noncomputable instance :
    Fintype
      (ProfiledRawJointRecurrentLeftToRightOwnerBisimPending A strategy hwin) := by
  classical
  infer_instance

noncomputable def profiledRawJointRecurrentLeftToRightOwnerBisimOwner
    (control :
      ProfiledRawJointRecurrentLeftToRightOwnerBisimPending A strategy hwin) :
    ProfiledRawJointLeftPhysicalSiblingExceptional A :=
  if control.1 then control.2.1.ownerFork.closedControl
  else control.2.1.ownerFork.openControl

noncomputable def profiledRawJointRecurrentLeftToRightOwnerBisimReceiver
    (control :
      ProfiledRawJointRecurrentLeftToRightOwnerBisimPending A strategy hwin) :
    ProfiledRawJointRecurrentBankedRightReceiver A strategy hwin :=
  if control.1 then control.2.1.receiverFork.closedControl
  else control.2.1.receiverFork.openControl

noncomputable def profiledRawJointRecurrentLeftToRightOwnerBisimStep
    (_member : Bool)
    (shared :
      ProfiledRawJointRecurrentLeftToRightOwnerBisimShared A strategy hwin)
    (input : In₂) :
    ProfiledRawJointRecurrentLeftToRightOwnerBisimShared A strategy hwin ×
      Out₂ :=
  let openNext := profiledRawJointRecurrentLeftOwnerNoRecv A
    shared.ownerFork.openControl input
  let closedNext := profiledRawJointRecurrentLeftOwnerNoRecv A
    shared.ownerFork.closedControl input
  ({ ownerFork := ⟨openNext.1, closedNext.1⟩
     receiverFork := shared.receiverFork
     compatible :=
       ProfiledRawJointRecurrentLeftOwnerCompatible.step A
         shared.ownerFork shared.compatible input },
    openNext.2)

theorem profiledRawJointRecurrentLeftToRightOwnerBisimStep_laws :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberStepLaws
      (profiledRawJointRecurrentLeftToRightOwnerBisimStep A strategy hwin) where
  outputEq := by intro shared input; rfl
  stateEq := by intro shared input; rfl

noncomputable def profiledRawJointRecurrentLeftToRightOwnerBisimNoRecv
    (control :
      ProfiledRawJointRecurrentLeftToRightOwnerBisimPending A strategy hwin)
    (input : In₂) :
    ProfiledRawJointRecurrentLeftToRightOwnerBisimPending A strategy hwin ×
      Out₂ :=
  FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
    (profiledRawJointRecurrentLeftToRightOwnerBisimStep A strategy hwin)
      control input

@[simp] theorem profiledRawJointRecurrentLeftToRightOwnerBisimNoRecv_owner
    (control :
      ProfiledRawJointRecurrentLeftToRightOwnerBisimPending A strategy hwin)
    (input : In₂) :
    profiledRawJointRecurrentLeftToRightOwnerBisimOwner A strategy hwin
        (profiledRawJointRecurrentLeftToRightOwnerBisimNoRecv A strategy hwin
          control input).1 =
      (profiledRawJointRecurrentLeftOwnerNoRecv A
        (profiledRawJointRecurrentLeftToRightOwnerBisimOwner A strategy hwin
          control) input).1 := by
  rcases control with ⟨member, shared, payload⟩
  cases member <;>
    simp [profiledRawJointRecurrentLeftToRightOwnerBisimNoRecv,
      profiledRawJointRecurrentLeftToRightOwnerBisimStep,
      profiledRawJointRecurrentLeftToRightOwnerBisimOwner,
      FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv]

@[simp] theorem profiledRawJointRecurrentLeftToRightOwnerBisimNoRecv_receiver
    (control :
      ProfiledRawJointRecurrentLeftToRightOwnerBisimPending A strategy hwin)
    (input : In₂) :
    profiledRawJointRecurrentLeftToRightOwnerBisimReceiver A strategy hwin
        (profiledRawJointRecurrentLeftToRightOwnerBisimNoRecv A strategy hwin
          control input).1 =
      profiledRawJointRecurrentLeftToRightOwnerBisimReceiver A strategy hwin
        control := by
  rcases control with ⟨member, shared, payload⟩
  cases member <;>
    simp [profiledRawJointRecurrentLeftToRightOwnerBisimNoRecv,
      profiledRawJointRecurrentLeftToRightOwnerBisimStep,
      profiledRawJointRecurrentLeftToRightOwnerBisimReceiver,
      FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv]

theorem profiledRawJointRecurrentLeftToRightOwnerBisimNoRecv_output
    (control :
      ProfiledRawJointRecurrentLeftToRightOwnerBisimPending A strategy hwin)
    (input : In₂) :
    (profiledRawJointRecurrentLeftToRightOwnerBisimNoRecv A strategy hwin
      control input).2 =
      (profiledRawJointRecurrentLeftOwnerNoRecv A
        (profiledRawJointRecurrentLeftToRightOwnerBisimOwner A strategy hwin
          control) input).2 := by
  rcases control with ⟨member, shared, payload⟩
  cases member with
  | false =>
      simp [profiledRawJointRecurrentLeftToRightOwnerBisimNoRecv,
        profiledRawJointRecurrentLeftToRightOwnerBisimStep,
        profiledRawJointRecurrentLeftToRightOwnerBisimOwner,
        FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv]
  | true =>
      simpa [profiledRawJointRecurrentLeftToRightOwnerBisimNoRecv,
        profiledRawJointRecurrentLeftToRightOwnerBisimStep,
        profiledRawJointRecurrentLeftToRightOwnerBisimOwner,
        profiledRawJointRecurrentLeftOwnerRun,
        FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv] using
          shared.compatible [] input

theorem profiledRawJointRecurrentLeftToRightOwnerBisim_blind_noRecv
    (left right :
      ProfiledRawJointRecurrentLeftToRightOwnerBisimPending A strategy hwin)
    (input : In₂)
    (hblind : FiniteAcknowledgedDelayedCarrier.DeferredMemberBlind left
      right) :
    (profiledRawJointRecurrentLeftToRightOwnerBisimNoRecv A strategy hwin left
        input).2 =
        (profiledRawJointRecurrentLeftToRightOwnerBisimNoRecv A strategy hwin
          right input).2 ∧
      FiniteAcknowledgedDelayedCarrier.DeferredMemberBlind
        (profiledRawJointRecurrentLeftToRightOwnerBisimNoRecv A strategy hwin
          left input).1
        (profiledRawJointRecurrentLeftToRightOwnerBisimNoRecv A strategy hwin
          right input).1 := by
  exact FiniteAcknowledgedDelayedCarrier.deferredMemberBlind_noRecv
    (profiledRawJointRecurrentLeftToRightOwnerBisimStep A strategy hwin)
    (profiledRawJointRecurrentLeftToRightOwnerBisimStep_laws A strategy hwin)
    left right input hblind

noncomputable def profiledRawJointRecurrentLeftToRightOwnerBisimRun :
    ProfiledRawJointRecurrentLeftToRightOwnerBisimPending A strategy hwin →
      List In₂ →
        ProfiledRawJointRecurrentLeftToRightOwnerBisimPending A strategy hwin
  | control, [] => control
  | control, input :: rest =>
      profiledRawJointRecurrentLeftToRightOwnerBisimRun
        (profiledRawJointRecurrentLeftToRightOwnerBisimNoRecv A strategy hwin
          control input).1 rest

theorem profiledRawJointRecurrentLeftToRightOwnerBisimRun_owner
    (control :
      ProfiledRawJointRecurrentLeftToRightOwnerBisimPending A strategy hwin)
    (inputs : List In₂) :
    profiledRawJointRecurrentLeftToRightOwnerBisimOwner A strategy hwin
        (profiledRawJointRecurrentLeftToRightOwnerBisimRun A strategy hwin
          control inputs) =
      profiledRawJointRecurrentLeftOwnerRun A
        (profiledRawJointRecurrentLeftToRightOwnerBisimOwner A strategy hwin
          control) inputs := by
  induction inputs generalizing control with
  | nil => rfl
  | cons input rest ih =>
      rw [profiledRawJointRecurrentLeftToRightOwnerBisimRun,
        profiledRawJointRecurrentLeftOwnerRun, ih]
      rw [profiledRawJointRecurrentLeftToRightOwnerBisimNoRecv_owner]

theorem profiledRawJointRecurrentLeftToRightOwnerBisimRun_output
    (control :
      ProfiledRawJointRecurrentLeftToRightOwnerBisimPending A strategy hwin)
    (past : List In₂) (input : In₂) :
    (profiledRawJointRecurrentLeftToRightOwnerBisimNoRecv A strategy hwin
      (profiledRawJointRecurrentLeftToRightOwnerBisimRun A strategy hwin
        control past) input).2 =
      (profiledRawJointRecurrentLeftOwnerNoRecv A
        (profiledRawJointRecurrentLeftOwnerRun A
          (profiledRawJointRecurrentLeftToRightOwnerBisimOwner A strategy hwin
            control) past) input).2 := by
  rw [profiledRawJointRecurrentLeftToRightOwnerBisimNoRecv_output,
    profiledRawJointRecurrentLeftToRightOwnerBisimRun_owner]

noncomputable def
    profiledRawJointRecurrentLeftToRightOwnerBisimPacketBoundaryFork
    (sender : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (oldState : BankControl A strategy hwin)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (input : In₂ × In₁)
    (hcompatible :
      ProfiledRawJointRecurrentLeftOwnerCompatible A
        ⟨sender,
          (profiledRawJointRecurrentLeftOwnerNoRecv A sender input.1).1⟩) :
    FiniteDelayedFork
        (ProfiledRawJointRecurrentLeftToRightOwnerBisimPending A strategy
          hwin) ×
      Out₂ :=
  let advancedReceiver :=
    profiledRawJointRecurrentLeftToRightAdvanceOldReceiver A strategy hwin
      oldState oldReceiver oldOwner input
  let newMove :=
    profiledRawJointRecurrentLeftToRightMove A strategy hwin packet oldReceiver
  let shared :
      ProfiledRawJointRecurrentLeftToRightOwnerBisimShared A strategy hwin :=
    { ownerFork :=
        ⟨sender,
          (profiledRawJointRecurrentLeftOwnerNoRecv A sender input.1).1⟩
      receiverFork :=
        ⟨advancedReceiver.1,
          (packet.successor,
            initialProfiledRawJointRightPhysicalSiblingReceiver A newMove
              .both)⟩
      compatible := hcompatible }
  (FiniteAcknowledgedDelayedCarrier.deferredMemberFork shared (),
    advancedReceiver.2)

@[simp] theorem
    profiledRawJointRecurrentLeftToRightOwnerBisimPacketBoundaryFork_open_owner
    (sender : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (oldState : BankControl A strategy hwin)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (input : In₂ × In₁)
    (hcompatible :
      ProfiledRawJointRecurrentLeftOwnerCompatible A
        ⟨sender,
          (profiledRawJointRecurrentLeftOwnerNoRecv A sender input.1).1⟩) :
    profiledRawJointRecurrentLeftToRightOwnerBisimOwner A strategy hwin
        (profiledRawJointRecurrentLeftToRightOwnerBisimPacketBoundaryFork A
          strategy hwin sender oldState oldReceiver oldOwner packet input
            hcompatible).1.openControl = sender :=
  rfl

@[simp] theorem
    profiledRawJointRecurrentLeftToRightOwnerBisimPacketBoundaryFork_closed_owner
    (sender : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (oldState : BankControl A strategy hwin)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (input : In₂ × In₁)
    (hcompatible :
      ProfiledRawJointRecurrentLeftOwnerCompatible A
        ⟨sender,
          (profiledRawJointRecurrentLeftOwnerNoRecv A sender input.1).1⟩) :
    profiledRawJointRecurrentLeftToRightOwnerBisimOwner A strategy hwin
        (profiledRawJointRecurrentLeftToRightOwnerBisimPacketBoundaryFork A
          strategy hwin sender oldState oldReceiver oldOwner packet input
            hcompatible).1.closedControl =
      (profiledRawJointRecurrentLeftOwnerNoRecv A sender input.1).1 :=
  rfl

theorem
    profiledRawJointRecurrentLeftToRightOwnerBisimPacketBoundaryFork_blind
    (sender : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (oldState : BankControl A strategy hwin)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (input : In₂ × In₁)
    (hcompatible :
      ProfiledRawJointRecurrentLeftOwnerCompatible A
        ⟨sender,
          (profiledRawJointRecurrentLeftOwnerNoRecv A sender input.1).1⟩) :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberBlind
      (profiledRawJointRecurrentLeftToRightOwnerBisimPacketBoundaryFork A
        strategy hwin sender oldState oldReceiver oldOwner packet input
          hcompatible).1.openControl
      (profiledRawJointRecurrentLeftToRightOwnerBisimPacketBoundaryFork A
        strategy hwin sender oldState oldReceiver oldOwner packet input
          hcompatible).1.closedControl := by
  apply FiniteAcknowledgedDelayedCarrier.deferredMemberFork_blind

end

end DetParityAutomaton

end DistributedSynthesis
