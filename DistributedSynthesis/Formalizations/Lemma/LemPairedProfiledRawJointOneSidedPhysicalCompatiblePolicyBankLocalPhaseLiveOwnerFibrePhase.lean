/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatiblePolicyBankLocalPhaseLiveOwnerFibreCarrier

/-!
# Fibre-backed phase payloads

This file performs the phase-live integration test in both orientations.  A
pending state replaces its bare owner by a finite owner-fibre carrier; the
old/new receiver fork is unchanged.  Erasing the virtual monitor recovers the
existing phase-live state exactly.

The new no-receive transition advances the owner and virtual monitor
together, preserves the fibre invariant, and commutes with erasure.  Thus all
existing structural decoder equations that inspect only the installed move,
owner, and receiver fork can be lifted through this erasure map.  A semantic
strict-direction decoder must nevertheless build its active boundary
invariant from the delivered fibre monitor, rather than from the stale
receiver branch retained only for delayed-information bookkeeping.
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

/-! ## Finite payload and erasure -/

abbrev ProfiledRawJointRecurrentRightToLeftOwnerFibreShared :=
  ProfiledRawJointRightOwnerFibreControl A ×
    FiniteDelayedFork
      (ProfiledRawJointRecurrentBankedLeftReceiver A strategy hwin)

abbrev ProfiledRawJointRecurrentRightToLeftOwnerFibrePending :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (ProfiledRawJointRecurrentRightToLeftOwnerFibreShared A strategy hwin) Unit

noncomputable instance :
    Fintype
      (ProfiledRawJointRecurrentRightToLeftOwnerFibreShared A strategy hwin) := by
  classical
  infer_instance

noncomputable instance :
    Fintype
      (ProfiledRawJointRecurrentRightToLeftOwnerFibrePending A strategy hwin) := by
  classical
  infer_instance

noncomputable def profiledRawJointRightOwnerFibreExceptional
    (control : ProfiledRawJointRightOwnerFibreControl A) :
    ProfiledRawJointRightPhysicalSiblingExceptional A :=
  ⟨control.1, control.2.1⟩

noncomputable def profiledRawJointRecurrentRightToLeftOwnerFibreErase
    (control :
      ProfiledRawJointRecurrentRightToLeftOwnerFibrePending A strategy hwin) :
    ProfiledRawJointRecurrentRightToLeftPhaseLivePending A strategy hwin :=
  ⟨control.1,
    (profiledRawJointRightOwnerFibreExceptional A control.2.1.1,
      control.2.1.2),
    control.2.2⟩

def ProfiledRawJointRecurrentRightToLeftOwnerFibreValid
    (control :
      ProfiledRawJointRecurrentRightToLeftOwnerFibrePending A strategy hwin) :
    Prop :=
  ProfiledRawJointRightOwnerFibreValid A control.2.1.1

/-! ## Boundary lift -/

/-- Enrich the existing exact packet boundary with a virtual receiver state
selected over its already-advanced shared right owner. -/
noncomputable def
    profiledRawJointRecurrentRightToLeftOwnerFibrePacketBoundaryFork
    (sender : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (oldState : BankControl A strategy hwin)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (input : In₁ × In₂) :
    FiniteDelayedFork
        (ProfiledRawJointRecurrentRightToLeftOwnerFibrePending A strategy
          hwin) ×
      Out₁ :=
  let oldResult :=
    profiledRawJointRecurrentRightToLeftPhaseLivePacketBoundaryFork A strategy
      hwin sender oldState oldReceiver oldOwner packet input
  let advancedSender := oldResult.1.openControl.2.1.1
  let fibre := profiledRawJointRightOwnerFibreControlOfOwner A advancedSender
  (FiniteAcknowledgedDelayedCarrier.deferredMemberFork
      (fibre, oldResult.1.openControl.2.1.2) (),
    oldResult.2)

/-- Erasing either unresolved member gives the corresponding member of the
previous exact packet boundary. -/
theorem
    profiledRawJointRecurrentRightToLeftOwnerFibrePacketBoundaryFork_erase
    (sender : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (oldState : BankControl A strategy hwin)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (input : In₁ × In₂) :
    let newFork :=
      (profiledRawJointRecurrentRightToLeftOwnerFibrePacketBoundaryFork A
        strategy hwin sender oldState oldReceiver oldOwner packet input).1
    let oldFork :=
      (profiledRawJointRecurrentRightToLeftPhaseLivePacketBoundaryFork A
        strategy hwin sender oldState oldReceiver oldOwner packet input).1
    profiledRawJointRecurrentRightToLeftOwnerFibreErase A strategy hwin
        newFork.openControl = oldFork.openControl ∧
      profiledRawJointRecurrentRightToLeftOwnerFibreErase A strategy hwin
        newFork.closedControl = oldFork.closedControl := by
  constructor <;> rfl

/-- Reachability of the incoming right owner makes both members of the new
boundary fork valid. -/
theorem
    profiledRawJointRecurrentRightToLeftOwnerFibrePacketBoundaryFork_valid
    (sender : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (hsender :
      ProfiledRawJointRightPhysicalSiblingOwnerReachable A sender.1 sender.2)
    (oldState : BankControl A strategy hwin)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (input : In₁ × In₂) :
    let fork :=
      (profiledRawJointRecurrentRightToLeftOwnerFibrePacketBoundaryFork A
        strategy hwin sender oldState oldReceiver oldOwner packet input).1
    ProfiledRawJointRecurrentRightToLeftOwnerFibreValid A strategy hwin
        fork.openControl ∧
      ProfiledRawJointRecurrentRightToLeftOwnerFibreValid A strategy hwin
        fork.closedControl := by
  dsimp only
  have hadvanced := hsender.step A sender.1 sender.2 input.1
  have hvalid := profiledRawJointRightOwnerFibreChoiceControl_valid A sender.1
    ((sender.1.memberController A false).step sender.2 input.1) hadvanced
  simpa only [
    profiledRawJointRecurrentRightToLeftOwnerFibrePacketBoundaryFork,
    profiledRawJointRecurrentRightToLeftPhaseLivePacketBoundaryFork,
    ProfiledRawJointRecurrentRightToLeftOwnerFibreValid,
    profiledRawJointRightOwnerFibreControlOfOwner] using And.intro hvalid hvalid

/-! ## Blind no-receive evolution -/

noncomputable def profiledRawJointRecurrentRightToLeftOwnerFibreStep
    (_member : Bool)
    (shared :
      ProfiledRawJointRecurrentRightToLeftOwnerFibreShared A strategy hwin)
    (input : In₁) :
    ProfiledRawJointRecurrentRightToLeftOwnerFibreShared A strategy hwin ×
      Out₁ :=
  let next := profiledRawJointRightOwnerFibreNoRecv A shared.1 input
  ((next.1, shared.2), next.2)

theorem profiledRawJointRecurrentRightToLeftOwnerFibreStep_laws :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberStepLaws
      (profiledRawJointRecurrentRightToLeftOwnerFibreStep A strategy hwin) where
  outputEq := by intro shared input; rfl
  stateEq := by intro shared input; rfl

noncomputable def profiledRawJointRecurrentRightToLeftOwnerFibreNoRecv
    (control :
      ProfiledRawJointRecurrentRightToLeftOwnerFibrePending A strategy hwin)
    (input : In₁) :
    ProfiledRawJointRecurrentRightToLeftOwnerFibrePending A strategy hwin ×
      Out₁ :=
  FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
    (profiledRawJointRecurrentRightToLeftOwnerFibreStep A strategy hwin)
      control input

theorem ProfiledRawJointRecurrentRightToLeftOwnerFibreValid.noRecv
    (control :
      ProfiledRawJointRecurrentRightToLeftOwnerFibrePending A strategy hwin)
    (hvalid :
      ProfiledRawJointRecurrentRightToLeftOwnerFibreValid A strategy hwin
        control)
    (input : In₁) :
    ProfiledRawJointRecurrentRightToLeftOwnerFibreValid A strategy hwin
      (profiledRawJointRecurrentRightToLeftOwnerFibreNoRecv A strategy hwin
        control input).1 := by
  rcases control with ⟨member, shared, payload⟩
  have hnext := ProfiledRawJointRightOwnerFibreValid.noRecv A shared.1 hvalid
    input
  cases member <;>
    simpa [ProfiledRawJointRecurrentRightToLeftOwnerFibreValid,
      profiledRawJointRecurrentRightToLeftOwnerFibreNoRecv,
      profiledRawJointRecurrentRightToLeftOwnerFibreStep,
      FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv] using hnext

/-- The enriched transition has exactly the old output and old decoder-facing
state after erasure. -/
theorem profiledRawJointRecurrentRightToLeftOwnerFibreNoRecv_erase
    (control :
      ProfiledRawJointRecurrentRightToLeftOwnerFibrePending A strategy hwin)
    (input : In₁) :
    (profiledRawJointRecurrentRightToLeftOwnerFibreNoRecv A strategy hwin
        control input).2 =
        (profiledRawJointRecurrentRightToLeftPhaseLiveNoRecv A strategy hwin
          (profiledRawJointRecurrentRightToLeftOwnerFibreErase A strategy hwin
            control) input).2 ∧
      profiledRawJointRecurrentRightToLeftOwnerFibreErase A strategy hwin
          (profiledRawJointRecurrentRightToLeftOwnerFibreNoRecv A strategy hwin
            control input).1 =
        (profiledRawJointRecurrentRightToLeftPhaseLiveNoRecv A strategy hwin
        (profiledRawJointRecurrentRightToLeftOwnerFibreErase A strategy hwin
            control) input).1 := by
  rcases control with ⟨member, shared, payload⟩
  cases member <;> constructor <;> rfl

theorem profiledRawJointRecurrentRightToLeftOwnerFibre_blind_noRecv
    (left right :
      ProfiledRawJointRecurrentRightToLeftOwnerFibrePending A strategy hwin)
    (input : In₁)
    (hblind : FiniteAcknowledgedDelayedCarrier.DeferredMemberBlind left right) :
    (profiledRawJointRecurrentRightToLeftOwnerFibreNoRecv A strategy hwin left
        input).2 =
        (profiledRawJointRecurrentRightToLeftOwnerFibreNoRecv A strategy hwin
          right input).2 ∧
      FiniteAcknowledgedDelayedCarrier.DeferredMemberBlind
        (profiledRawJointRecurrentRightToLeftOwnerFibreNoRecv A strategy hwin
          left input).1
        (profiledRawJointRecurrentRightToLeftOwnerFibreNoRecv A strategy hwin
          right input).1 := by
  exact FiniteAcknowledgedDelayedCarrier.deferredMemberBlind_noRecv
    (profiledRawJointRecurrentRightToLeftOwnerFibreStep A strategy hwin)
    (profiledRawJointRecurrentRightToLeftOwnerFibreStep_laws A strategy hwin)
    left right input hblind

/-! ## Left-to-right mirror -/

abbrev ProfiledRawJointRecurrentLeftToRightOwnerFibreShared :=
  ProfiledRawJointLeftOwnerFibreControl A ×
    FiniteDelayedFork
      (ProfiledRawJointRecurrentBankedRightReceiver A strategy hwin)

abbrev ProfiledRawJointRecurrentLeftToRightOwnerFibrePending :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (ProfiledRawJointRecurrentLeftToRightOwnerFibreShared A strategy hwin) Unit

noncomputable instance :
    Fintype
      (ProfiledRawJointRecurrentLeftToRightOwnerFibreShared A strategy hwin) := by
  classical
  infer_instance

noncomputable instance :
    Fintype
      (ProfiledRawJointRecurrentLeftToRightOwnerFibrePending A strategy hwin) := by
  classical
  infer_instance

noncomputable def profiledRawJointLeftOwnerFibreExceptional
    (control : ProfiledRawJointLeftOwnerFibreControl A) :
    ProfiledRawJointLeftPhysicalSiblingExceptional A :=
  ⟨control.1, control.2.1⟩

noncomputable def profiledRawJointRecurrentLeftToRightOwnerFibreErase
    (control :
      ProfiledRawJointRecurrentLeftToRightOwnerFibrePending A strategy hwin) :
    ProfiledRawJointRecurrentLeftToRightPhaseLivePending A strategy hwin :=
  ⟨control.1,
    (profiledRawJointLeftOwnerFibreExceptional A control.2.1.1,
      control.2.1.2),
    control.2.2⟩

def ProfiledRawJointRecurrentLeftToRightOwnerFibreValid
    (control :
      ProfiledRawJointRecurrentLeftToRightOwnerFibrePending A strategy hwin) :
    Prop :=
  ProfiledRawJointLeftOwnerFibreValid A control.2.1.1

noncomputable def
    profiledRawJointRecurrentLeftToRightOwnerFibrePacketBoundaryFork
    (sender : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (oldState : BankControl A strategy hwin)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (input : In₂ × In₁) :
    FiniteDelayedFork
        (ProfiledRawJointRecurrentLeftToRightOwnerFibrePending A strategy
          hwin) ×
      Out₂ :=
  let oldResult :=
    profiledRawJointRecurrentLeftToRightPhaseLivePacketBoundaryFork A strategy
      hwin sender oldState oldReceiver oldOwner packet input
  let advancedSender := oldResult.1.openControl.2.1.1
  let fibre := profiledRawJointLeftOwnerFibreControlOfOwner A advancedSender
  (FiniteAcknowledgedDelayedCarrier.deferredMemberFork
      (fibre, oldResult.1.openControl.2.1.2) (),
    oldResult.2)

theorem
    profiledRawJointRecurrentLeftToRightOwnerFibrePacketBoundaryFork_erase
    (sender : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (oldState : BankControl A strategy hwin)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (input : In₂ × In₁) :
    let newFork :=
      (profiledRawJointRecurrentLeftToRightOwnerFibrePacketBoundaryFork A
        strategy hwin sender oldState oldReceiver oldOwner packet input).1
    let oldFork :=
      (profiledRawJointRecurrentLeftToRightPhaseLivePacketBoundaryFork A
        strategy hwin sender oldState oldReceiver oldOwner packet input).1
    profiledRawJointRecurrentLeftToRightOwnerFibreErase A strategy hwin
        newFork.openControl = oldFork.openControl ∧
      profiledRawJointRecurrentLeftToRightOwnerFibreErase A strategy hwin
        newFork.closedControl = oldFork.closedControl := by
  constructor <;> rfl

theorem
    profiledRawJointRecurrentLeftToRightOwnerFibrePacketBoundaryFork_valid
    (sender : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (hsender :
      ProfiledRawJointLeftPhysicalSiblingOwnerReachable A sender.1 sender.2)
    (oldState : BankControl A strategy hwin)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (input : In₂ × In₁) :
    let fork :=
      (profiledRawJointRecurrentLeftToRightOwnerFibrePacketBoundaryFork A
        strategy hwin sender oldState oldReceiver oldOwner packet input).1
    ProfiledRawJointRecurrentLeftToRightOwnerFibreValid A strategy hwin
        fork.openControl ∧
      ProfiledRawJointRecurrentLeftToRightOwnerFibreValid A strategy hwin
        fork.closedControl := by
  dsimp only
  have hadvanced := hsender.step A sender.1 sender.2 input.1
  have hvalid := profiledRawJointLeftOwnerFibreChoiceControl_valid A sender.1
    ((sender.1.memberController A false).step sender.2 input.1) hadvanced
  simpa only [
    profiledRawJointRecurrentLeftToRightOwnerFibrePacketBoundaryFork,
    profiledRawJointRecurrentLeftToRightPhaseLivePacketBoundaryFork,
    ProfiledRawJointRecurrentLeftToRightOwnerFibreValid,
    profiledRawJointLeftOwnerFibreControlOfOwner] using And.intro hvalid hvalid

noncomputable def profiledRawJointRecurrentLeftToRightOwnerFibreStep
    (_member : Bool)
    (shared :
      ProfiledRawJointRecurrentLeftToRightOwnerFibreShared A strategy hwin)
    (input : In₂) :
    ProfiledRawJointRecurrentLeftToRightOwnerFibreShared A strategy hwin ×
      Out₂ :=
  let next := profiledRawJointLeftOwnerFibreNoRecv A shared.1 input
  ((next.1, shared.2), next.2)

theorem profiledRawJointRecurrentLeftToRightOwnerFibreStep_laws :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberStepLaws
      (profiledRawJointRecurrentLeftToRightOwnerFibreStep A strategy hwin) where
  outputEq := by intro shared input; rfl
  stateEq := by intro shared input; rfl

noncomputable def profiledRawJointRecurrentLeftToRightOwnerFibreNoRecv
    (control :
      ProfiledRawJointRecurrentLeftToRightOwnerFibrePending A strategy hwin)
    (input : In₂) :
    ProfiledRawJointRecurrentLeftToRightOwnerFibrePending A strategy hwin ×
      Out₂ :=
  FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
    (profiledRawJointRecurrentLeftToRightOwnerFibreStep A strategy hwin)
      control input

theorem ProfiledRawJointRecurrentLeftToRightOwnerFibreValid.noRecv
    (control :
      ProfiledRawJointRecurrentLeftToRightOwnerFibrePending A strategy hwin)
    (hvalid :
      ProfiledRawJointRecurrentLeftToRightOwnerFibreValid A strategy hwin
        control)
    (input : In₂) :
    ProfiledRawJointRecurrentLeftToRightOwnerFibreValid A strategy hwin
      (profiledRawJointRecurrentLeftToRightOwnerFibreNoRecv A strategy hwin
        control input).1 := by
  rcases control with ⟨member, shared, payload⟩
  have hnext := ProfiledRawJointLeftOwnerFibreValid.noRecv A shared.1 hvalid
    input
  cases member <;>
    simpa [ProfiledRawJointRecurrentLeftToRightOwnerFibreValid,
      profiledRawJointRecurrentLeftToRightOwnerFibreNoRecv,
      profiledRawJointRecurrentLeftToRightOwnerFibreStep,
      FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv] using hnext

theorem profiledRawJointRecurrentLeftToRightOwnerFibreNoRecv_erase
    (control :
      ProfiledRawJointRecurrentLeftToRightOwnerFibrePending A strategy hwin)
    (input : In₂) :
    (profiledRawJointRecurrentLeftToRightOwnerFibreNoRecv A strategy hwin
        control input).2 =
        (profiledRawJointRecurrentLeftToRightPhaseLiveNoRecv A strategy hwin
          (profiledRawJointRecurrentLeftToRightOwnerFibreErase A strategy hwin
            control) input).2 ∧
      profiledRawJointRecurrentLeftToRightOwnerFibreErase A strategy hwin
          (profiledRawJointRecurrentLeftToRightOwnerFibreNoRecv A strategy hwin
            control input).1 =
        (profiledRawJointRecurrentLeftToRightPhaseLiveNoRecv A strategy hwin
          (profiledRawJointRecurrentLeftToRightOwnerFibreErase A strategy hwin
            control) input).1 := by
  rcases control with ⟨member, shared, payload⟩
  cases member <;> constructor <;> rfl

theorem profiledRawJointRecurrentLeftToRightOwnerFibre_blind_noRecv
    (left right :
      ProfiledRawJointRecurrentLeftToRightOwnerFibrePending A strategy hwin)
    (input : In₂)
    (hblind : FiniteAcknowledgedDelayedCarrier.DeferredMemberBlind left right) :
    (profiledRawJointRecurrentLeftToRightOwnerFibreNoRecv A strategy hwin left
        input).2 =
        (profiledRawJointRecurrentLeftToRightOwnerFibreNoRecv A strategy hwin
          right input).2 ∧
      FiniteAcknowledgedDelayedCarrier.DeferredMemberBlind
        (profiledRawJointRecurrentLeftToRightOwnerFibreNoRecv A strategy hwin
          left input).1
        (profiledRawJointRecurrentLeftToRightOwnerFibreNoRecv A strategy hwin
          right input).1 := by
  exact FiniteAcknowledgedDelayedCarrier.deferredMemberBlind_noRecv
    (profiledRawJointRecurrentLeftToRightOwnerFibreStep A strategy hwin)
    (profiledRawJointRecurrentLeftToRightOwnerFibreStep_laws A strategy hwin)
    left right input hblind

end


end DetParityAutomaton

end DistributedSynthesis
