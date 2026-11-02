/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyBankLocalPhaseLive
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatiblePolicyBankLocalPhaseLiveOwnerFibreCarrier

/-!
# Fibre-backed finite-memory reversal payloads

This is the first owner-fibre layer of the augmented recurrent bank.  The
virtual receiver monitor is independent of the bank policy, while each
dormant receiver branch keeps its own augmented bank coordinate.  Boundary
creation and blind evolution therefore lift without identifying or
centralizing the two policy memories.
-/

namespace DistributedSynthesis

universe u v x y s m

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable {Memory : Type m}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable [Fintype Memory]

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

private abbrev RootKey :=
  ProfiledRawJointOneSidedPhysicalCompatibleRootKey A strategy

private abbrev BankControl :=
  ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankControl
    (Memory := Memory) A strategy

private abbrev Packet :=
  ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankResolvedTarget
    (Memory := Memory) A strategy

/-! ## Right-to-left payload -/

abbrev
    ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreShared :=
  ProfiledRawJointRightOwnerFibreControl A ×
    FiniteDelayedFork
      (ProfiledRawJointRecurrentFiniteMemoryBankedLeftReceiver
        (Memory := Memory) A strategy)

abbrev
    ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibrePending :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreShared
      (Memory := Memory) A strategy) Unit

noncomputable instance :
    Fintype
      (ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreShared
        (Memory := Memory) A strategy) := by
  classical
  infer_instance

noncomputable instance :
    Fintype
      (ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibrePending
        (Memory := Memory) A strategy) := by
  classical
  infer_instance

def ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreValid
    (control :
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibrePending
        (Memory := Memory) A strategy) : Prop :=
  ProfiledRawJointRightOwnerFibreValid A control.2.1.1

noncomputable def
    profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreReceiver
    (control :
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibrePending
        (Memory := Memory) A strategy) :
    ProfiledRawJointRecurrentFiniteMemoryBankedLeftReceiver
      (Memory := Memory) A strategy :=
  if control.1 then control.2.1.2.closedControl
  else control.2.1.2.openControl

/-- Enrich the augmented phase-live boundary by a virtual monitor selected
over its already-advanced right owner. -/
noncomputable def
    profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibrePacketBoundaryFork
    (sender : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (oldState : BankControl (Memory := Memory) A strategy)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet : Packet (Memory := Memory) A strategy)
    (input : In₁ × In₂) :
    FiniteDelayedFork
        (ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibrePending
          (Memory := Memory) A strategy) × Out₁ :=
  let oldResult :=
    profiledRawJointRecurrentFiniteMemoryRightToLeftPacketBoundaryFork
      (Memory := Memory) A strategy sender oldState oldReceiver oldOwner
        packet input
  let advancedSender := oldResult.1.openControl.2.1.1
  let fibre := profiledRawJointRightOwnerFibreControlOfOwner A advancedSender
  (FiniteAcknowledgedDelayedCarrier.deferredMemberFork
      (fibre, oldResult.1.openControl.2.1.2) (),
    oldResult.2)

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype Memory] in
/-- The old and fresh receiver branches keep precisely the two augmented
coordinates created by the phase-live packet boundary. -/
theorem
    profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibrePacketBoundaryFork_coordinates
    (sender : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (oldState : BankControl (Memory := Memory) A strategy)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet : Packet (Memory := Memory) A strategy)
    (input : In₁ × In₂) :
    let fork :=
      (profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibrePacketBoundaryFork
        (Memory := Memory) A strategy sender oldState oldReceiver oldOwner
          packet input).1
    (profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreReceiver
        (Memory := Memory) A strategy fork.openControl).1 = oldState ∧
      (profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreReceiver
        (Memory := Memory) A strategy fork.closedControl).1 =
          packet.successor :=
  ⟨rfl, rfl⟩

omit [Fintype Memory] [Inhabited Out₁] [Inhabited Out₂] in
/-- Reachability of the incoming owner makes both unresolved fibre members
valid.  Bank memory does not occur in this physical-monitor invariant. -/
theorem
    profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibrePacketBoundaryFork_valid
    (sender : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (hsender :
      ProfiledRawJointRightPhysicalSiblingOwnerReachable A sender.1 sender.2)
    (oldState : BankControl (Memory := Memory) A strategy)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet : Packet (Memory := Memory) A strategy)
    (input : In₁ × In₂) :
    let fork :=
      (profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibrePacketBoundaryFork
        (Memory := Memory) A strategy sender oldState oldReceiver oldOwner
          packet input).1
    ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreValid
        (Memory := Memory) A strategy fork.openControl ∧
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreValid
        (Memory := Memory) A strategy fork.closedControl := by
  dsimp only
  have hadvanced := hsender.step A sender.1 sender.2 input.1
  have hvalid := profiledRawJointRightOwnerFibreChoiceControl_valid A sender.1
    ((sender.1.memberController A false).step sender.2 input.1) hadvanced
  simpa only [
    profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibrePacketBoundaryFork,
    profiledRawJointRecurrentFiniteMemoryRightToLeftPacketBoundaryFork,
    ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreValid,
    profiledRawJointRightOwnerFibreControlOfOwner] using And.intro hvalid hvalid

noncomputable def
    profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreStep
    (_member : Bool)
    (shared :
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreShared
        (Memory := Memory) A strategy)
    (input : In₁) :
    ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreShared
        (Memory := Memory) A strategy × Out₁ :=
  let next := profiledRawJointRightOwnerFibreNoRecv A shared.1 input
  ((next.1, shared.2), next.2)

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype Memory] in
theorem profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreStep_laws :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberStepLaws
      (profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreStep
        (Memory := Memory) A strategy) where
  outputEq := by intro shared input; rfl
  stateEq := by intro shared input; rfl

noncomputable def
    profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreNoRecv
    (control :
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibrePending
        (Memory := Memory) A strategy)
    (input : In₁) :
    ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibrePending
        (Memory := Memory) A strategy × Out₁ :=
  FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
    (profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreStep
      (Memory := Memory) A strategy) control input

omit [Fintype Memory] [Inhabited Out₁] [Inhabited Out₂] in
theorem
    ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreValid.noRecv
    (control :
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibrePending
        (Memory := Memory) A strategy)
    (hvalid :
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreValid
        (Memory := Memory) A strategy control)
    (input : In₁) :
    ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreValid
      (Memory := Memory) A strategy
      (profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreNoRecv
        (Memory := Memory) A strategy control input).1 := by
  rcases control with ⟨member, shared, payload⟩
  have hnext := ProfiledRawJointRightOwnerFibreValid.noRecv A shared.1 hvalid
    input
  cases member <;>
    simpa [
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreValid,
      profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreNoRecv,
      profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreStep,
      FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv] using hnext

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype Memory] in
theorem
    profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibre_blind_noRecv
    (left right :
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibrePending
        (Memory := Memory) A strategy)
    (input : In₁)
    (hblind :
      FiniteAcknowledgedDelayedCarrier.DeferredMemberBlind left right) :
    (profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreNoRecv
        (Memory := Memory) A strategy left input).2 =
        (profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreNoRecv
          (Memory := Memory) A strategy right input).2 ∧
      FiniteAcknowledgedDelayedCarrier.DeferredMemberBlind
        (profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreNoRecv
          (Memory := Memory) A strategy left input).1
        (profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreNoRecv
          (Memory := Memory) A strategy right input).1 := by
  exact FiniteAcknowledgedDelayedCarrier.deferredMemberBlind_noRecv
    (profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreStep
      (Memory := Memory) A strategy)
    (profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreStep_laws
      (Memory := Memory) A strategy) left right input hblind

/-! ## Left-to-right mirror -/

abbrev
    ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreShared :=
  ProfiledRawJointLeftOwnerFibreControl A ×
    FiniteDelayedFork
      (ProfiledRawJointRecurrentFiniteMemoryBankedRightReceiver
        (Memory := Memory) A strategy)

abbrev
    ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibrePending :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreShared
      (Memory := Memory) A strategy) Unit

noncomputable instance :
    Fintype
      (ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreShared
        (Memory := Memory) A strategy) := by
  classical
  infer_instance

noncomputable instance :
    Fintype
      (ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibrePending
        (Memory := Memory) A strategy) := by
  classical
  infer_instance

def ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreValid
    (control :
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibrePending
        (Memory := Memory) A strategy) : Prop :=
  ProfiledRawJointLeftOwnerFibreValid A control.2.1.1

noncomputable def
    profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreReceiver
    (control :
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibrePending
        (Memory := Memory) A strategy) :
    ProfiledRawJointRecurrentFiniteMemoryBankedRightReceiver
      (Memory := Memory) A strategy :=
  if control.1 then control.2.1.2.closedControl
  else control.2.1.2.openControl

noncomputable def
    profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibrePacketBoundaryFork
    (sender : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (oldState : BankControl (Memory := Memory) A strategy)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet : Packet (Memory := Memory) A strategy)
    (input : In₂ × In₁) :
    FiniteDelayedFork
        (ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibrePending
          (Memory := Memory) A strategy) × Out₂ :=
  let oldResult :=
    profiledRawJointRecurrentFiniteMemoryLeftToRightPacketBoundaryFork
      (Memory := Memory) A strategy sender oldState oldReceiver oldOwner
        packet input
  let advancedSender := oldResult.1.openControl.2.1.1
  let fibre := profiledRawJointLeftOwnerFibreControlOfOwner A advancedSender
  (FiniteAcknowledgedDelayedCarrier.deferredMemberFork
      (fibre, oldResult.1.openControl.2.1.2) (),
    oldResult.2)

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype Memory] in
theorem
    profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibrePacketBoundaryFork_coordinates
    (sender : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (oldState : BankControl (Memory := Memory) A strategy)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet : Packet (Memory := Memory) A strategy)
    (input : In₂ × In₁) :
    let fork :=
      (profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibrePacketBoundaryFork
        (Memory := Memory) A strategy sender oldState oldReceiver oldOwner
          packet input).1
    (profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreReceiver
        (Memory := Memory) A strategy fork.openControl).1 = oldState ∧
      (profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreReceiver
        (Memory := Memory) A strategy fork.closedControl).1 =
          packet.successor :=
  ⟨rfl, rfl⟩

omit [Fintype Memory] [Inhabited Out₁] [Inhabited Out₂] in
theorem
    profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibrePacketBoundaryFork_valid
    (sender : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (hsender :
      ProfiledRawJointLeftPhysicalSiblingOwnerReachable A sender.1 sender.2)
    (oldState : BankControl (Memory := Memory) A strategy)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet : Packet (Memory := Memory) A strategy)
    (input : In₂ × In₁) :
    let fork :=
      (profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibrePacketBoundaryFork
        (Memory := Memory) A strategy sender oldState oldReceiver oldOwner
          packet input).1
    ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreValid
        (Memory := Memory) A strategy fork.openControl ∧
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreValid
        (Memory := Memory) A strategy fork.closedControl := by
  dsimp only
  have hadvanced := hsender.step A sender.1 sender.2 input.1
  have hvalid := profiledRawJointLeftOwnerFibreChoiceControl_valid A sender.1
    ((sender.1.memberController A false).step sender.2 input.1) hadvanced
  simpa only [
    profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibrePacketBoundaryFork,
    profiledRawJointRecurrentFiniteMemoryLeftToRightPacketBoundaryFork,
    ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreValid,
    profiledRawJointLeftOwnerFibreControlOfOwner] using And.intro hvalid hvalid

noncomputable def
    profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreStep
    (_member : Bool)
    (shared :
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreShared
        (Memory := Memory) A strategy)
    (input : In₂) :
    ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreShared
        (Memory := Memory) A strategy × Out₂ :=
  let next := profiledRawJointLeftOwnerFibreNoRecv A shared.1 input
  ((next.1, shared.2), next.2)

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype Memory] in
theorem profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreStep_laws :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberStepLaws
      (profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreStep
        (Memory := Memory) A strategy) where
  outputEq := by intro shared input; rfl
  stateEq := by intro shared input; rfl

noncomputable def
    profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreNoRecv
    (control :
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibrePending
        (Memory := Memory) A strategy)
    (input : In₂) :
    ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibrePending
        (Memory := Memory) A strategy × Out₂ :=
  FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
    (profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreStep
      (Memory := Memory) A strategy) control input

omit [Fintype Memory] [Inhabited Out₁] [Inhabited Out₂] in
theorem
    ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreValid.noRecv
    (control :
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibrePending
        (Memory := Memory) A strategy)
    (hvalid :
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreValid
        (Memory := Memory) A strategy control)
    (input : In₂) :
    ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreValid
      (Memory := Memory) A strategy
      (profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreNoRecv
        (Memory := Memory) A strategy control input).1 := by
  rcases control with ⟨member, shared, payload⟩
  have hnext := ProfiledRawJointLeftOwnerFibreValid.noRecv A shared.1 hvalid
    input
  cases member <;>
    simpa [
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreValid,
      profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreNoRecv,
      profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreStep,
      FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv] using hnext

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype Memory] in
theorem
    profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibre_blind_noRecv
    (left right :
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibrePending
        (Memory := Memory) A strategy)
    (input : In₂)
    (hblind :
      FiniteAcknowledgedDelayedCarrier.DeferredMemberBlind left right) :
    (profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreNoRecv
        (Memory := Memory) A strategy left input).2 =
        (profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreNoRecv
          (Memory := Memory) A strategy right input).2 ∧
      FiniteAcknowledgedDelayedCarrier.DeferredMemberBlind
        (profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreNoRecv
          (Memory := Memory) A strategy left input).1
        (profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreNoRecv
          (Memory := Memory) A strategy right input).1 := by
  exact FiniteAcknowledgedDelayedCarrier.deferredMemberBlind_noRecv
    (profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreStep
      (Memory := Memory) A strategy)
    (profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreStep_laws
      (Memory := Memory) A strategy) left right input hblind

/-! ## Exact selected-policy boundary specialization -/

namespace
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection

variable
  (initialMemory : RootKey A strategy → Memory)
  (selection :
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection
      (Memory := Memory) A strategy hwin initialMemory)

/-- At a realized right-to-left reversal, the fresh closed receiver uses the
literal left move installed by the selected augmented successor.  Hence the
total fallback in the executable fork is unreachable, and the successor's
memory is retained literally. -/
theorem rightToLeftOwnerFibrePacketBoundaryFork_closed_of_realizes
    (sender : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (oldState : BankControl (Memory := Memory) A strategy)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (state : BankControl (Memory := Memory) A strategy)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (hrealizes :
      selection.ChildRealizes A strategy hwin initialMemory state target
        (selection.resolveTarget A strategy hwin initialMemory state target))
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .left target () =
      some root)
    (input : In₁ × In₂) :
    let packet :=
      selection.resolvePacket A strategy hwin initialMemory state target
    ∃ move : ProfiledRawJointLeftPhysicalSiblingMove A,
      profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreReceiver
          (Memory := Memory) A strategy
          (profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibrePacketBoundaryFork
            (Memory := Memory) A strategy sender oldState oldReceiver oldOwner
              packet input).1.closedControl =
        (packet.successor,
          initialProfiledRawJointLeftPhysicalSiblingReceiver A move
            .both) := by
  dsimp only
  obtain ⟨move, hmove⟩ :=
    selection.resolvePacket_leftMove_exists A strategy hwin initialMemory
      state target hrealizes root hroot
  refine ⟨move, ?_⟩
  exact
    profiledRawJointRecurrentFiniteMemoryRightToLeftPacketBoundaryFork_closed_of_move
      (Memory := Memory) A strategy sender oldState oldReceiver oldOwner
        (selection.resolvePacket A strategy hwin initialMemory state target)
          input move hmove

/-- Mirrored exact closed-receiver specialization. -/
theorem leftToRightOwnerFibrePacketBoundaryFork_closed_of_realizes
    (sender : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (oldState : BankControl (Memory := Memory) A strategy)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (state : BankControl (Memory := Memory) A strategy)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (hrealizes :
      selection.ChildRealizes A strategy hwin initialMemory state target
        (selection.resolveTarget A strategy hwin initialMemory state target))
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .right target () =
      some root)
    (input : In₂ × In₁) :
    let packet :=
      selection.resolvePacket A strategy hwin initialMemory state target
    ∃ move : ProfiledRawJointRightPhysicalSiblingMove A,
      profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreReceiver
          (Memory := Memory) A strategy
          (profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibrePacketBoundaryFork
            (Memory := Memory) A strategy sender oldState oldReceiver oldOwner
              packet input).1.closedControl =
        (packet.successor,
          initialProfiledRawJointRightPhysicalSiblingReceiver A move
            .both) := by
  dsimp only
  obtain ⟨move, hmove⟩ :=
    selection.resolvePacket_rightMove_exists A strategy hwin initialMemory
      state target hrealizes root hroot
  refine ⟨move, ?_⟩
  exact
    profiledRawJointRecurrentFiniteMemoryLeftToRightPacketBoundaryFork_closed_of_move
      (Memory := Memory) A strategy sender oldState oldReceiver oldOwner
        (selection.resolvePacket A strategy hwin initialMemory state target)
          input move hmove

end
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection

end

end DetParityAutomaton

end DistributedSynthesis
