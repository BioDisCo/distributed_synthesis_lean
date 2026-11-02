/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPulsedSourceInstallationAudit

/-!
# Literal output pairs at owner reversals

The installed/staged decoder replaces the dormant template by the packet's
fresh receiver. Both endpoints therefore use the same fresh table at the
first reversal. This is an output identity of the raw owner kernel.
-/

namespace DistributedSynthesis
namespace DetParityAutomaton

universe u v x y s m
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable {Memory : Type m}
variable (A : DetParityAutomaton.{max u v x y, s}
  (RoundRecord In₁ In₂ Graph Out₁ Out₂))
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
variable (hwin : ∀ env, A.Accepts (execution strategy env))

noncomputable section

namespace ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection

theorem ownerFibreRound_left_installedStaged_outputs
    (tables : ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection
      (Memory := Memory) A strategy)
    (state : ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankControl
      (Memory := Memory) A strategy)
    (receiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (template : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (packet : ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankResolvedTarget
      (Memory := Memory) A strategy)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hmove : packet.successor.2.1.1.2.2 = some move)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentFiniteMemoryBoundaryBankCoordinates
        (Memory := Memory) A strategy)
    (input : In₁ × In₂) :
    (tables.ownerFibreRound A strategy hwin
      ((.inl (.inr (state, ⟨receiver.1, owner⟩, template)), oneCoordinates),
       (.inl (.inl (state, receiver, some packet)), twoCoordinates))
      input .left).2 =
    ((stepProfiledRawJointLeftPhysicalSiblingReceiverFor A move
      (move.memberController A false).initial .first
      (profiledRawJointLeftPhysicalSiblingMonitor A move.1 false).initial input).1,
     ((move.memberController A false).labelOf
       (move.memberController A false).initial).1 input.2) := by
  have hdecode :=
    profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?_installedStaged
      (Memory := Memory) A strategy state receiver owner template packet move
        hmove oneCoordinates twoCoordinates
  simp only [ownerFibreRound, ownerFibreBoundaryOpenRecvOne,
    ownerFibreBoundaryReceive?, hdecode]
  simp only [rightPhaseOwnerFibreReceive, rightBoundaryOwnerFibreReceive,
    profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibrePacketBoundaryFork,
    profiledRawJointRecurrentFiniteMemoryRightToLeftPacketBoundaryFork_output,
    profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvTwo,
    profiledRawJointRecurrentFiniteMemoryRightToLeftBridgeNoRecv, hmove]
  rfl

/-- After the first left reversal, a following right round reads the old
right owner advanced once. The fresh left installation does not reset or
receipt-update that retained right controller. -/
theorem ownerFibreRound_left_right_installedStaged_blind
    (tables : ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection
      (Memory := Memory) A strategy)
    (state : ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankControl
      (Memory := Memory) A strategy)
    (receiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (template : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (packet : ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankResolvedTarget
      (Memory := Memory) A strategy)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hmove : packet.successor.2.1.1.2.2 = some move)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentFiniteMemoryBoundaryBankCoordinates
        (Memory := Memory) A strategy)
    (first second : In₁ × In₂) :
    (tables.ownerFibreRound A strategy hwin
      (tables.ownerFibreRound A strategy hwin
        ((.inl (.inr (state, ⟨receiver.1, owner⟩, template)), oneCoordinates),
         (.inl (.inl (state, receiver, some packet)), twoCoordinates))
        first .left).1 second .right).2.1 =
      (((receiver.1.memberController A false).labelOf
        ((receiver.1.memberController A false).step owner first.1)).1 second.1) := by
  have hdecode :=
    profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?_installedStaged
      (Memory := Memory) A strategy state receiver owner template packet move
        hmove oneCoordinates twoCoordinates
  simp only [ownerFibreRound, ownerFibreBoundaryOpenRecvOne,
    ownerFibreBoundaryReceive?, hdecode]
  rfl

end ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection
end
end DetParityAutomaton

namespace PulsedSourceInstallationAudit
open DetParityAutomaton TwoProcessNoResetReversalObstruction
open TwoProcessPhysicalTargetAudit (pulsedSource pulsedSource_wins)

noncomputable section
universe m
variable {Memory : Type m}

/-- Both literal outputs, not merely the newly blind endpoint, grant at the
installed/staged reversal following the candidate's non-granting target. -/
theorem owner_first_reversal_grants
    (tables : ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection
      (Memory := Memory) objective pulsedSource)
    (state : ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankControl
      (Memory := Memory) objective pulsedSource)
    (hrealizes : tables.ChildRealizes objective pulsedSource pulsedSource_wins
      state (PulsedSourceBlockFlexibility.rightTarget false)
      (tables.resolveTarget objective pulsedSource pulsedSource_wins state
        (PulsedSourceBlockFlexibility.rightTarget false)))
    (receiver : ProfiledRawJointRightPhysicalSiblingReceiver objective)
    (owner : (receiver.1.memberController objective false).Control)
    (template : ProfiledRawJointLeftPhysicalSiblingReceiver objective)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentFiniteMemoryBoundaryBankCoordinates
        (Memory := Memory) objective pulsedSource) :
    let packet := tables.resolvePacket objective pulsedSource pulsedSource_wins
      state (PulsedSourceBlockFlexibility.rightTarget false)
    (tables.ownerFibreRound objective pulsedSource pulsedSource_wins
      ((.inl (.inr (state, ⟨receiver.1, owner⟩, template)), oneCoordinates),
       (.inl (.inl (state, receiver, some packet)), twoCoordinates))
      ((), ()) .left).2 = (true, true) := by
  obtain ⟨move, hmove⟩ :=
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTable.childRealizes_resolvePacket_leftMove_exists
      objective pulsedSource pulsedSource_wins tables state _ hrealizes
      (.inr nonGrantingTargetSlot) rightTarget_false_currentSlot
  obtain ⟨family, direction, member, hmember, hsource, hdescriptor⟩ :=
    realized_packet_left_provenance tables state hrealizes move hmove
  have hgrant := Bool.and_eq_true_iff.mp
    (left_first_outputs_grant family direction member hmember hsource move hdescriptor)
  dsimp only
  rw [tables.ownerFibreRound_left_installedStaged_outputs objective pulsedSource
    pulsedSource_wins state receiver owner template _ move hmove
      oneCoordinates twoCoordinates ((), ())]
  exact Prod.ext hgrant.1 hgrant.2

end
end PulsedSourceInstallationAudit
end DistributedSynthesis
