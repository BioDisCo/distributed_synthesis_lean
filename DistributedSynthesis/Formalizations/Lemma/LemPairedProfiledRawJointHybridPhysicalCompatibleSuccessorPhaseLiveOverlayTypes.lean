/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingPhaseLiveOverlay
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorLocalReachability

/-!
# Finite phase-live overlay types for compatible successor tables

The one-cut compatible-successor controller kept the dormant sender which is
delivered to the opposite endpoint, but discarded the receiver just advanced
by the informed endpoint.  That is insufficient on a repeated one-way block.
This file instantiates the generic finite `PhaseLiveShared` wrapper with the
compatible successor data:

* the original frontier shared value is the dormant outgoing owner;
* the original frontier payload is retained inside the shared value, so its
  old member can be reconstructed after acknowledgement;
* the endpoint-local phase distinguishes a repeated receive from a switch;
* a finite fork retains the two interpretations of the locally live receiver.

The outer deferred payload is consequently `PUnit`.  Process one's blind step
writes phase `false`; process two's writes phase `true`.  These constants are
facts about which local handler ran.  They are not observations of a graph,
orientation, hierarchy side, leader, or strict leader.
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

private abbrev CompatiblePolicy
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleRationalPolicy A strategy hwin
    initial

private abbrev CompatibleState
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatiblePolicyState A strategy hwin initial

private abbrev BaseOneShared
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  ProfiledRawJointHybridPhysicalCompatibleFrontierOneShared.{u, v, x, y, s,
    max u v x y s} A strategy hwin policy

private abbrev BaseTwoShared
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  ProfiledRawJointHybridPhysicalCompatibleFrontierTwoShared.{u, v, x, y, s,
    max u v x y s} A strategy hwin policy

private abbrev BaseOnePayload
    {initial : ProfiledRawJointCommonBaseWorld A strategy} :=
  ProfiledRawJointHybridPhysicalCompatibleFrontierOnePayload A strategy hwin
    (initial := initial)

private abbrev BaseTwoPayload
    {initial : ProfiledRawJointCommonBaseWorld A strategy} :=
  ProfiledRawJointHybridPhysicalCompatibleFrontierTwoPayload A strategy hwin
    (initial := initial)

/-! ## Dormant owner aliases -/

/-- Sigma-packed right owner carried by process one and delivered to process
two. -/
noncomputable abbrev
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightOwner
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  ProfiledRawJointHybridPhysicalCompatibleFrontierOneShared.{u, v, x, y, s,
    max u v x y s} A strategy hwin policy

/-- Sigma-packed left owner carried by process two and delivered to process
one. -/
noncomputable abbrev
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftOwner
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  ProfiledRawJointHybridPhysicalCompatibleFrontierTwoShared.{u, v, x, y, s,
    max u v x y s} A strategy hwin policy

noncomputable instance
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :
    Fintype
      (ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightOwner A strategy
        hwin policy) := by
  classical infer_instance

noncomputable instance
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :
    Fintype
      (ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftOwner A strategy
        hwin policy) := by
  classical infer_instance

/-! ## Retained receiver payloads -/

/-- Process two receives a right-table owner from process one.  Its retained
receiver is packed with the compatible key at which that payload is typed. -/
noncomputable abbrev
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiver
    {initial : ProfiledRawJointCommonBaseWorld A strategy} :=
  Σ state : CompatibleState A strategy hwin initial,
    ProfiledRawJointHybridPhysicalCompatibleRightPayload A strategy hwin
      (initial := initial)

/-- Process-one mirror for a delivered left-table owner. -/
noncomputable abbrev
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiver
    {initial : ProfiledRawJointCommonBaseWorld A strategy} :=
  Σ state : CompatibleState A strategy hwin initial,
    ProfiledRawJointHybridPhysicalCompatibleLeftPayload A strategy hwin
      (initial := initial)

noncomputable instance
    {initial : ProfiledRawJointCommonBaseWorld A strategy} :
    Fintype
      (ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiver A
        strategy hwin (initial := initial)) := by
  classical infer_instance

noncomputable instance
    {initial : ProfiledRawJointCommonBaseWorld A strategy} :
    Fintype
      (ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiver A strategy
        hwin (initial := initial)) := by
  classical infer_instance

/-! ## Endpoint overlays -/

/-- Process one carries its dormant right owner, its original left-output
pending payload, and the two possible locally retained left receivers. -/
noncomputable abbrev
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveOneShared
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  FiniteAcknowledgedDelayedCarrier.PhaseLiveShared
    (BaseOneShared A strategy hwin policy)
    (BaseOnePayload A strategy hwin (initial := initial))
    (ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiver A strategy
      hwin (initial := initial))

/-- Process-two mirror: dormant left owner, original right-output payload, and
the two retained right-receiver interpretations. -/
noncomputable abbrev
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTwoShared
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  FiniteAcknowledgedDelayedCarrier.PhaseLiveShared
    (BaseTwoShared A strategy hwin policy)
    (BaseTwoPayload A strategy hwin (initial := initial))
    (ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiver A strategy
      hwin (initial := initial))

noncomputable instance
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :
    Fintype
      (ProfiledRawJointHybridPhysicalCompatiblePhaseLiveOneShared A strategy
        hwin policy) := by
  classical infer_instance

noncomputable instance
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :
    Fintype
      (ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTwoShared A strategy
        hwin policy) := by
  classical infer_instance

abbrev ProfiledRawJointHybridPhysicalCompatiblePhaseLiveOnePending
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (ProfiledRawJointHybridPhysicalCompatiblePhaseLiveOneShared A strategy hwin
      policy)
    PUnit

abbrev ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTwoPending
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTwoShared A strategy hwin
      policy)
    PUnit

/-! ## Reconstruction of the old compatible frontier controls -/

/-- The overlay does not alter the acknowledged old control: selecting its
outer member reconstructs exactly the former process-one pending shape. -/
def profiledRawJointHybridPhysicalCompatiblePhaseLiveOneBasePending
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    (pending :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveOnePending A strategy
        hwin policy) :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
      (BaseOneShared A strategy hwin policy)
      (BaseOnePayload A strategy hwin (initial := initial)) :=
  pending.2.1.basePending pending.1

/-- Process-two mirror. -/
def profiledRawJointHybridPhysicalCompatiblePhaseLiveTwoBasePending
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    (pending :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTwoPending A strategy
        hwin policy) :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
      (BaseTwoShared A strategy hwin policy)
      (BaseTwoPayload A strategy hwin (initial := initial)) :=
  pending.2.1.basePending pending.1

@[simp] theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveOneBasePending_member
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    (pending :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveOnePending A strategy
        hwin policy) :
    (profiledRawJointHybridPhysicalCompatiblePhaseLiveOneBasePending A strategy
      hwin pending).1 = pending.1 :=
  rfl

@[simp] theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveTwoBasePending_member
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    (pending :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTwoPending A strategy
        hwin policy) :
    (profiledRawJointHybridPhysicalCompatiblePhaseLiveTwoBasePending A strategy
      hwin pending).1 = pending.1 :=
  rfl

/-! ## Member-coherent blind steps with local phase writes -/

/-- A process-one nonreceive advances only its dormant right owner and writes
the local switch phase `false`. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatiblePhaseLiveOnePendingStep
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  FiniteAcknowledgedDelayedCarrier.phaseLivePendingStep
    (BasePayload := BaseOnePayload A strategy hwin (initial := initial))
    (Receiver :=
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiver A strategy
        hwin (initial := initial))
    false
    (profiledRawJointHybridPhysicalCompatibleFrontierOnePendingStep A strategy
      hwin policy)

/-- Process-two nonreceive mirror; its locally meaningful switch phase is
`true`. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatiblePhaseLiveTwoPendingStep
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  FiniteAcknowledgedDelayedCarrier.phaseLivePendingStep
    (BasePayload := BaseTwoPayload A strategy hwin (initial := initial))
    (Receiver :=
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiver A strategy
        hwin (initial := initial))
    true
    (profiledRawJointHybridPhysicalCompatibleFrontierTwoPendingStep A strategy
      hwin policy)

theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveOnePendingStep_laws
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberStepLaws
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveOnePendingStep A
        strategy hwin policy) := by
  exact FiniteAcknowledgedDelayedCarrier.phaseLivePendingStep_laws
    (BasePayload := BaseOnePayload A strategy hwin (initial := initial))
    (Receiver :=
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiver A strategy
        hwin (initial := initial))
    false
    (profiledRawJointHybridPhysicalCompatibleFrontierOnePendingStep A strategy
      hwin policy)
    (profiledRawJointHybridPhysicalCompatibleFrontierOnePendingStep_laws A
      strategy hwin policy)

theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveTwoPendingStep_laws
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberStepLaws
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveTwoPendingStep A
        strategy hwin policy) := by
  exact FiniteAcknowledgedDelayedCarrier.phaseLivePendingStep_laws
    (BasePayload := BaseTwoPayload A strategy hwin (initial := initial))
    (Receiver :=
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiver A strategy
        hwin (initial := initial))
    true
    (profiledRawJointHybridPhysicalCompatibleFrontierTwoPendingStep A strategy
      hwin policy)
    (profiledRawJointHybridPhysicalCompatibleFrontierTwoPendingStep_laws A
      strategy hwin policy)

@[simp] theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveOnePendingStep_phase
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) (member : Bool)
    (shared :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveOneShared A strategy
        hwin policy)
    (input : In₁) :
    (profiledRawJointHybridPhysicalCompatiblePhaseLiveOnePendingStep A strategy
      hwin policy member shared input).1.localPhase = false :=
  rfl

@[simp] theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveTwoPendingStep_phase
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) (member : Bool)
    (shared :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveTwoShared A strategy
        hwin policy)
    (input : In₂) :
    (profiledRawJointHybridPhysicalCompatiblePhaseLiveTwoPendingStep A strategy
      hwin policy member shared input).1.localPhase = true :=
  rfl

end

end DetParityAutomaton

end DistributedSynthesis
