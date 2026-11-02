/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailCarrier
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorOperationalClose

/-!
# Finite phase-live types in a delivered-tag tail fibre

The run-automaton state type does not depend on its chosen initial control.
Consequently the already tested row/payload containers can be reused as
finite *data containers* below the re-rooted tag, while all semantic key laws
come from the tail-relative decoration and never from the old common-root
policy.

Each type is nevertheless indexed by the complete finite tag.  This keeps the
initial guarded occurrence available to the outer dependent bank and prevents
mixing fibres which merely share the same unguarded annotation IDs.
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

private abbrev Tag :=
  ProfiledRawJointHybridShadowPhaseLiveTag A strategy hwin

private abbrev TailState (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailState A strategy hwin tag

private abbrev TailInitial (tag : Tag A strategy hwin) :=
  (profiledRawJointHybridShadowPhaseLiveInstalled A strategy hwin tag.origin
    ).world

private abbrev RightOutput (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailRightReceiverOutput A strategy hwin
    tag

private abbrev LeftOutput (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailLeftReceiverOutput A strategy hwin
    tag

/-! ## Reusing the row/payload data containers -/

/-- Tail states are definitionally the same finite carrier type as the old
run automaton at the tag's installed world; only their policy and reachability
meaning differ. -/
theorem profiledRawJointHybridShadowPhaseLiveTailState_carrier_rfl
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag) :
    (state : ProfiledRawJointHybridPhysicalCompatiblePolicyState A strategy
      hwin (TailInitial A strategy hwin tag)) = state :=
  rfl

noncomputable abbrev
    ProfiledRawJointHybridShadowPhaseLiveTailRightPayload
    (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridPhysicalCompatibleRightPayload A strategy hwin
    (initial := TailInitial A strategy hwin tag)

noncomputable abbrev
    ProfiledRawJointHybridShadowPhaseLiveTailLeftPayload
    (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridPhysicalCompatibleLeftPayload A strategy hwin
    (initial := TailInitial A strategy hwin tag)

noncomputable def profiledRawJointHybridShadowPhaseLiveTailRightPayloadAtRow
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag)
    (row : PairedEntryRow) :
    ProfiledRawJointHybridShadowPhaseLiveTailRightPayload A strategy hwin tag :=
  profiledRawJointHybridPhysicalCompatibleRightPayloadAtRow A strategy hwin
    state row

noncomputable def profiledRawJointHybridShadowPhaseLiveTailLeftPayloadAtRow
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag)
    (row : PairedEntryRow) :
    ProfiledRawJointHybridShadowPhaseLiveTailLeftPayload A strategy hwin tag :=
  profiledRawJointHybridPhysicalCompatibleLeftPayloadAtRow A strategy hwin
    state row

/-- One right close has selected a tail key and retains both possible next
left-receiver rows. -/
noncomputable abbrev
    ProfiledRawJointHybridShadowPhaseLiveTailRightPendingPayload
    (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridPhysicalCompatibleRightPendingPayload A strategy hwin
    (initial := TailInitial A strategy hwin tag)

/-- Left-close mirror. -/
noncomputable abbrev
    ProfiledRawJointHybridShadowPhaseLiveTailLeftPendingPayload
    (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridPhysicalCompatibleLeftPendingPayload A strategy hwin
    (initial := TailInitial A strategy hwin tag)

noncomputable def
    profiledRawJointHybridShadowPhaseLiveTailRightPendingPayloadOfOutput
    (tag : Tag A strategy hwin) (output : RightOutput A strategy hwin tag)
    (entryRow : PairedEntryRow) :
    ProfiledRawJointHybridShadowPhaseLiveTailRightPendingPayload A strategy hwin
      tag :=
  profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfOutput A
    strategy hwin output entryRow

noncomputable def
    profiledRawJointHybridShadowPhaseLiveTailLeftPendingPayloadOfOutput
    (tag : Tag A strategy hwin) (output : LeftOutput A strategy hwin tag)
    (entryRow : PairedEntryRow) :
    ProfiledRawJointHybridShadowPhaseLiveTailLeftPendingPayload A strategy hwin
      tag :=
  profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfOutput A strategy
    hwin output entryRow

def profiledRawJointHybridShadowPhaseLiveTailRightPendingPayloadTarget
    (tag : Tag A strategy hwin)
    (payload :
      ProfiledRawJointHybridShadowPhaseLiveTailRightPendingPayload A strategy
        hwin tag)
    (member : Bool) :
    ProfiledRawJointHybridShadowPhaseLiveTailSuccessorTarget A strategy hwin
      tag :=
  profiledRawJointHybridPhysicalCompatibleRightPendingPayloadTarget A strategy
    hwin payload member

def profiledRawJointHybridShadowPhaseLiveTailLeftPendingPayloadTarget
    (tag : Tag A strategy hwin)
    (payload :
      ProfiledRawJointHybridShadowPhaseLiveTailLeftPendingPayload A strategy
        hwin tag)
    (member : Bool) :
    ProfiledRawJointHybridShadowPhaseLiveTailSuccessorTarget A strategy hwin
      tag :=
  profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadTarget A strategy
    hwin payload member

def profiledRawJointHybridShadowPhaseLiveTailRightPendingPayloadReceiver
    (tag : Tag A strategy hwin)
    (payload :
      ProfiledRawJointHybridShadowPhaseLiveTailRightPendingPayload A strategy
        hwin tag)
    (member : Bool) :
    ProfiledRawJointHybridShadowPhaseLiveTailLeftPayload A strategy hwin tag :=
  profiledRawJointHybridPhysicalCompatibleRightPendingPayloadReceiver A
    strategy hwin payload member

def profiledRawJointHybridShadowPhaseLiveTailLeftPendingPayloadReceiver
    (tag : Tag A strategy hwin)
    (payload :
      ProfiledRawJointHybridShadowPhaseLiveTailLeftPendingPayload A strategy
        hwin tag)
    (member : Bool) :
    ProfiledRawJointHybridShadowPhaseLiveTailRightPayload A strategy hwin tag :=
  profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadReceiver A strategy
    hwin payload member

@[simp] theorem
    profiledRawJointHybridShadowPhaseLiveTailRightPendingPayloadOfOutput_target
    (tag : Tag A strategy hwin) (output : RightOutput A strategy hwin tag)
    (entryRow : PairedEntryRow) (closeMember : Bool) :
    profiledRawJointHybridShadowPhaseLiveTailRightPendingPayloadTarget A
        strategy hwin tag
        (profiledRawJointHybridShadowPhaseLiveTailRightPendingPayloadOfOutput A
          strategy hwin tag output entryRow) closeMember =
      (output.target entryRow).1 :=
  rfl

@[simp] theorem
    profiledRawJointHybridShadowPhaseLiveTailLeftPendingPayloadOfOutput_target
    (tag : Tag A strategy hwin) (output : LeftOutput A strategy hwin tag)
    (entryRow : PairedEntryRow) (closeMember : Bool) :
    profiledRawJointHybridShadowPhaseLiveTailLeftPendingPayloadTarget A strategy
        hwin tag
        (profiledRawJointHybridShadowPhaseLiveTailLeftPendingPayloadOfOutput A
          strategy hwin tag output entryRow) closeMember =
      (output.target entryRow).1 :=
  rfl

/-! ## Tag-indexed phase-live endpoint types -/

/-- Process one's dormant right owner, with the dynamic tail key packed in the
same tag fibre. -/
noncomputable abbrev
    ProfiledRawJointHybridShadowPhaseLiveTailFrontierOneShared
    (tag : Tag A strategy hwin) :=
  Σ state : TailState A strategy hwin tag,
    ProfiledRawJointHybridShadowPhaseLiveTailRightShared A strategy hwin tag
      state

/-- Process-two dormant left owner. -/
noncomputable abbrev
    ProfiledRawJointHybridShadowPhaseLiveTailFrontierTwoShared
    (tag : Tag A strategy hwin) :=
  Σ state : TailState A strategy hwin tag,
    ProfiledRawJointHybridShadowPhaseLiveTailLeftShared A strategy hwin tag
      state

noncomputable instance (tag : Tag A strategy hwin) :
    Fintype
      (ProfiledRawJointHybridShadowPhaseLiveTailFrontierOneShared A strategy
        hwin tag) := by
  classical infer_instance

noncomputable instance (tag : Tag A strategy hwin) :
    Fintype
      (ProfiledRawJointHybridShadowPhaseLiveTailFrontierTwoShared A strategy
        hwin tag) := by
  classical infer_instance

/-- Process one retains a left receiver at the tail key where it is typed. -/
noncomputable abbrev
    ProfiledRawJointHybridShadowPhaseLiveTailLeftReceiver
    (tag : Tag A strategy hwin) :=
  TailState A strategy hwin tag ×
    ProfiledRawJointHybridShadowPhaseLiveTailLeftPayload A strategy hwin tag

/-- Process-two right receiver mirror. -/
noncomputable abbrev
    ProfiledRawJointHybridShadowPhaseLiveTailRightReceiver
    (tag : Tag A strategy hwin) :=
  TailState A strategy hwin tag ×
    ProfiledRawJointHybridShadowPhaseLiveTailRightPayload A strategy hwin tag

noncomputable instance (tag : Tag A strategy hwin) :
    Fintype
      (ProfiledRawJointHybridShadowPhaseLiveTailLeftReceiver A strategy hwin
        tag) := by
  classical infer_instance

noncomputable instance (tag : Tag A strategy hwin) :
    Fintype
      (ProfiledRawJointHybridShadowPhaseLiveTailRightReceiver A strategy hwin
        tag) := by
  classical infer_instance

noncomputable abbrev
    ProfiledRawJointHybridShadowPhaseLiveTailOneShared
    (tag : Tag A strategy hwin) :=
  FiniteAcknowledgedDelayedCarrier.PhaseLiveShared
    (ProfiledRawJointHybridShadowPhaseLiveTailFrontierOneShared A strategy hwin
      tag)
    (ProfiledRawJointHybridShadowPhaseLiveTailLeftPendingPayload A strategy hwin
      tag)
    (ProfiledRawJointHybridShadowPhaseLiveTailLeftReceiver A strategy hwin tag)

noncomputable abbrev
    ProfiledRawJointHybridShadowPhaseLiveTailTwoShared
    (tag : Tag A strategy hwin) :=
  FiniteAcknowledgedDelayedCarrier.PhaseLiveShared
    (ProfiledRawJointHybridShadowPhaseLiveTailFrontierTwoShared A strategy hwin
      tag)
    (ProfiledRawJointHybridShadowPhaseLiveTailRightPendingPayload A strategy
      hwin tag)
    (ProfiledRawJointHybridShadowPhaseLiveTailRightReceiver A strategy hwin
      tag)

noncomputable instance (tag : Tag A strategy hwin) :
    Fintype
      (ProfiledRawJointHybridShadowPhaseLiveTailOneShared A strategy hwin
        tag) := by
  classical infer_instance

noncomputable instance (tag : Tag A strategy hwin) :
    Fintype
      (ProfiledRawJointHybridShadowPhaseLiveTailTwoShared A strategy hwin
        tag) := by
  classical infer_instance

abbrev ProfiledRawJointHybridShadowPhaseLiveTailOnePending
    (tag : Tag A strategy hwin) :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (ProfiledRawJointHybridShadowPhaseLiveTailOneShared A strategy hwin tag)
    PUnit

abbrev ProfiledRawJointHybridShadowPhaseLiveTailTwoPending
    (tag : Tag A strategy hwin) :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (ProfiledRawJointHybridShadowPhaseLiveTailTwoShared A strategy hwin tag)
    PUnit

/-! ## Member-coherent local blind steps -/

noncomputable def
    profiledRawJointHybridShadowPhaseLiveTailFrontierOnePendingStep
    (tag : Tag A strategy hwin) :=
  FiniteAcknowledgedDelayedCarrier.keyedDeferredSharedStep
    (fun state ↦
      profiledRawJointHybridShadowPhaseLiveTailRightSharedStep A strategy hwin
        tag state)

noncomputable def
    profiledRawJointHybridShadowPhaseLiveTailFrontierTwoPendingStep
    (tag : Tag A strategy hwin) :=
  FiniteAcknowledgedDelayedCarrier.keyedDeferredSharedStep
    (fun state ↦
      profiledRawJointHybridShadowPhaseLiveTailLeftSharedStep A strategy hwin
        tag state)

theorem
    profiledRawJointHybridShadowPhaseLiveTailFrontierOnePendingStep_laws
    (tag : Tag A strategy hwin) :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberStepLaws
      (profiledRawJointHybridShadowPhaseLiveTailFrontierOnePendingStep A
        strategy hwin tag) :=
  profiledRawJointHybridShadowPhaseLiveTailRightDeferredStep_laws A strategy
    hwin tag

theorem
    profiledRawJointHybridShadowPhaseLiveTailFrontierTwoPendingStep_laws
    (tag : Tag A strategy hwin) :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberStepLaws
      (profiledRawJointHybridShadowPhaseLiveTailFrontierTwoPendingStep A
        strategy hwin tag) :=
  profiledRawJointHybridShadowPhaseLiveTailLeftDeferredStep_laws A strategy hwin
    tag

noncomputable def
    profiledRawJointHybridShadowPhaseLiveTailOnePendingStep
    (tag : Tag A strategy hwin) :=
  FiniteAcknowledgedDelayedCarrier.phaseLivePendingStep
    (BasePayload :=
      ProfiledRawJointHybridShadowPhaseLiveTailLeftPendingPayload A strategy
        hwin tag)
    (Receiver :=
      ProfiledRawJointHybridShadowPhaseLiveTailLeftReceiver A strategy hwin
        tag)
    false
    (profiledRawJointHybridShadowPhaseLiveTailFrontierOnePendingStep A strategy
      hwin tag)

noncomputable def
    profiledRawJointHybridShadowPhaseLiveTailTwoPendingStep
    (tag : Tag A strategy hwin) :=
  FiniteAcknowledgedDelayedCarrier.phaseLivePendingStep
    (BasePayload :=
      ProfiledRawJointHybridShadowPhaseLiveTailRightPendingPayload A strategy
        hwin tag)
    (Receiver :=
      ProfiledRawJointHybridShadowPhaseLiveTailRightReceiver A strategy hwin
        tag)
    true
    (profiledRawJointHybridShadowPhaseLiveTailFrontierTwoPendingStep A strategy
      hwin tag)

theorem profiledRawJointHybridShadowPhaseLiveTailOnePendingStep_laws
    (tag : Tag A strategy hwin) :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberStepLaws
      (profiledRawJointHybridShadowPhaseLiveTailOnePendingStep A strategy hwin
        tag) := by
  exact FiniteAcknowledgedDelayedCarrier.phaseLivePendingStep_laws
    (BasePayload :=
      ProfiledRawJointHybridShadowPhaseLiveTailLeftPendingPayload A strategy
        hwin tag)
    (Receiver :=
      ProfiledRawJointHybridShadowPhaseLiveTailLeftReceiver A strategy hwin
        tag)
    false
    (profiledRawJointHybridShadowPhaseLiveTailFrontierOnePendingStep A strategy
      hwin tag)
    (profiledRawJointHybridShadowPhaseLiveTailFrontierOnePendingStep_laws A
      strategy hwin tag)

theorem profiledRawJointHybridShadowPhaseLiveTailTwoPendingStep_laws
    (tag : Tag A strategy hwin) :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberStepLaws
      (profiledRawJointHybridShadowPhaseLiveTailTwoPendingStep A strategy hwin
        tag) := by
  exact FiniteAcknowledgedDelayedCarrier.phaseLivePendingStep_laws
    (BasePayload :=
      ProfiledRawJointHybridShadowPhaseLiveTailRightPendingPayload A strategy
        hwin tag)
    (Receiver :=
      ProfiledRawJointHybridShadowPhaseLiveTailRightReceiver A strategy hwin
        tag)
    true
    (profiledRawJointHybridShadowPhaseLiveTailFrontierTwoPendingStep A strategy
      hwin tag)
    (profiledRawJointHybridShadowPhaseLiveTailFrontierTwoPendingStep_laws A
      strategy hwin tag)

end

end DetParityAutomaton

end DistributedSynthesis
