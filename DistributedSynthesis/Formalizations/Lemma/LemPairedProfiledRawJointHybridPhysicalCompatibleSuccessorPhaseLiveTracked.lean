/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorPhaseLiveFreshPair
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorAlignedOutputTarget

/-!
# Reachable live keys for the compatible successor phase overlay

The local alignment predicates remember that an owner and receiver have read
one common finite prefix.  For recurrent composition we additionally retain
the proof-side facts that their policy key is reachable, one-sided, and has a
literal live crossed root.  None of these witnesses is executable controller
data, and in particular no process is told a graph orientation or strict
leader.
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

private abbrev RightOwner
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightOwner A strategy hwin
    policy

private abbrev LeftOwner
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftOwner A strategy hwin
    policy

private abbrev RightReceiver
    {initial : ProfiledRawJointCommonBaseWorld A strategy} :=
  ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiver A strategy
    hwin (initial := initial)

private abbrev LeftReceiver
    {initial : ProfiledRawJointCommonBaseWorld A strategy} :=
  ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiver A strategy hwin
    (initial := initial)

private abbrev RightOutput
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleSuccessorRightReceiverOutput A
    strategy hwin initial

private abbrev LeftOutput
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleSuccessorLeftReceiverOutput A
    strategy hwin initial

/-! ## The two proof-side tracked relations -/

/-- A right owner/receiver pair that is aligned at one reachable, one-sided
compatible-policy key with a literal right live root. -/
structure ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightTracked
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (owner : RightOwner A strategy hwin policy)
    (receiver : RightReceiver A strategy hwin (initial := initial)) : Prop where
  aligned :
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightAligned A strategy
      hwin policy owner receiver
  reachable :
    ProfiledRawJointHybridPhysicalCompatibleReachable A strategy hwin initial
      policy owner.1
  oneSided : ∃ code : ProfiledRawJointIncidenceCode A (I := Unit),
    owner.1.1.1 = .oneSided code
  live : ∃ root : ProfiledRawJointThreadRoot A,
    profiledRawJointHybridCurrentSlots A .right owner.1.1.1 () = some root

/-- Left mirror. -/
structure ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftTracked
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (owner : LeftOwner A strategy hwin policy)
    (receiver : LeftReceiver A strategy hwin (initial := initial)) : Prop where
  aligned :
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftAligned A strategy
      hwin policy owner receiver
  reachable :
    ProfiledRawJointHybridPhysicalCompatibleReachable A strategy hwin initial
      policy owner.1
  oneSided : ∃ code : ProfiledRawJointIncidenceCode A (I := Unit),
    owner.1.1.1 = .oneSided code
  live : ∃ root : ProfiledRawJointThreadRoot A,
    profiledRawJointHybridCurrentSlots A .left owner.1.1.1 () = some root

/-! ## Repeated one-way rounds preserve tracked keys -/

theorem
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightTracked.step
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {owner : RightOwner A strategy hwin policy}
    {receiver : RightReceiver A strategy hwin (initial := initial)}
    (tracked :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightTracked A strategy
        hwin policy owner receiver)
    (fallback : RightOutput A strategy hwin initial)
    (member : Bool) (input : In₂ × In₁) :
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightTracked A strategy
      hwin policy
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightOwnerStep A
        strategy hwin policy member owner input.2).1
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverStep A
        strategy hwin policy fallback owner receiver input).2 := by
  refine
    { aligned :=
        profiledRawJointHybridPhysicalCompatiblePhaseLiveRight_step_preserves
          A strategy hwin policy fallback owner receiver tracked.aligned member
            input
      reachable := ?_
      oneSided := ?_
      live := ?_ }
  · simpa
      [profiledRawJointHybridPhysicalCompatiblePhaseLiveRightOwnerStep]
      using tracked.reachable
  · rcases tracked.oneSided with ⟨code, hcode⟩
    exact ⟨code, by
      simpa [profiledRawJointHybridPhysicalCompatiblePhaseLiveRightOwnerStep]
        using hcode⟩
  · rcases tracked.live with ⟨root, hlive⟩
    exact ⟨root, by
      simpa [profiledRawJointHybridPhysicalCompatiblePhaseLiveRightOwnerStep]
        using hlive⟩

theorem
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftTracked.step
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {owner : LeftOwner A strategy hwin policy}
    {receiver : LeftReceiver A strategy hwin (initial := initial)}
    (tracked :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftTracked A strategy
        hwin policy owner receiver)
    (fallback : LeftOutput A strategy hwin initial)
    (member : Bool) (input : In₁ × In₂) :
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftTracked A strategy
      hwin policy
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftOwnerStep A
        strategy hwin policy member owner input.2).1
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverStep A
        strategy hwin policy fallback owner receiver input).2 := by
  refine
    { aligned :=
        profiledRawJointHybridPhysicalCompatiblePhaseLiveLeft_step_preserves A
          strategy hwin policy fallback owner receiver tracked.aligned member
            input
      reachable := ?_
      oneSided := ?_
      live := ?_ }
  · simpa
      [profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftOwnerStep]
      using tracked.reachable
  · rcases tracked.oneSided with ⟨code, hcode⟩
    exact ⟨code, by
      simpa [profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftOwnerStep]
        using hcode⟩
  · rcases tracked.live with ⟨root, hlive⟩
    exact ⟨root, by
      simpa [profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftOwnerStep]
        using hlive⟩

/-! ## The actual emitted record selects an exact successor -/

/-- A tracked right pair turns its total receiver step into the exact
same-policy left successor selected by the carried entry row. -/
theorem
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightTracked.exists_rootAlignedTargetAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {owner : RightOwner A strategy hwin policy}
    {receiver : RightReceiver A strategy hwin (initial := initial)}
    (tracked :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightTracked A strategy
        hwin policy owner receiver)
    (fallback : RightOutput A strategy hwin initial)
    (input : In₂ × In₁) (closeMember : Bool) :
    let row :=
      profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverRow A
        strategy hwin receiver
    let output :=
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverStep A
        strategy hwin policy fallback owner receiver input).1
    let payload :=
      profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfOutput A
        strategy hwin output row
    let target :=
      profiledRawJointHybridPhysicalCompatibleRightPendingPayloadTarget A
        strategy hwin payload closeMember
    ∃ slot : ProfiledRawLeftSlot A,
      ProfiledRawJointHybridPhysicalCompatibleRootAlignedSuccessorTargetAt A
        strategy hwin policy owner.1 target .left (.inr slot) := by
  rcases tracked with ⟨haligned, hreachable, ⟨code, hcode⟩,
    ⟨root, hlive⟩⟩
  rcases haligned with
    ⟨state, move, ownerControl, row, monitorState, staged, howner, hreceiver,
      hlocal, hmove⟩
  subst owner
  subst receiver
  simp only
    [profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverRow_live,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverStep_live]
  exact
    exists_profiledRawJointHybridPhysicalCompatibleRightReceiverStepFor_targetAt
      A strategy hwin policy state hreachable code hcode root hlive move hmove
        ownerControl monitorState hlocal row input closeMember

/-- Weak projection retained for clients that do not consume move-source
lineage. -/
theorem
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightTracked.exists_targetAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {owner : RightOwner A strategy hwin policy}
    {receiver : RightReceiver A strategy hwin (initial := initial)}
    (tracked :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightTracked A strategy
        hwin policy owner receiver)
    (fallback : RightOutput A strategy hwin initial)
    (input : In₂ × In₁) (closeMember : Bool) :
    let row :=
      profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverRow A
        strategy hwin receiver
    let output :=
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveRightReceiverStep A
        strategy hwin policy fallback owner receiver input).1
    let payload :=
      profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfOutput A
        strategy hwin output row
    let target :=
      profiledRawJointHybridPhysicalCompatibleRightPendingPayloadTarget A
        strategy hwin payload closeMember
    ∃ slot : ProfiledRawLeftSlot A,
      ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetAt A strategy hwin
        policy owner.1 target .left (.inr slot) := by
  dsimp only
  obtain ⟨slot, targetAt⟩ :=
    tracked.exists_rootAlignedTargetAt A strategy hwin fallback input
      closeMember
  exact ⟨slot, targetAt.toSuccessorTargetAt A strategy hwin⟩

/-- Left mirror. -/
theorem
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftTracked.exists_rootAlignedTargetAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {owner : LeftOwner A strategy hwin policy}
    {receiver : LeftReceiver A strategy hwin (initial := initial)}
    (tracked :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftTracked A strategy
        hwin policy owner receiver)
    (fallback : LeftOutput A strategy hwin initial)
    (input : In₁ × In₂) (closeMember : Bool) :
    let row :=
      profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverRow A
        strategy hwin receiver
    let output :=
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverStep A
        strategy hwin policy fallback owner receiver input).1
    let payload :=
      profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfOutput A
        strategy hwin output row
    let target :=
      profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadTarget A
        strategy hwin payload closeMember
    ∃ slot : ProfiledRawRightSlot A,
      ProfiledRawJointHybridPhysicalCompatibleRootAlignedSuccessorTargetAt A
        strategy hwin policy owner.1 target .right (.inl slot) := by
  rcases tracked with ⟨haligned, hreachable, ⟨code, hcode⟩,
    ⟨root, hlive⟩⟩
  rcases haligned with
    ⟨state, move, ownerControl, row, monitorState, staged, howner, hreceiver,
      hlocal, hmove⟩
  subst owner
  subst receiver
  simp only
    [profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverRow_live,
      profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverStep_live]
  exact
    exists_profiledRawJointHybridPhysicalCompatibleLeftReceiverStepFor_targetAt
      A strategy hwin policy state hreachable code hcode root hlive move hmove
        ownerControl monitorState hlocal row input closeMember

/-- Weak left projection retained for existing target-path clients. -/
theorem
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftTracked.exists_targetAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {owner : LeftOwner A strategy hwin policy}
    {receiver : LeftReceiver A strategy hwin (initial := initial)}
    (tracked :
      ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftTracked A strategy
        hwin policy owner receiver)
    (fallback : LeftOutput A strategy hwin initial)
    (input : In₁ × In₂) (closeMember : Bool) :
    let row :=
      profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverRow A
        strategy hwin receiver
    let output :=
      (profiledRawJointHybridPhysicalCompatiblePhaseLiveLeftReceiverStep A
        strategy hwin policy fallback owner receiver input).1
    let payload :=
      profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfOutput A
        strategy hwin output row
    let target :=
      profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadTarget A
        strategy hwin payload closeMember
    ∃ slot : ProfiledRawRightSlot A,
      ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetAt A strategy hwin
        policy owner.1 target .right (.inl slot) := by
  dsimp only
  obtain ⟨slot, targetAt⟩ :=
    tracked.exists_rootAlignedTargetAt A strategy hwin fallback input
      closeMember
  exact ⟨slot, targetAt.toSuccessorTargetAt A strategy hwin⟩

/-! ## Exact target transitions start fresh tracked pairs -/

theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshRight_tracked_of_targetAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : ProfiledRawJointHybridPhysicalCompatiblePolicyState A strategy
      hwin initial)
    (hstate : ProfiledRawJointHybridPhysicalCompatibleReachable A strategy
      hwin initial policy state)
    (parent : RightOwner A strategy hwin policy)
    (output : LeftOutput A strategy hwin initial)
    (entryRow : PairedEntryRow) (receiverMember : Bool)
    (root : ProfiledRawJointThreadRoot A)
    (htarget :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetAt A strategy
        hwin policy state (output.target entryRow).1 .right root) :
    let payload :=
      profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfOutput A
        strategy hwin output entryRow
    let owner :=
      profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshRightOwner A
        strategy hwin policy parent payload
    let installed :=
      profiledRawJointHybridPhysicalCompatibleInstallRightPendingMember.{u, v,
        x, y, s, max u v x y s, max u v x y s} A strategy hwin policy
          (receiverMember, owner, payload)
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveRightTracked A strategy
      hwin policy owner ⟨installed.1.1, installed.2⟩ := by
  dsimp only
  obtain ⟨haligned, hreachable⟩ :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshRight_aligned_of_targetAt
      A strategy hwin policy state hstate parent output entryRow receiverMember
        root htarget
  rcases htarget.transition with ⟨transition⟩
  obtain ⟨code, hcode⟩ := transition.child_oneSided
  refine
    { aligned := haligned
      reachable := hreachable
      oneSided := ⟨code, ?_⟩
      live := ⟨root, ?_⟩ }
  · simpa
      [profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshRightOwner,
        profiledRawJointHybridPhysicalCompatibleInstallRightPendingMember,
        profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfOutput,
        profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadTarget]
      using hcode
  · simpa
      [profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshRightOwner,
        profiledRawJointHybridPhysicalCompatibleInstallRightPendingMember,
        profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfOutput,
        profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadTarget]
      using transition.child_live

theorem
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshLeft_tracked_of_targetAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : ProfiledRawJointHybridPhysicalCompatiblePolicyState A strategy
      hwin initial)
    (hstate : ProfiledRawJointHybridPhysicalCompatibleReachable A strategy
      hwin initial policy state)
    (parent : LeftOwner A strategy hwin policy)
    (output : RightOutput A strategy hwin initial)
    (entryRow : PairedEntryRow) (receiverMember : Bool)
    (root : ProfiledRawJointThreadRoot A)
    (htarget :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetAt A strategy
        hwin policy state (output.target entryRow).1 .left root) :
    let payload :=
      profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfOutput A
        strategy hwin output entryRow
    let owner :=
      profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshLeftOwner A
        strategy hwin policy parent payload
    let installed :=
      profiledRawJointHybridPhysicalCompatibleInstallLeftPendingMember.{u, v,
        x, y, s, max u v x y s, max u v x y s} A strategy hwin policy
          (receiverMember, owner, payload)
    ProfiledRawJointHybridPhysicalCompatiblePhaseLiveLeftTracked A strategy hwin
      policy owner ⟨installed.1.1, installed.2⟩ := by
  dsimp only
  obtain ⟨haligned, hreachable⟩ :=
    profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshLeft_aligned_of_targetAt
      A strategy hwin policy state hstate parent output entryRow receiverMember
        root htarget
  rcases htarget.transition with ⟨transition⟩
  obtain ⟨code, hcode⟩ := transition.child_oneSided
  refine
    { aligned := haligned
      reachable := hreachable
      oneSided := ⟨code, ?_⟩
      live := ⟨root, ?_⟩ }
  · simpa
      [profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshLeftOwner,
        profiledRawJointHybridPhysicalCompatibleInstallLeftPendingMember,
        profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfOutput,
        profiledRawJointHybridPhysicalCompatibleRightPendingPayloadTarget]
      using hcode
  · simpa
      [profiledRawJointHybridPhysicalCompatiblePhaseLiveFreshLeftOwner,
        profiledRawJointHybridPhysicalCompatibleInstallLeftPendingMember,
        profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfOutput,
        profiledRawJointHybridPhysicalCompatibleRightPendingPayloadTarget]
      using transition.child_live

end

end DetParityAutomaton

end DistributedSynthesis
