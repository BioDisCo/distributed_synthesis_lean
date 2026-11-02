/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingCanonicalFreshHandlers
import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingDeferredFamily
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatiblePendingMemberTransition

/-!
# Canonical deferred family for the two-row compatible frontier

The already acknowledged table member selects the current output's entry-row
target.  Independently, the new member chooses whether the next receiver row
is `.first` (strict/open) or `.both` (simultaneous/closed).  Both candidates
therefore have the same target and compatible-policy key.  The executable
continuation keeps one parent shared control and stores that target together
with both next-row receiver initializations as inert payload.

The generic deferred exact-closing construction then gives the ordinary and
joint receive continuations the same shared control and the same payload.
Blind steps advance only that shared parent.  Once a later delivered
acknowledgement resolves the new member, the common child key and the receiver
initialized at exactly the selected next row are installed.

The functions supplied to the constructor below read only the two finite local
controls, the receiver's own input, and the delivered partner control/input.
No graph, orientation, hierarchy side, leader bit, strict-leader bit, history,
or semantic view is an argument.
-/

namespace DistributedSynthesis

universe u v x y s c

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

/-! ## The crossed endpoint types -/

/-- Process one's unresolved parent control.  The dependent compatible key is
packed with the right-table owner control; it is not an observation. -/
noncomputable abbrev
    ProfiledRawJointHybridPhysicalCompatibleFrontierOneShared
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  Σ state : CompatibleState A strategy hwin initial,
    ProfiledRawJointHybridPhysicalCompatibleRightShared A strategy hwin
      policy state

/-- Process two's mirror parent control. -/
noncomputable abbrev
    ProfiledRawJointHybridPhysicalCompatibleFrontierTwoShared
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  Σ state : CompatibleState A strategy hwin initial,
    ProfiledRawJointHybridPhysicalCompatibleLeftShared A strategy hwin
      policy state

/-- A process-one receive closes a left table and therefore retains the
two-row payload which will install a right child. -/
noncomputable abbrev
    ProfiledRawJointHybridPhysicalCompatibleFrontierOnePayload
    {initial : ProfiledRawJointCommonBaseWorld A strategy} :=
  ProfiledRawJointHybridPhysicalCompatibleLeftPendingPayload A strategy hwin
    (initial := initial)

/-- Process-two mirror: a right-table receive will eventually install a left
child. -/
noncomputable abbrev
    ProfiledRawJointHybridPhysicalCompatibleFrontierTwoPayload
    {initial : ProfiledRawJointCommonBaseWorld A strategy} :=
  ProfiledRawJointHybridPhysicalCompatibleRightPendingPayload A strategy hwin
    (initial := initial)

noncomputable abbrev
    ProfiledRawJointHybridPhysicalCompatibleFrontierOneControl
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (ProfiledRawJointHybridPhysicalCompatibleFrontierOneShared A strategy hwin
      policy)
    (ProfiledRawJointHybridPhysicalCompatibleFrontierOnePayload A strategy
      hwin (initial := initial))
    PUnit

noncomputable abbrev
    ProfiledRawJointHybridPhysicalCompatibleFrontierTwoControl
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (ProfiledRawJointHybridPhysicalCompatibleFrontierTwoShared A strategy hwin
      policy)
    (ProfiledRawJointHybridPhysicalCompatibleFrontierTwoPayload A strategy
      hwin (initial := initial))
    PUnit

/-! ## Parent steps and their unconditional member laws -/

noncomputable def
    profiledRawJointHybridPhysicalCompatibleFrontierOnePendingStep
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  FiniteAcknowledgedDelayedCarrier.keyedDeferredSharedStep
    (fun state ↦
      profiledRawJointHybridPhysicalCompatibleRightSharedStep A strategy hwin
        policy state)

noncomputable def
    profiledRawJointHybridPhysicalCompatibleFrontierTwoPendingStep
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  FiniteAcknowledgedDelayedCarrier.keyedDeferredSharedStep
    (fun state ↦
      profiledRawJointHybridPhysicalCompatibleLeftSharedStep A strategy hwin
        policy state)

theorem
    profiledRawJointHybridPhysicalCompatibleFrontierOnePendingStep_laws
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberStepLaws
      (profiledRawJointHybridPhysicalCompatibleFrontierOnePendingStep A
        strategy hwin policy) := by
  simpa [profiledRawJointHybridPhysicalCompatibleFrontierOnePendingStep] using
    profiledRawJointHybridPhysicalCompatibleRightDeferredStep_laws A strategy
      hwin policy

theorem
    profiledRawJointHybridPhysicalCompatibleFrontierTwoPendingStep_laws
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberStepLaws
      (profiledRawJointHybridPhysicalCompatibleFrontierTwoPendingStep A
        strategy hwin policy) := by
  simpa [profiledRawJointHybridPhysicalCompatibleFrontierTwoPendingStep] using
    profiledRawJointHybridPhysicalCompatibleLeftDeferredStep_laws A strategy
      hwin policy

noncomputable def
    profiledRawJointHybridPhysicalCompatibleFrontierOneRecurrentStep
    (_state : PUnit) (_input : In₁) : PUnit × Out₁ :=
  (PUnit.unit, default)

noncomputable def
    profiledRawJointHybridPhysicalCompatibleFrontierTwoRecurrentStep
    (_state : PUnit) (_input : In₂) : PUnit × Out₂ :=
  (PUnit.unit, default)

/-! ## Fresh data is one parent plus both row-exact children -/

variable {initial : ProfiledRawJointCommonBaseWorld A strategy}
variable (policy : CompatiblePolicy A strategy hwin initial)

private abbrev OneShared :=
  ProfiledRawJointHybridPhysicalCompatibleFrontierOneShared A strategy hwin
    policy
private abbrev TwoShared :=
  ProfiledRawJointHybridPhysicalCompatibleFrontierTwoShared A strategy hwin
    policy
private abbrev OnePayload :=
  ProfiledRawJointHybridPhysicalCompatibleFrontierOnePayload A strategy hwin
    (initial := initial)
private abbrev TwoPayload :=
  ProfiledRawJointHybridPhysicalCompatibleFrontierTwoPayload A strategy hwin
    (initial := initial)
private abbrev OneControl :=
  ProfiledRawJointHybridPhysicalCompatibleFrontierOneControl A strategy hwin
    policy
private abbrev TwoControl :=
  ProfiledRawJointHybridPhysicalCompatibleFrontierTwoControl A strategy hwin
    policy
private abbrev LeftOutput :=
  ProfiledRawJointHybridPhysicalCompatibleSuccessorLeftReceiverOutput A
    strategy hwin initial
private abbrev RightOutput :=
  ProfiledRawJointHybridPhysicalCompatibleSuccessorRightReceiverOutput A
    strategy hwin initial

/-- Assemble process one's canonical fresh datum.  `parent` is the single
shared state used while the old member is unresolved; `receiverOutput`
contains both row-exact child keys. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleFrontierFreshOne
    (parent : OneControl A strategy hwin policy → In₁ →
      TwoControl A strategy hwin policy → In₂ →
        OneShared A strategy hwin policy)
    (receiverOutput : OneControl A strategy hwin policy → In₁ →
      TwoControl A strategy hwin policy → In₂ →
        PairedEntryRow × LeftOutput A strategy hwin (initial := initial))
    (one : OneControl A strategy hwin policy) (inputOne : In₁)
    (two : TwoControl A strategy hwin policy) (inputTwo : In₂) :
    OneShared A strategy hwin policy ×
      OnePayload A strategy hwin (initial := initial) :=
  (parent one inputOne two inputTwo,
    profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfOutput A
      strategy hwin (receiverOutput one inputOne two inputTwo).2
        (receiverOutput one inputOne two inputTwo).1)

/-- Process-two mirror. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleFrontierFreshTwo
    (parent : TwoControl A strategy hwin policy → In₂ →
      OneControl A strategy hwin policy → In₁ →
        TwoShared A strategy hwin policy)
    (receiverOutput : TwoControl A strategy hwin policy → In₂ →
      OneControl A strategy hwin policy → In₁ →
        PairedEntryRow × RightOutput A strategy hwin (initial := initial))
    (two : TwoControl A strategy hwin policy) (inputTwo : In₂)
    (one : OneControl A strategy hwin policy) (inputOne : In₁) :
    TwoShared A strategy hwin policy ×
      TwoPayload A strategy hwin (initial := initial) :=
  (parent two inputTwo one inputOne,
    profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfOutput A
      strategy hwin (receiverOutput two inputTwo one inputOne).2
        (receiverOutput two inputTwo one inputOne).1)

/-! ## Canonical family -/

/-- One fixed finite deferred family.  The package key is `PUnit`; the
changing compatible-policy key is already carried dependently in each shared
parent state.  The only proof fields are discharged by the generic canonical
handler and the two unconditional member-step laws above. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleSuccessorDeferredFamily
    (initialOne : OneControl A strategy hwin policy)
    (initialTwo : TwoControl A strategy hwin policy)
    (parentOne : OneControl A strategy hwin policy → In₁ →
      TwoControl A strategy hwin policy → In₂ →
        OneShared A strategy hwin policy)
    (frontierOne : OneControl A strategy hwin policy → In₁ →
      TwoControl A strategy hwin policy → In₂ →
        PairedEntryRow × LeftOutput A strategy hwin (initial := initial))
    (parentTwo : TwoControl A strategy hwin policy → In₂ →
      OneControl A strategy hwin policy → In₁ →
        TwoShared A strategy hwin policy)
    (frontierTwo : TwoControl A strategy hwin policy → In₂ →
      OneControl A strategy hwin policy → In₁ →
        PairedEntryRow × RightOutput A strategy hwin (initial := initial))
    (outputOne : OneControl A strategy hwin policy → In₁ →
      TwoControl A strategy hwin policy → In₂ → Out₁)
    (outputTwo : TwoControl A strategy hwin policy → In₂ →
      OneControl A strategy hwin policy → In₁ → Out₂) :
    FiniteAcknowledgedDelayedCarrier.FiniteDeferredExactClosingFamily
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
      PUnit where
  SharedOne _ := OneShared A strategy hwin policy
  PayloadOne _ := OnePayload A strategy hwin (initial := initial)
  RecurrentOne _ := PUnit
  SharedTwo _ := TwoShared A strategy hwin policy
  PayloadTwo _ := TwoPayload A strategy hwin (initial := initial)
  RecurrentTwo _ := PUnit
  oneFinite _ := by classical infer_instance
  twoFinite _ := by classical infer_instance
  initialOne _ := initialOne
  initialTwo _ := initialTwo
  pendingStepOne _ :=
    profiledRawJointHybridPhysicalCompatibleFrontierOnePendingStep A strategy
      hwin policy
  recurrentStepOne _ :=
    profiledRawJointHybridPhysicalCompatibleFrontierOneRecurrentStep
  pendingStepTwo _ :=
    profiledRawJointHybridPhysicalCompatibleFrontierTwoPendingStep A strategy
      hwin policy
  recurrentStepTwo _ :=
    profiledRawJointHybridPhysicalCompatibleFrontierTwoRecurrentStep
  openRecvOne _ :=
    FiniteAcknowledgedDelayedCarrier.canonicalDeferredOpenRecvOne
      (profiledRawJointHybridPhysicalCompatibleFrontierFreshOne A strategy hwin
        policy parentOne frontierOne)
      outputOne
  openRecvTwo _ :=
    FiniteAcknowledgedDelayedCarrier.canonicalDeferredOpenRecvTwo
      (profiledRawJointHybridPhysicalCompatibleFrontierFreshTwo A strategy hwin
        policy parentTwo frontierTwo)
      outputTwo
  close _ :=
    FiniteAcknowledgedDelayedCarrier.canonicalDeferredClose
      (profiledRawJointHybridPhysicalCompatibleFrontierFreshOne A strategy hwin
        policy parentOne frontierOne)
      (profiledRawJointHybridPhysicalCompatibleFrontierFreshTwo A strategy hwin
        policy parentTwo frontierTwo)
  Rel _ _ _ := True
  laws _ :=
    FiniteAcknowledgedDelayedCarrier.canonicalDeferredExactClosingForkLaws
      initialOne initialTwo
      (profiledRawJointHybridPhysicalCompatibleFrontierOnePendingStep A
        strategy hwin policy)
      (profiledRawJointHybridPhysicalCompatibleFrontierOnePendingStep_laws A
        strategy hwin policy)
      profiledRawJointHybridPhysicalCompatibleFrontierOneRecurrentStep
      (profiledRawJointHybridPhysicalCompatibleFrontierTwoPendingStep A
        strategy hwin policy)
      (profiledRawJointHybridPhysicalCompatibleFrontierTwoPendingStep_laws A
        strategy hwin policy)
      profiledRawJointHybridPhysicalCompatibleFrontierTwoRecurrentStep
      (profiledRawJointHybridPhysicalCompatibleFrontierFreshOne A strategy hwin
        policy parentOne frontierOne)
      (profiledRawJointHybridPhysicalCompatibleFrontierFreshTwo A strategy hwin
        policy parentTwo frontierTwo)
      outputOne outputTwo

/-! ## The exact open/close and later-install equations -/

/-- Process one's ordinary and simultaneous receive continuations differ only
in the delayed member.  The parent shared control and both-child payload are
literally identical. -/
theorem
    profiledRawJointHybridPhysicalCompatibleFrontierOne_open_close_same
    (parentOne : OneControl A strategy hwin policy → In₁ →
      TwoControl A strategy hwin policy → In₂ →
        OneShared A strategy hwin policy)
    (frontierOne : OneControl A strategy hwin policy → In₁ →
      TwoControl A strategy hwin policy → In₂ →
        PairedEntryRow × LeftOutput A strategy hwin (initial := initial))
    (parentTwo : TwoControl A strategy hwin policy → In₂ →
      OneControl A strategy hwin policy → In₁ →
        TwoShared A strategy hwin policy)
    (frontierTwo : TwoControl A strategy hwin policy → In₂ →
      OneControl A strategy hwin policy → In₁ →
        PairedEntryRow × RightOutput A strategy hwin (initial := initial))
    (outputOne : OneControl A strategy hwin policy → In₁ →
      TwoControl A strategy hwin policy → In₂ → Out₁)
    (one : OneControl A strategy hwin policy) (inputOne : In₁)
    (two : TwoControl A strategy hwin policy) (inputTwo : In₂) :
    let fresh :=
      profiledRawJointHybridPhysicalCompatibleFrontierFreshOne A strategy hwin
        policy parentOne frontierOne one inputOne two inputTwo
    (FiniteAcknowledgedDelayedCarrier.canonicalDeferredOpenRecvOne
        (profiledRawJointHybridPhysicalCompatibleFrontierFreshOne A strategy
          hwin policy parentOne frontierOne)
        outputOne one inputOne two inputTwo).1 = .inl (false, fresh.1, fresh.2)
      ∧
    (FiniteAcknowledgedDelayedCarrier.canonicalDeferredClose
        (profiledRawJointHybridPhysicalCompatibleFrontierFreshOne A strategy
          hwin policy parentOne frontierOne)
        (profiledRawJointHybridPhysicalCompatibleFrontierFreshTwo A strategy
          hwin policy parentTwo frontierTwo)
        one inputOne two inputTwo).1 = .inl (true, fresh.1, fresh.2) := by
  exact ⟨rfl, rfl⟩

/-- Process-two mirror. -/
theorem
    profiledRawJointHybridPhysicalCompatibleFrontierTwo_open_close_same
    (parentOne : OneControl A strategy hwin policy → In₁ →
      TwoControl A strategy hwin policy → In₂ →
        OneShared A strategy hwin policy)
    (frontierOne : OneControl A strategy hwin policy → In₁ →
      TwoControl A strategy hwin policy → In₂ →
        PairedEntryRow × LeftOutput A strategy hwin (initial := initial))
    (parentTwo : TwoControl A strategy hwin policy → In₂ →
      OneControl A strategy hwin policy → In₁ →
        TwoShared A strategy hwin policy)
    (frontierTwo : TwoControl A strategy hwin policy → In₂ →
      OneControl A strategy hwin policy → In₁ →
        PairedEntryRow × RightOutput A strategy hwin (initial := initial))
    (outputTwo : TwoControl A strategy hwin policy → In₂ →
      OneControl A strategy hwin policy → In₁ → Out₂)
    (one : OneControl A strategy hwin policy) (inputOne : In₁)
    (two : TwoControl A strategy hwin policy) (inputTwo : In₂) :
    let fresh :=
      profiledRawJointHybridPhysicalCompatibleFrontierFreshTwo A strategy hwin
        policy parentTwo frontierTwo two inputTwo one inputOne
    (FiniteAcknowledgedDelayedCarrier.canonicalDeferredOpenRecvTwo
        (profiledRawJointHybridPhysicalCompatibleFrontierFreshTwo A strategy
          hwin policy parentTwo frontierTwo)
        outputTwo two inputTwo one inputOne).1 = .inl (false, fresh.1, fresh.2)
      ∧
    (FiniteAcknowledgedDelayedCarrier.canonicalDeferredClose
        (profiledRawJointHybridPhysicalCompatibleFrontierFreshOne A strategy
          hwin policy parentOne frontierOne)
        (profiledRawJointHybridPhysicalCompatibleFrontierFreshTwo A strategy
          hwin policy parentTwo frontierTwo)
        one inputOne two inputTwo).2 = .inl (true, fresh.1, fresh.2) := by
  exact ⟨rfl, rfl⟩

/-- The old entry row selects the left output's one target and compatible key;
the independent fresh member selects only the next right receiver row.  The
proof covers all four `(entryRow, closeMember)` pairs. -/
theorem
    profiledRawJointHybridPhysicalCompatible_ackInstallRight_of_leftOutput
    {ParentShared : Type c} (shared : ParentShared)
    (output : LeftOutput A strategy hwin (initial := initial))
    (entryRow : PairedEntryRow) (closeMember : Bool) :
    let pending :=
      (profiledRawJointHybridPhysicalCompatibleLeftPendingFork A strategy hwin
        shared
        (profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfOutput A
          strategy hwin output entryRow)).candidate closeMember
    let target := (output.target entryRow).1
    (profiledRawJointHybridPhysicalCompatibleInstallRightPendingMember A
        strategy hwin policy pending).1.1 =
          profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
            hwin target ∧
      (profiledRawJointHybridPhysicalCompatibleInstallRightPendingMember A
        strategy hwin policy pending).2 =
          profiledRawJointHybridPhysicalCompatibleRightPayloadAtRow A strategy
            hwin
            (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A
              strategy hwin target)
            (profiledRawJointHybridPhysicalCompatiblePendingRow closeMember) := by
  dsimp only
  constructor
  · cases closeMember <;> rfl
  · exact
      (by
        simpa only
          [profiledRawJointHybridPhysicalCompatibleLeftPendingFork_candidate]
          using
            profiledRawJointHybridPhysicalCompatibleInstallRightOfOutput_payload
              A strategy hwin policy shared output entryRow closeMember)

/-- Right-output mirror: the resolved candidate installs the selected left
child key and row. -/
theorem
    profiledRawJointHybridPhysicalCompatible_ackInstallLeft_of_rightOutput
    {ParentShared : Type c} (shared : ParentShared)
    (output : RightOutput A strategy hwin (initial := initial))
    (entryRow : PairedEntryRow) (closeMember : Bool) :
    let pending :=
      (profiledRawJointHybridPhysicalCompatibleRightPendingFork A strategy hwin
        shared
        (profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfOutput A
          strategy hwin output entryRow)).candidate closeMember
    let target := (output.target entryRow).1
    (profiledRawJointHybridPhysicalCompatibleInstallLeftPendingMember A
        strategy hwin policy pending).1.1 =
          profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
            hwin target ∧
      (profiledRawJointHybridPhysicalCompatibleInstallLeftPendingMember A
        strategy hwin policy pending).2 =
          profiledRawJointHybridPhysicalCompatibleLeftPayloadAtRow A strategy
            hwin
            (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A
              strategy hwin target)
            (profiledRawJointHybridPhysicalCompatiblePendingRow closeMember) := by
  dsimp only
  constructor
  · cases closeMember <;> rfl
  · exact
      (by
        simpa only
          [profiledRawJointHybridPhysicalCompatibleRightPendingFork_candidate]
          using
            profiledRawJointHybridPhysicalCompatibleInstallLeftOfOutput_payload
              A strategy hwin policy shared output entryRow closeMember)

/-! ## Same-policy transition exposed after acknowledgement -/

/-- The acknowledged right-output candidate is not only installed at the
selected key: whenever the row-exact table cell carries its standard key
certificate, it is an exact crossed successor of the same fixed policy. -/
theorem
    exists_profiledRawJointHybridPhysicalCompatible_ackInstallLeftTransition
    (state : CompatibleState A strategy hwin initial)
    {ParentShared : Type c} (shared : ParentShared)
    (output : RightOutput A strategy hwin (initial := initial))
    (entryRow : PairedEntryRow) (closeMember : Bool)
    (hkey :
      let target := (output.target entryRow).1
      ProfiledRawJointHybridPhysicalCompatibleRightSuccessorKeyAt A strategy
        hwin policy state
          (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A
            strategy hwin target)
          target.1) :
    let payload :=
      profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfOutput A
        strategy hwin output entryRow
    let pending :=
      (profiledRawJointHybridPhysicalCompatibleRightPendingFork A strategy hwin
        shared payload).candidate closeMember
    let target :=
      profiledRawJointHybridPhysicalCompatibleRightPendingPayloadTarget A
        strategy hwin payload closeMember
    let installed :=
      profiledRawJointHybridPhysicalCompatibleInstallLeftPendingMember A
        strategy hwin policy pending
    ∃ slot : ProfiledRawLeftSlot A,
      installed.1.1 =
          profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
            hwin target ∧
        ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetAt A strategy
          hwin policy state target .left (.inr slot) := by
  dsimp only
  simpa only
    [profiledRawJointHybridPhysicalCompatibleRightPendingFork_candidate]
    using
      exists_profiledRawJointHybridPhysicalCompatibleTargetAt_of_installLeftPendingOutput.{u,
        v, x, y, s, c, max u v x y s}
        A strategy hwin policy state shared output entryRow closeMember hkey

/-- Left-output mirror. -/
theorem
    exists_profiledRawJointHybridPhysicalCompatible_ackInstallRightTransition
    (state : CompatibleState A strategy hwin initial)
    {ParentShared : Type c} (shared : ParentShared)
    (output : LeftOutput A strategy hwin (initial := initial))
    (entryRow : PairedEntryRow) (closeMember : Bool)
    (hkey :
      let target := (output.target entryRow).1
      ProfiledRawJointHybridPhysicalCompatibleLeftSuccessorKeyAt A strategy
        hwin policy state
          (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A
            strategy hwin target)
          target.1) :
    let payload :=
      profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfOutput A
        strategy hwin output entryRow
    let pending :=
      (profiledRawJointHybridPhysicalCompatibleLeftPendingFork A strategy hwin
        shared payload).candidate closeMember
    let target :=
      profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadTarget A
        strategy hwin payload closeMember
    let installed :=
      profiledRawJointHybridPhysicalCompatibleInstallRightPendingMember A
        strategy hwin policy pending
    ∃ slot : ProfiledRawRightSlot A,
      installed.1.1 =
          profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
            hwin target ∧
        ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetAt A strategy
          hwin policy state target .right (.inl slot) := by
  dsimp only
  simpa only
    [profiledRawJointHybridPhysicalCompatibleLeftPendingFork_candidate]
    using
      exists_profiledRawJointHybridPhysicalCompatibleTargetAt_of_installRightPendingOutput.{u,
        v, x, y, s, c, max u v x y s}
        A strategy hwin policy state shared output entryRow closeMember hkey

end

end DetParityAutomaton

end DistributedSynthesis
