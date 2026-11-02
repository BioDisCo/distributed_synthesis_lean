/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailFreshPair
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailSingleTableInvariant
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailTransitionRootAlignment

/-!
# The phase-indexed one-table invariant in a tagged recurrent tail

The two endpoint phase bits select among four already-carried finite
relations.  They are local history written by the endpoint transitions, not
an oracle for the current graph or hierarchy.  At every admissible phase the
selected owner and receiver name one literal tail state and physical move.

Fresh owners and receivers are initialized from the same exact successor key.
This is the recurrence seam connecting the one-table simultaneous output to
the re-rooted tail policy.
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

private abbrev OnePending (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailOnePending A strategy hwin tag

private abbrev TwoPending (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailTwoPending A strategy hwin tag

private abbrev RightOutput (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailRightReceiverOutput A strategy hwin
    tag

private abbrev LeftOutput (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailLeftReceiverOutput A strategy hwin
    tag

/-! ## Current and dormant one-table relations -/

def ProfiledRawJointHybridShadowPhaseLiveTailRightCurrentAligned
    (tag : Tag A strategy hwin) (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) : Prop :=
  ProfiledRawJointHybridShadowPhaseLiveTailRightPendingAligned A strategy hwin
    tag one two

def ProfiledRawJointHybridShadowPhaseLiveTailLeftCurrentAligned
    (tag : Tag A strategy hwin) (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) : Prop :=
  ProfiledRawJointHybridShadowPhaseLiveTailLeftPendingAligned A strategy hwin
    tag one two

/-- The right table selected when process two's local phase says that its
retained receiver must be refreshed from process one's payload. -/
def ProfiledRawJointHybridShadowPhaseLiveTailRightSwitchAligned
    (tag : Tag A strategy hwin) (one : OnePending A strategy hwin tag) : Prop :=
  ProfiledRawJointHybridShadowPhaseLiveTailRightSingleTableAligned A strategy
    hwin tag one.2.1.baseShared
      (profiledRawJointHybridShadowPhaseLiveTailFreshRightReceiver A strategy
        hwin tag one.2.1.basePayload one.1)

/-- Dormant left-table mirror. -/
def ProfiledRawJointHybridShadowPhaseLiveTailLeftSwitchAligned
    (tag : Tag A strategy hwin) (two : TwoPending A strategy hwin tag) : Prop :=
  ProfiledRawJointHybridShadowPhaseLiveTailLeftSingleTableAligned A strategy
    hwin tag two.2.1.baseShared
      (profiledRawJointHybridShadowPhaseLiveTailFreshLeftReceiver A strategy
        hwin tag two.2.1.basePayload two.1)

/-- The smallest phase-indexed alignment relation closed by strict-right,
strict-left, and simultaneous rounds. -/
def ProfiledRawJointHybridShadowPhaseLiveTailTableInvariant
    (tag : Tag A strategy hwin) (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) : Prop :=
  match one.2.1.localPhase, two.2.1.localPhase with
  | false, false =>
      ProfiledRawJointHybridShadowPhaseLiveTailRightCurrentAligned A strategy
          hwin tag one two ∧
        ProfiledRawJointHybridShadowPhaseLiveTailLeftSwitchAligned A strategy
          hwin tag two
  | true, true =>
      ProfiledRawJointHybridShadowPhaseLiveTailLeftCurrentAligned A strategy
          hwin tag one two ∧
        ProfiledRawJointHybridShadowPhaseLiveTailRightSwitchAligned A strategy
          hwin tag one
  | true, false =>
      ProfiledRawJointHybridShadowPhaseLiveTailRightCurrentAligned A strategy
          hwin tag one two ∧
        ProfiledRawJointHybridShadowPhaseLiveTailLeftCurrentAligned A strategy
          hwin tag one two
  | false, true => False

/-! ## The receiver chosen by each local dispatcher is aligned -/

theorem
    ProfiledRawJointHybridShadowPhaseLiveTailTableInvariant.right_selected
    {tag : Tag A strategy hwin} {one : OnePending A strategy hwin tag}
    {two : TwoPending A strategy hwin tag}
    (hinvariant :
      ProfiledRawJointHybridShadowPhaseLiveTailTableInvariant A strategy hwin
        tag one two) :
    ProfiledRawJointHybridShadowPhaseLiveTailRightSingleTableAligned A strategy
      hwin tag one.2.1.baseShared
        (profiledRawJointHybridShadowPhaseLiveTailRightReceiverForRecvTwo A
          strategy hwin tag two one) := by
  cases hone : one.2.1.localPhase <;> cases htwo : two.2.1.localPhase
  · simp only
      [ProfiledRawJointHybridShadowPhaseLiveTailTableInvariant, hone, htwo,
        ProfiledRawJointHybridShadowPhaseLiveTailRightCurrentAligned,
        ProfiledRawJointHybridShadowPhaseLiveTailRightPendingAligned]
      at hinvariant
    simpa [profiledRawJointHybridShadowPhaseLiveTailRightReceiverForRecvTwo,
      htwo] using hinvariant.1
  · simp only
      [ProfiledRawJointHybridShadowPhaseLiveTailTableInvariant, hone, htwo]
      at hinvariant
  · simp only
      [ProfiledRawJointHybridShadowPhaseLiveTailTableInvariant, hone, htwo,
        ProfiledRawJointHybridShadowPhaseLiveTailRightCurrentAligned,
        ProfiledRawJointHybridShadowPhaseLiveTailRightPendingAligned]
      at hinvariant
    simpa [profiledRawJointHybridShadowPhaseLiveTailRightReceiverForRecvTwo,
      htwo] using hinvariant.1
  · simp only
      [ProfiledRawJointHybridShadowPhaseLiveTailTableInvariant, hone, htwo,
        ProfiledRawJointHybridShadowPhaseLiveTailRightSwitchAligned]
      at hinvariant
    simpa [profiledRawJointHybridShadowPhaseLiveTailRightReceiverForRecvTwo,
      htwo] using hinvariant.2

theorem
    ProfiledRawJointHybridShadowPhaseLiveTailTableInvariant.left_selected
    {tag : Tag A strategy hwin} {one : OnePending A strategy hwin tag}
    {two : TwoPending A strategy hwin tag}
    (hinvariant :
      ProfiledRawJointHybridShadowPhaseLiveTailTableInvariant A strategy hwin
        tag one two) :
    ProfiledRawJointHybridShadowPhaseLiveTailLeftSingleTableAligned A strategy
      hwin tag two.2.1.baseShared
        (profiledRawJointHybridShadowPhaseLiveTailLeftReceiverForRecvOne A
          strategy hwin tag one two) := by
  cases hone : one.2.1.localPhase <;> cases htwo : two.2.1.localPhase
  · simp only
      [ProfiledRawJointHybridShadowPhaseLiveTailTableInvariant, hone, htwo,
        ProfiledRawJointHybridShadowPhaseLiveTailLeftSwitchAligned]
      at hinvariant
    simpa [profiledRawJointHybridShadowPhaseLiveTailLeftReceiverForRecvOne,
      hone] using hinvariant.2
  · simp only
      [ProfiledRawJointHybridShadowPhaseLiveTailTableInvariant, hone, htwo]
      at hinvariant
  · simp only
      [ProfiledRawJointHybridShadowPhaseLiveTailTableInvariant, hone, htwo,
        ProfiledRawJointHybridShadowPhaseLiveTailLeftCurrentAligned,
        ProfiledRawJointHybridShadowPhaseLiveTailLeftPendingAligned]
      at hinvariant
    simpa [profiledRawJointHybridShadowPhaseLiveTailLeftReceiverForRecvOne,
      hone] using hinvariant.2
  · simp only
      [ProfiledRawJointHybridShadowPhaseLiveTailTableInvariant, hone, htwo,
        ProfiledRawJointHybridShadowPhaseLiveTailLeftCurrentAligned,
        ProfiledRawJointHybridShadowPhaseLiveTailLeftPendingAligned]
      at hinvariant
    simpa [profiledRawJointHybridShadowPhaseLiveTailLeftReceiverForRecvOne,
      hone] using hinvariant.1

/-! ## Selected receiver steps preserve alignment -/

theorem
    ProfiledRawJointHybridShadowPhaseLiveTailRightSingleTableAligned.receiverStep
    (tag : Tag A strategy hwin) (fallback : RightOutput A strategy hwin tag)
    (owner :
      ProfiledRawJointHybridShadowPhaseLiveTailFrontierOneShared A strategy
        hwin tag)
    (receiver :
      ProfiledRawJointHybridShadowPhaseLiveTailRightReceiver A strategy hwin
        tag)
    (haligned :
      ProfiledRawJointHybridShadowPhaseLiveTailRightSingleTableAligned A
        strategy hwin tag owner receiver)
    (member : Bool) (input : In₂ × In₁) :
    ProfiledRawJointHybridShadowPhaseLiveTailRightSingleTableAligned A strategy
      hwin tag
      ⟨owner.1,
        (profiledRawJointHybridShadowPhaseLiveTailRightSharedStep A strategy
          hwin tag owner.1 member owner.2 input.2).1⟩
      (profiledRawJointHybridShadowPhaseLiveTailRightReceiverStep A strategy hwin
        tag fallback owner receiver input).2 := by
  rcases haligned with
    ⟨state, move, ownerControl, row, monitorState, staged, rfl, rfl⟩
  simpa using
    (profiledRawJointHybridShadowPhaseLiveTailRightSingleTableAligned_stepFor A
      strategy hwin tag state move ownerControl row monitorState staged member
        (input.2, input.1))

theorem
    ProfiledRawJointHybridShadowPhaseLiveTailLeftSingleTableAligned.receiverStep
    (tag : Tag A strategy hwin) (fallback : LeftOutput A strategy hwin tag)
    (owner :
      ProfiledRawJointHybridShadowPhaseLiveTailFrontierTwoShared A strategy
        hwin tag)
    (receiver :
      ProfiledRawJointHybridShadowPhaseLiveTailLeftReceiver A strategy hwin tag)
    (haligned :
      ProfiledRawJointHybridShadowPhaseLiveTailLeftSingleTableAligned A strategy
        hwin tag owner receiver)
    (member : Bool) (input : In₁ × In₂) :
    ProfiledRawJointHybridShadowPhaseLiveTailLeftSingleTableAligned A strategy
      hwin tag
      ⟨owner.1,
        (profiledRawJointHybridShadowPhaseLiveTailLeftSharedStep A strategy hwin
          tag owner.1 member owner.2 input.2).1⟩
      (profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStep A strategy hwin
        tag fallback owner receiver input).2 := by
  rcases haligned with
    ⟨state, move, ownerControl, row, monitorState, staged, rfl, rfl⟩
  simpa using
    (profiledRawJointHybridShadowPhaseLiveTailLeftSingleTableAligned_stepFor A
      strategy hwin tag state move ownerControl row monitorState staged member
        input)

/-! ## Exact successor keys seed both fresh endpoint values -/

/-- A left-table record carries a right-live successor.  The fresh right owner
and either fresh receiver interpretation are therefore aligned at that exact
successor key. -/
theorem
    profiledRawJointHybridShadowPhaseLiveTailFreshRight_aligned_of_key
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag)
    (parent :
      ProfiledRawJointHybridShadowPhaseLiveTailFrontierOneShared A strategy
        hwin tag)
    (output : LeftOutput A strategy hwin tag) (entryRow : PairedEntryRow)
    (receiverMember : Bool)
    (hkey :
      ProfiledRawJointHybridShadowPhaseLiveTailLeftSuccessorKeyAt A strategy
        hwin state
          (profiledRawJointHybridShadowPhaseLiveTailSuccessorTargetKey A
            strategy hwin (output.target entryRow).1)
          (output.target entryRow).1.1) :
    let payload :=
      profiledRawJointHybridShadowPhaseLiveTailLeftPendingPayloadOfOutput A
        strategy hwin tag output entryRow
    ProfiledRawJointHybridShadowPhaseLiveTailRightSingleTableAligned A strategy
      hwin tag
        (profiledRawJointHybridShadowPhaseLiveTailFreshRightOwner A strategy
          hwin tag parent payload)
        (profiledRawJointHybridShadowPhaseLiveTailFreshRightReceiver A strategy
          hwin tag payload receiverMember) := by
  dsimp only
  rcases hkey with ⟨slot, hlive, ⟨transition⟩⟩
  have hseed := transition.transition.rightSeed_aligned A strategy hwin
    (profiledRawJointHybridPhysicalCompatiblePendingRow receiverMember)
  simpa
    [profiledRawJointHybridShadowPhaseLiveTailFreshRightOwner,
      profiledRawJointHybridShadowPhaseLiveTailFreshRightReceiver,
      profiledRawJointHybridShadowPhaseLiveTailLeftPendingPayloadOfOutput,
      profiledRawJointHybridShadowPhaseLiveTailLeftPendingPayloadTarget,
      profiledRawJointHybridShadowPhaseLiveTailLeftPendingPayloadReceiver,
      profiledRawJointHybridShadowPhaseLiveTailSuccessorTargetKey,
      profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfOutput_receiver]
    using hseed

/-- Right-table/left-live mirror. -/
theorem
    profiledRawJointHybridShadowPhaseLiveTailFreshLeft_aligned_of_key
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag)
    (parent :
      ProfiledRawJointHybridShadowPhaseLiveTailFrontierTwoShared A strategy
        hwin tag)
    (output : RightOutput A strategy hwin tag) (entryRow : PairedEntryRow)
    (receiverMember : Bool)
    (hkey :
      ProfiledRawJointHybridShadowPhaseLiveTailRightSuccessorKeyAt A strategy
        hwin state
          (profiledRawJointHybridShadowPhaseLiveTailSuccessorTargetKey A
            strategy hwin (output.target entryRow).1)
          (output.target entryRow).1.1) :
    let payload :=
      profiledRawJointHybridShadowPhaseLiveTailRightPendingPayloadOfOutput A
        strategy hwin tag output entryRow
    ProfiledRawJointHybridShadowPhaseLiveTailLeftSingleTableAligned A strategy
      hwin tag
        (profiledRawJointHybridShadowPhaseLiveTailFreshLeftOwner A strategy hwin
          tag parent payload)
        (profiledRawJointHybridShadowPhaseLiveTailFreshLeftReceiver A strategy
          hwin tag payload receiverMember) := by
  dsimp only
  rcases hkey with ⟨slot, hlive, ⟨transition⟩⟩
  have hseed := transition.transition.leftSeed_aligned A strategy hwin
    (profiledRawJointHybridPhysicalCompatiblePendingRow receiverMember)
  simpa
    [profiledRawJointHybridShadowPhaseLiveTailFreshLeftOwner,
      profiledRawJointHybridShadowPhaseLiveTailFreshLeftReceiver,
      profiledRawJointHybridShadowPhaseLiveTailRightPendingPayloadOfOutput,
      profiledRawJointHybridShadowPhaseLiveTailRightPendingPayloadTarget,
      profiledRawJointHybridShadowPhaseLiveTailRightPendingPayloadReceiver,
      profiledRawJointHybridShadowPhaseLiveTailSuccessorTargetKey,
      profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfOutput_receiver]
    using hseed

/-! ## Fresh-pair closure at exact successor keys -/

/-- The closed candidates of one simultaneous receive carry both freshly
selected one-table relations.  Each relation is obtained from its own exact
successor key; the physical output is still selected from only one old live
table by `TailFreshPair`. -/
theorem
    profiledRawJointHybridShadowPhaseLiveTailFreshPair_closed_bothAligned
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂)
    (hleftKey :
      let leftReceiver :=
        profiledRawJointHybridShadowPhaseLiveTailLeftReceiverForRecvOne A
          strategy hwin tag one two
      let leftResult :=
        profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStep A strategy
          hwin tag fallbackLeft two.2.1.baseShared leftReceiver input
      let leftRow :=
        profiledRawJointHybridShadowPhaseLiveTailLeftReceiverRow A strategy hwin
          tag leftReceiver
      ProfiledRawJointHybridShadowPhaseLiveTailLeftSuccessorKeyAt A strategy
        hwin two.2.1.baseShared.1
          (profiledRawJointHybridShadowPhaseLiveTailSuccessorTargetKey A
            strategy hwin (leftResult.1.target leftRow).1)
          (leftResult.1.target leftRow).1.1)
    (hrightKey :
      let rightReceiver :=
        profiledRawJointHybridShadowPhaseLiveTailRightReceiverForRecvTwo A
          strategy hwin tag two one
      let rightResult :=
        profiledRawJointHybridShadowPhaseLiveTailRightReceiverStep A strategy
          hwin tag fallbackRight one.2.1.baseShared rightReceiver
            (input.2, input.1)
      let rightRow :=
        profiledRawJointHybridShadowPhaseLiveTailRightReceiverRow A strategy
          hwin tag rightReceiver
      ProfiledRawJointHybridShadowPhaseLiveTailRightSuccessorKeyAt A strategy
        hwin one.2.1.baseShared.1
          (profiledRawJointHybridShadowPhaseLiveTailSuccessorTargetKey A
            strategy hwin (rightResult.1.target rightRow).1)
          (rightResult.1.target rightRow).1.1) :
    let fresh :=
      profiledRawJointHybridShadowPhaseLiveTailFreshPair A strategy hwin tag
        fallbackLeft fallbackRight one two input
    ProfiledRawJointHybridShadowPhaseLiveTailRightCurrentAligned A strategy hwin
        tag fresh.1.1.closedControl fresh.1.2.closedControl ∧
      ProfiledRawJointHybridShadowPhaseLiveTailLeftCurrentAligned A strategy hwin
        tag fresh.1.1.closedControl fresh.1.2.closedControl := by
  dsimp only at hleftKey hrightKey ⊢
  let leftReceiver :=
    profiledRawJointHybridShadowPhaseLiveTailLeftReceiverForRecvOne A strategy
      hwin tag one two
  let rightReceiver :=
    profiledRawJointHybridShadowPhaseLiveTailRightReceiverForRecvTwo A strategy
      hwin tag two one
  let leftResult :=
    profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStep A strategy hwin
      tag fallbackLeft two.2.1.baseShared leftReceiver input
  let rightResult :=
    profiledRawJointHybridShadowPhaseLiveTailRightReceiverStep A strategy hwin
      tag fallbackRight one.2.1.baseShared rightReceiver (input.2, input.1)
  let leftRow :=
    profiledRawJointHybridShadowPhaseLiveTailLeftReceiverRow A strategy hwin tag
      leftReceiver
  let rightRow :=
    profiledRawJointHybridShadowPhaseLiveTailRightReceiverRow A strategy hwin tag
      rightReceiver
  have hright :=
    profiledRawJointHybridShadowPhaseLiveTailFreshRight_aligned_of_key A strategy
      hwin tag two.2.1.baseShared.1 one.2.1.baseShared leftResult.1 leftRow true
        hleftKey
  have hleft :=
    profiledRawJointHybridShadowPhaseLiveTailFreshLeft_aligned_of_key A strategy
      hwin tag one.2.1.baseShared.1 two.2.1.baseShared rightResult.1 rightRow true
        hrightKey
  simpa
    [ProfiledRawJointHybridShadowPhaseLiveTailRightCurrentAligned,
      ProfiledRawJointHybridShadowPhaseLiveTailLeftCurrentAligned,
      ProfiledRawJointHybridShadowPhaseLiveTailRightPendingAligned,
      ProfiledRawJointHybridShadowPhaseLiveTailLeftPendingAligned,
      profiledRawJointHybridShadowPhaseLiveTailFreshPair,
      leftReceiver, rightReceiver, leftResult, rightResult, leftRow, rightRow,
      FiniteAcknowledgedDelayedCarrier.PhaseLiveShared.receiver]
    using And.intro hright hleft

/-- In the closed phase `true,false`, the two fresh current relations are
exactly the full phase invariant. -/
theorem
    profiledRawJointHybridShadowPhaseLiveTailFreshPair_closed_invariant
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂)
    (hleftKey :
      let leftReceiver :=
        profiledRawJointHybridShadowPhaseLiveTailLeftReceiverForRecvOne A
          strategy hwin tag one two
      let leftResult :=
        profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStep A strategy
          hwin tag fallbackLeft two.2.1.baseShared leftReceiver input
      let leftRow :=
        profiledRawJointHybridShadowPhaseLiveTailLeftReceiverRow A strategy hwin
          tag leftReceiver
      ProfiledRawJointHybridShadowPhaseLiveTailLeftSuccessorKeyAt A strategy
        hwin two.2.1.baseShared.1
          (profiledRawJointHybridShadowPhaseLiveTailSuccessorTargetKey A
            strategy hwin (leftResult.1.target leftRow).1)
          (leftResult.1.target leftRow).1.1)
    (hrightKey :
      let rightReceiver :=
        profiledRawJointHybridShadowPhaseLiveTailRightReceiverForRecvTwo A
          strategy hwin tag two one
      let rightResult :=
        profiledRawJointHybridShadowPhaseLiveTailRightReceiverStep A strategy
          hwin tag fallbackRight one.2.1.baseShared rightReceiver
            (input.2, input.1)
      let rightRow :=
        profiledRawJointHybridShadowPhaseLiveTailRightReceiverRow A strategy
          hwin tag rightReceiver
      ProfiledRawJointHybridShadowPhaseLiveTailRightSuccessorKeyAt A strategy
        hwin one.2.1.baseShared.1
          (profiledRawJointHybridShadowPhaseLiveTailSuccessorTargetKey A
            strategy hwin (rightResult.1.target rightRow).1)
          (rightResult.1.target rightRow).1.1) :
    let fresh :=
      profiledRawJointHybridShadowPhaseLiveTailFreshPair A strategy hwin tag
        fallbackLeft fallbackRight one two input
    ProfiledRawJointHybridShadowPhaseLiveTailTableInvariant A strategy hwin tag
      fresh.1.1.closedControl fresh.1.2.closedControl := by
  dsimp only
  have hboth :=
    profiledRawJointHybridShadowPhaseLiveTailFreshPair_closed_bothAligned A
      strategy hwin tag fallbackLeft fallbackRight one two input hleftKey
        hrightKey
  simpa
    [ProfiledRawJointHybridShadowPhaseLiveTailTableInvariant,
      profiledRawJointHybridShadowPhaseLiveTailFreshPair]
    using hboth

/-! ## The two one-way phase transitions -/

/-- A strict-right round advances the currently selected right table and
prepares the exact left successor as the dormant switch table. -/
theorem
    ProfiledRawJointHybridShadowPhaseLiveTailTableInvariant.strictRight
    {tag : Tag A strategy hwin} {one : OnePending A strategy hwin tag}
    {two : TwoPending A strategy hwin tag}
    (hinvariant :
      ProfiledRawJointHybridShadowPhaseLiveTailTableInvariant A strategy hwin
        tag one two)
    (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (input : In₁ × In₂)
    (hrightKey :
      let rightReceiver :=
        profiledRawJointHybridShadowPhaseLiveTailRightReceiverForRecvTwo A
          strategy hwin tag two one
      let rightResult :=
        profiledRawJointHybridShadowPhaseLiveTailFreshRightResult A strategy
          hwin tag fallbackRight one two input
      let rightRow :=
        profiledRawJointHybridShadowPhaseLiveTailRightReceiverRow A strategy
          hwin tag rightReceiver
      ProfiledRawJointHybridShadowPhaseLiveTailRightSuccessorKeyAt A strategy
        hwin one.2.1.baseShared.1
          (profiledRawJointHybridShadowPhaseLiveTailSuccessorTargetKey A
            strategy hwin (rightResult.1.target rightRow).1)
          (rightResult.1.target rightRow).1.1) :
    let oneNext :=
      (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
        (profiledRawJointHybridShadowPhaseLiveTailOnePendingStep A strategy hwin
          tag) one input.1).1
    let fresh :=
      profiledRawJointHybridShadowPhaseLiveTailFreshPair A strategy hwin tag
        fallbackLeft fallbackRight one two input
    let twoNext := fresh.1.2.openControl
    ProfiledRawJointHybridShadowPhaseLiveTailTableInvariant A strategy hwin tag
      oneNext twoNext := by
  dsimp only at hrightKey ⊢
  let selected := hinvariant.right_selected A strategy hwin
  have hright :=
    ProfiledRawJointHybridShadowPhaseLiveTailRightSingleTableAligned.receiverStep
      A strategy hwin tag fallbackRight one.2.1.baseShared
        (profiledRawJointHybridShadowPhaseLiveTailRightReceiverForRecvTwo A
          strategy hwin tag two one) selected one.1 (input.2, input.1)
  let rightReceiver :=
    profiledRawJointHybridShadowPhaseLiveTailRightReceiverForRecvTwo A strategy
      hwin tag two one
  let rightResult :=
    profiledRawJointHybridShadowPhaseLiveTailFreshRightResult A strategy hwin tag
      fallbackRight one two input
  let rightRow :=
    profiledRawJointHybridShadowPhaseLiveTailRightReceiverRow A strategy hwin tag
      rightReceiver
  have hleft :=
    profiledRawJointHybridShadowPhaseLiveTailFreshLeft_aligned_of_key A strategy
      hwin tag one.2.1.baseShared.1 two.2.1.baseShared rightResult.1 rightRow false
        hrightKey
  simpa
    [ProfiledRawJointHybridShadowPhaseLiveTailTableInvariant,
      ProfiledRawJointHybridShadowPhaseLiveTailRightCurrentAligned,
      ProfiledRawJointHybridShadowPhaseLiveTailLeftSwitchAligned,
      ProfiledRawJointHybridShadowPhaseLiveTailRightPendingAligned,
      profiledRawJointHybridShadowPhaseLiveTailFreshPair,
      profiledRawJointHybridShadowPhaseLiveTailFreshRightResult,
      profiledRawJointHybridShadowPhaseLiveTailRecvTwoRight,
      profiledRawJointHybridShadowPhaseLiveTailOnePendingStep,
      FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv,
      FiniteAcknowledgedDelayedCarrier.phaseLivePendingStep,
      profiledRawJointHybridShadowPhaseLiveTailFrontierOnePendingStep,
      FiniteAcknowledgedDelayedCarrier.keyedDeferredSharedStep,
      rightReceiver, rightResult, rightRow]
    using And.intro hright hleft

/-- Strict-left mirror: advance the selected left table and retain the exact
right successor as the dormant switch table. -/
theorem
    ProfiledRawJointHybridShadowPhaseLiveTailTableInvariant.strictLeft
    {tag : Tag A strategy hwin} {one : OnePending A strategy hwin tag}
    {two : TwoPending A strategy hwin tag}
    (hinvariant :
      ProfiledRawJointHybridShadowPhaseLiveTailTableInvariant A strategy hwin
        tag one two)
    (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (input : In₁ × In₂)
    (hleftKey :
      let leftReceiver :=
        profiledRawJointHybridShadowPhaseLiveTailLeftReceiverForRecvOne A
          strategy hwin tag one two
      let leftResult :=
        profiledRawJointHybridShadowPhaseLiveTailFreshLeftResult A strategy
          hwin tag fallbackLeft one two input
      let leftRow :=
        profiledRawJointHybridShadowPhaseLiveTailLeftReceiverRow A strategy hwin
          tag leftReceiver
      ProfiledRawJointHybridShadowPhaseLiveTailLeftSuccessorKeyAt A strategy
        hwin two.2.1.baseShared.1
          (profiledRawJointHybridShadowPhaseLiveTailSuccessorTargetKey A
            strategy hwin (leftResult.1.target leftRow).1)
          (leftResult.1.target leftRow).1.1) :
    let fresh :=
      profiledRawJointHybridShadowPhaseLiveTailFreshPair A strategy hwin tag
        fallbackLeft fallbackRight one two input
    let oneNext := fresh.1.1.openControl
    let twoNext :=
      (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
        (profiledRawJointHybridShadowPhaseLiveTailTwoPendingStep A strategy hwin
          tag) two input.2).1
    ProfiledRawJointHybridShadowPhaseLiveTailTableInvariant A strategy hwin tag
      oneNext twoNext := by
  dsimp only at hleftKey ⊢
  let selected := hinvariant.left_selected A strategy hwin
  have hleft :=
    ProfiledRawJointHybridShadowPhaseLiveTailLeftSingleTableAligned.receiverStep
      A strategy hwin tag fallbackLeft two.2.1.baseShared
        (profiledRawJointHybridShadowPhaseLiveTailLeftReceiverForRecvOne A
          strategy hwin tag one two) selected two.1 input
  let leftReceiver :=
    profiledRawJointHybridShadowPhaseLiveTailLeftReceiverForRecvOne A strategy
      hwin tag one two
  let leftResult :=
    profiledRawJointHybridShadowPhaseLiveTailFreshLeftResult A strategy hwin tag
      fallbackLeft one two input
  let leftRow :=
    profiledRawJointHybridShadowPhaseLiveTailLeftReceiverRow A strategy hwin tag
      leftReceiver
  have hright :=
    profiledRawJointHybridShadowPhaseLiveTailFreshRight_aligned_of_key A strategy
      hwin tag two.2.1.baseShared.1 one.2.1.baseShared leftResult.1 leftRow false
        hleftKey
  simpa
    [ProfiledRawJointHybridShadowPhaseLiveTailTableInvariant,
      ProfiledRawJointHybridShadowPhaseLiveTailLeftCurrentAligned,
      ProfiledRawJointHybridShadowPhaseLiveTailRightSwitchAligned,
      ProfiledRawJointHybridShadowPhaseLiveTailLeftPendingAligned,
      profiledRawJointHybridShadowPhaseLiveTailFreshPair,
      profiledRawJointHybridShadowPhaseLiveTailFreshLeftResult,
      profiledRawJointHybridShadowPhaseLiveTailRecvOneLeft,
      profiledRawJointHybridShadowPhaseLiveTailTwoPendingStep,
      FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv,
      FiniteAcknowledgedDelayedCarrier.phaseLivePendingStep,
      profiledRawJointHybridShadowPhaseLiveTailFrontierTwoPendingStep,
      FiniteAcknowledgedDelayedCarrier.keyedDeferredSharedStep,
      leftReceiver, leftResult, leftRow]
    using And.intro hleft hright

end

end DetParityAutomaton

end DistributedSynthesis
