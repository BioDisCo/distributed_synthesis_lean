/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTagBankController
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailTrackedBootstrap

/-!
# Tracked bootstrap at a delivered tag-bank root

The first one-sided child has exactly one semantically live thread lane.  A
strict-right tag therefore starts with a tracked left table, and a strict-left
tag with a tracked right table.  This is a proof-side classification of the
finite tag already delivered by the shadow front; no endpoint guesses or
observes the current strict leader.

On the matching later receive, the one-live-lane bootstrap theorem constructs
the opposite table from the selected table's exact successor key.  From that
cut onward the ordinary full tracked invariant applies.
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

private abbrev OnePending (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailOnePending A strategy hwin tag

private abbrev TwoPending (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailTwoPending A strategy hwin tag

/-! ## The live root selected by a strict tag -/

/-- The actual proof-tree direction stored by a delayed tag. -/
def ProfiledRawJointHybridShadowPhaseLiveTag.strictActual
    (tag : Tag A strategy hwin) :
    ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂) :=
  match tag.side with
  | .right => profiledRawJointCommonOneRoundStrictRight tag.input
  | .left => profiledRawJointCommonOneRoundStrictLeft tag.input

omit [DecidableEq In₁] [DecidableEq In₂] in
omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem ProfiledRawJointHybridShadowPhaseLiveTag.direction_eq_strict
    (tag : Tag A strategy hwin) :
    tag.direction (A := A) = .strict (tag.strictActual (A := A)) := by
  cases tag with
  | mk origin input side => cases side <;> rfl

/-- Parent-linked compatibility identifies the physical table selected at the
tagged child with the unique live root of that same semantic strict edge. -/
theorem ProfiledRawJointHybridShadowPhaseLiveTag.tailRoot_cutRoot
    (tag : Tag A strategy hwin) :
    profiledRawJointHybridStrictPhysicalCutRoot A
        (tag.strictActual (A := A))
        (tag.tailRoot A strategy hwin).1.2 =
      profiledRawJointHybridCurrentSlots A
        (tag.strictActual (A := A)).side.other
        (tag.tailRoot A strategy hwin).1.1 () := by
  let package :=
    profiledRawJointHybridShadowPhaseLiveRootPackageBank A strategy hwin
      tag.origin
  have hlink := package.rootMove_realizes.1.2
  rcases hlink with
    ⟨source, hsourceCode, hsourceMove, hcurrent, hchildren⟩
  change source.code A = (tag.initialCode A strategy hwin).1 at hsourceCode
  change source.move A = package.rootMove.1 at hsourceMove
  change ∀ direction,
      profiledRawJointHybridPhysicalAnnotationAdvance A strategy hwin source
          (tag.initialCode A strategy hwin).2 direction =
        package.rootMove.2 direction at hchildren
  have hrootCode := tag.tailRoot_code A strategy hwin
  have hpublic :
      (tag.tailRoot A strategy hwin).1.1 =
        (source.step A (.strict (tag.strictActual (A := A)))).code A := by
    rw [hrootCode]
    dsimp only [ProfiledRawJointHybridShadowPhaseLiveTag.childCode,
      sourceFreeBeliefParentLinkedNext]
    rw [tag.direction_eq_strict A strategy hwin]
    rw [← hsourceCode, ← hsourceMove]
    exact (source.step_code A
      (.strict (tag.strictActual (A := A)))).symm
  have hannotation :
      (tag.tailRoot A strategy hwin).1.2 =
        profiledRawJointHybridPhysicalAnnotationAdvance A strategy hwin source
          (tag.initialCode A strategy hwin).2
          (.strict (tag.strictActual (A := A))) := by
    rw [hrootCode]
    dsimp only [ProfiledRawJointHybridShadowPhaseLiveTag.childCode,
      sourceFreeBeliefParentLinkedNext]
    rw [tag.direction_eq_strict A strategy hwin]
    exact (hchildren (.strict (tag.strictActual (A := A)))).symm
  rw [hannotation]
  rw [profiledRawJointHybridPhysicalAnnotationAdvance_strict_root_eq A strategy
    hwin]
  rw [source.strictLiveRoot_eq_currentSlots A strategy]
  rw [← hpublic]

/-- A strict-right first child has the left lane live. -/
theorem profiledRawJointHybridShadowPhaseLiveRightTag_tailRoot_leftLive
    (origin : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    let tag :=
      profiledRawJointHybridShadowPhaseLiveRightTag A strategy hwin origin input
    profiledRawJointHybridCurrentSlots A .left
        (tag.tailRoot A strategy hwin).1.1 () =
      some (.inr (tag.initialLeftMove A strategy hwin).1.source) := by
  dsimp only
  let tag :=
    profiledRawJointHybridShadowPhaseLiveRightTag A strategy hwin origin input
  have hcut := tag.tailRoot_cutRoot A strategy hwin
  have hmoves := tag.initialMoves_eq A strategy hwin
  simpa [tag, ProfiledRawJointHybridShadowPhaseLiveTag.strictActual,
    profiledRawJointHybridStrictPhysicalCutRoot, hmoves] using hcut.symm

/-- Strict-left mirror. -/
theorem profiledRawJointHybridShadowPhaseLiveLeftTag_tailRoot_rightLive
    (origin : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    let tag :=
      profiledRawJointHybridShadowPhaseLiveLeftTag A strategy hwin origin input
    profiledRawJointHybridCurrentSlots A .right
        (tag.tailRoot A strategy hwin).1.1 () =
      some (.inl (tag.initialRightMove A strategy hwin).1.source) := by
  dsimp only
  let tag :=
    profiledRawJointHybridShadowPhaseLiveLeftTag A strategy hwin origin input
  have hcut := tag.tailRoot_cutRoot A strategy hwin
  have hmoves := tag.initialMoves_eq A strategy hwin
  simpa [tag, ProfiledRawJointHybridShadowPhaseLiveTag.strictActual,
    profiledRawJointHybridStrictPhysicalCutRoot, hmoves] using hcut.symm

/-! ## Side-indexed tracked initial controls -/

theorem profiledRawJointHybridShadowPhaseLiveRightTag_initial_leftTracked
    (origin : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    let tag :=
      profiledRawJointHybridShadowPhaseLiveRightTag A strategy hwin origin input
    ProfiledRawJointHybridShadowPhaseLiveTailLeftCurrentTracked A strategy hwin
      tag (tag.initialOne A strategy hwin) (tag.initialTwo A strategy hwin) := by
  dsimp only
  let tag :=
    profiledRawJointHybridShadowPhaseLiveRightTag A strategy hwin origin input
  let state := tag.tailRoot A strategy hwin
  let move := tag.initialLeftMove A strategy hwin
  let ownerControl :=
    (profiledRawJointHybridShadowPhaseLiveTailDecoratedLeftMemberController A
      strategy hwin state move false).initial
  let monitorState :=
    (profiledRawJointHybridShadowPhaseLiveTailSuccessorLeftMonitor A strategy
      hwin (tag := tag) move false).initial
  have hmoves := tag.initialMoves_eq A strategy hwin
  have hmove : state.1.2.2 = some move := congrArg Prod.snd hmoves
  have hlive :=
    profiledRawJointHybridShadowPhaseLiveRightTag_tailRoot_leftLive A strategy
      hwin origin input
  refine ⟨state, move, ownerControl, .first, monitorState, none, [], ?_, ?_,
    hmove, ?_, ?_, ?_, ?_⟩
  · simp [tag, state, move, ownerControl,
      ProfiledRawJointHybridShadowPhaseLiveTag.initialTwo,
      ProfiledRawJointHybridShadowPhaseLiveTag.initialTwoShared,
      FiniteAcknowledgedDelayedCarrier.PhaseLiveShared.fresh,
      profiledRawJointHybridShadowPhaseLiveTailLeftSeedOwner,
      profiledRawJointHybridShadowPhaseLiveTailLeftSharedInitial, hmove]
  · simp [tag, state, move, monitorState,
      ProfiledRawJointHybridShadowPhaseLiveTag.initialOne,
      ProfiledRawJointHybridShadowPhaseLiveTag.initialOneShared,
      FiniteAcknowledgedDelayedCarrier.PhaseLiveShared.fresh,
      profiledRawJointHybridShadowPhaseLiveTailLeftSeedReceiver,
      profiledRawJointHybridShadowPhaseLiveTailLeftPayloadAtRow,
      profiledRawJointHybridShadowPhaseLiveTailSuccessorLeftMonitor,
      profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor,
      BlockRecordMonitor.comapReceiverOutput,
      profiledRawJointHybridPhysicalCompatibleLeftPayloadAtRow, hmove]
    rfl
  · exact tag.tailRoot_reachable A strategy hwin
  · exact ⟨tag.childIncidence A strategy hwin,
      tag.tailRoot_publicCode A strategy hwin⟩
  · exact ⟨.inr move.1.source, by simpa [tag, state, move] using hlive⟩
  · simpa [ownerControl, monitorState] using
      (profiledRawJointHybridShadowPhaseLiveTailLeftLocallyReachableAt_initial A
        strategy hwin tag state move)

theorem profiledRawJointHybridShadowPhaseLiveLeftTag_initial_rightTracked
    (origin : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    let tag :=
      profiledRawJointHybridShadowPhaseLiveLeftTag A strategy hwin origin input
    ProfiledRawJointHybridShadowPhaseLiveTailRightCurrentTracked A strategy hwin
      tag (tag.initialOne A strategy hwin) (tag.initialTwo A strategy hwin) := by
  dsimp only
  let tag :=
    profiledRawJointHybridShadowPhaseLiveLeftTag A strategy hwin origin input
  let state := tag.tailRoot A strategy hwin
  let move := tag.initialRightMove A strategy hwin
  let ownerControl :=
    (profiledRawJointHybridShadowPhaseLiveTailDecoratedRightMemberController A
      strategy hwin state move false).initial
  let monitorState :=
    (profiledRawJointHybridShadowPhaseLiveTailSuccessorRightMonitor A strategy
      hwin (tag := tag) move false).initial
  have hmoves := tag.initialMoves_eq A strategy hwin
  have hmove : state.1.2.1 = some move := congrArg Prod.fst hmoves
  have hlive :=
    profiledRawJointHybridShadowPhaseLiveLeftTag_tailRoot_rightLive A strategy
      hwin origin input
  refine ⟨state, move, ownerControl, .first, monitorState, none, [], ?_, ?_,
    hmove, ?_, ?_, ?_, ?_⟩
  · simp [tag, state, move, ownerControl,
      ProfiledRawJointHybridShadowPhaseLiveTag.initialOne,
      ProfiledRawJointHybridShadowPhaseLiveTag.initialOneShared,
      FiniteAcknowledgedDelayedCarrier.PhaseLiveShared.fresh,
      profiledRawJointHybridShadowPhaseLiveTailRightSeedOwner,
      profiledRawJointHybridShadowPhaseLiveTailRightSharedInitial, hmove]
  · simp [tag, state, move, monitorState,
      ProfiledRawJointHybridShadowPhaseLiveTag.initialTwo,
      ProfiledRawJointHybridShadowPhaseLiveTag.initialTwoShared,
      FiniteAcknowledgedDelayedCarrier.PhaseLiveShared.fresh,
      profiledRawJointHybridShadowPhaseLiveTailRightSeedReceiver,
      profiledRawJointHybridShadowPhaseLiveTailRightPayloadAtRow,
      profiledRawJointHybridShadowPhaseLiveTailSuccessorRightMonitor,
      profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor,
      BlockRecordMonitor.comapReceiverOutput,
      profiledRawJointHybridPhysicalCompatibleRightPayloadAtRow, hmove]
    rfl
  · exact tag.tailRoot_reachable A strategy hwin
  · exact ⟨tag.childIncidence A strategy hwin,
      tag.tailRoot_publicCode A strategy hwin⟩
  · exact ⟨.inl move.1.source, by simpa [tag, state, move] using hlive⟩
  · simpa [ownerControl, monitorState] using
      (profiledRawJointHybridShadowPhaseLiveTailRightLocallyReachableAt_initial A
        strategy hwin tag state move)

/-! ## One matching receive enters the full invariant -/

theorem profiledRawJointHybridShadowPhaseLiveRightTag_bootstrap_strictLeft
    (origin : ProfiledRawJointHybridCommonControl A strategy hwin)
    (first input : In₁ × In₂) :
    let tag :=
      profiledRawJointHybridShadowPhaseLiveRightTag A strategy hwin origin first
    let one := tag.initialOne A strategy hwin
    let two := tag.initialTwo A strategy hwin
    let fresh :=
      profiledRawJointHybridShadowPhaseLiveTailFreshPair A strategy hwin tag
        (tag.fallbackLeftOutput A strategy hwin)
        (tag.fallbackRightOutput A strategy hwin) one two input
    let oneNext := fresh.1.1.openControl
    let twoNext :=
      (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
        (profiledRawJointHybridShadowPhaseLiveTailTwoPendingStep A strategy hwin
          tag) two input.2).1
    ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant.{u, v, x, y, s,
      0, 0, 0, 0} A strategy hwin tag oneNext twoNext := by
  dsimp only
  let tag :=
    profiledRawJointHybridShadowPhaseLiveRightTag A strategy hwin origin first
  simpa only [tag] using
    ProfiledRawJointHybridShadowPhaseLiveTailLeftCurrentTracked.strictLeft.{u,
      v, x, y, s, 0, 0, 0, 0, 0, 0, 0, 0}
      (A := A) (strategy := strategy) (hwin := hwin) (tag := tag)
      (one := tag.initialOne A strategy hwin)
      (two := tag.initialTwo A strategy hwin)
      (profiledRawJointHybridShadowPhaseLiveRightTag_initial_leftTracked A
        strategy hwin origin first) rfl
      (tag.fallbackLeftOutput A strategy hwin)
      (tag.fallbackRightOutput A strategy hwin) input

theorem profiledRawJointHybridShadowPhaseLiveLeftTag_bootstrap_strictRight
    (origin : ProfiledRawJointHybridCommonControl A strategy hwin)
    (first input : In₁ × In₂) :
    let tag :=
      profiledRawJointHybridShadowPhaseLiveLeftTag A strategy hwin origin first
    let one := tag.initialOne A strategy hwin
    let two := tag.initialTwo A strategy hwin
    let oneNext :=
      (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
        (profiledRawJointHybridShadowPhaseLiveTailOnePendingStep A strategy hwin
          tag) one input.1).1
    let fresh :=
      profiledRawJointHybridShadowPhaseLiveTailFreshPair A strategy hwin tag
        (tag.fallbackLeftOutput A strategy hwin)
        (tag.fallbackRightOutput A strategy hwin) one two input
    let twoNext := fresh.1.2.openControl
    ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant.{u, v, x, y, s,
      0, 0, 0, 0} A strategy hwin tag oneNext twoNext := by
  dsimp only
  let tag :=
    profiledRawJointHybridShadowPhaseLiveLeftTag A strategy hwin origin first
  simpa only [tag] using
    ProfiledRawJointHybridShadowPhaseLiveTailRightCurrentTracked.strictRight.{u,
      v, x, y, s, 0, 0, 0, 0, 0, 0, 0, 0}
      (A := A) (strategy := strategy) (hwin := hwin) (tag := tag)
      (one := tag.initialOne A strategy hwin)
      (two := tag.initialTwo A strategy hwin)
      (profiledRawJointHybridShadowPhaseLiveLeftTag_initial_rightTracked A
        strategy hwin origin first) rfl
      (tag.fallbackLeftOutput A strategy hwin)
      (tag.fallbackRightOutput A strategy hwin) input

end

end DetParityAutomaton

end DistributedSynthesis
