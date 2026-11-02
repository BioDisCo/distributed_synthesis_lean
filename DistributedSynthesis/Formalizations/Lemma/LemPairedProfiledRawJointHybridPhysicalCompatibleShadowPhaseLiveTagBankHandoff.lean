/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailTableInvariant

/-!
# Initializing the finite tagged tail bank

This file connects the delayed finite tag installed by the leader-free shadow
front to the phase-live controller in the tag's ordinary accepting tail.  The
initialization is a lookup in the finite tag bank.  It does not inspect the
current graph, a hierarchy orientation, a leader bit, a strict-leader bit, a
semantic history, or either endpoint's full view.

The first technical point is that the empty state of the re-rooted tail is
literally the child named by the tag.  The second is that both optional
physical lanes at that child are present.  This does not tell either process
which lane is currently live: both tables are installed together from the
same common occurrence, and the local phase bits select their retained
interpretations later.
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

/-! ## The literal root of one tag fibre -/

/-- Empty-node state of the ordinary accepting policy below the tagged strict
child. -/
noncomputable def ProfiledRawJointHybridShadowPhaseLiveTag.tailRoot
    (tag : Tag A strategy hwin) : TailState A strategy hwin tag :=
  (tag.tailCodePolicy A strategy hwin).run []

/-- Re-rooting changes the initial objective control, but not the literal code
stored at the root of the tail. -/
theorem ProfiledRawJointHybridShadowPhaseLiveTag.tailRoot_code
    (tag : Tag A strategy hwin) :
    (tag.tailRoot A strategy hwin).1 = tag.childCode A strategy hwin := by
  let package :=
    profiledRawJointHybridShadowPhaseLiveRootPackageBank A strategy hwin
      tag.origin
  have hchild := congrArg Prod.snd (tag.childRun A strategy hwin)
  simpa [ProfiledRawJointHybridShadowPhaseLiveTag.tailRoot,
    SourceFreeBeliefCodeParityRootPinnedPolicy.tailCodePolicy_run,
    package] using congrArg Prod.fst hchild

/-- The first tagged strict child installs both physical sibling lanes from
one common semantic source.  The existential moves are proof-side witnesses;
the executable state contains only their finite optional encodings. -/
theorem ProfiledRawJointHybridShadowPhaseLiveTag.tailRoot_lanes
    (tag : Tag A strategy hwin) :
    ∃ rightMove : ProfiledRawJointRightPhysicalSiblingMove A,
      ∃ leftMove : ProfiledRawJointLeftPhysicalSiblingMove A,
        (tag.tailRoot A strategy hwin).1.2 =
          (some rightMove, some leftMove) := by
  let installed :=
    profiledRawJointHybridShadowPhaseLiveInstalled A strategy hwin tag.origin
  let package :=
    profiledRawJointHybridShadowPhaseLiveRootPackageBank A strategy hwin
      tag.origin
  have hlink := package.rootMove_realizes.1.2
  rcases hlink with
    ⟨source, hsourceCode, hsourceMove, hcurrent, hchildren⟩
  have hrootCode := tag.tailRoot_code A strategy hwin
  cases source with
  | common world =>
      have hright :=
        profiledRawJointHybridPhysicalAnnotationOf_right A strategy hwin
          (profiledRawJointCommonWorldFamily A world)
          (profiledRawJointBothRestartDirection tag.input)
          ((profiledRawJointCommonWorldAfterBoth A world tag.input
            ).procOneMember A)
          (profiledRawJointCommonWorld_semanticChild_right_bothRestart A world
            tag.input)
      have hleft :=
        profiledRawJointHybridPhysicalAnnotationOf_left A strategy hwin
          (profiledRawJointCommonWorldFamily A world)
          (profiledRawJointBothRestartDirection tag.input)
          ((profiledRawJointCommonWorldAfterBoth A world tag.input
            ).procTwoMember A)
          (profiledRawJointCommonWorld_semanticChild_left_bothRestart A world
            tag.input)
      rcases hright with ⟨rightMove, hright⟩
      rcases hleft with ⟨leftMove, hleft⟩
      refine ⟨rightMove, leftMove, ?_⟩
      rw [hrootCode]
      change package.rootMove.2 (tag.direction (A := A)) =
        (some rightMove, some leftMove)
      rw [← hchildren (tag.direction (A := A))]
      have hann :
          profiledRawJointHybridPhysicalAnnotationOf A strategy hwin
              (profiledRawJointCommonWorldFamily A world)
              (profiledRawJointBothRestartDirection tag.input) =
            (some rightMove, some leftMove) := by
        exact Prod.ext hright hleft
      cases tag with
      | mk origin input side =>
          cases side <;> simpa
            [ProfiledRawJointHybridShadowPhaseLiveTag.direction,
              profiledRawJointCommonOneRoundStrictRight,
              profiledRawJointCommonOneRoundStrictLeft,
              profiledRawJointCommonActualDirection,
              profiledRawJointForceBothPivots] using hann
  | oneSided source =>
      simp [ProfiledRawJointHybridShadowPhaseLiveTag.initialCode,
        ProfiledRawJointHybridSemanticState.code] at hsourceCode
  | dead =>
      simp [ProfiledRawJointHybridShadowPhaseLiveTag.initialCode,
        ProfiledRawJointHybridSemanticState.code] at hsourceCode

/-! ## A canonical finite pending pair in each tag fibre -/

/-- The public one-sided incidence code named by a tag. -/
noncomputable def ProfiledRawJointHybridShadowPhaseLiveTag.childIncidence
    (tag : Tag A strategy hwin) :
    ProfiledRawJointIncidenceCode A (I := Unit) :=
  let installed :=
    profiledRawJointHybridShadowPhaseLiveInstalled A strategy hwin tag.origin
  match tag.side with
  | .right =>
      profiledRawJointOneSidedNext A installed.incidenceCode installed.rawMove
        (profiledRawJointCommonOneRoundStrictRight tag.input)
  | .left =>
      profiledRawJointOneSidedNext A installed.incidenceCode installed.rawMove
        (profiledRawJointCommonOneRoundStrictLeft tag.input)

@[simp] theorem ProfiledRawJointHybridShadowPhaseLiveTag.tailRoot_publicCode
    (tag : Tag A strategy hwin) :
    (tag.tailRoot A strategy hwin).1.1 =
      .oneSided (tag.childIncidence A strategy hwin) := by
  rw [tag.tailRoot_code A strategy hwin]
  cases tag with
  | mk origin input side =>
      cases side
      · exact profiledRawJointHybridShadowPhaseLiveRightTag_childCode_fst A
          strategy hwin origin input
      · exact profiledRawJointHybridShadowPhaseLiveLeftTag_childCode_fst A
          strategy hwin origin input

/-- Dormant payload held by process one at installation.  Both interpretations
point to the same literal tail root and differ only in the next entry row. -/
noncomputable def
    ProfiledRawJointHybridShadowPhaseLiveTag.initialOnePayload
    (tag : Tag A strategy hwin) :
    ProfiledRawJointHybridShadowPhaseLiveTailLeftPendingPayload A strategy hwin
      tag :=
  { target :=
      (tag.childIncidence A strategy hwin,
        (.first, tag.tailRoot A strategy hwin))
    firstReceiver :=
      profiledRawJointHybridShadowPhaseLiveTailRightPayloadAtRow A strategy hwin
        tag (tag.tailRoot A strategy hwin) .first
    bothReceiver :=
      profiledRawJointHybridShadowPhaseLiveTailRightPayloadAtRow A strategy hwin
        tag (tag.tailRoot A strategy hwin) .both }

/-- Process-two mirror. -/
noncomputable def
    ProfiledRawJointHybridShadowPhaseLiveTag.initialTwoPayload
    (tag : Tag A strategy hwin) :
    ProfiledRawJointHybridShadowPhaseLiveTailRightPendingPayload A strategy
      hwin tag :=
  { target :=
      (tag.childIncidence A strategy hwin,
        (.first, tag.tailRoot A strategy hwin))
    firstReceiver :=
      profiledRawJointHybridShadowPhaseLiveTailLeftPayloadAtRow A strategy hwin
        tag (tag.tailRoot A strategy hwin) .first
    bothReceiver :=
      profiledRawJointHybridShadowPhaseLiveTailLeftPayloadAtRow A strategy hwin
        tag (tag.tailRoot A strategy hwin) .both }

/-- Process one's initial phase-live state.  The phase `true` and process
two's phase `false` are the same canonical post-receive phase pair installed
by every later fresh close. -/
noncomputable def ProfiledRawJointHybridShadowPhaseLiveTag.initialOneShared
    (tag : Tag A strategy hwin) :
    ProfiledRawJointHybridShadowPhaseLiveTailOneShared A strategy hwin tag :=
  FiniteAcknowledgedDelayedCarrier.PhaseLiveShared.fresh
    (profiledRawJointHybridShadowPhaseLiveTailRightSeedOwner A strategy hwin
      tag (tag.tailRoot A strategy hwin))
    (tag.initialOnePayload A strategy hwin) true
    (profiledRawJointHybridShadowPhaseLiveTailLeftSeedReceiver A strategy hwin
      tag (tag.tailRoot A strategy hwin) .first)
    (profiledRawJointHybridShadowPhaseLiveTailLeftSeedReceiver A strategy hwin
      tag (tag.tailRoot A strategy hwin) .both)

/-- Process-two mirror, with the complementary local phase. -/
noncomputable def ProfiledRawJointHybridShadowPhaseLiveTag.initialTwoShared
    (tag : Tag A strategy hwin) :
    ProfiledRawJointHybridShadowPhaseLiveTailTwoShared A strategy hwin tag :=
  FiniteAcknowledgedDelayedCarrier.PhaseLiveShared.fresh
    (profiledRawJointHybridShadowPhaseLiveTailLeftSeedOwner A strategy hwin tag
      (tag.tailRoot A strategy hwin))
    (tag.initialTwoPayload A strategy hwin) false
    (profiledRawJointHybridShadowPhaseLiveTailRightSeedReceiver A strategy hwin
      tag (tag.tailRoot A strategy hwin) .first)
    (profiledRawJointHybridShadowPhaseLiveTailRightSeedReceiver A strategy hwin
      tag (tag.tailRoot A strategy hwin) .both)

/-- Canonical unresolved controls delivered to the two endpoint controllers.
The outer member is initially `false`; it is stored control, not a graph bit. -/
noncomputable def ProfiledRawJointHybridShadowPhaseLiveTag.initialOne
    (tag : Tag A strategy hwin) : OnePending A strategy hwin tag :=
  (false, tag.initialOneShared A strategy hwin, PUnit.unit)

noncomputable def ProfiledRawJointHybridShadowPhaseLiveTag.initialTwo
    (tag : Tag A strategy hwin) : TwoPending A strategy hwin tag :=
  (false, tag.initialTwoShared A strategy hwin, PUnit.unit)

@[simp] theorem ProfiledRawJointHybridShadowPhaseLiveTag.initialOne_member
    (tag : Tag A strategy hwin) :
    (tag.initialOne A strategy hwin).1 = false :=
  rfl

@[simp] theorem ProfiledRawJointHybridShadowPhaseLiveTag.initialTwo_member
    (tag : Tag A strategy hwin) :
    (tag.initialTwo A strategy hwin).1 = false :=
  rfl

@[simp] theorem ProfiledRawJointHybridShadowPhaseLiveTag.initialOne_phase
    (tag : Tag A strategy hwin) :
    (tag.initialOne A strategy hwin).2.1.localPhase = true :=
  rfl

@[simp] theorem ProfiledRawJointHybridShadowPhaseLiveTag.initialTwo_phase
    (tag : Tag A strategy hwin) :
    (tag.initialTwo A strategy hwin).2.1.localPhase = false :=
  rfl

/-- The selected finite tag initializes the complete phase-indexed table
invariant without a hierarchy or leader premise. -/
theorem ProfiledRawJointHybridShadowPhaseLiveTag.initial_tableInvariant
    (tag : Tag A strategy hwin) :
    ProfiledRawJointHybridShadowPhaseLiveTailTableInvariant A strategy hwin tag
      (tag.initialOne A strategy hwin)
      (tag.initialTwo A strategy hwin) := by
  rcases tag.tailRoot_lanes A strategy hwin with
    ⟨rightMove, leftMove, hlanes⟩
  have hright : (tag.tailRoot A strategy hwin).1.2.1 = some rightMove :=
    congrArg Prod.fst hlanes
  have hleft : (tag.tailRoot A strategy hwin).1.2.2 = some leftMove :=
    congrArg Prod.snd hlanes
  change
    ProfiledRawJointHybridShadowPhaseLiveTailRightPendingAligned A strategy
        hwin tag (tag.initialOne A strategy hwin)
          (tag.initialTwo A strategy hwin) ∧
      ProfiledRawJointHybridShadowPhaseLiveTailLeftPendingAligned A strategy
        hwin tag (tag.initialOne A strategy hwin)
          (tag.initialTwo A strategy hwin)
  constructor
  · simpa [ProfiledRawJointHybridShadowPhaseLiveTag.initialOne,
      ProfiledRawJointHybridShadowPhaseLiveTag.initialTwo,
      ProfiledRawJointHybridShadowPhaseLiveTag.initialOneShared,
      ProfiledRawJointHybridShadowPhaseLiveTag.initialTwoShared,
      ProfiledRawJointHybridShadowPhaseLiveTailRightPendingAligned] using
      (profiledRawJointHybridShadowPhaseLiveTailRightSeed_aligned A strategy
        hwin tag (tag.tailRoot A strategy hwin) rightMove hright .first)
  · simpa [ProfiledRawJointHybridShadowPhaseLiveTag.initialOne,
      ProfiledRawJointHybridShadowPhaseLiveTag.initialTwo,
      ProfiledRawJointHybridShadowPhaseLiveTag.initialOneShared,
      ProfiledRawJointHybridShadowPhaseLiveTag.initialTwoShared,
      ProfiledRawJointHybridShadowPhaseLiveTailLeftPendingAligned] using
      (profiledRawJointHybridShadowPhaseLiveTailLeftSeed_aligned A strategy hwin
        tag (tag.tailRoot A strategy hwin) leftMove hleft .first)

end

end DetParityAutomaton

end DistributedSynthesis
