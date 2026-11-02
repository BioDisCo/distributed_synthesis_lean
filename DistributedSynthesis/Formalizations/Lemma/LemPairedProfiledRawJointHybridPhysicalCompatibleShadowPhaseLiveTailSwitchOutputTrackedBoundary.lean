/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailSwitchOutputAudit
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveBothOutput
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralHeterogeneousSeam

/-!
# The tracked/output boundary at a tagged-tail switch

`TailTrackedInvariant` supplies two *separately* literal selected tables.  Its
right and left witnesses may use different reachable tail states, moves,
controls, rows, and private words.  Consequently a phase split extracts the
two tracked witnesses but creates no cross-receiver equation between them.

This file records the exact positive boundary.

* At one public phase only one of the two anti-mosaic equations is needed to
  identify the locally forced receive pair with the existing phase-selected
  physical pair.
* A pair of records pinned to one represented guarded-common occurrence has
  both equations, by `ProfiledRawJointGuardedCommonPair.root_outputOne` and
  `root_outputTwo`.

Thus the missing invariant is a coupled same-occurrence relation.  Individual
literal-prefix reachability is not such a relation.  The heterogeneous seam
imported above supplies the complementary same-sender law at a fresh
right/`both` seam
(`profiledRawJointLiteralRightBothExactHeterogeneousLeftTableAtChild_noRecv_output_eq`),
but by itself it mentions only the two hidden interpretations of the left
sender and therefore cannot prove a right/left receiver cross equation.
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

private abbrev RightOutput (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailRightReceiverOutput A strategy hwin
    tag

private abbrev LeftOutput (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailLeftReceiverOutput A strategy hwin
    tag

/-! ## Exactly what the tracked invariant exposes -/

/-- Phase splitting a tracked invariant yields the two selected literal
tables.  Notice that the conclusion is a conjunction of two unary tracked
relations, not a relation coupling their semantic occurrences. -/
theorem
    ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant.selected_pair
    {tag : Tag A strategy hwin} {one : OnePending A strategy hwin tag}
    {two : TwoPending A strategy hwin tag}
    (hinvariant :
      ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant A strategy hwin
        tag one two) :
    ProfiledRawJointHybridShadowPhaseLiveTailRightTracked A strategy hwin tag
        one.2.1.baseShared
          (profiledRawJointHybridShadowPhaseLiveTailRightReceiverForRecvTwo A
            strategy hwin tag two one) ∧
      ProfiledRawJointHybridShadowPhaseLiveTailLeftTracked A strategy hwin tag
        two.2.1.baseShared
          (profiledRawJointHybridShadowPhaseLiveTailLeftReceiverForRecvOne A
            strategy hwin tag one two) := by
  exact ⟨hinvariant.right_selected A strategy hwin,
    hinvariant.left_selected A strategy hwin⟩

/-! ## The minimal phase-selected cross law -/

/-- Only the cross equation used by the currently selected whole-table pair.
When process one's public phase is `false`, the existing pair is the right
record, so only its process-one closing coordinate must agree with the left
receiver.  At phase `true` the mirror equation is the only required one. -/
def ProfiledRawJointHybridShadowPhaseLiveTailPhaseSwitchOutputCompatible
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂) : Prop :=
  let right :=
    profiledRawJointHybridShadowPhaseLiveTailSwitchRightRecord A strategy hwin
      tag fallbackRight one two input
  let left :=
    profiledRawJointHybridShadowPhaseLiveTailSwitchLeftRecord A strategy hwin
      tag fallbackLeft one two input
  if one.2.1.localPhase then
    left.physical.closingBoth =
      pairedRightInformedForRow .both right.physical
  else
    right.physical.closingBoth =
      pairedLeftInformedForRow .both left.physical

/-- The full audit law implies the smaller phase-selected law. -/
theorem
    ProfiledRawJointHybridShadowPhaseLiveTailSwitchOutputCompatible.phase
    {tag : Tag A strategy hwin} {fallbackLeft : LeftOutput A strategy hwin tag}
    {fallbackRight : RightOutput A strategy hwin tag}
    {one : OnePending A strategy hwin tag}
    {two : TwoPending A strategy hwin tag} {input : In₁ × In₂}
    (hcompatible :
      ProfiledRawJointHybridShadowPhaseLiveTailSwitchOutputCompatible A
        strategy hwin tag fallbackLeft fallbackRight one two input) :
    ProfiledRawJointHybridShadowPhaseLiveTailPhaseSwitchOutputCompatible A
      strategy hwin tag fallbackLeft fallbackRight one two input := by
  cases hphase : one.2.1.localPhase
  · simpa [ProfiledRawJointHybridShadowPhaseLiveTailPhaseSwitchOutputCompatible,
      hphase] using hcompatible.1
  · simpa [ProfiledRawJointHybridShadowPhaseLiveTailPhaseSwitchOutputCompatible,
      hphase] using hcompatible.2

/-- The minimal phase-selected equation is exactly sufficient: the two
locally forced receive projections reproduce the physical output pair of the
existing phase-selected controller. -/
theorem
    ProfiledRawJointHybridShadowPhaseLiveTailPhaseSwitchOutputCompatible.output_eq_freshPair
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂)
    (hinvariant :
      ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant A strategy hwin
        tag one two)
    (hcompatible :
      ProfiledRawJointHybridShadowPhaseLiveTailPhaseSwitchOutputCompatible A
        strategy hwin tag fallbackLeft fallbackRight one two input) :
    (profiledRawJointHybridShadowPhaseLiveTailSwitchOutputOne A strategy hwin
        tag fallbackLeft one two input,
      profiledRawJointHybridShadowPhaseLiveTailSwitchOutputTwo A strategy hwin
        tag fallbackRight one two input) =
      (profiledRawJointHybridShadowPhaseLiveTailFreshPair A strategy hwin tag
        fallbackLeft fallbackRight one two input).2 := by
  cases hphase : one.2.1.localPhase
  · cases htwo : two.2.1.localPhase
    · simp only
        [ProfiledRawJointHybridShadowPhaseLiveTailPhaseSwitchOutputCompatible,
          hphase, Bool.false_eq_true, ↓reduceIte] at hcompatible
      simp only [profiledRawJointHybridShadowPhaseLiveTailFreshPair,
        profiledRawJointHybridShadowPhaseLiveTailPendingBothOutputOne,
        profiledRawJointHybridShadowPhaseLiveTailPendingBothOutputTwo, hphase,
        htwo, Bool.false_eq_true, ↓reduceIte,
        profiledRawJointHybridShadowPhaseLiveTailSwitchOutputOne,
        profiledRawJointHybridShadowPhaseLiveTailSwitchOutputTwo,
        profiledRawJointHybridShadowPhaseLiveTailSwitchRightRecord,
        profiledRawJointHybridShadowPhaseLiveTailSwitchLeftRecord,
        profiledRawJointHybridShadowPhaseLiveTailRightReceiverForRecvTwo,
        profiledRawJointHybridShadowPhaseLiveTailLeftReceiverForRecvOne,
        profiledRawJointHybridShadowPhaseLiveTailRightSingleTableBothOutputOne,
        profiledRawJointHybridShadowPhaseLiveTailRightSingleTableBothOutputTwo]
      apply Prod.ext
      · simpa [profiledRawJointHybridShadowPhaseLiveTailSwitchRightRecord,
          profiledRawJointHybridShadowPhaseLiveTailSwitchLeftRecord,
          profiledRawJointHybridShadowPhaseLiveTailRightReceiverForRecvTwo,
          profiledRawJointHybridShadowPhaseLiveTailLeftReceiverForRecvOne,
          hphase, htwo] using hcompatible.symm
      · rfl
    · simp only [ProfiledRawJointHybridShadowPhaseLiveTailTrackedInvariant,
        hphase, htwo] at hinvariant
  · cases htwo : two.2.1.localPhase
    · simp only
        [ProfiledRawJointHybridShadowPhaseLiveTailPhaseSwitchOutputCompatible,
          hphase, ↓reduceIte] at hcompatible
      simp only [profiledRawJointHybridShadowPhaseLiveTailFreshPair,
        profiledRawJointHybridShadowPhaseLiveTailPendingBothOutputOne,
        profiledRawJointHybridShadowPhaseLiveTailPendingBothOutputTwo, hphase,
        htwo, ↓reduceIte,
        profiledRawJointHybridShadowPhaseLiveTailSwitchOutputOne,
        profiledRawJointHybridShadowPhaseLiveTailSwitchOutputTwo,
        profiledRawJointHybridShadowPhaseLiveTailSwitchRightRecord,
        profiledRawJointHybridShadowPhaseLiveTailSwitchLeftRecord,
        profiledRawJointHybridShadowPhaseLiveTailRightReceiverForRecvTwo,
        profiledRawJointHybridShadowPhaseLiveTailLeftReceiverForRecvOne,
        profiledRawJointHybridShadowPhaseLiveTailLeftSingleTableBothOutputOne,
        profiledRawJointHybridShadowPhaseLiveTailLeftSingleTableBothOutputTwo]
      apply Prod.ext
      · rfl
      · simpa [profiledRawJointHybridShadowPhaseLiveTailSwitchRightRecord,
          profiledRawJointHybridShadowPhaseLiveTailSwitchLeftRecord,
          profiledRawJointHybridShadowPhaseLiveTailRightReceiverForRecvTwo,
          profiledRawJointHybridShadowPhaseLiveTailLeftReceiverForRecvOne,
          hphase, htwo] using hcompatible.symm
    · simp only
        [ProfiledRawJointHybridShadowPhaseLiveTailPhaseSwitchOutputCompatible,
          hphase, ↓reduceIte] at hcompatible
      simp only [profiledRawJointHybridShadowPhaseLiveTailFreshPair,
        profiledRawJointHybridShadowPhaseLiveTailPendingBothOutputOne,
        profiledRawJointHybridShadowPhaseLiveTailPendingBothOutputTwo, hphase,
        htwo, ↓reduceIte,
        profiledRawJointHybridShadowPhaseLiveTailSwitchOutputOne,
        profiledRawJointHybridShadowPhaseLiveTailSwitchOutputTwo,
        profiledRawJointHybridShadowPhaseLiveTailSwitchRightRecord,
        profiledRawJointHybridShadowPhaseLiveTailSwitchLeftRecord,
        profiledRawJointHybridShadowPhaseLiveTailRightReceiverForRecvTwo,
        profiledRawJointHybridShadowPhaseLiveTailLeftReceiverForRecvOne,
        profiledRawJointHybridShadowPhaseLiveTailLeftSingleTableBothOutputOne,
        profiledRawJointHybridShadowPhaseLiveTailLeftSingleTableBothOutputTwo]
      apply Prod.ext
      · rfl
      · simpa [profiledRawJointHybridShadowPhaseLiveTailSwitchRightRecord,
          profiledRawJointHybridShadowPhaseLiveTailSwitchLeftRecord,
          profiledRawJointHybridShadowPhaseLiveTailRightReceiverForRecvTwo,
          profiledRawJointHybridShadowPhaseLiveTailLeftReceiverForRecvOne,
          hphase, htwo] using hcompatible.symm

/-! ## The coupled relation which actually supplies the law -/

/-- The two selected records are the two receiver roots of one represented
guarded-common pair.  This is proof-only occurrence coupling; it exposes no
side or leader bit to either endpoint. -/
def ProfiledRawJointHybridShadowPhaseLiveTailSwitchRecordsJointlyPinned
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂) : Prop :=
  ∃ pair : ProfiledRawJointGuardedCommonPair A strategy hwin,
    let right :=
      profiledRawJointHybridShadowPhaseLiveTailSwitchRightRecord A strategy hwin
        tag fallbackRight one two input
    let left :=
      profiledRawJointHybridShadowPhaseLiveTailSwitchLeftRecord A strategy hwin
        tag fallbackLeft one two input
    right.physical =
        (pair.rightRootRecord A strategy hwin input).2.1.physical ∧
      left.physical =
        (pair.leftRootRecord A strategy hwin input).2.1.physical

/-- Joint occurrence pinning supplies both anti-mosaic equations, hence the
full audit law. -/
theorem
    ProfiledRawJointHybridShadowPhaseLiveTailSwitchRecordsJointlyPinned.compatible
    {tag : Tag A strategy hwin} {fallbackLeft : LeftOutput A strategy hwin tag}
    {fallbackRight : RightOutput A strategy hwin tag}
    {one : OnePending A strategy hwin tag}
    {two : TwoPending A strategy hwin tag} {input : In₁ × In₂}
    (hpinned :
      ProfiledRawJointHybridShadowPhaseLiveTailSwitchRecordsJointlyPinned A
        strategy hwin tag fallbackLeft fallbackRight one two input) :
    ProfiledRawJointHybridShadowPhaseLiveTailSwitchOutputCompatible A strategy
      hwin tag fallbackLeft fallbackRight one two input := by
  rcases hpinned with ⟨pair, hright, hleft⟩
  unfold ProfiledRawJointHybridShadowPhaseLiveTailSwitchOutputCompatible
  dsimp only
  constructor
  · rw [hright, hleft]
    exact pair.root_outputOne A strategy hwin input
  · rw [hleft, hright]
    exact pair.root_outputTwo A strategy hwin input

/-- The tag's canonical guarded pair is a convenient specialization of the
same-occurrence relation. -/
def ProfiledRawJointHybridShadowPhaseLiveTailSwitchRecordsPinnedToTagRoot
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (input : In₁ × In₂) : Prop :=
  let pair := tag.guardedCommonPair A strategy hwin
  let right :=
    profiledRawJointHybridShadowPhaseLiveTailSwitchRightRecord A strategy hwin
      tag fallbackRight one two input
  let left :=
    profiledRawJointHybridShadowPhaseLiveTailSwitchLeftRecord A strategy hwin
      tag fallbackLeft one two input
  right.physical =
      (pair.rightRootRecord A strategy hwin input).2.1.physical ∧
    left.physical =
      (pair.leftRootRecord A strategy hwin input).2.1.physical

theorem
    ProfiledRawJointHybridShadowPhaseLiveTailSwitchRecordsPinnedToTagRoot.jointlyPinned
    {tag : Tag A strategy hwin} {fallbackLeft : LeftOutput A strategy hwin tag}
    {fallbackRight : RightOutput A strategy hwin tag}
    {one : OnePending A strategy hwin tag}
    {two : TwoPending A strategy hwin tag} {input : In₁ × In₂}
    (hpinned :
      ProfiledRawJointHybridShadowPhaseLiveTailSwitchRecordsPinnedToTagRoot A
        strategy hwin tag fallbackLeft fallbackRight one two input) :
    ProfiledRawJointHybridShadowPhaseLiveTailSwitchRecordsJointlyPinned A
      strategy hwin tag fallbackLeft fallbackRight one two input := by
  exact ⟨tag.guardedCommonPair A strategy hwin, hpinned⟩

theorem
    ProfiledRawJointHybridShadowPhaseLiveTailSwitchRecordsPinnedToTagRoot.compatible
    {tag : Tag A strategy hwin} {fallbackLeft : LeftOutput A strategy hwin tag}
    {fallbackRight : RightOutput A strategy hwin tag}
    {one : OnePending A strategy hwin tag}
    {two : TwoPending A strategy hwin tag} {input : In₁ × In₂}
    (hpinned :
      ProfiledRawJointHybridShadowPhaseLiveTailSwitchRecordsPinnedToTagRoot A
        strategy hwin tag fallbackLeft fallbackRight one two input) :
    ProfiledRawJointHybridShadowPhaseLiveTailSwitchOutputCompatible A strategy
      hwin tag fallbackLeft fallbackRight one two input :=
  (hpinned.jointlyPinned A strategy hwin).compatible A strategy hwin

end

end DetParityAutomaton

end DistributedSynthesis
