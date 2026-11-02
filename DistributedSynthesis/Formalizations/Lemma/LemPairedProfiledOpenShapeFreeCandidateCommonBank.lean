/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenShapeFreeSidewiseBankAdapter
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenReanchoredSidewiseSuccessor
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenLocalFibreSuccessorHomogeneity
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenShapeFreeFixedPolicyTable
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenShapeFreeInitialCandidate

/-!
# A shape-free common sidewise bank

The active-side projected value retains a literal semantic witness for every
advertised descriptor, at every reachable controller node.  This file first
adapts that retained provenance to the re-anchored-row interface consumed by
the pointed successor construction.  The adaptation is deliberately
one-way: membership produces an attained controlled-fibre witness; equality
of public projected classes is never reflected back into equality of hidden
views, controls, or optional lane shapes.

This is the information-safe direction required at a permanently hidden-bit
boundary.  No process recovers the hidden bit, detects the strict leader, or
branches on the proof-side optional shape.
-/

namespace DistributedSynthesis

universe i u v x y s

namespace DetParityAutomaton

variable {I : Type i}
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Fintype I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
variable (hwin : ∀ env : EnvironmentSequence In₁ In₂,
  A.Accepts (execution strategy env))
variable (basis : ∀ state : PairedProfiledTreeState A,
  (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
variable (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))

private abbrev ShapeFreeDescriptor :=
  ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode

private abbrev ShapeFreeFamily :=
  ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I) initialCode

/-- Each process-local tag is a finite projected image of hidden
descriptors.  The two occurrences are used independently. -/
abbrev ProfiledOpenActiveLaneSideClass :=
  Finset (ShapeFreeDescriptor A initialCode)

noncomputable local instance activeLaneShapeFreeDescriptorDecidableEq :
    DecidableEq (ShapeFreeDescriptor A initialCode) :=
  Classical.decEq _

noncomputable instance : Fintype
    (ProfiledOpenActiveLaneSideClass A initialCode) := by
  classical
  infer_instance

/-! ## Retained active-fibre provenance gives exact re-anchored rows -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- A projected right value with retained strong provenance satisfies the
general per-member re-anchoring law.  The re-anchored state is the literal
controlled source-fibre point represented by the requested member. -/
theorem profiledOpenActiveRightFixedValue_hasReanchoredRows_of_shapeFreeProvenance
    (source : ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy
      hwin basis initialCode)
    (value : ProfiledOpenFixedRightPinnedValue A initialCode)
    (hprovenance :
      ProfiledOpenActiveRightFixedValueHasShapeFreeProvenance A strategy hwin
        basis initialCode source value) :
    ProfiledOpenFixedRightValueHasReanchoredRows A strategy hwin basis
      initialCode value := by
  rcases hprovenance with ⟨move, rfl⟩
  intro current hmember query hreachable
  let member : ProfiledOpenHiddenDescriptorRightCarrier A
      (profiledOpenActiveRightProjectedFamily A strategy hwin basis initialCode
        source) := ⟨current, hmember⟩
  let point := profiledOpenActiveRightProjectedPoint A strategy hwin basis
    initialCode source member
  let state : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode :=
    point.toOptionalControlled A strategy hwin basis initialCode
  refine ⟨{
    state := state
    member := member
    member_eq := rfl
    state_descriptor := ?_
    reachable := hreachable
    semantic := ?_ }⟩
  · exact profiledOpenActiveRightProjectedPoint_descriptor A strategy hwin
      basis initialCode source member
  · refine ⟨point.1.lane, point.1.active,
      profiledOpenActiveRightProjectedPoint_descriptor A strategy hwin basis
        initialCode source member, ?_⟩
    let table := ((point.1.lane.realization.coherentTable A).table
      |>.toClassified A point.1.lane.source)
    let hmove := profiledOpenActiveRightProjectedPoint_moveIdentity A strategy
      hwin basis initialCode source member
    refine ⟨hmove, ?_⟩
    rcases hreachable with ⟨word, hword⟩
    have hsemantic := move.2 word query.2 member
    unfold profiledOpenFixedRightQueryResponses
    rw [← hword]
    exact hsemantic

/-- In particular, the canonical projected right value chosen from a winning
strategy satisfies the re-anchored-row interface. -/
theorem profiledOpenActiveRightFixedValueOfWinning_hasReanchoredRows
    (source : ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy
      hwin basis initialCode) :
    ProfiledOpenFixedRightValueHasReanchoredRows A strategy hwin basis
      initialCode
      (profiledOpenActiveRightFixedValueOfWinning A strategy hwin basis
        initialCode source) :=
  profiledOpenActiveRightFixedValue_hasReanchoredRows_of_shapeFreeProvenance A
    strategy hwin basis initialCode source _
    (profiledOpenActiveRightFixedValueOfWinning_hasShapeFreeProvenance A
      strategy hwin basis initialCode source)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Left mirror: every advertised member is re-anchored at its literal
controlled source-fibre witness, independently of the optional lane shape of
the original anchor. -/
theorem profiledOpenActiveLeftFixedValue_hasReanchoredRows_of_shapeFreeProvenance
    (source : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy
      hwin basis initialCode)
    (value : ProfiledOpenFixedLeftPinnedValue A initialCode)
    (hprovenance :
      ProfiledOpenActiveLeftFixedValueHasShapeFreeProvenance A strategy hwin
        basis initialCode source value) :
    ProfiledOpenFixedLeftValueHasReanchoredRows A strategy hwin basis
      initialCode value := by
  rcases hprovenance with ⟨move, rfl⟩
  intro current hmember query hreachable
  let member : ProfiledOpenHiddenDescriptorLeftCarrier A
      (profiledOpenActiveLeftProjectedFamily A strategy hwin basis initialCode
        source) := ⟨current, hmember⟩
  let point := profiledOpenActiveLeftProjectedPoint A strategy hwin basis
    initialCode source member
  let state : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode :=
    point.toOptionalControlled A strategy hwin basis initialCode
  refine ⟨{
    state := state
    member := member
    member_eq := rfl
    state_descriptor := ?_
    reachable := hreachable
    semantic := ?_ }⟩
  · exact profiledOpenActiveLeftProjectedPoint_descriptor A strategy hwin
      basis initialCode source member
  · refine ⟨point.1.lane, point.1.active,
      profiledOpenActiveLeftProjectedPoint_descriptor A strategy hwin basis
        initialCode source member, ?_⟩
    let table := ((point.1.lane.realization.coherentTable A).table
      |>.toClassified A point.1.lane.source)
    let hmove := profiledOpenActiveLeftProjectedPoint_moveIdentity A strategy
      hwin basis initialCode source member
    refine ⟨hmove, ?_⟩
    rcases hreachable with ⟨word, hword⟩
    have hsemantic := move.2 word query.2 member
    unfold profiledOpenFixedLeftQueryResponses
    rw [← hword]
    exact hsemantic

/-- Canonical winning left value, at the general re-anchored-row interface. -/
theorem profiledOpenActiveLeftFixedValueOfWinning_hasReanchoredRows
    (source : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy
      hwin basis initialCode) :
    ProfiledOpenFixedLeftValueHasReanchoredRows A strategy hwin basis
      initialCode
      (profiledOpenActiveLeftFixedValueOfWinning A strategy hwin basis
        initialCode source) :=
  profiledOpenActiveLeftFixedValue_hasReanchoredRows_of_shapeFreeProvenance A
    strategy hwin basis initialCode source _
    (profiledOpenActiveLeftFixedValueOfWinning_hasShapeFreeProvenance A
      strategy hwin basis initialCode source)

/-! ## Canonical active-lane classes of a semantic representative -/

/-- Canonical active-right witness when an optional semantic point has a
right lane.  The witness is proof-side and contains the point's literal DPA
control. -/
noncomputable def profiledOpenActiveLaneRightPoint
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode)
    (hactive : ∃ lane : ProfiledOpenIndexedRightSemanticLane A strategy hwin
      basis (I := I), point.1.state.right = some lane) :
    ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy hwin basis
      initialCode :=
  let lane := Classical.choose hactive
  ((⟨point.1, lane, Classical.choose_spec hactive⟩), point.2)

/-- Canonical active-left witness. -/
noncomputable def profiledOpenActiveLaneLeftPoint
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode)
    (hactive : ∃ lane : ProfiledOpenIndexedLeftSemanticLane A strategy hwin
      basis (I := I), point.1.state.left = some lane) :
    ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy hwin basis
      initialCode :=
  let lane := Classical.choose hactive
  ((⟨point.1, lane, Classical.choose_spec hactive⟩), point.2)

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledOpenActiveLaneRightPoint_toOptionalControlled
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode)
    (hactive : ∃ lane : ProfiledOpenIndexedRightSemanticLane A strategy hwin
      basis (I := I), point.1.state.right = some lane) :
    (profiledOpenActiveLaneRightPoint A strategy hwin basis initialCode point
      hactive).toOptionalControlled A strategy hwin basis initialCode = point :=
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledOpenActiveLaneLeftPoint_toOptionalControlled
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode)
    (hactive : ∃ lane : ProfiledOpenIndexedLeftSemanticLane A strategy hwin
      basis (I := I), point.1.state.left = some lane) :
    (profiledOpenActiveLaneLeftPoint A strategy hwin basis initialCode point
      hactive).toOptionalControlled A strategy hwin basis initialCode = point :=
  rfl

/-- A right-family member rules out the inactive and left-only source cases.
This produces a proof-side lane witness; it is not a local test performed by
process one. -/
theorem profiledOpenOptionalControlled_rightActive_of_mem
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode)
    (hmember :
      profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
          basis initialCode point ∈
        (profiledOpenOptionalControlledFamilyOf A strategy hwin basis
          initialCode point).1) :
    ∃ lane : ProfiledOpenIndexedRightSemanticLane A strategy hwin basis
      (I := I), point.1.state.right = some lane := by
  classical
  cases hright : point.1.state.right with
  | some lane => exact ⟨lane, rfl⟩
  | none =>
      cases hleft : point.1.state.left with
      | none =>
          rw [profiledOpenOptionalControlledFamilyOf_eq_sink A strategy hwin
            basis initialCode point hright hleft] at hmember
          simpa [profiledOpenOptionalSinkFamilyCode] using hmember
      | some lane =>
          rw [profiledOpenOptionalControlledFamilyOf_eq_leftOnly A strategy
            hwin basis initialCode point lane hright hleft] at hmember
          have hempty := profiledOpenOptionalLeftOnlyFamilyCode_right A
            strategy hwin basis initialCode (fun _ ↦ point.2)
            (point.1.toLeftOnly A strategy hwin basis lane hright hleft)
          rw [hempty] at hmember
          simpa using hmember

/-- Left-family membership symmetrically produces an active-left witness. -/
theorem profiledOpenOptionalControlled_leftActive_of_mem
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode)
    (hmember :
      profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
          basis initialCode point ∈
        (profiledOpenOptionalControlledFamilyOf A strategy hwin basis
          initialCode point).2) :
    ∃ lane : ProfiledOpenIndexedLeftSemanticLane A strategy hwin basis
      (I := I), point.1.state.left = some lane := by
  classical
  cases hleft : point.1.state.left with
  | some lane => exact ⟨lane, rfl⟩
  | none =>
      cases hright : point.1.state.right with
      | none =>
          rw [profiledOpenOptionalControlledFamilyOf_eq_sink A strategy hwin
            basis initialCode point hright hleft] at hmember
          simpa [profiledOpenOptionalSinkFamilyCode] using hmember
      | some lane =>
          rw [profiledOpenOptionalControlledFamilyOf_eq_rightOnly A strategy
            hwin basis initialCode point lane hright hleft] at hmember
          have hempty := profiledOpenOptionalRightOnlyFamilyCode_left A
            strategy hwin basis initialCode (fun _ ↦ point.2)
            (point.1.toRightOnly A strategy hwin basis lane hright hleft)
          rw [hempty] at hmember
          simpa using hmember

/-- Projected process-one class of one semantic representative.  If the
right lane is inactive the coordinate is the harmless empty default. -/
noncomputable def profiledOpenActiveLaneRightClassOfPoint
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode) :
    ProfiledOpenActiveLaneSideClass A initialCode := by
  classical
  exact if hactive : ∃ lane : ProfiledOpenIndexedRightSemanticLane A
      strategy hwin basis (I := I), point.1.state.right = some lane then
    profiledOpenActiveRightProjectedClass A strategy hwin basis initialCode
      (profiledOpenActiveLaneRightPoint A strategy hwin basis initialCode point
        hactive)
  else ∅

/-- Process-two mirror. -/
noncomputable def profiledOpenActiveLaneLeftClassOfPoint
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode) :
    ProfiledOpenActiveLaneSideClass A initialCode := by
  classical
  exact if hactive : ∃ lane : ProfiledOpenIndexedLeftSemanticLane A
      strategy hwin basis (I := I), point.1.state.left = some lane then
    profiledOpenActiveLeftProjectedClass A strategy hwin basis initialCode
      (profiledOpenActiveLaneLeftPoint A strategy hwin basis initialCode point
        hactive)
  else ∅

/-! ## Canonical public tags from an attained semantic representative -/

/-- Assign a pair of projected active-lane classes to a descriptor/family
pair.  On the live fragment the point is an attained semantic
representative; outside it both coordinates use the harmless empty default.

The choice is proof-side.  The public tag contains only the two finite
projected descriptor images, never the chosen point or its optional shape. -/
noncomputable def profiledOpenActiveLaneClassOf
    (descriptor : ShapeFreeDescriptor A initialCode)
    (family : ShapeFreeFamily A initialCode) :
    ProfiledOpenActiveLaneSideClass A initialCode ×
      ProfiledOpenActiveLaneSideClass A initialCode := by
  classical
  exact if hlive : ProfiledOpenOptionalPointedSemanticLive A strategy hwin
      basis initialCode descriptor family then
    let point := Classical.choose hlive
    (profiledOpenActiveLaneRightClassOfPoint A strategy hwin basis initialCode
        point,
      profiledOpenActiveLaneLeftClassOfPoint A strategy hwin basis initialCode
        point)
  else (∅, ∅)

/-- The concrete sticky-tag invariant, definitionally the canonical generic
class-tag invariant consumed by the fixed-policy adapter. -/
abbrev ProfiledOpenActiveLaneClassTagInvariant :=
  ProfiledOpenShapeFreeClassTagInvariant A initialCode
    (profiledOpenActiveLaneClassOf A strategy hwin basis initialCode)

/-- At a live right-active candidate, the canonical tag comes with an
attained active-right controlled source whose literal descriptor is the
candidate's current descriptor.  Only this forward witness law is used. -/
theorem profiledOpenActiveLaneClassOf_rightAnchor
    (descriptor : ShapeFreeDescriptor A initialCode)
    (family : ShapeFreeFamily A initialCode)
    (hlive : ProfiledOpenOptionalPointedSemanticLive A strategy hwin basis
      initialCode descriptor family)
    (hmember : descriptor ∈ family.1) :
    ∃ source : ProfiledOpenIndexedActiveRightControlledSemanticPoint A
        strategy hwin basis initialCode,
      profiledOpenActiveRightControlledDescriptor A strategy hwin basis
          initialCode source = descriptor ∧
        profiledOpenActiveRightProjectedClass A strategy hwin basis initialCode
            source =
          (profiledOpenActiveLaneClassOf A strategy hwin basis initialCode
            descriptor family).1 := by
  let point := Classical.choose hlive
  have hpoint := Classical.choose_spec hlive
  have hmemberPoint :
      profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
          basis initialCode point ∈
        (profiledOpenOptionalControlledFamilyOf A strategy hwin basis
          initialCode point).1 := by
    rw [hpoint.1, hpoint.2]
    exact hmember
  let hactive := profiledOpenOptionalControlled_rightActive_of_mem A strategy
    hwin basis initialCode point hmemberPoint
  let source := profiledOpenActiveLaneRightPoint A strategy hwin basis
    initialCode point hactive
  refine ⟨source, ?_, ?_⟩
  · change
      profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis initialCode point = descriptor
    exact hpoint.1
  · unfold profiledOpenActiveLaneClassOf
    rw [dif_pos hlive]
    change
      profiledOpenActiveRightProjectedClass A strategy hwin basis initialCode
          source =
        profiledOpenActiveLaneRightClassOfPoint A strategy hwin basis
          initialCode point
    unfold profiledOpenActiveLaneRightClassOfPoint
    rw [dif_pos hactive]

/-- Left mirror of the attained-anchor law. -/
theorem profiledOpenActiveLaneClassOf_leftAnchor
    (descriptor : ShapeFreeDescriptor A initialCode)
    (family : ShapeFreeFamily A initialCode)
    (hlive : ProfiledOpenOptionalPointedSemanticLive A strategy hwin basis
      initialCode descriptor family)
    (hmember : descriptor ∈ family.2) :
    ∃ source : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A
        strategy hwin basis initialCode,
      profiledOpenActiveLeftControlledDescriptor A strategy hwin basis
          initialCode source = descriptor ∧
        profiledOpenActiveLeftProjectedClass A strategy hwin basis initialCode
            source =
          (profiledOpenActiveLaneClassOf A strategy hwin basis initialCode
            descriptor family).2 := by
  let point := Classical.choose hlive
  have hpoint := Classical.choose_spec hlive
  have hmemberPoint :
      profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
          basis initialCode point ∈
        (profiledOpenOptionalControlledFamilyOf A strategy hwin basis
          initialCode point).2 := by
    rw [hpoint.1, hpoint.2]
    exact hmember
  let hactive := profiledOpenOptionalControlled_leftActive_of_mem A strategy
    hwin basis initialCode point hmemberPoint
  let source := profiledOpenActiveLaneLeftPoint A strategy hwin basis
    initialCode point hactive
  refine ⟨source, ?_, ?_⟩
  · change
      profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis initialCode point = descriptor
    exact hpoint.1
  · unfold profiledOpenActiveLaneClassOf
    rw [dif_pos hlive]
    change
      profiledOpenActiveLeftProjectedClass A strategy hwin basis initialCode
          source =
        profiledOpenActiveLaneLeftClassOfPoint A strategy hwin basis
          initialCode point
    unfold profiledOpenActiveLaneLeftClassOfPoint
    rw [dif_pos hactive]

/-! ## Candidate-wide selection by projected active-lane class -/

/-- Candidate type at the concrete pair of active-lane class alphabets. -/
abbrev ProfiledOpenActiveLaneTaggedCandidate :=
  RelationalFamilyCandidate
    (SidewiseTaggedFamily
      (ProfiledOpenActiveLaneSideClass A initialCode)
      (ProfiledOpenActiveLaneSideClass A initialCode)
      (ShapeFreeFamily A initialCode))
    (ShapeFreeDescriptor A initialCode)

/-- A right class is attained when some live right-active candidate supplies
an exact controlled anchor in that projected class. -/
def ProfiledOpenActiveLaneRightClassAttained
    (candidates : Finset (ProfiledOpenActiveLaneTaggedCandidate A initialCode))
    (sideClass : ProfiledOpenActiveLaneSideClass A initialCode) : Prop :=
  ∃ source : ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy
      hwin basis initialCode,
    profiledOpenActiveRightProjectedClass A strategy hwin basis initialCode
        source = sideClass ∧
      ∃ candidate ∈ candidates,
        ProfiledOpenFixedSidewiseSemanticLive A strategy hwin basis initialCode
            (ProfiledOpenActiveLaneClassTagInvariant A strategy hwin basis
              initialCode)
            candidate.2 candidate.1 ∧
          candidate.2 ∈ candidate.1.2.1 ∧
          profiledOpenActiveRightControlledDescriptor A strategy hwin basis
              initialCode source = candidate.2

/-- Left attained class. -/
def ProfiledOpenActiveLaneLeftClassAttained
    (candidates : Finset (ProfiledOpenActiveLaneTaggedCandidate A initialCode))
    (sideClass : ProfiledOpenActiveLaneSideClass A initialCode) : Prop :=
  ∃ source : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy
      hwin basis initialCode,
    profiledOpenActiveLeftProjectedClass A strategy hwin basis initialCode
        source = sideClass ∧
      ∃ candidate ∈ candidates,
        ProfiledOpenFixedSidewiseSemanticLive A strategy hwin basis initialCode
            (ProfiledOpenActiveLaneClassTagInvariant A strategy hwin basis
              initialCode)
            candidate.2 candidate.1 ∧
          candidate.2 ∈ candidate.1.2.2 ∧
          profiledOpenActiveLeftControlledDescriptor A strategy hwin basis
              initialCode source = candidate.2

/-- The right fixed value selected at an attained projected class. -/
noncomputable def profiledOpenActiveLaneRightValueForClass
    (candidates : Finset (ProfiledOpenActiveLaneTaggedCandidate A initialCode))
    (sideClass : ProfiledOpenActiveLaneSideClass A initialCode) :
    ProfiledOpenFixedRightPinnedValue A initialCode := by
  classical
  exact if hattained : ProfiledOpenActiveLaneRightClassAttained A strategy hwin
      basis initialCode candidates sideClass then
    profiledOpenActiveRightFixedValueOfWinning A strategy hwin basis
      initialCode (Classical.choose hattained)
  else
    profiledOpenFixedDefaultRightPinnedValue A initialCode strategy hwin basis

/-- Left selector. -/
noncomputable def profiledOpenActiveLaneLeftValueForClass
    (candidates : Finset (ProfiledOpenActiveLaneTaggedCandidate A initialCode))
    (sideClass : ProfiledOpenActiveLaneSideClass A initialCode) :
    ProfiledOpenFixedLeftPinnedValue A initialCode := by
  classical
  exact if hattained : ProfiledOpenActiveLaneLeftClassAttained A strategy hwin
      basis initialCode candidates sideClass then
    profiledOpenActiveLeftFixedValueOfWinning A strategy hwin basis initialCode
      (Classical.choose hattained)
  else
    profiledOpenFixedDefaultLeftPinnedValue A initialCode strategy hwin basis

/-- The complete symmetric bank.  Each process indexes only its own finite
projected-class coordinate. -/
noncomputable def profiledOpenActiveLaneSidewiseBank
    (candidates : Finset
      (ProfiledOpenActiveLaneTaggedCandidate A initialCode)) :
    ProfiledOpenFixedSidewisePinnedBank A initialCode
      (ProfiledOpenActiveLaneSideClass A initialCode)
      (ProfiledOpenActiveLaneSideClass A initialCode) :=
  (profiledOpenActiveLaneRightValueForClass A strategy hwin basis initialCode
      candidates,
    profiledOpenActiveLaneLeftValueForClass A strategy hwin basis initialCode
      candidates)

/-- Every live right-active candidate is covered by the value selected at
its canonical process-one tag.  The proof uses only the current descriptor
of an attained anchor; it never reflects equality of projected images. -/
theorem profiledOpenActiveLaneRightValueForClass_covers
    (candidates : Finset (ProfiledOpenActiveLaneTaggedCandidate A initialCode))
    (candidate : ProfiledOpenActiveLaneTaggedCandidate A initialCode)
    (hcandidate : candidate ∈ candidates)
    (hlive : ProfiledOpenFixedSidewiseSemanticLive A strategy hwin basis
      initialCode
      (ProfiledOpenActiveLaneClassTagInvariant A strategy hwin basis
        initialCode)
      candidate.2 candidate.1)
    (hmember : candidate.2 ∈ candidate.1.2.1) :
    candidate.2 ∈
      (profiledOpenActiveLaneRightValueForClass A strategy hwin basis
        initialCode candidates candidate.1.1.1).1.1 := by
  rcases profiledOpenActiveLaneClassOf_rightAnchor A strategy hwin basis
      initialCode candidate.2 candidate.1.2 hlive.1 hmember with
    ⟨source, hdescriptor, hsourceClass⟩
  have htag : candidate.1.1 =
      profiledOpenActiveLaneClassOf A strategy hwin basis initialCode
        candidate.2 candidate.1.2 := hlive.2
  have hsourceTag :
      profiledOpenActiveRightProjectedClass A strategy hwin basis initialCode
          source = candidate.1.1.1 :=
    hsourceClass.trans (congrArg Prod.fst htag).symm
  let hattained : ProfiledOpenActiveLaneRightClassAttained A strategy hwin
      basis initialCode candidates candidate.1.1.1 :=
    ⟨source, hsourceTag, candidate, hcandidate, hlive, hmember, hdescriptor⟩
  unfold profiledOpenActiveLaneRightValueForClass
  rw [dif_pos hattained,
    profiledOpenActiveRightFixedValueOfWinning_family]
  change candidate.2 ∈
    profiledOpenActiveRightProjectedClass A strategy hwin basis initialCode
      (Classical.choose hattained)
  rw [(Classical.choose_spec hattained).1]
  have hcurrent :=
    profiledOpenActiveRightControlledDescriptor_mem_projectedClass A strategy
      hwin basis initialCode source
  rw [hdescriptor, hsourceTag] at hcurrent
  exact hcurrent

/-- Left coverage mirror. -/
theorem profiledOpenActiveLaneLeftValueForClass_covers
    (candidates : Finset (ProfiledOpenActiveLaneTaggedCandidate A initialCode))
    (candidate : ProfiledOpenActiveLaneTaggedCandidate A initialCode)
    (hcandidate : candidate ∈ candidates)
    (hlive : ProfiledOpenFixedSidewiseSemanticLive A strategy hwin basis
      initialCode
      (ProfiledOpenActiveLaneClassTagInvariant A strategy hwin basis
        initialCode)
      candidate.2 candidate.1)
    (hmember : candidate.2 ∈ candidate.1.2.2) :
    candidate.2 ∈
      (profiledOpenActiveLaneLeftValueForClass A strategy hwin basis
        initialCode candidates candidate.1.1.2).1.2 := by
  rcases profiledOpenActiveLaneClassOf_leftAnchor A strategy hwin basis
      initialCode candidate.2 candidate.1.2 hlive.1 hmember with
    ⟨source, hdescriptor, hsourceClass⟩
  have htag : candidate.1.1 =
      profiledOpenActiveLaneClassOf A strategy hwin basis initialCode
        candidate.2 candidate.1.2 := hlive.2
  have hsourceTag :
      profiledOpenActiveLeftProjectedClass A strategy hwin basis initialCode
          source = candidate.1.1.2 :=
    hsourceClass.trans (congrArg Prod.snd htag).symm
  let hattained : ProfiledOpenActiveLaneLeftClassAttained A strategy hwin
      basis initialCode candidates candidate.1.1.2 :=
    ⟨source, hsourceTag, candidate, hcandidate, hlive, hmember, hdescriptor⟩
  unfold profiledOpenActiveLaneLeftValueForClass
  rw [dif_pos hattained,
    profiledOpenActiveLeftFixedValueOfWinning_family]
  change candidate.2 ∈
    profiledOpenActiveLeftProjectedClass A strategy hwin basis initialCode
      (Classical.choose hattained)
  rw [(Classical.choose_spec hattained).1]
  have hcurrent :=
    profiledOpenActiveLeftControlledDescriptor_mem_projectedClass A strategy
      hwin basis initialCode source
  rw [hdescriptor, hsourceTag] at hcurrent
  exact hcurrent

/-- One live right member supplies the attained-class certificate used by
both coverage and provenance. -/
theorem profiledOpenActiveLaneRightClassAttained_of_live_mem
    (candidates : Finset (ProfiledOpenActiveLaneTaggedCandidate A initialCode))
    (candidate : ProfiledOpenActiveLaneTaggedCandidate A initialCode)
    (hcandidate : candidate ∈ candidates)
    (hlive : ProfiledOpenFixedSidewiseSemanticLive A strategy hwin basis
      initialCode
      (ProfiledOpenActiveLaneClassTagInvariant A strategy hwin basis
        initialCode)
      candidate.2 candidate.1)
    (hmember : candidate.2 ∈ candidate.1.2.1) :
    ProfiledOpenActiveLaneRightClassAttained A strategy hwin basis initialCode
      candidates candidate.1.1.1 := by
  rcases profiledOpenActiveLaneClassOf_rightAnchor A strategy hwin basis
      initialCode candidate.2 candidate.1.2 hlive.1 hmember with
    ⟨source, hdescriptor, hsourceClass⟩
  have htag : candidate.1.1 =
      profiledOpenActiveLaneClassOf A strategy hwin basis initialCode
        candidate.2 candidate.1.2 := hlive.2
  exact ⟨source,
    hsourceClass.trans (congrArg Prod.fst htag).symm,
    candidate, hcandidate, hlive, hmember, hdescriptor⟩

/-- Left attained certificate. -/
theorem profiledOpenActiveLaneLeftClassAttained_of_live_mem
    (candidates : Finset (ProfiledOpenActiveLaneTaggedCandidate A initialCode))
    (candidate : ProfiledOpenActiveLaneTaggedCandidate A initialCode)
    (hcandidate : candidate ∈ candidates)
    (hlive : ProfiledOpenFixedSidewiseSemanticLive A strategy hwin basis
      initialCode
      (ProfiledOpenActiveLaneClassTagInvariant A strategy hwin basis
        initialCode)
      candidate.2 candidate.1)
    (hmember : candidate.2 ∈ candidate.1.2.2) :
    ProfiledOpenActiveLaneLeftClassAttained A strategy hwin basis initialCode
      candidates candidate.1.1.2 := by
  rcases profiledOpenActiveLaneClassOf_leftAnchor A strategy hwin basis
      initialCode candidate.2 candidate.1.2 hlive.1 hmember with
    ⟨source, hdescriptor, hsourceClass⟩
  have htag : candidate.1.1 =
      profiledOpenActiveLaneClassOf A strategy hwin basis initialCode
        candidate.2 candidate.1.2 := hlive.2
  exact ⟨source,
    hsourceClass.trans (congrArg Prod.snd htag).symm,
    candidate, hcandidate, hlive, hmember, hdescriptor⟩

/-- Every attained selected right value retains exact per-member
re-anchoring rows. -/
theorem profiledOpenActiveLaneRightValueForClass_hasReanchoredRows
    (candidates : Finset (ProfiledOpenActiveLaneTaggedCandidate A initialCode))
    (sideClass : ProfiledOpenActiveLaneSideClass A initialCode)
    (hattained : ProfiledOpenActiveLaneRightClassAttained A strategy hwin basis
      initialCode candidates sideClass) :
    ProfiledOpenFixedRightValueHasReanchoredRows A strategy hwin basis
      initialCode
      (profiledOpenActiveLaneRightValueForClass A strategy hwin basis
        initialCode candidates sideClass) := by
  unfold profiledOpenActiveLaneRightValueForClass
  rw [dif_pos hattained]
  exact profiledOpenActiveRightFixedValueOfWinning_hasReanchoredRows A strategy
    hwin basis initialCode (Classical.choose hattained)

/-- Left retained-row law. -/
theorem profiledOpenActiveLaneLeftValueForClass_hasReanchoredRows
    (candidates : Finset (ProfiledOpenActiveLaneTaggedCandidate A initialCode))
    (sideClass : ProfiledOpenActiveLaneSideClass A initialCode)
    (hattained : ProfiledOpenActiveLaneLeftClassAttained A strategy hwin basis
      initialCode candidates sideClass) :
    ProfiledOpenFixedLeftValueHasReanchoredRows A strategy hwin basis
      initialCode
      (profiledOpenActiveLaneLeftValueForClass A strategy hwin basis
        initialCode candidates sideClass) := by
  unfold profiledOpenActiveLaneLeftValueForClass
  rw [dif_pos hattained]
  exact profiledOpenActiveLeftFixedValueOfWinning_hasReanchoredRows A strategy
    hwin basis initialCode (Classical.choose hattained)

/-! ## Re-anchored common-bank theorem -/

/-- The shape-free bank is simultaneously re-anchored-valid for every live
candidate.  Right and left values may use different proof-side anchors, but
each selected value is uniform on its public projected class and carries
literal per-descriptor semantic rows. -/
theorem profiledOpenActiveLaneSidewiseBank_commonMove
    (candidates : Finset
      (ProfiledOpenActiveLaneTaggedCandidate A initialCode)) :
    RelationalCandidateCommonMove
      (ProfiledOpenFixedSidewiseSemanticLive A strategy hwin basis initialCode
        (ProfiledOpenActiveLaneClassTagInvariant A strategy hwin basis
          initialCode))
      (ProfiledOpenFixedSidewiseReanchoredCandidateValid A strategy hwin basis
        initialCode)
      candidates
      (profiledOpenActiveLaneSidewiseBank A strategy hwin basis initialCode
        candidates) := by
  intro candidate hcandidate hlive
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro hmember
    exact profiledOpenActiveLaneRightValueForClass_covers A strategy hwin basis
      initialCode candidates candidate hcandidate hlive hmember
  · intro hmember
    exact profiledOpenActiveLaneLeftValueForClass_covers A strategy hwin basis
      initialCode candidates candidate hcandidate hlive hmember
  · intro hmember
    let hattained :=
      profiledOpenActiveLaneRightClassAttained_of_live_mem A strategy hwin
        basis initialCode candidates candidate hcandidate hlive hmember
    exact profiledOpenActiveLaneRightValueForClass_hasReanchoredRows A strategy
      hwin basis initialCode candidates candidate.1.1.1 hattained
  · intro hmember
    let hattained :=
      profiledOpenActiveLaneLeftClassAttained_of_live_mem A strategy hwin basis
        initialCode candidates candidate hcandidate hlive hmember
    exact profiledOpenActiveLaneLeftValueForClass_hasReanchoredRows A strategy
      hwin basis initialCode candidates candidate.1.1.2 hattained

/-- Hence the exact common-bank premise consumed by the fixed-policy
shape-free table is unconditional at the two finite projected-class
alphabets. -/
theorem profiledOpenActiveLane_commonMoveExists :
    RelationalCandidateCommonMoveExists
      (Family := SidewiseTaggedFamily
        (ProfiledOpenActiveLaneSideClass A initialCode)
        (ProfiledOpenActiveLaneSideClass A initialCode)
        (ShapeFreeFamily A initialCode))
      (Descriptor := ShapeFreeDescriptor A initialCode)
      (Move := ProfiledOpenFixedSidewisePinnedBank A initialCode
        (ProfiledOpenActiveLaneSideClass A initialCode)
        (ProfiledOpenActiveLaneSideClass A initialCode))
      (ProfiledOpenFixedSidewiseSemanticLive A strategy hwin basis initialCode
        (ProfiledOpenActiveLaneClassTagInvariant A strategy hwin basis
          initialCode))
      (ProfiledOpenFixedSidewiseReanchoredCandidateValid A strategy hwin basis
        initialCode) := by
  intro candidates _hactive
  exact ⟨profiledOpenActiveLaneSidewiseBank A strategy hwin basis initialCode
      candidates,
    profiledOpenActiveLaneSidewiseBank_commonMove A strategy hwin basis
      initialCode candidates⟩

/-! ## One-arrow fixed-policy table -/

/-- One explicit semantic initial state and one recurrent rational-policy
root now suffice to construct the complete shape-free fixed-policy candidate
table.  All class tagging, initial-candidate data, common-bank validity, and
exact re-anchored successor coverage are discharged above. -/
theorem exists_profiledOpenActiveLaneFixedPolicyRelationalCandidateTable
    [Inhabited I]
    {initialState : PairedProfiledTreeState A}
    (policy :
      (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)
    (state : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode)
    (initialRoot : ProfiledFixedPolicyRoot A policy)
    (hinitialRoot : initialRoot.state A policy = policy.run []) :
    ∃ package : FixedPolicyRelationalCandidateTablePackage A policy
        (ProfiledOpenFixedSidewiseSemanticLive A strategy hwin basis
          initialCode
          (ProfiledOpenShapeFreeClassTagInvariant A initialCode
            (profiledOpenActiveLaneClassOf A strategy hwin basis initialCode)))
        (ProfiledOpenFixedSidewiseReanchoredCandidateValid A strategy hwin
          basis initialCode)
        (ProfiledOpenFixedSidewiseReanchoredExactEdge A strategy hwin basis
          initialCode
          (ProfiledOpenShapeFreeClassTagInvariant A initialCode
            (profiledOpenActiveLaneClassOf A strategy hwin basis initialCode))
          (profiledOpenShapeFreeClassTargetTag A initialCode
            (profiledOpenActiveLaneClassOf A strategy hwin basis initialCode)))
        (ProfiledOpenFixedSidewiseControlStep A initialCode)
        initialRoot
        (profiledOpenShapeFreeInitialCandidateSet A strategy hwin basis
          initialCode
          (profiledOpenActiveLaneClassOf A strategy hwin basis initialCode)
          state)
        (profiledOpenShapeFreeInitialCandidate A strategy hwin basis
          initialCode
          (profiledOpenActiveLaneClassOf A strategy hwin basis initialCode)
          state),
      ∀ query : Nat →
          ProfiledOpenFixedSidewiseReachablePointedQuery A initialCode,
        Nonempty (RelationalFamilyExactThread
          (ProfiledOpenFixedSidewiseReanchoredExactEdge A strategy hwin basis
            initialCode
            (ProfiledOpenShapeFreeClassTagInvariant A initialCode
              (profiledOpenActiveLaneClassOf A strategy hwin basis
                initialCode))
            (profiledOpenShapeFreeClassTargetTag A initialCode
              (profiledOpenActiveLaneClassOf A strategy hwin basis
                initialCode)))
          (ProfiledOpenFixedSidewiseControlStep A initialCode)
          (profiledOpenShapeFreeInitialCandidateSet A strategy hwin basis
            initialCode
            (profiledOpenActiveLaneClassOf A strategy hwin basis initialCode)
            state)
          (package.branch.moveAt query) query) := by
  exact
    exists_profiledOpenShapeFreeFixedPolicyRelationalCandidateTable_of_initialState
      A strategy hwin basis initialCode policy
      (profiledOpenActiveLaneClassOf A strategy hwin basis initialCode)
      (profiledOpenActiveLane_commonMoveExists A strategy hwin basis
        initialCode)
      state initialRoot hinitialRoot

end

end DetParityAutomaton

end DistributedSynthesis
