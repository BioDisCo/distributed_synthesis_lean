/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenShapeFreeCandidateCommonBank
import DistributedSynthesis.Formalizations.Lemma.LemSourceAwareRelationalCandidateAdapter

/-!
# Context-faithful shape-free tags

The canonical class tag used by the first shape-free table chooses one live
semantic representative of a public descriptor/family pair.  That is safe as
a finite name, but it does not by itself say that a different semantic point
with the same public pair has the same projected class.  In particular, this
cannot be justified by saying that only one hidden bit was lost: a permanently
unavailable bit must either remain as finite set-valued uncertainty or be
proved irrelevant by an explicit semantic law.

This file makes that boundary exact.  First, the canonical tag is pointwise
faithful iff projected classes are functional on public descriptor/family
fibres.  Thus a same-public-pair class collision is a kernel-checked
fail-fast refutation of the canonical-representative argument.

Second, we give the minimal positive repair.  Tags are witnessed by an actual
semantic point, and the exact edge receives the literal source family and
tags its literal semantic child.  The witness is proof-only; the runtime state
still carries only a finite pair of projected classes.  No orientation,
optional lane shape, strict-leader flag, or hidden bit is exposed.
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

private abbrev ContextDescriptor :=
  ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode

private abbrev ContextFamily :=
  ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I) initialCode

private abbrev ContextClass :=
  ProfiledOpenActiveLaneSideClass A initialCode

private abbrev ContextTaggedFamily :=
  SidewiseTaggedFamily (ContextClass A initialCode)
    (ContextClass A initialCode) (ContextFamily A initialCode)

private abbrev ContextCandidate :=
  RelationalFamilyCandidate (ContextTaggedFamily A initialCode)
    (ContextDescriptor A initialCode)

private abbrev ContextBank :=
  ProfiledOpenFixedSidewisePinnedBank A initialCode
    (ContextClass A initialCode) (ContextClass A initialCode)

private abbrev ContextQuery :=
  ProfiledOpenFixedSidewiseReachablePointedQuery A initialCode

private abbrev ContextPoint :=
  ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin basis
    initialCode

/-! ## Exact audit of the canonical representative -/

/-- The two public projected classes of one concrete semantic point. -/
noncomputable def profiledOpenActiveLaneClassPairOfPoint
    (point : ContextPoint A strategy hwin basis initialCode) :
    ContextClass A initialCode × ContextClass A initialCode :=
  (profiledOpenActiveLaneRightClassOfPoint A strategy hwin basis initialCode
      point,
    profiledOpenActiveLaneLeftClassOfPoint A strategy hwin basis initialCode
      point)

/-- The missing semantic law behind an arbitrary representative: within one
public descriptor/family fibre, the projected class pair is unique. -/
def ProfiledOpenActiveLanePublicClassFunctional : Prop :=
  ∀ left right : ContextPoint A strategy hwin basis initialCode,
    profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis initialCode left =
      profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis initialCode right →
    profiledOpenOptionalControlledFamilyOf A strategy hwin basis initialCode
        left =
      profiledOpenOptionalControlledFamilyOf A strategy hwin basis initialCode
        right →
    profiledOpenActiveLaneClassPairOfPoint A strategy hwin basis initialCode
        left =
      profiledOpenActiveLaneClassPairOfPoint A strategy hwin basis initialCode
        right

/-- Pointwise faithfulness of the existing canonical choice. -/
def ProfiledOpenActiveLaneCanonicalClassFaithful : Prop :=
  ∀ point : ContextPoint A strategy hwin basis initialCode,
    profiledOpenActiveLaneClassOf A strategy hwin basis initialCode
        (profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy
          hwin basis initialCode point)
        (profiledOpenOptionalControlledFamilyOf A strategy hwin basis
          initialCode point) =
      profiledOpenActiveLaneClassPairOfPoint A strategy hwin basis initialCode
        point

/-- The canonical representative is faithful exactly when public fibres have
unique projected classes.  No converse from class equality to view equality
is used. -/
theorem profiledOpenActiveLaneCanonicalClassFaithful_iff_functional :
    ProfiledOpenActiveLaneCanonicalClassFaithful A strategy hwin basis
        initialCode ↔
      ProfiledOpenActiveLanePublicClassFunctional A strategy hwin basis
        initialCode := by
  constructor
  · intro hfaithful left right hdescriptor hfamily
    rw [← hfaithful left, ← hfaithful right, hdescriptor, hfamily]
  · intro hfunctional point
    let descriptor :=
      profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis initialCode point
    let family :=
      profiledOpenOptionalControlledFamilyOf A strategy hwin basis initialCode
        point
    have hlive : ProfiledOpenOptionalPointedSemanticLive A strategy hwin basis
        initialCode descriptor family := ⟨point, rfl, rfl⟩
    let chosen := Classical.choose hlive
    have hchosen := Classical.choose_spec hlive
    unfold profiledOpenActiveLaneClassOf
    rw [dif_pos hlive]
    exact hfunctional chosen point hchosen.1 hchosen.2

/-- A concrete same-public-pair class collision.  Such a pair may differ only
in information hidden from the public descriptor/family interface. -/
def ProfiledOpenActiveLanePublicClassCollision : Prop :=
  ∃ left right : ContextPoint A strategy hwin basis initialCode,
    profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis initialCode left =
      profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis initialCode right ∧
    profiledOpenOptionalControlledFamilyOf A strategy hwin basis initialCode
        left =
      profiledOpenOptionalControlledFamilyOf A strategy hwin basis initialCode
        right ∧
    profiledOpenActiveLaneClassPairOfPoint A strategy hwin basis initialCode
        left ≠
      profiledOpenActiveLaneClassPairOfPoint A strategy hwin basis initialCode
        right

/-- Fail fast: one contextual collision invalidates pointwise use of the
canonical target tag. -/
theorem not_profiledOpenActiveLaneCanonicalClassFaithful_of_collision
    (hcollision : ProfiledOpenActiveLanePublicClassCollision A strategy hwin
      basis initialCode) :
    ¬ ProfiledOpenActiveLaneCanonicalClassFaithful A strategy hwin basis
      initialCode := by
  rw [profiledOpenActiveLaneCanonicalClassFaithful_iff_functional]
  rintro hfunctional
  rcases hcollision with ⟨left, right, hdescriptor, hfamily, hne⟩
  exact hne (hfunctional left right hdescriptor hfamily)

/-! ## Witness-carrying source-aware repair -/

/-- A finite public tag is justified by one actual semantic point with the
advertised descriptor and family.  The point is an erased proof witness. -/
def ProfiledOpenActiveLaneWitnessedTagInvariant
    (descriptor : ContextDescriptor A initialCode)
    (taggedFamily : ContextTaggedFamily A initialCode) : Prop :=
  ∃ point : ContextPoint A strategy hwin basis initialCode,
    profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis initialCode point = descriptor ∧
    profiledOpenOptionalControlledFamilyOf A strategy hwin basis initialCode
        point = taggedFamily.2 ∧
    taggedFamily.1 =
      profiledOpenActiveLaneClassPairOfPoint A strategy hwin basis initialCode
        point

/-- The witnessed invariant implies ordinary pointed semantic liveness. -/
theorem profiledOpenActiveLaneWitnessedTagInvariant_live
    {descriptor : ContextDescriptor A initialCode}
    {taggedFamily : ContextTaggedFamily A initialCode}
    (hwitnessed : ProfiledOpenActiveLaneWitnessedTagInvariant A strategy hwin
      basis initialCode descriptor taggedFamily) :
    ProfiledOpenOptionalPointedSemanticLive A strategy hwin basis initialCode
      descriptor taggedFamily.2 := by
  rcases hwitnessed with ⟨point, hdescriptor, hfamily, _htag⟩
  exact ⟨point, hdescriptor, hfamily⟩

/-- Source-family-aware re-anchored edge whose target tag is the projected
class of its literal semantic child.  Unlike the old `targetTag` interface,
this relation has enough context to retain provenance without a fibre
functionality assumption. -/
def ProfiledOpenFixedSidewiseWitnessedReanchoredExactEdge
    (sourceFamily : ContextTaggedFamily A initialCode)
    (source : ContextDescriptor A initialCode)
    (bank : ContextBank A initialCode)
    (query : ContextQuery A initialCode)
    (targetFamily : ContextTaggedFamily A initialCode)
    (target : ContextDescriptor A initialCode) : Prop :=
  ∃ sourceState stepState,
    profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis initialCode sourceState = source ∧
    profiledOpenOptionalControlledFamilyOf A strategy hwin basis initialCode
        sourceState = sourceFamily.2 ∧
    sourceFamily.1 =
      profiledOpenActiveLaneClassPairOfPoint A strategy hwin basis initialCode
        sourceState ∧
    ProfiledOpenFixedSidewiseReanchoredCandidateValid A strategy hwin basis
        initialCode source sourceFamily bank ∧
    ProfiledOpenFixedSidewiseReanchoredStep A strategy hwin basis initialCode
        sourceState sourceFamily bank query.1 stepState ∧
    profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis initialCode stepState = source ∧
    profiledOpenOptionalControlledFamilyOf A strategy hwin basis initialCode
        (profiledOpenFixedSidewiseSemanticNext A strategy hwin basis
          initialCode stepState query.1) = targetFamily.2 ∧
    profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis initialCode
        (profiledOpenFixedSidewiseSemanticNext A strategy hwin basis
          initialCode stepState query.1) = target ∧
    targetFamily.1 =
      profiledOpenActiveLaneClassPairOfPoint A strategy hwin basis initialCode
        (profiledOpenFixedSidewiseSemanticNext A strategy hwin basis
          initialCode stepState query.1)

/-- The contextual edge has complete source-aware live-successor coverage.
The source witness supplied by the public tag is re-anchored, and the literal
child supplies the next tag witness. -/
theorem profiledOpenFixedSidewiseWitnessedReanchored_liveSuccessorCoverage :
    EncodedSourceAwareRelationalCandidateLiveSuccessorCoverage
      (ProfiledOpenFixedSidewiseSemanticLive A strategy hwin basis initialCode
        (ProfiledOpenActiveLaneWitnessedTagInvariant A strategy hwin basis
          initialCode))
      (ProfiledOpenFixedSidewiseReanchoredCandidateValid A strategy hwin basis
        initialCode)
      (ProfiledOpenFixedSidewiseWitnessedReanchoredExactEdge A strategy hwin
        basis initialCode)
      (ProfiledOpenFixedSidewiseControlStep A initialCode) := by
  intro source bank query hlive hvalid
  rcases hlive.2 with
    ⟨sourceState, hsource, hsourceFamily, hsourceTag⟩
  have hvalidState :
      ProfiledOpenFixedSidewiseReanchoredCandidateValid A strategy hwin basis
        initialCode
        (profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy
          hwin basis initialCode sourceState) source.1 bank := by
    simpa only [hsource] using hvalid
  obtain ⟨stepState, hstep, hstepDescriptor⟩ :=
    exists_profiledOpenFixedSidewiseReanchoredStep A strategy hwin basis
      initialCode sourceState source.1 bank query hvalidState
  have hstepSource :
      profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
          basis initialCode stepState = source.2 :=
    hstepDescriptor.trans hsource
  let child := profiledOpenFixedSidewiseSemanticNext A strategy hwin basis
    initialCode stepState query.1
  let target : ContextDescriptor A initialCode :=
    profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
      basis initialCode child
  let family : ContextFamily A initialCode :=
    profiledOpenOptionalControlledFamilyOf A strategy hwin basis initialCode
      child
  let targetFamily : ContextTaggedFamily A initialCode :=
    (profiledOpenActiveLaneClassPairOfPoint A strategy hwin basis initialCode
      child, family)
  refine ⟨(targetFamily, target), ?_, ?_, ?_⟩
  · exact ⟨sourceState, stepState, hsource, hsourceFamily, hsourceTag,
      hvalid, hstep, hstepSource, rfl, rfl, rfl⟩
  · change target.control =
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).step
        source.2.control target.code
    rw [← hstepSource]
    exact profiledOpenIndexedOptionalControlledSemanticNext_control A strategy
      hwin basis initialCode stepState query.1.2
  · constructor
    · exact ⟨child, rfl, rfl⟩
    · exact ⟨child, rfl, rfl, rfl⟩

/-- The generic family-in-descriptor adapter turns the witnessed contextual
edge into the ordinary fixed-table coverage interface.  The additional
descriptor component is finite public provenance, not a hidden-bit guess. -/
theorem
    profiledOpenFixedSidewiseWitnessedReanchored_encodedLiveSuccessorCoverage :
    RelationalCandidateLiveSuccessorCoverage
      (SourceAwareRelationalLive
        (ProfiledOpenFixedSidewiseSemanticLive A strategy hwin basis
          initialCode
          (ProfiledOpenActiveLaneWitnessedTagInvariant A strategy hwin basis
            initialCode)))
      (SourceAwareRelationalCandidateValid
        (ProfiledOpenFixedSidewiseReanchoredCandidateValid A strategy hwin
          basis initialCode))
      (sourceAwareRelationalExactEdge
        (ProfiledOpenFixedSidewiseWitnessedReanchoredExactEdge A strategy hwin
          basis initialCode))
      (sourceAwareRelationalControlStep
        (ProfiledOpenFixedSidewiseControlStep A initialCode)) := by
  exact relationalCandidateLiveSuccessorCoverage_sourceAware
    (ProfiledOpenFixedSidewiseSemanticLive A strategy hwin basis initialCode
      (ProfiledOpenActiveLaneWitnessedTagInvariant A strategy hwin basis
        initialCode))
    (ProfiledOpenFixedSidewiseReanchoredCandidateValid A strategy hwin basis
      initialCode)
    (ProfiledOpenFixedSidewiseWitnessedReanchoredExactEdge A strategy hwin
      basis initialCode)
    (ProfiledOpenFixedSidewiseControlStep A initialCode)
    (profiledOpenFixedSidewiseWitnessedReanchored_liveSuccessorCoverage A
      strategy hwin basis initialCode)

end

end DetParityAutomaton

end DistributedSynthesis
