/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenShapeFreeBankLocalConsumption
import DistributedSynthesis.Formalizations.Lemma.LemSourceAwareRelationalFamilySaturation

/-!
# Propagating shape-free receipt coherence

The relational candidate table carries the *global* saturation of every exact
successor.  A process-local receipt need not carry that entire set: successors
which produce different local receipts must be separated.  This distinction
is essential because re-anchoring deliberately saturates the unobserved
opposite lane.

This file states the weakest pairwise law for one such finite local filter and
proves that it is exactly the law needed to preserve the receipt-coherence
predicate of `LemPairedProfiledOpenShapeFreeBankLocalConsumption`.

The filter is a predicate on the already finite target-candidate type.  Hence
the resulting local receipt is finite and contains no semantic witness,
leader, orientation, lane, optional shape, DPA control, or hidden bit.  All
anchors below remain proof-only.

The concrete model still has to show that the filter selected by one
observable local transition satisfies the pairwise law.  The unfiltered
relational saturation does not supply this automatically: an exact edge may
re-anchor one active lane inside a shape-saturated fibre, and its arbitrary
opposite lane may create locally different successors after reversal.
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

private abbrev ReceiptDescriptor :=
  ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode

private abbrev ReceiptFamily :=
  ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I) initialCode

private abbrev ReceiptClass :=
  ProfiledOpenActiveLaneSideClass A initialCode

private abbrev ReceiptTaggedFamily :=
  SidewiseTaggedFamily (ReceiptClass A initialCode)
    (ReceiptClass A initialCode) (ReceiptFamily A initialCode)

private abbrev ReceiptCandidate :=
  ProfiledOpenActiveLaneTaggedCandidate A initialCode

private abbrev ReceiptSummary :=
  SidewiseFiniteCandidateSummary
    (ReceiptClass A initialCode) (ReceiptClass A initialCode)
    (ReceiptFamily A initialCode) (ReceiptDescriptor A initialCode)

private abbrev ReceiptBank :=
  ProfiledOpenFixedSidewisePinnedBank A initialCode
    (ReceiptClass A initialCode) (ReceiptClass A initialCode)

private abbrev ReceiptQuery :=
  ProfiledOpenFixedSidewiseReachablePointedQuery A initialCode

private abbrev ReceiptTagInvariant :=
  ProfiledOpenActiveLaneClassTagInvariant A strategy hwin basis initialCode

private abbrev ReceiptTargetTag :=
  profiledOpenShapeFreeClassTargetTag A initialCode
    (profiledOpenActiveLaneClassOf A strategy hwin basis initialCode)

private abbrev ReceiptExactEdge :=
  ProfiledOpenFixedSidewiseReanchoredExactEdge A strategy hwin basis
    initialCode
    (ReceiptTagInvariant A strategy hwin basis initialCode)
    (ReceiptTargetTag A strategy hwin basis initialCode)

private abbrev ReceiptControlStep :=
  ProfiledOpenFixedSidewiseControlStep A initialCode

/-! ## Repairing the lost source-family argument -/

/-- Source-aware form of the concrete re-anchored edge.

This is the old edge with its existential `sourceFamily` replaced by the
literal family stored in the source candidate.  It is the weakest repair of
the generic interface: all semantic equations are unchanged. -/
def ProfiledOpenFixedSidewiseReanchoredSourceAwareExactEdge
    (sourceFamily : ReceiptTaggedFamily A initialCode)
    (source : ReceiptDescriptor A initialCode)
    (bank : ReceiptBank A initialCode)
    (query : ReceiptQuery A initialCode)
    (targetFamily : ReceiptTaggedFamily A initialCode)
    (target : ReceiptDescriptor A initialCode) : Prop :=
  ∃ sourceState stepState,
    profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis initialCode sourceState = source ∧
    profiledOpenOptionalControlledFamilyOf A strategy hwin basis initialCode
        sourceState = sourceFamily.2 ∧
    ReceiptTagInvariant A strategy hwin basis initialCode source sourceFamily ∧
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
      ReceiptTargetTag A strategy hwin basis initialCode source bank query
        targetFamily.2 target

/-- The repaired edge safely erases to the existing descriptor-only edge.
The converse is unavailable because the old witness may choose a different
source family. -/
theorem profiledOpenFixedSidewiseReanchoredSourceAwareExactEdge_to_old
    {source target : ReceiptCandidate A initialCode}
    {bank : ReceiptBank A initialCode}
    {query : ReceiptQuery A initialCode}
    (hedge : ProfiledOpenFixedSidewiseReanchoredSourceAwareExactEdge A
      strategy hwin basis initialCode source.1 source.2 bank query target.1
        target.2) :
    ReceiptExactEdge A strategy hwin basis initialCode source.2 bank query
      target.1 target.2 := by
  rcases hedge with ⟨sourceState, stepState, hsource, hsourceFamily, htag,
    hvalid, hstep, hstepSource, htargetFamily, htarget, htargetTag⟩
  exact ⟨sourceState, source.1, stepState, hsource, hsourceFamily, htag,
    hvalid, hstep, hstepSource, htargetFamily, htarget, htargetTag⟩

private abbrev ReceiptSourceAwareExactEdge :=
  ProfiledOpenFixedSidewiseReanchoredSourceAwareExactEdge A strategy hwin basis
    initialCode

private abbrev ReceiptSourceAwareCandidateEdge
    (source : ReceiptCandidate A initialCode)
    (bank : ReceiptBank A initialCode)
    (query : ReceiptQuery A initialCode)
    (target : ReceiptCandidate A initialCode) : Prop :=
  ReceiptSourceAwareExactEdge A strategy hwin basis initialCode source.1
    source.2 bank query target.1 target.2

private abbrev ReceiptSourceAwareGood
    (source : ReceiptCandidate A initialCode)
    (bank : ReceiptBank A initialCode)
    (query : ReceiptQuery A initialCode)
    (target : ReceiptCandidate A initialCode) : Prop :=
  SourceAwareRelationalFamilyCandidateGood
    (ReceiptSourceAwareCandidateEdge A strategy hwin basis initialCode)
    (ReceiptControlStep A initialCode) source bank query target

/-- The source-aware repair preserves the existing live-successor theorem.
Thus retaining the source family costs no mathematical coverage assumption;
it only prevents the saturation from silently changing that family. -/
theorem
    profiledOpenFixedSidewiseReanchoredSourceAware_liveSuccessorCoverage :
    SourceAwareRelationalCandidateLiveSuccessorCoverage
      (ProfiledOpenFixedSidewiseSemanticLive A strategy hwin basis initialCode
        (ReceiptTagInvariant A strategy hwin basis initialCode))
      (ProfiledOpenFixedSidewiseReanchoredCandidateValid A strategy hwin basis
        initialCode)
      (ReceiptSourceAwareCandidateEdge A strategy hwin basis initialCode)
      (ReceiptControlStep A initialCode) := by
  intro source bank query hlive hvalid
  rcases hlive.1 with ⟨sourceState, hsource, hsourceFamily⟩
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
  let targetDescriptor :=
    profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
      basis initialCode child
  let targetFamily :=
    profiledOpenOptionalControlledFamilyOf A strategy hwin basis initialCode
      child
  let taggedTarget : ReceiptTaggedFamily A initialCode :=
    (ReceiptTargetTag A strategy hwin basis initialCode source.2 bank query
      targetFamily targetDescriptor,
      targetFamily)
  let target : ReceiptCandidate A initialCode :=
    (taggedTarget, targetDescriptor)
  refine ⟨target, ?_, ?_⟩
  · constructor
    · exact ⟨sourceState, stepState, hsource, hsourceFamily, hlive.2,
        hvalid, hstep, hstepSource, rfl, rfl, rfl⟩
    · change targetDescriptor.control =
        (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).step
          source.2.control targetDescriptor.code
      rw [← hstepSource]
      exact profiledOpenIndexedOptionalControlledSemanticNext_control A
        strategy hwin basis initialCode stepState query.1.2
  · constructor
    · exact ⟨child, rfl, rfl⟩
    · rfl

/-! ## A finite locally filtered relational successor -/

/-- The global exact saturation, filtered by one process-local receipt class.

`Keep` is part of the finite transition table.  It is not evaluated on a
semantic history at run time. -/
noncomputable def profiledOpenActiveLaneFilteredSaturation
    (current : ReceiptSummary A initialCode)
    (bank : ReceiptBank A initialCode)
    (query : ReceiptQuery A initialCode)
    (Keep : ReceiptCandidate A initialCode → Prop) :
    ReceiptSummary A initialCode := by
  classical
  exact Finset.univ.filter fun target ↦
    Keep target ∧
      ∃ source ∈ current,
        ReceiptSourceAwareGood A strategy hwin basis initialCode source bank
          query target

theorem mem_profiledOpenActiveLaneFilteredSaturation_iff
    (current : ReceiptSummary A initialCode)
    (bank : ReceiptBank A initialCode)
    (query : ReceiptQuery A initialCode)
    (Keep : ReceiptCandidate A initialCode → Prop)
    (target : ReceiptCandidate A initialCode) :
    target ∈ profiledOpenActiveLaneFilteredSaturation A strategy hwin basis
        initialCode current bank query Keep ↔
      Keep target ∧
        ∃ source ∈ current,
          ReceiptSourceAwareGood A strategy hwin basis initialCode source bank
            query target := by
  classical
  simp [profiledOpenActiveLaneFilteredSaturation]

/-! ## The exact local-receipt successor laws -/

/-- Weakest process-one pairwise law for one locally filtered successor set.

Every two retained, right-active targets of exact edges must admit honest
anchors in one active-right local fibre.  The sources and edge witnesses are
proof data only. -/
def ProfiledOpenActiveLaneRightLocalReceiptSuccessorLaw
    (current : ReceiptSummary A initialCode)
    (bank : ReceiptBank A initialCode)
    (query : ReceiptQuery A initialCode)
    (Keep : ReceiptCandidate A initialCode → Prop) : Prop :=
  ∀ leftSource leftTarget rightSource rightTarget,
    leftSource ∈ current →
    ReceiptSourceAwareGood A strategy hwin basis initialCode leftSource bank
        query leftTarget →
    Keep leftTarget →
    ProfiledOpenActiveLaneRightRuntimeLive A strategy hwin basis initialCode
        leftTarget.2 leftTarget.1 →
    rightSource ∈ current →
    ReceiptSourceAwareGood A strategy hwin basis initialCode rightSource bank
        query rightTarget →
    Keep rightTarget →
    ProfiledOpenActiveLaneRightRuntimeLive A strategy hwin basis initialCode
        rightTarget.2 rightTarget.1 →
    ∃ leftAnchor : ProfiledOpenActiveLaneRightCandidateAnchor A strategy hwin
        basis initialCode leftTarget,
      ∃ rightAnchor : ProfiledOpenActiveLaneRightCandidateAnchor A strategy
          hwin basis initialCode rightTarget,
        ProfiledOpenIndexedActiveRightControlledLocalFibreRel A strategy hwin
          basis initialCode leftAnchor.source rightAnchor.source

/-- Process-two mirror. -/
def ProfiledOpenActiveLaneLeftLocalReceiptSuccessorLaw
    (current : ReceiptSummary A initialCode)
    (bank : ReceiptBank A initialCode)
    (query : ReceiptQuery A initialCode)
    (Keep : ReceiptCandidate A initialCode → Prop) : Prop :=
  ∀ leftSource leftTarget rightSource rightTarget,
    leftSource ∈ current →
    ReceiptSourceAwareGood A strategy hwin basis initialCode leftSource bank
        query leftTarget →
    Keep leftTarget →
    ProfiledOpenActiveLaneLeftRuntimeLive A strategy hwin basis initialCode
        leftTarget.2 leftTarget.1 →
    rightSource ∈ current →
    ReceiptSourceAwareGood A strategy hwin basis initialCode rightSource bank
        query rightTarget →
    Keep rightTarget →
    ProfiledOpenActiveLaneLeftRuntimeLive A strategy hwin basis initialCode
        rightTarget.2 rightTarget.1 →
    ∃ leftAnchor : ProfiledOpenActiveLaneLeftCandidateAnchor A strategy hwin
        basis initialCode leftTarget,
      ∃ rightAnchor : ProfiledOpenActiveLaneLeftCandidateAnchor A strategy
          hwin basis initialCode rightTarget,
        ProfiledOpenIndexedActiveLeftControlledLocalFibreRel A strategy hwin
          basis initialCode leftAnchor.source rightAnchor.source

/-! ## One-step preservation -/

/-- The process-one local successor law preserves the exact finite receipt
coherence consumed by the local bank compiler. -/
theorem profiledOpenActiveLaneRightReceiptCoherentAt_filteredSaturation
    (current : ReceiptSummary A initialCode)
    (bank : ReceiptBank A initialCode)
    (query : ReceiptQuery A initialCode)
    (Keep : ReceiptCandidate A initialCode → Prop)
    (hstep : ProfiledOpenActiveLaneRightLocalReceiptSuccessorLaw A strategy
      hwin basis initialCode current bank query Keep)
    (Reachable : ReceiptSummary A initialCode → Prop) :
    ProfiledOpenActiveLaneRightReceiptCoherentAt A strategy hwin basis
      initialCode Reachable
      (profiledOpenActiveLaneFilteredSaturation A strategy hwin basis
        initialCode current bank query Keep) := by
  intro left right hleft hleftLive hright hrightLive
  rw [sidewiseFiniteCandidatePossible] at hleft hright
  rcases (mem_profiledOpenActiveLaneFilteredSaturation_iff A strategy hwin
      basis initialCode current bank query Keep left).1 hleft.2 with
    ⟨hkeepLeft, leftSource, hleftSource, hleftEdge⟩
  rcases (mem_profiledOpenActiveLaneFilteredSaturation_iff A strategy hwin
      basis initialCode current bank query Keep right).1 hright.2 with
    ⟨hkeepRight, rightSource, hrightSource, hrightEdge⟩
  exact hstep leftSource left rightSource right hleftSource hleftEdge
    hkeepLeft hleftLive hrightSource hrightEdge hkeepRight hrightLive

/-- Process-two one-step preservation. -/
theorem profiledOpenActiveLaneLeftReceiptCoherentAt_filteredSaturation
    (current : ReceiptSummary A initialCode)
    (bank : ReceiptBank A initialCode)
    (query : ReceiptQuery A initialCode)
    (Keep : ReceiptCandidate A initialCode → Prop)
    (hstep : ProfiledOpenActiveLaneLeftLocalReceiptSuccessorLaw A strategy
      hwin basis initialCode current bank query Keep)
    (Reachable : ReceiptSummary A initialCode → Prop) :
    ProfiledOpenActiveLaneLeftReceiptCoherentAt A strategy hwin basis
      initialCode Reachable
      (profiledOpenActiveLaneFilteredSaturation A strategy hwin basis
        initialCode current bank query Keep) := by
  intro left right hleft hleftLive hright hrightLive
  rw [sidewiseFiniteCandidatePossible] at hleft hright
  rcases (mem_profiledOpenActiveLaneFilteredSaturation_iff A strategy hwin
      basis initialCode current bank query Keep left).1 hleft.2 with
    ⟨hkeepLeft, leftSource, hleftSource, hleftEdge⟩
  rcases (mem_profiledOpenActiveLaneFilteredSaturation_iff A strategy hwin
      basis initialCode current bank query Keep right).1 hright.2 with
    ⟨hkeepRight, rightSource, hrightSource, hrightEdge⟩
  exact hstep leftSource left rightSource right hleftSource hleftEdge
    hkeepLeft hleftLive hrightSource hrightEdge hkeepRight hrightLive

/-! ## Exactness of the criterion -/

/-- With every finite summary declared reachable, the pairwise edge law is
equivalent to receipt coherence of the filtered saturation.  Thus the model
obligation above is neither stronger nor weaker than the consumer needs. -/
theorem
    profiledOpenActiveLaneRightLocalReceiptSuccessorLaw_iff_coherentSaturation
    (current : ReceiptSummary A initialCode)
    (bank : ReceiptBank A initialCode)
    (query : ReceiptQuery A initialCode)
    (Keep : ReceiptCandidate A initialCode → Prop) :
    ProfiledOpenActiveLaneRightLocalReceiptSuccessorLaw A strategy hwin basis
        initialCode current bank query Keep ↔
      ProfiledOpenActiveLaneRightReceiptCoherentAt A strategy hwin basis
        initialCode (fun _ ↦ True)
        (profiledOpenActiveLaneFilteredSaturation A strategy hwin basis
          initialCode current bank query Keep) := by
  constructor
  · intro hstep
    exact profiledOpenActiveLaneRightReceiptCoherentAt_filteredSaturation A
      strategy hwin basis initialCode current bank query Keep hstep
      (fun _ ↦ True)
  · intro hcoherent leftSource leftTarget rightSource rightTarget
      hleftSource hleftEdge hkeepLeft hleftLive hrightSource hrightEdge
      hkeepRight hrightLive
    apply hcoherent leftTarget rightTarget
    · exact ⟨trivial,
        (mem_profiledOpenActiveLaneFilteredSaturation_iff A strategy hwin
          basis initialCode current bank query Keep leftTarget).2
          ⟨hkeepLeft, leftSource, hleftSource, hleftEdge⟩⟩
    · exact hleftLive
    · exact ⟨trivial,
        (mem_profiledOpenActiveLaneFilteredSaturation_iff A strategy hwin
          basis initialCode current bank query Keep rightTarget).2
          ⟨hkeepRight, rightSource, hrightSource, hrightEdge⟩⟩
    · exact hrightLive

/-- Process-two exactness. -/
theorem
    profiledOpenActiveLaneLeftLocalReceiptSuccessorLaw_iff_coherentSaturation
    (current : ReceiptSummary A initialCode)
    (bank : ReceiptBank A initialCode)
    (query : ReceiptQuery A initialCode)
    (Keep : ReceiptCandidate A initialCode → Prop) :
    ProfiledOpenActiveLaneLeftLocalReceiptSuccessorLaw A strategy hwin basis
        initialCode current bank query Keep ↔
      ProfiledOpenActiveLaneLeftReceiptCoherentAt A strategy hwin basis
        initialCode (fun _ ↦ True)
        (profiledOpenActiveLaneFilteredSaturation A strategy hwin basis
          initialCode current bank query Keep) := by
  constructor
  · intro hstep
    exact profiledOpenActiveLaneLeftReceiptCoherentAt_filteredSaturation A
      strategy hwin basis initialCode current bank query Keep hstep
      (fun _ ↦ True)
  · intro hcoherent leftSource leftTarget rightSource rightTarget
      hleftSource hleftEdge hkeepLeft hleftLive hrightSource hrightEdge
      hkeepRight hrightLive
    apply hcoherent leftTarget rightTarget
    · exact ⟨trivial,
        (mem_profiledOpenActiveLaneFilteredSaturation_iff A strategy hwin
          basis initialCode current bank query Keep leftTarget).2
          ⟨hkeepLeft, leftSource, hleftSource, hleftEdge⟩⟩
    · exact hleftLive
    · exact ⟨trivial,
        (mem_profiledOpenActiveLaneFilteredSaturation_iff A strategy hwin
          basis initialCode current bank query Keep rightTarget).2
          ⟨hkeepRight, rightSource, hrightSource, hrightEdge⟩⟩
    · exact hrightLive

/-! ## Initialization -/

/-- Every singleton finite receipt is process-one coherent.  If its unique
candidate is inactive the claim is vacuous; otherwise its honest anchor is
related to itself. -/
theorem profiledOpenActiveLaneRightReceiptCoherentAt_singleton
    (Reachable : ReceiptSummary A initialCode → Prop)
    (candidate : ReceiptCandidate A initialCode) :
    ProfiledOpenActiveLaneRightReceiptCoherentAt A strategy hwin basis
      initialCode Reachable {candidate} := by
  intro left right hleft hleftLive hright hrightLive
  rw [sidewiseFiniteCandidatePossible] at hleft hright
  have hleftEq : left = candidate := by simpa using hleft.2
  have hrightEq : right = candidate := by simpa using hright.2
  subst left
  subst right
  rcases exists_profiledOpenActiveLaneRightCandidateAnchor A strategy hwin
      basis initialCode candidate hleftLive with ⟨anchor⟩
  exact ⟨anchor, anchor,
    (profiledOpenIndexedActiveRightControlledLocalFibreRel_reflexive A
      strategy hwin basis initialCode).refl anchor.source⟩

/-- Singleton initialization for process two. -/
theorem profiledOpenActiveLaneLeftReceiptCoherentAt_singleton
    (Reachable : ReceiptSummary A initialCode → Prop)
    (candidate : ReceiptCandidate A initialCode) :
    ProfiledOpenActiveLaneLeftReceiptCoherentAt A strategy hwin basis
      initialCode Reachable {candidate} := by
  intro left right hleft hleftLive hright hrightLive
  rw [sidewiseFiniteCandidatePossible] at hleft hright
  have hleftEq : left = candidate := by simpa using hleft.2
  have hrightEq : right = candidate := by simpa using hright.2
  subst left
  subst right
  rcases exists_profiledOpenActiveLaneLeftCandidateAnchor A strategy hwin
      basis initialCode candidate hleftLive with ⟨anchor⟩
  exact ⟨anchor, anchor,
    (profiledOpenIndexedActiveLeftControlledLocalFibreRel_reflexive A strategy
      hwin basis initialCode).refl anchor.source⟩

/-- The concrete initial candidate set used by the fixed-policy table is a
singleton, hence initializes the process-one receipt invariant without any
leader or shape premise. -/
theorem profiledOpenShapeFreeInitialCandidateSet_rightReceiptCoherent
    (Reachable : ReceiptSummary A initialCode → Prop)
    (state : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode) :
    ProfiledOpenActiveLaneRightReceiptCoherentAt A strategy hwin basis
      initialCode Reachable
      (profiledOpenShapeFreeInitialCandidateSet A strategy hwin basis
        initialCode
        (profiledOpenActiveLaneClassOf A strategy hwin basis initialCode)
        state) := by
  simpa [profiledOpenShapeFreeInitialCandidateSet] using
    (profiledOpenActiveLaneRightReceiptCoherentAt_singleton A strategy hwin
      basis initialCode Reachable
      (profiledOpenShapeFreeInitialCandidate A strategy hwin basis initialCode
        (profiledOpenActiveLaneClassOf A strategy hwin basis initialCode)
        state))

/-- Concrete process-two initialization. -/
theorem profiledOpenShapeFreeInitialCandidateSet_leftReceiptCoherent
    (Reachable : ReceiptSummary A initialCode → Prop)
    (state : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode) :
    ProfiledOpenActiveLaneLeftReceiptCoherentAt A strategy hwin basis
      initialCode Reachable
      (profiledOpenShapeFreeInitialCandidateSet A strategy hwin basis
        initialCode
        (profiledOpenActiveLaneClassOf A strategy hwin basis initialCode)
        state) := by
  simpa [profiledOpenShapeFreeInitialCandidateSet] using
    (profiledOpenActiveLaneLeftReceiptCoherentAt_singleton A strategy hwin
      basis initialCode Reachable
      (profiledOpenShapeFreeInitialCandidate A strategy hwin basis initialCode
        (profiledOpenActiveLaneClassOf A strategy hwin basis initialCode)
        state))

end

end DetParityAutomaton

end DistributedSynthesis
