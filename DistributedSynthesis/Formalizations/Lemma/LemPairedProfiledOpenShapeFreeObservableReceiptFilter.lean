/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenShapeFreeContextualTag
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenShapeFreeReceiptCoherencePropagation

/-!
# Observable receipt filters for witnessed shape-free successors

The source-aware contextual edge tags its literal semantic child by the two
finite projected local-fibre images.  A process may retain the candidates
whose own projected coordinate is one fixed finite receipt.  It does not
inspect the other coordinate, an optional lane shape, a graph direction, a
strict-leader flag, parity control, or the permanently hidden bit.

Equality of two projected images is deliberately *not* reflected back to
equality of their literal semantic children.  For local consumption we need
only honest anchors for the two public candidates.  The descriptor of the
second literal child belongs to its projected image; after receipt equality
it therefore belongs to the first image, which supplies a re-anchored point
in the first exact local fibre.  This is the safe image-membership direction.
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

private abbrev ObservableDescriptor :=
  ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode

private abbrev ObservableFamily :=
  ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I) initialCode

private abbrev ObservableClass :=
  ProfiledOpenActiveLaneSideClass A initialCode

private abbrev ObservableTaggedFamily :=
  SidewiseTaggedFamily (ObservableClass A initialCode)
    (ObservableClass A initialCode) (ObservableFamily A initialCode)

private abbrev ObservableCandidate :=
  ProfiledOpenActiveLaneTaggedCandidate A initialCode

private abbrev ObservableSummary :=
  SidewiseFiniteCandidateSummary
    (ObservableClass A initialCode) (ObservableClass A initialCode)
    (ObservableFamily A initialCode) (ObservableDescriptor A initialCode)

private abbrev ObservableBank :=
  ProfiledOpenFixedSidewisePinnedBank A initialCode
    (ObservableClass A initialCode) (ObservableClass A initialCode)

private abbrev ObservableQuery :=
  ProfiledOpenFixedSidewiseReachablePointedQuery A initialCode

private abbrev ObservableControlStep :=
  ProfiledOpenFixedSidewiseControlStep A initialCode

/-! ## Witnessed runtime liveness and honest anchors -/

/-- Process one's active fragment under the contextual witnessed tag. -/
def ProfiledOpenActiveLaneRightWitnessedRuntimeLive
    (descriptor : ObservableDescriptor A initialCode)
    (family : ObservableTaggedFamily A initialCode) : Prop :=
  ProfiledOpenFixedSidewiseSemanticLive A strategy hwin basis initialCode
      (ProfiledOpenActiveLaneWitnessedTagInvariant A strategy hwin basis
        initialCode)
      descriptor family ∧
    descriptor ∈ family.2.1

/-- Process-two mirror. -/
def ProfiledOpenActiveLaneLeftWitnessedRuntimeLive
    (descriptor : ObservableDescriptor A initialCode)
    (family : ObservableTaggedFamily A initialCode) : Prop :=
  ProfiledOpenFixedSidewiseSemanticLive A strategy hwin basis initialCode
      (ProfiledOpenActiveLaneWitnessedTagInvariant A strategy hwin basis
        initialCode)
      descriptor family ∧
    descriptor ∈ family.2.2

/-- A witnessed right-active candidate has an anchor at its literal semantic
witness.  The lane witness is proof-only and is derived from membership in
the advertised right family. -/
theorem exists_profiledOpenActiveLaneRightWitnessedCandidateAnchor
    (candidate : ObservableCandidate A initialCode)
    (hlive : ProfiledOpenActiveLaneRightWitnessedRuntimeLive A strategy hwin
      basis initialCode candidate.2 candidate.1) :
    Nonempty (ProfiledOpenActiveLaneRightCandidateAnchor A strategy hwin basis
      initialCode candidate) := by
  rcases hlive.1.2 with
    ⟨point, hdescriptor, hfamily, htag⟩
  have hmember :
      profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
          basis initialCode point ∈
        (profiledOpenOptionalControlledFamilyOf A strategy hwin basis
          initialCode point).1 := by
    rw [hdescriptor, hfamily]
    exact hlive.2
  let hactive := profiledOpenOptionalControlled_rightActive_of_mem A strategy
    hwin basis initialCode point hmember
  let source := profiledOpenActiveLaneRightPoint A strategy hwin basis
    initialCode point hactive
  refine ⟨⟨source, ?_, ?_⟩⟩
  · change
      profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis initialCode point = candidate.2
    exact hdescriptor
  · have htagRight := congrArg Prod.fst htag
    change
      profiledOpenActiveRightProjectedClass A strategy hwin basis initialCode
          source = candidate.1.1.1
    unfold profiledOpenActiveLaneClassPairOfPoint at htagRight
    unfold profiledOpenActiveLaneRightClassOfPoint at htagRight
    rw [dif_pos hactive] at htagRight
    exact htagRight.symm

/-- Witnessed left-active anchor. -/
theorem exists_profiledOpenActiveLaneLeftWitnessedCandidateAnchor
    (candidate : ObservableCandidate A initialCode)
    (hlive : ProfiledOpenActiveLaneLeftWitnessedRuntimeLive A strategy hwin
      basis initialCode candidate.2 candidate.1) :
    Nonempty (ProfiledOpenActiveLaneLeftCandidateAnchor A strategy hwin basis
      initialCode candidate) := by
  rcases hlive.1.2 with
    ⟨point, hdescriptor, hfamily, htag⟩
  have hmember :
      profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
          basis initialCode point ∈
        (profiledOpenOptionalControlledFamilyOf A strategy hwin basis
          initialCode point).2 := by
    rw [hdescriptor, hfamily]
    exact hlive.2
  let hactive := profiledOpenOptionalControlled_leftActive_of_mem A strategy
    hwin basis initialCode point hmember
  let source := profiledOpenActiveLaneLeftPoint A strategy hwin basis
    initialCode point hactive
  refine ⟨⟨source, ?_, ?_⟩⟩
  · change
      profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis initialCode point = candidate.2
    exact hdescriptor
  · have htagLeft := congrArg Prod.snd htag
    change
      profiledOpenActiveLeftProjectedClass A strategy hwin basis initialCode
          source = candidate.1.1.2
    unfold profiledOpenActiveLaneClassPairOfPoint at htagLeft
    unfold profiledOpenActiveLaneLeftClassOfPoint at htagLeft
    rw [dif_pos hactive] at htagLeft
    exact htagLeft.symm

/-! ## Finite process-local receipt filters -/

/-- Process one retains exactly one finite projected-class receipt. -/
def profiledOpenActiveLaneRightObservableReceiptKeep
    (receipt : ObservableClass A initialCode)
    (candidate : ObservableCandidate A initialCode) : Prop :=
  candidate.1.1.1 = receipt

/-- Process-two mirror. -/
def profiledOpenActiveLaneLeftObservableReceiptKeep
    (receipt : ObservableClass A initialCode)
    (candidate : ObservableCandidate A initialCode) : Prop :=
  candidate.1.1.2 = receipt

/-- Equal process-one finite receipts yield anchors in one exact right local
fibre.  The proof uses membership in the finite fibre image, never a converse
from image equality to relation equality. -/
theorem profiledOpenActiveLaneRightWitnessedAnchors_of_receipt_eq
    (left right : ObservableCandidate A initialCode)
    (hleftLive : ProfiledOpenActiveLaneRightWitnessedRuntimeLive A strategy
      hwin basis initialCode left.2 left.1)
    (hrightLive : ProfiledOpenActiveLaneRightWitnessedRuntimeLive A strategy
      hwin basis initialCode right.2 right.1)
    (hreceipt : left.1.1.1 = right.1.1.1) :
    ∃ leftAnchor : ProfiledOpenActiveLaneRightCandidateAnchor A strategy hwin
        basis initialCode left,
      ∃ rightAnchor : ProfiledOpenActiveLaneRightCandidateAnchor A strategy
          hwin basis initialCode right,
        ProfiledOpenIndexedActiveRightControlledLocalFibreRel A strategy hwin
          basis initialCode leftAnchor.source rightAnchor.source := by
  classical
  obtain ⟨leftAnchor⟩ :=
    exists_profiledOpenActiveLaneRightWitnessedCandidateAnchor A strategy hwin
      basis initialCode left hleftLive
  obtain ⟨literalRightAnchor⟩ :=
    exists_profiledOpenActiveLaneRightWitnessedCandidateAnchor A strategy hwin
      basis initialCode right hrightLive
  have hclass :
      profiledOpenActiveRightProjectedClass A strategy hwin basis initialCode
          leftAnchor.source =
        profiledOpenActiveRightProjectedClass A strategy hwin basis initialCode
          literalRightAnchor.source :=
    leftAnchor.class_eq.trans
      (hreceipt.trans literalRightAnchor.class_eq.symm)
  have hrightDescriptorMem :
      profiledOpenActiveRightControlledDescriptor A strategy hwin basis
          initialCode literalRightAnchor.source ∈
        profiledOpenActiveRightProjectedClass A strategy hwin basis initialCode
          leftAnchor.source := by
    rw [hclass]
    exact profiledOpenActiveRightControlledDescriptor_mem_projectedClass A
      strategy hwin basis initialCode literalRightAnchor.source
  rcases (mem_semanticFibreImage_iff
      (profiledOpenActiveRightControlledDescriptor A strategy hwin basis
        initialCode)
      (ProfiledOpenIndexedActiveRightControlledLocalFibreRel A strategy hwin
        basis initialCode)
      leftAnchor.source
      (profiledOpenActiveRightControlledDescriptor A strategy hwin basis
        initialCode literalRightAnchor.source)).1 hrightDescriptorMem with
    ⟨rightSource, hrel, hdescriptor⟩
  let rightAnchor : ProfiledOpenActiveLaneRightCandidateAnchor A strategy hwin
      basis initialCode right := {
    source := rightSource
    descriptor_eq := hdescriptor.trans literalRightAnchor.descriptor_eq
    class_eq :=
      (profiledOpenActiveRightProjectedClass_eq_of_rel A strategy hwin basis
        initialCode hrel).symm.trans
        (leftAnchor.class_eq.trans hreceipt) }
  exact ⟨leftAnchor, rightAnchor, hrel⟩

/-- Process-two finite-receipt re-anchoring. -/
theorem profiledOpenActiveLaneLeftWitnessedAnchors_of_receipt_eq
    (left right : ObservableCandidate A initialCode)
    (hleftLive : ProfiledOpenActiveLaneLeftWitnessedRuntimeLive A strategy hwin
      basis initialCode left.2 left.1)
    (hrightLive : ProfiledOpenActiveLaneLeftWitnessedRuntimeLive A strategy
      hwin basis initialCode right.2 right.1)
    (hreceipt : left.1.1.2 = right.1.1.2) :
    ∃ leftAnchor : ProfiledOpenActiveLaneLeftCandidateAnchor A strategy hwin
        basis initialCode left,
      ∃ rightAnchor : ProfiledOpenActiveLaneLeftCandidateAnchor A strategy
          hwin basis initialCode right,
        ProfiledOpenIndexedActiveLeftControlledLocalFibreRel A strategy hwin
          basis initialCode leftAnchor.source rightAnchor.source := by
  classical
  obtain ⟨leftAnchor⟩ :=
    exists_profiledOpenActiveLaneLeftWitnessedCandidateAnchor A strategy hwin
      basis initialCode left hleftLive
  obtain ⟨literalRightAnchor⟩ :=
    exists_profiledOpenActiveLaneLeftWitnessedCandidateAnchor A strategy hwin
      basis initialCode right hrightLive
  have hclass :
      profiledOpenActiveLeftProjectedClass A strategy hwin basis initialCode
          leftAnchor.source =
        profiledOpenActiveLeftProjectedClass A strategy hwin basis initialCode
          literalRightAnchor.source :=
    leftAnchor.class_eq.trans
      (hreceipt.trans literalRightAnchor.class_eq.symm)
  have hrightDescriptorMem :
      profiledOpenActiveLeftControlledDescriptor A strategy hwin basis
          initialCode literalRightAnchor.source ∈
        profiledOpenActiveLeftProjectedClass A strategy hwin basis initialCode
          leftAnchor.source := by
    rw [hclass]
    exact profiledOpenActiveLeftControlledDescriptor_mem_projectedClass A
      strategy hwin basis initialCode literalRightAnchor.source
  rcases (mem_semanticFibreImage_iff
      (profiledOpenActiveLeftControlledDescriptor A strategy hwin basis
        initialCode)
      (ProfiledOpenIndexedActiveLeftControlledLocalFibreRel A strategy hwin
        basis initialCode)
      leftAnchor.source
      (profiledOpenActiveLeftControlledDescriptor A strategy hwin basis
        initialCode literalRightAnchor.source)).1 hrightDescriptorMem with
    ⟨rightSource, hrel, hdescriptor⟩
  let rightAnchor : ProfiledOpenActiveLaneLeftCandidateAnchor A strategy hwin
      basis initialCode right := {
    source := rightSource
    descriptor_eq := hdescriptor.trans literalRightAnchor.descriptor_eq
    class_eq :=
      (profiledOpenActiveLeftProjectedClass_eq_of_rel A strategy hwin basis
        initialCode hrel).symm.trans
        (leftAnchor.class_eq.trans hreceipt) }
  exact ⟨leftAnchor, rightAnchor, hrel⟩

/-! ## The witnessed source-aware successor laws -/

/-- Candidate-level form of the contextual witnessed exact edge. -/
def profiledOpenActiveLaneWitnessedCandidateEdge
    (source : ObservableCandidate A initialCode)
    (bank : ObservableBank A initialCode)
    (query : ObservableQuery A initialCode)
    (target : ObservableCandidate A initialCode) : Prop :=
  ProfiledOpenFixedSidewiseWitnessedReanchoredExactEdge A strategy hwin basis
    initialCode source.1 source.2 bank query target.1 target.2

private abbrev ObservableWitnessedGood
    (source : ObservableCandidate A initialCode)
    (bank : ObservableBank A initialCode)
    (query : ObservableQuery A initialCode)
    (target : ObservableCandidate A initialCode) : Prop :=
  SourceAwareRelationalFamilyCandidateGood
    (profiledOpenActiveLaneWitnessedCandidateEdge A strategy hwin basis
      initialCode)
    (ObservableControlStep A initialCode) source bank query target

/-- Exact process-one law for the witnessed edge and witnessed liveness. -/
def ProfiledOpenActiveLaneRightWitnessedLocalReceiptSuccessorLaw
    (current : ObservableSummary A initialCode)
    (bank : ObservableBank A initialCode)
    (query : ObservableQuery A initialCode)
    (Keep : ObservableCandidate A initialCode → Prop) : Prop :=
  ∀ leftSource leftTarget rightSource rightTarget,
    leftSource ∈ current →
    ObservableWitnessedGood A strategy hwin basis initialCode leftSource bank
        query leftTarget →
    Keep leftTarget →
    ProfiledOpenActiveLaneRightWitnessedRuntimeLive A strategy hwin basis
        initialCode leftTarget.2 leftTarget.1 →
    rightSource ∈ current →
    ObservableWitnessedGood A strategy hwin basis initialCode rightSource bank
        query rightTarget →
    Keep rightTarget →
    ProfiledOpenActiveLaneRightWitnessedRuntimeLive A strategy hwin basis
        initialCode rightTarget.2 rightTarget.1 →
    ∃ leftAnchor : ProfiledOpenActiveLaneRightCandidateAnchor A strategy hwin
        basis initialCode leftTarget,
      ∃ rightAnchor : ProfiledOpenActiveLaneRightCandidateAnchor A strategy
          hwin basis initialCode rightTarget,
        ProfiledOpenIndexedActiveRightControlledLocalFibreRel A strategy hwin
          basis initialCode leftAnchor.source rightAnchor.source

/-- Process-two witnessed successor law. -/
def ProfiledOpenActiveLaneLeftWitnessedLocalReceiptSuccessorLaw
    (current : ObservableSummary A initialCode)
    (bank : ObservableBank A initialCode)
    (query : ObservableQuery A initialCode)
    (Keep : ObservableCandidate A initialCode → Prop) : Prop :=
  ∀ leftSource leftTarget rightSource rightTarget,
    leftSource ∈ current →
    ObservableWitnessedGood A strategy hwin basis initialCode leftSource bank
        query leftTarget →
    Keep leftTarget →
    ProfiledOpenActiveLaneLeftWitnessedRuntimeLive A strategy hwin basis
        initialCode leftTarget.2 leftTarget.1 →
    rightSource ∈ current →
    ObservableWitnessedGood A strategy hwin basis initialCode rightSource bank
        query rightTarget →
    Keep rightTarget →
    ProfiledOpenActiveLaneLeftWitnessedRuntimeLive A strategy hwin basis
        initialCode rightTarget.2 rightTarget.1 →
    ∃ leftAnchor : ProfiledOpenActiveLaneLeftCandidateAnchor A strategy hwin
        basis initialCode leftTarget,
      ∃ rightAnchor : ProfiledOpenActiveLaneLeftCandidateAnchor A strategy
          hwin basis initialCode rightTarget,
        ProfiledOpenIndexedActiveLeftControlledLocalFibreRel A strategy hwin
          basis initialCode leftAnchor.source rightAnchor.source

/-- A fixed literal process-one finite receipt discharges the entire
witnessed successor law.  Source candidates and edge witnesses are irrelevant
to the local equality proof and remain proof-only. -/
theorem profiledOpenActiveLaneRightWitnessedLocalReceiptSuccessorLaw_receipt
    (current : ObservableSummary A initialCode)
    (bank : ObservableBank A initialCode)
    (query : ObservableQuery A initialCode)
    (receipt : ObservableClass A initialCode) :
    ProfiledOpenActiveLaneRightWitnessedLocalReceiptSuccessorLaw A strategy
      hwin basis initialCode current bank query
      (profiledOpenActiveLaneRightObservableReceiptKeep A initialCode
        receipt) := by
  intro _leftSource leftTarget _rightSource rightTarget _ _ hkeepLeft
    hleftLive _ _ hkeepRight hrightLive
  exact profiledOpenActiveLaneRightWitnessedAnchors_of_receipt_eq A strategy
    hwin basis initialCode leftTarget rightTarget hleftLive hrightLive
    (hkeepLeft.trans hkeepRight.symm)

/-- Process-two fixed finite receipt. -/
theorem profiledOpenActiveLaneLeftWitnessedLocalReceiptSuccessorLaw_receipt
    (current : ObservableSummary A initialCode)
    (bank : ObservableBank A initialCode)
    (query : ObservableQuery A initialCode)
    (receipt : ObservableClass A initialCode) :
    ProfiledOpenActiveLaneLeftWitnessedLocalReceiptSuccessorLaw A strategy
      hwin basis initialCode current bank query
      (profiledOpenActiveLaneLeftObservableReceiptKeep A initialCode
        receipt) := by
  intro _leftSource leftTarget _rightSource rightTarget _ _ hkeepLeft
    hleftLive _ _ hkeepRight hrightLive
  exact profiledOpenActiveLaneLeftWitnessedAnchors_of_receipt_eq A strategy
    hwin basis initialCode leftTarget rightTarget hleftLive hrightLive
    (hkeepLeft.trans hkeepRight.symm)

end

end DetParityAutomaton

end DistributedSynthesis
