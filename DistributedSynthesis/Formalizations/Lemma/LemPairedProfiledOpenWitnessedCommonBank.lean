/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenShapeFreeContextualTag

/-!
# A common bank for context-witnessed shape-free tags

The canonical common-bank construction indexes a value by the class of a
chosen representative.  The context-faithful route instead lets every live
candidate carry an erased semantic witness for its literal public tag.  This
file repeats only the finite candidate-wide selection layer for that stronger
invariant.

For each attained right or left class, one witnessed candidate supplies an
active controlled anchor.  The published bank still contains only finite
class-indexed fixed values.  Different hidden-bit alternatives remain
different relational candidates; no process learns which witness, lane, or
orientation generated a class.
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

private abbrev WitnessedDescriptor :=
  ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode

private abbrev WitnessedFamily :=
  ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I) initialCode

private abbrev WitnessedClass :=
  ProfiledOpenActiveLaneSideClass A initialCode

private abbrev WitnessedTaggedFamily :=
  SidewiseTaggedFamily (WitnessedClass A initialCode)
    (WitnessedClass A initialCode) (WitnessedFamily A initialCode)

private abbrev WitnessedCandidate :=
  RelationalFamilyCandidate (WitnessedTaggedFamily A initialCode)
    (WitnessedDescriptor A initialCode)

private abbrev WitnessedLive :=
  ProfiledOpenFixedSidewiseSemanticLive A strategy hwin basis initialCode
    (ProfiledOpenActiveLaneWitnessedTagInvariant A strategy hwin basis
      initialCode)

/-! ## Honest active-side anchors -/

/-- A right-active witnessed candidate supplies an active controlled point
whose projected class is its literal public right tag. -/
theorem exists_profiledOpenActiveLaneWitnessedRightAnchor
    (candidate : WitnessedCandidate A initialCode)
    (hwitnessed : ProfiledOpenActiveLaneWitnessedTagInvariant A strategy hwin
      basis initialCode candidate.2 candidate.1)
    (hmember : candidate.2 ∈ candidate.1.2.1) :
    ∃ source : ProfiledOpenIndexedActiveRightControlledSemanticPoint A
        strategy hwin basis initialCode,
      profiledOpenActiveRightControlledDescriptor A strategy hwin basis
          initialCode source = candidate.2 ∧
        profiledOpenActiveRightProjectedClass A strategy hwin basis initialCode
            source = candidate.1.1.1 := by
  rcases hwitnessed with ⟨point, hdescriptor, hfamily, htag⟩
  have hmemberPoint :
      profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
          basis initialCode point ∈
        (profiledOpenOptionalControlledFamilyOf A strategy hwin basis
          initialCode point).1 := by
    rw [hdescriptor, hfamily]
    exact hmember
  let hactive := profiledOpenOptionalControlled_rightActive_of_mem A strategy
    hwin basis initialCode point hmemberPoint
  let source := profiledOpenActiveLaneRightPoint A strategy hwin basis
    initialCode point hactive
  have htagRight : candidate.1.1.1 =
      profiledOpenActiveLaneRightClassOfPoint A strategy hwin basis initialCode
        point := by
    simpa only [profiledOpenActiveLaneClassPairOfPoint] using
      congrArg Prod.fst htag
  unfold profiledOpenActiveLaneRightClassOfPoint at htagRight
  rw [dif_pos hactive] at htagRight
  exact ⟨source, hdescriptor, htagRight.symm⟩

/-- Process-two mirror. -/
theorem exists_profiledOpenActiveLaneWitnessedLeftAnchor
    (candidate : WitnessedCandidate A initialCode)
    (hwitnessed : ProfiledOpenActiveLaneWitnessedTagInvariant A strategy hwin
      basis initialCode candidate.2 candidate.1)
    (hmember : candidate.2 ∈ candidate.1.2.2) :
    ∃ source : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A
        strategy hwin basis initialCode,
      profiledOpenActiveLeftControlledDescriptor A strategy hwin basis
          initialCode source = candidate.2 ∧
        profiledOpenActiveLeftProjectedClass A strategy hwin basis initialCode
            source = candidate.1.1.2 := by
  rcases hwitnessed with ⟨point, hdescriptor, hfamily, htag⟩
  have hmemberPoint :
      profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
          basis initialCode point ∈
        (profiledOpenOptionalControlledFamilyOf A strategy hwin basis
          initialCode point).2 := by
    rw [hdescriptor, hfamily]
    exact hmember
  let hactive := profiledOpenOptionalControlled_leftActive_of_mem A strategy
    hwin basis initialCode point hmemberPoint
  let source := profiledOpenActiveLaneLeftPoint A strategy hwin basis
    initialCode point hactive
  have htagLeft : candidate.1.1.2 =
      profiledOpenActiveLaneLeftClassOfPoint A strategy hwin basis initialCode
        point := by
    simpa only [profiledOpenActiveLaneClassPairOfPoint] using
      congrArg Prod.snd htag
  unfold profiledOpenActiveLaneLeftClassOfPoint at htagLeft
  rw [dif_pos hactive] at htagLeft
  exact ⟨source, hdescriptor, htagLeft.symm⟩

/-! ## Finite witnessed class selection -/

def ProfiledOpenActiveLaneWitnessedRightClassAttained
    (candidates : Finset (WitnessedCandidate A initialCode))
    (sideClass : WitnessedClass A initialCode) : Prop :=
  ∃ source : ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy
      hwin basis initialCode,
    profiledOpenActiveRightProjectedClass A strategy hwin basis initialCode
        source = sideClass ∧
      ∃ candidate ∈ candidates,
        WitnessedLive A strategy hwin basis initialCode candidate.2
            candidate.1 ∧
          candidate.2 ∈ candidate.1.2.1 ∧
          profiledOpenActiveRightControlledDescriptor A strategy hwin basis
              initialCode source = candidate.2

def ProfiledOpenActiveLaneWitnessedLeftClassAttained
    (candidates : Finset (WitnessedCandidate A initialCode))
    (sideClass : WitnessedClass A initialCode) : Prop :=
  ∃ source : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy
      hwin basis initialCode,
    profiledOpenActiveLeftProjectedClass A strategy hwin basis initialCode
        source = sideClass ∧
      ∃ candidate ∈ candidates,
        WitnessedLive A strategy hwin basis initialCode candidate.2
            candidate.1 ∧
          candidate.2 ∈ candidate.1.2.2 ∧
          profiledOpenActiveLeftControlledDescriptor A strategy hwin basis
              initialCode source = candidate.2

noncomputable def profiledOpenActiveLaneWitnessedRightValueForClass
    (candidates : Finset (WitnessedCandidate A initialCode))
    (sideClass : WitnessedClass A initialCode) :
    ProfiledOpenFixedRightPinnedValue A initialCode := by
  classical
  exact if hattained : ProfiledOpenActiveLaneWitnessedRightClassAttained A
      strategy hwin basis initialCode candidates sideClass then
    profiledOpenActiveRightFixedValueOfWinning A strategy hwin basis
      initialCode (Classical.choose hattained)
  else
    profiledOpenFixedDefaultRightPinnedValue A initialCode strategy hwin basis

noncomputable def profiledOpenActiveLaneWitnessedLeftValueForClass
    (candidates : Finset (WitnessedCandidate A initialCode))
    (sideClass : WitnessedClass A initialCode) :
    ProfiledOpenFixedLeftPinnedValue A initialCode := by
  classical
  exact if hattained : ProfiledOpenActiveLaneWitnessedLeftClassAttained A
      strategy hwin basis initialCode candidates sideClass then
    profiledOpenActiveLeftFixedValueOfWinning A strategy hwin basis initialCode
      (Classical.choose hattained)
  else
    profiledOpenFixedDefaultLeftPinnedValue A initialCode strategy hwin basis

/-- Symmetric finite bank indexed by the two literal witnessed class tags. -/
noncomputable def profiledOpenActiveLaneWitnessedSidewiseBank
    (candidates : Finset (WitnessedCandidate A initialCode)) :
    ProfiledOpenFixedSidewisePinnedBank A initialCode
      (WitnessedClass A initialCode) (WitnessedClass A initialCode) :=
  (profiledOpenActiveLaneWitnessedRightValueForClass A strategy hwin basis
      initialCode candidates,
    profiledOpenActiveLaneWitnessedLeftValueForClass A strategy hwin basis
      initialCode candidates)

/-! ## Coverage and retained re-anchoring rows -/

theorem profiledOpenActiveLaneWitnessedRightClassAttained_of_live_mem
    (candidates : Finset (WitnessedCandidate A initialCode))
    (candidate : WitnessedCandidate A initialCode)
    (hcandidate : candidate ∈ candidates)
    (hlive : WitnessedLive A strategy hwin basis initialCode candidate.2
      candidate.1)
    (hmember : candidate.2 ∈ candidate.1.2.1) :
    ProfiledOpenActiveLaneWitnessedRightClassAttained A strategy hwin basis
      initialCode candidates candidate.1.1.1 := by
  rcases exists_profiledOpenActiveLaneWitnessedRightAnchor A strategy hwin
      basis initialCode candidate hlive.2 hmember with
    ⟨source, hdescriptor, hsourceClass⟩
  exact ⟨source, hsourceClass, candidate, hcandidate, hlive, hmember,
    hdescriptor⟩

theorem profiledOpenActiveLaneWitnessedLeftClassAttained_of_live_mem
    (candidates : Finset (WitnessedCandidate A initialCode))
    (candidate : WitnessedCandidate A initialCode)
    (hcandidate : candidate ∈ candidates)
    (hlive : WitnessedLive A strategy hwin basis initialCode candidate.2
      candidate.1)
    (hmember : candidate.2 ∈ candidate.1.2.2) :
    ProfiledOpenActiveLaneWitnessedLeftClassAttained A strategy hwin basis
      initialCode candidates candidate.1.1.2 := by
  rcases exists_profiledOpenActiveLaneWitnessedLeftAnchor A strategy hwin basis
      initialCode candidate hlive.2 hmember with
    ⟨source, hdescriptor, hsourceClass⟩
  exact ⟨source, hsourceClass, candidate, hcandidate, hlive, hmember,
    hdescriptor⟩

theorem profiledOpenActiveLaneWitnessedRightValueForClass_covers
    (candidates : Finset (WitnessedCandidate A initialCode))
    (candidate : WitnessedCandidate A initialCode)
    (hcandidate : candidate ∈ candidates)
    (hlive : WitnessedLive A strategy hwin basis initialCode candidate.2
      candidate.1)
    (hmember : candidate.2 ∈ candidate.1.2.1) :
    candidate.2 ∈
      (profiledOpenActiveLaneWitnessedRightValueForClass A strategy hwin basis
        initialCode candidates candidate.1.1.1).1.1 := by
  let hattained :=
    profiledOpenActiveLaneWitnessedRightClassAttained_of_live_mem A strategy
      hwin basis initialCode candidates candidate hcandidate hlive hmember
  unfold profiledOpenActiveLaneWitnessedRightValueForClass
  rw [dif_pos hattained,
    profiledOpenActiveRightFixedValueOfWinning_family]
  change candidate.2 ∈
    profiledOpenActiveRightProjectedClass A strategy hwin basis initialCode
      (Classical.choose hattained)
  rw [(Classical.choose_spec hattained).1]
  rcases exists_profiledOpenActiveLaneWitnessedRightAnchor A strategy hwin
      basis initialCode candidate hlive.2 hmember with
    ⟨source, hdescriptor, hsourceClass⟩
  have hcurrent :=
    profiledOpenActiveRightControlledDescriptor_mem_projectedClass A strategy
      hwin basis initialCode source
  rw [hdescriptor, hsourceClass] at hcurrent
  exact hcurrent

theorem profiledOpenActiveLaneWitnessedLeftValueForClass_covers
    (candidates : Finset (WitnessedCandidate A initialCode))
    (candidate : WitnessedCandidate A initialCode)
    (hcandidate : candidate ∈ candidates)
    (hlive : WitnessedLive A strategy hwin basis initialCode candidate.2
      candidate.1)
    (hmember : candidate.2 ∈ candidate.1.2.2) :
    candidate.2 ∈
      (profiledOpenActiveLaneWitnessedLeftValueForClass A strategy hwin basis
        initialCode candidates candidate.1.1.2).1.2 := by
  let hattained :=
    profiledOpenActiveLaneWitnessedLeftClassAttained_of_live_mem A strategy
      hwin basis initialCode candidates candidate hcandidate hlive hmember
  unfold profiledOpenActiveLaneWitnessedLeftValueForClass
  rw [dif_pos hattained,
    profiledOpenActiveLeftFixedValueOfWinning_family]
  change candidate.2 ∈
    profiledOpenActiveLeftProjectedClass A strategy hwin basis initialCode
      (Classical.choose hattained)
  rw [(Classical.choose_spec hattained).1]
  rcases exists_profiledOpenActiveLaneWitnessedLeftAnchor A strategy hwin basis
      initialCode candidate hlive.2 hmember with
    ⟨source, hdescriptor, hsourceClass⟩
  have hcurrent :=
    profiledOpenActiveLeftControlledDescriptor_mem_projectedClass A strategy
      hwin basis initialCode source
  rw [hdescriptor, hsourceClass] at hcurrent
  exact hcurrent

theorem profiledOpenActiveLaneWitnessedRightValueForClass_hasReanchoredRows
    (candidates : Finset (WitnessedCandidate A initialCode))
    (sideClass : WitnessedClass A initialCode)
    (hattained : ProfiledOpenActiveLaneWitnessedRightClassAttained A strategy
      hwin basis initialCode candidates sideClass) :
    ProfiledOpenFixedRightValueHasReanchoredRows A strategy hwin basis
      initialCode
      (profiledOpenActiveLaneWitnessedRightValueForClass A strategy hwin basis
        initialCode candidates sideClass) := by
  unfold profiledOpenActiveLaneWitnessedRightValueForClass
  rw [dif_pos hattained]
  exact profiledOpenActiveRightFixedValueOfWinning_hasReanchoredRows A strategy
    hwin basis initialCode (Classical.choose hattained)

theorem profiledOpenActiveLaneWitnessedLeftValueForClass_hasReanchoredRows
    (candidates : Finset (WitnessedCandidate A initialCode))
    (sideClass : WitnessedClass A initialCode)
    (hattained : ProfiledOpenActiveLaneWitnessedLeftClassAttained A strategy
      hwin basis initialCode candidates sideClass) :
    ProfiledOpenFixedLeftValueHasReanchoredRows A strategy hwin basis
      initialCode
      (profiledOpenActiveLaneWitnessedLeftValueForClass A strategy hwin basis
        initialCode candidates sideClass) := by
  unfold profiledOpenActiveLaneWitnessedLeftValueForClass
  rw [dif_pos hattained]
  exact profiledOpenActiveLeftFixedValueOfWinning_hasReanchoredRows A strategy
    hwin basis initialCode (Classical.choose hattained)

/-! ## Candidate-wide common bank -/

theorem profiledOpenActiveLaneWitnessedSidewiseBank_commonMove
    (candidates : Finset (WitnessedCandidate A initialCode)) :
    RelationalCandidateCommonMove
      (WitnessedLive A strategy hwin basis initialCode)
      (ProfiledOpenFixedSidewiseReanchoredCandidateValid A strategy hwin basis
        initialCode)
      candidates
      (profiledOpenActiveLaneWitnessedSidewiseBank A strategy hwin basis
        initialCode candidates) := by
  intro candidate hcandidate hlive
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro hmember
    exact profiledOpenActiveLaneWitnessedRightValueForClass_covers A strategy
      hwin basis initialCode candidates candidate hcandidate hlive hmember
  · intro hmember
    exact profiledOpenActiveLaneWitnessedLeftValueForClass_covers A strategy
      hwin basis initialCode candidates candidate hcandidate hlive hmember
  · intro hmember
    let hattained :=
      profiledOpenActiveLaneWitnessedRightClassAttained_of_live_mem A strategy
        hwin basis initialCode candidates candidate hcandidate hlive hmember
    exact
      profiledOpenActiveLaneWitnessedRightValueForClass_hasReanchoredRows A
        strategy hwin basis initialCode candidates candidate.1.1.1 hattained
  · intro hmember
    let hattained :=
      profiledOpenActiveLaneWitnessedLeftClassAttained_of_live_mem A strategy
        hwin basis initialCode candidates candidate hcandidate hlive hmember
    exact profiledOpenActiveLaneWitnessedLeftValueForClass_hasReanchoredRows A
      strategy hwin basis initialCode candidates candidate.1.1.2 hattained

/-- The witnessed public tags have one common finite sidewise bank on every
finite candidate set. -/
theorem profiledOpenActiveLaneWitnessed_commonMoveExists :
    RelationalCandidateCommonMoveExists
      (Family := WitnessedTaggedFamily A initialCode)
      (Descriptor := WitnessedDescriptor A initialCode)
      (Move := ProfiledOpenFixedSidewisePinnedBank A initialCode
        (WitnessedClass A initialCode) (WitnessedClass A initialCode))
      (WitnessedLive A strategy hwin basis initialCode)
      (ProfiledOpenFixedSidewiseReanchoredCandidateValid A strategy hwin basis
        initialCode) := by
  intro candidates _hactive
  exact ⟨profiledOpenActiveLaneWitnessedSidewiseBank A strategy hwin basis
      initialCode candidates,
    profiledOpenActiveLaneWitnessedSidewiseBank_commonMove A strategy hwin basis
      initialCode candidates⟩

/-- The family-in-descriptor source-aware encoding preserves the witnessed
common-bank theorem. -/
theorem profiledOpenActiveLaneWitnessed_encodedCommonMoveExists :
    RelationalCandidateCommonMoveExists
      (SourceAwareRelationalLive
        (WitnessedLive A strategy hwin basis initialCode))
      (SourceAwareRelationalCandidateValid
        (ProfiledOpenFixedSidewiseReanchoredCandidateValid A strategy hwin
          basis initialCode)) := by
  exact relationalCandidateCommonMoveExists_sourceAware
    (WitnessedLive A strategy hwin basis initialCode)
    (ProfiledOpenFixedSidewiseReanchoredCandidateValid A strategy hwin basis
      initialCode)
    (profiledOpenActiveLaneWitnessed_commonMoveExists A strategy hwin basis
      initialCode)

end

end DetParityAutomaton

end DistributedSynthesis
