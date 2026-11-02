/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenFixedSidewiseBankAlphabet
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenConcretePinnedRealization

/-!
# Componentwise common moves indexed by the two public fibre coordinates

The old complete pinned move cannot cover live candidates with different full
two-fibre families.  At the weaker componentwise interface, however, the
family itself already supplies two honest finite local classes: its right and
left `Finset` coordinates.

For every attained right coordinate we choose one live anchor, construct its
strong provenance-preserving complete move, and retain only its right pinned
value.  Every right-active candidate with that coordinate is covered by
membership.  The left bank is built independently.  Empty classes use the
fixed defaults.  This proves the weak `RelationalCandidateCommonMoveExists`
premise without finite-image reflection, raw-sender factorization, a selected
global descriptor, orientation, or leader information.

The result is candidate-wide *table validity*, not yet an executable local
readback.  A runtime process must either have its own finite summary determine
its own family coordinate (equivalently, its process-local candidate set is
homogeneous on that coordinate) or use a consumer of the whole bank that never
selects an actual hidden candidate.  The global candidate set may contain
several classes; the theorem does not make one of them observable.

This is deliberately not a joint-provenance theorem.  The independently
chosen right and left values need not be projections of one complete pinned
move at a candidate.  `ProfiledOpenFixedCoordinatePairedProvenance` names
that exact additional condition, so componentwise coverage cannot be mistaken
for sibling-output or joint-DPA-word compatibility.
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

private abbrev CoordinateDescriptor :=
  ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode

private abbrev CoordinateFamily :=
  ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I) initialCode

/-- The fixed side-class alphabet is one finite set of hidden descriptors.
The same carrier is used independently on the two processes. -/
abbrev ProfiledOpenFixedCoordinateSideClass :=
  Finset (CoordinateDescriptor A initialCode)

noncomputable local instance coordinateDescriptorDecidableEq :
    DecidableEq (CoordinateDescriptor A initialCode) :=
  Classical.decEq _

noncomputable instance : Fintype
    (ProfiledOpenFixedCoordinateSideClass A initialCode) := by
  classical
  infer_instance

/-- Canonical enrichment of a full two-fibre family by its two coordinates. -/
def profiledOpenFixedCoordinateTaggedFamily
    (family : CoordinateFamily A initialCode) :
    SidewiseTaggedFamily
      (ProfiledOpenFixedCoordinateSideClass A initialCode)
      (ProfiledOpenFixedCoordinateSideClass A initialCode)
      (CoordinateFamily A initialCode) :=
  ((family.1, family.2), family)

/-- A tagged family carries exactly its own two finite coordinates. -/
def ProfiledOpenFixedCoordinateTagsCorrect
    (family : SidewiseTaggedFamily
      (ProfiledOpenFixedCoordinateSideClass A initialCode)
      (ProfiledOpenFixedCoordinateSideClass A initialCode)
      (CoordinateFamily A initialCode)) : Prop :=
  family.1.1 = family.2.1 ∧ family.1.2 = family.2.2

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledOpenFixedCoordinateTaggedFamily_tagsCorrect
    (family : CoordinateFamily A initialCode) :
    ProfiledOpenFixedCoordinateTagsCorrect A initialCode
      (profiledOpenFixedCoordinateTaggedFamily A initialCode family) := by
  exact ⟨rfl, rfl⟩

/-- Pointed semantic liveness together with the canonical coordinate tags. -/
noncomputable def ProfiledOpenFixedCoordinateTaggedLive
    (descriptor : CoordinateDescriptor A initialCode)
    (family : SidewiseTaggedFamily
      (ProfiledOpenFixedCoordinateSideClass A initialCode)
      (ProfiledOpenFixedCoordinateSideClass A initialCode)
      (CoordinateFamily A initialCode)) : Prop :=
  ProfiledOpenOptionalPointedSemanticLive A strategy hwin basis initialCode
      descriptor family.2 ∧
    ProfiledOpenFixedCoordinateTagsCorrect A initialCode family

@[simp] theorem profiledOpenFixedCoordinateTaggedFamily_live_iff
    (descriptor : CoordinateDescriptor A initialCode)
    (family : CoordinateFamily A initialCode) :
    ProfiledOpenFixedCoordinateTaggedLive A strategy hwin basis initialCode
        descriptor
        (profiledOpenFixedCoordinateTaggedFamily A initialCode family) ↔
      ProfiledOpenOptionalPointedSemanticLive A strategy hwin basis
        initialCode descriptor family := by
  simp only [ProfiledOpenFixedCoordinateTaggedLive,
    profiledOpenFixedCoordinateTaggedFamily,
    ProfiledOpenFixedCoordinateTagsCorrect, and_self, and_true]

/-! ## One strong fixed value from one live anchor -/

/-- Right projection of the strong complete move supplied by a live anchor. -/
noncomputable def profiledOpenFixedRightValueOfLive
    {descriptor : CoordinateDescriptor A initialCode}
    {family : CoordinateFamily A initialCode}
    (hlive : ProfiledOpenOptionalPointedSemanticLive A strategy hwin basis
      initialCode descriptor family) :
    ProfiledOpenFixedRightPinnedValue A initialCode :=
  let point := Classical.choose hlive
  let move :=
    profiledOpenOptionalFixedPinnedSemanticMoveOfWinning.{i, u, v, x, y, s,
      max i u v x y s, max i u v x y s} A strategy hwin basis initialCode
      (fun _ ↦ point.2) point.1
  move.rightValue A initialCode

/-- Left projection of the same anchor construction. -/
noncomputable def profiledOpenFixedLeftValueOfLive
    {descriptor : CoordinateDescriptor A initialCode}
    {family : CoordinateFamily A initialCode}
    (hlive : ProfiledOpenOptionalPointedSemanticLive A strategy hwin basis
      initialCode descriptor family) :
    ProfiledOpenFixedLeftPinnedValue A initialCode :=
  let point := Classical.choose hlive
  let move :=
    profiledOpenOptionalFixedPinnedSemanticMoveOfWinning.{i, u, v, x, y, s,
      max i u v x y s, max i u v x y s} A strategy hwin basis initialCode
      (fun _ ↦ point.2) point.1
  move.leftValue A initialCode

/-- The right anchor value advertises literally the anchor's full family. -/
theorem profiledOpenFixedRightValueOfLive_family
    {descriptor : CoordinateDescriptor A initialCode}
    {family : CoordinateFamily A initialCode}
    (hlive : ProfiledOpenOptionalPointedSemanticLive A strategy hwin basis
      initialCode descriptor family) :
    (profiledOpenFixedRightValueOfLive A strategy hwin basis initialCode
      hlive).1 = family := by
  let point := Classical.choose hlive
  have hpoint := Classical.choose_spec hlive
  change
    (profiledOpenOptionalFixedPinnedSemanticMoveOfWinning.{i, u, v, x, y, s,
      max i u v x y s, max i u v x y s} A strategy hwin basis initialCode
      (fun _ ↦ point.2)
      point.1).1 = family
  have huniv :
      (profiledOpenOptionalFixedPinnedSemanticMoveOfWinning.{i, u, v, x, y,
        s, max i u v x y s, max i u v x y s} A strategy hwin basis
        initialCode (fun _ ↦ point.2) point.1).1 =
      (profiledOpenOptionalFixedPinnedSemanticMoveOfWinning.{i, u, v, x, y,
        s, 0, 0} A strategy hwin basis initialCode (fun _ ↦ point.2)
        point.1).1 := by
    unfold profiledOpenOptionalFixedPinnedSemanticMoveOfWinning
    generalize hbank :
      profiledOpenIndexedOptionalSourceFibreProvenanceBankOfWinning A strategy
        hwin basis
        (profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
          initialCode (fun _ ↦ point.2)) point.1 = bank
    cases bank <;> rfl
  exact huniv.trans
    ((profiledOpenOptionalPinnedPublicFamilyAgreement A strategy hwin basis
      initialCode point).trans hpoint.2)

/-- Left anchor value has the same advertised family. -/
theorem profiledOpenFixedLeftValueOfLive_family
    {descriptor : CoordinateDescriptor A initialCode}
    {family : CoordinateFamily A initialCode}
    (hlive : ProfiledOpenOptionalPointedSemanticLive A strategy hwin basis
      initialCode descriptor family) :
    (profiledOpenFixedLeftValueOfLive A strategy hwin basis initialCode
      hlive).1 = family := by
  let point := Classical.choose hlive
  have hpoint := Classical.choose_spec hlive
  change
    (profiledOpenOptionalFixedPinnedSemanticMoveOfWinning.{i, u, v, x, y, s,
      max i u v x y s, max i u v x y s} A strategy hwin basis initialCode
      (fun _ ↦ point.2)
      point.1).1 = family
  have huniv :
      (profiledOpenOptionalFixedPinnedSemanticMoveOfWinning.{i, u, v, x, y,
        s, max i u v x y s, max i u v x y s} A strategy hwin basis
        initialCode (fun _ ↦ point.2) point.1).1 =
      (profiledOpenOptionalFixedPinnedSemanticMoveOfWinning.{i, u, v, x, y,
        s, 0, 0} A strategy hwin basis initialCode (fun _ ↦ point.2)
        point.1).1 := by
    unfold profiledOpenOptionalFixedPinnedSemanticMoveOfWinning
    generalize hbank :
      profiledOpenIndexedOptionalSourceFibreProvenanceBankOfWinning A strategy
        hwin basis
        (profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
          initialCode (fun _ ↦ point.2)) point.1 = bank
    cases bank <;> rfl
  exact huniv.trans
    ((profiledOpenOptionalPinnedPublicFamilyAgreement A strategy hwin basis
      initialCode point).trans hpoint.2)

/-! ## Coordinate-indexed anchor selection -/

private abbrev CoordinateTaggedCandidate :=
  RelationalFamilyCandidate
    (SidewiseTaggedFamily
      (ProfiledOpenFixedCoordinateSideClass A initialCode)
      (ProfiledOpenFixedCoordinateSideClass A initialCode)
      (CoordinateFamily A initialCode))
    (CoordinateDescriptor A initialCode)

/-- A right class is attained when a live right-active candidate in that
class occurs in the current finite set. -/
def ProfiledOpenFixedRightCoordinateAttained
    (candidates : Finset (CoordinateTaggedCandidate A initialCode))
    (sideClass : ProfiledOpenFixedCoordinateSideClass A initialCode) : Prop :=
  ∃ candidate ∈ candidates,
    ProfiledOpenFixedCoordinateTaggedLive A strategy hwin basis initialCode
        candidate.2 candidate.1 ∧
      candidate.2 ∈ candidate.1.2.1 ∧ candidate.1.1.1 = sideClass

/-- Left-active mirror. -/
def ProfiledOpenFixedLeftCoordinateAttained
    (candidates : Finset (CoordinateTaggedCandidate A initialCode))
    (sideClass : ProfiledOpenFixedCoordinateSideClass A initialCode) : Prop :=
  ∃ candidate ∈ candidates,
    ProfiledOpenFixedCoordinateTaggedLive A strategy hwin basis initialCode
        candidate.2 candidate.1 ∧
      candidate.2 ∈ candidate.1.2.2 ∧ candidate.1.1.2 = sideClass

/-- Strategy-dependent proof that one fixed right value is literally the
projection of a strong dispatcher at a live anchor of the requested class.
The value type itself remains strategy-independent. -/
def ProfiledOpenFixedRightValueHasProvenance
    (sideClass : ProfiledOpenFixedCoordinateSideClass A initialCode)
    (value : ProfiledOpenFixedRightPinnedValue A initialCode) : Prop :=
  ∃ descriptor : CoordinateDescriptor A initialCode,
    ∃ family : CoordinateFamily A initialCode,
      ∃ hlive : ProfiledOpenOptionalPointedSemanticLive A strategy hwin basis
          initialCode descriptor family,
        family.1 = sideClass ∧
          value = profiledOpenFixedRightValueOfLive A strategy hwin basis
            initialCode hlive

/-- Left one-side provenance. -/
def ProfiledOpenFixedLeftValueHasProvenance
    (sideClass : ProfiledOpenFixedCoordinateSideClass A initialCode)
    (value : ProfiledOpenFixedLeftPinnedValue A initialCode) : Prop :=
  ∃ descriptor : CoordinateDescriptor A initialCode,
    ∃ family : CoordinateFamily A initialCode,
      ∃ hlive : ProfiledOpenOptionalPointedSemanticLive A strategy hwin basis
          initialCode descriptor family,
        family.2 = sideClass ∧
          value = profiledOpenFixedLeftValueOfLive A strategy hwin basis
            initialCode hlive

/-- Select the strong right projection at an attained class and the fixed
default at an unattained class. -/
noncomputable def profiledOpenFixedRightValueForCoordinate
    (candidates : Finset (CoordinateTaggedCandidate A initialCode))
    (sideClass : ProfiledOpenFixedCoordinateSideClass A initialCode) :
    ProfiledOpenFixedRightPinnedValue A initialCode := by
  classical
  exact if h : ProfiledOpenFixedRightCoordinateAttained A strategy hwin basis
      initialCode candidates sideClass then
    let anchor := Classical.choose h
    let hanchor := Classical.choose_spec h
    profiledOpenFixedRightValueOfLive A strategy hwin basis initialCode
      hanchor.2.1.1
  else
    profiledOpenFixedDefaultRightPinnedValue A initialCode strategy hwin basis

/-- Left coordinate selector. -/
noncomputable def profiledOpenFixedLeftValueForCoordinate
    (candidates : Finset (CoordinateTaggedCandidate A initialCode))
    (sideClass : ProfiledOpenFixedCoordinateSideClass A initialCode) :
    ProfiledOpenFixedLeftPinnedValue A initialCode := by
  classical
  exact if h : ProfiledOpenFixedLeftCoordinateAttained A strategy hwin basis
      initialCode candidates sideClass then
    let anchor := Classical.choose h
    let hanchor := Classical.choose_spec h
    profiledOpenFixedLeftValueOfLive A strategy hwin basis initialCode
      hanchor.2.1.1
  else
    profiledOpenFixedDefaultLeftPinnedValue A initialCode strategy hwin basis

/-- The fixed sidewise bank selected from one finite candidate set. -/
noncomputable def profiledOpenFixedCoordinateSidewiseBank
    (candidates : Finset (CoordinateTaggedCandidate A initialCode)) :
    ProfiledOpenFixedSidewisePinnedBank A initialCode
      (ProfiledOpenFixedCoordinateSideClass A initialCode)
      (ProfiledOpenFixedCoordinateSideClass A initialCode) :=
  (profiledOpenFixedRightValueForCoordinate A strategy hwin basis initialCode
      candidates,
    profiledOpenFixedLeftValueForCoordinate A strategy hwin basis initialCode
      candidates)

/-- Every live right-active member is covered by the value at its canonical
right coordinate. -/
theorem profiledOpenFixedRightValueForCoordinate_covers
    (candidates : Finset (CoordinateTaggedCandidate A initialCode))
    (candidate : CoordinateTaggedCandidate A initialCode)
    (hcandidate : candidate ∈ candidates)
    (hlive : ProfiledOpenFixedCoordinateTaggedLive A strategy hwin basis
      initialCode candidate.2 candidate.1)
    (hmember : candidate.2 ∈ candidate.1.2.1) :
    candidate.2 ∈
      (profiledOpenFixedRightValueForCoordinate A strategy hwin basis
        initialCode candidates candidate.1.1.1).1.1 := by
  let hattained : ProfiledOpenFixedRightCoordinateAttained A strategy hwin
      basis initialCode candidates candidate.1.1.1 :=
    ⟨candidate, hcandidate, hlive, hmember, rfl⟩
  unfold profiledOpenFixedRightValueForCoordinate
  rw [dif_pos hattained]
  let anchor := Classical.choose hattained
  have hanchor := Classical.choose_spec hattained
  have hfamily := profiledOpenFixedRightValueOfLive_family A strategy hwin
    basis initialCode hanchor.2.1.1
  rw [hfamily]
  have hanchorClass : anchor.1.2.1 = candidate.1.1.1 :=
    hanchor.2.1.2.1.symm.trans hanchor.2.2.2
  rw [hanchorClass, hlive.2.1]
  exact hmember

/-- Left coverage. -/
theorem profiledOpenFixedLeftValueForCoordinate_covers
    (candidates : Finset (CoordinateTaggedCandidate A initialCode))
    (candidate : CoordinateTaggedCandidate A initialCode)
    (hcandidate : candidate ∈ candidates)
    (hlive : ProfiledOpenFixedCoordinateTaggedLive A strategy hwin basis
      initialCode candidate.2 candidate.1)
    (hmember : candidate.2 ∈ candidate.1.2.2) :
    candidate.2 ∈
      (profiledOpenFixedLeftValueForCoordinate A strategy hwin basis
        initialCode candidates candidate.1.1.2).1.2 := by
  let hattained : ProfiledOpenFixedLeftCoordinateAttained A strategy hwin
      basis initialCode candidates candidate.1.1.2 :=
    ⟨candidate, hcandidate, hlive, hmember, rfl⟩
  unfold profiledOpenFixedLeftValueForCoordinate
  rw [dif_pos hattained]
  let anchor := Classical.choose hattained
  have hanchor := Classical.choose_spec hattained
  have hfamily := profiledOpenFixedLeftValueOfLive_family A strategy hwin
    basis initialCode hanchor.2.1.1
  rw [hfamily]
  have hanchorClass : anchor.1.2.2 = candidate.1.1.2 :=
    hanchor.2.1.2.2.symm.trans hanchor.2.2.2
  rw [hanchorClass, hlive.2.2]
  exact hmember

/-- Every attained right-bank component carries a live strong-dispatcher
provenance witness, not merely a membership proof. -/
theorem profiledOpenFixedRightValueForCoordinate_hasProvenance
    (candidates : Finset (CoordinateTaggedCandidate A initialCode))
    (sideClass : ProfiledOpenFixedCoordinateSideClass A initialCode)
    (hattained : ProfiledOpenFixedRightCoordinateAttained A strategy hwin
      basis initialCode candidates sideClass) :
    ProfiledOpenFixedRightValueHasProvenance A strategy hwin basis initialCode
      sideClass
      (profiledOpenFixedRightValueForCoordinate A strategy hwin basis
        initialCode candidates sideClass) := by
  unfold profiledOpenFixedRightValueForCoordinate
  rw [dif_pos hattained]
  let anchor := Classical.choose hattained
  have hanchor := Classical.choose_spec hattained
  refine ⟨anchor.2, anchor.1.2, hanchor.2.1.1, ?_, rfl⟩
  exact hanchor.2.1.2.1.symm.trans hanchor.2.2.2

/-- Left provenance mirror. -/
theorem profiledOpenFixedLeftValueForCoordinate_hasProvenance
    (candidates : Finset (CoordinateTaggedCandidate A initialCode))
    (sideClass : ProfiledOpenFixedCoordinateSideClass A initialCode)
    (hattained : ProfiledOpenFixedLeftCoordinateAttained A strategy hwin
      basis initialCode candidates sideClass) :
    ProfiledOpenFixedLeftValueHasProvenance A strategy hwin basis initialCode
      sideClass
      (profiledOpenFixedLeftValueForCoordinate A strategy hwin basis
        initialCode candidates sideClass) := by
  unfold profiledOpenFixedLeftValueForCoordinate
  rw [dif_pos hattained]
  let anchor := Classical.choose hattained
  have hanchor := Classical.choose_spec hattained
  refine ⟨anchor.2, anchor.1.2, hanchor.2.1.1, ?_, rfl⟩
  exact hanchor.2.1.2.2.symm.trans hanchor.2.2.2

/-! ## Weak componentwise common-move theorem -/

/-- The family-coordinate bank is simultaneously componentwise-valid for
every live candidate in the set.  This is exactly the current weak fixed-bank
predicate: each active descriptor is covered by the selected one-side value. -/
theorem profiledOpenFixedCoordinateSidewiseBank_commonMove
    (candidates : Finset (CoordinateTaggedCandidate A initialCode)) :
    RelationalCandidateCommonMove
      (ProfiledOpenFixedCoordinateTaggedLive A strategy hwin basis initialCode)
      (ProfiledOpenFixedSidewiseCandidateValid A initialCode)
      candidates
      (profiledOpenFixedCoordinateSidewiseBank A strategy hwin basis
        initialCode candidates) := by
  intro candidate hcandidate hlive
  constructor
  · intro hmember
    exact profiledOpenFixedRightValueForCoordinate_covers A strategy hwin
      basis initialCode candidates candidate hcandidate hlive hmember
  · intro hmember
    exact profiledOpenFixedLeftValueForCoordinate_covers A strategy hwin
      basis initialCode candidates candidate hcandidate hlive hmember

/-- Hence the weak relational-table common-move premise is unconditional at
the two family-coordinate class alphabets.  This statement constructs one
whole bank as a table move; it does not assert that a runtime process can yet
select its own bank component from its finite local summary. -/
theorem profiledOpenFixedCoordinate_commonMoveExists :
    RelationalCandidateCommonMoveExists
      (Family := SidewiseTaggedFamily
        (ProfiledOpenFixedCoordinateSideClass A initialCode)
        (ProfiledOpenFixedCoordinateSideClass A initialCode)
        (CoordinateFamily A initialCode))
      (Descriptor := CoordinateDescriptor A initialCode)
      (Move := ProfiledOpenFixedSidewisePinnedBank A initialCode
        (ProfiledOpenFixedCoordinateSideClass A initialCode)
        (ProfiledOpenFixedCoordinateSideClass A initialCode))
      (ProfiledOpenFixedCoordinateTaggedLive A strategy hwin basis initialCode)
      (ProfiledOpenFixedSidewiseCandidateValid A initialCode) := by
  intro candidates _hactive
  exact ⟨profiledOpenFixedCoordinateSidewiseBank A strategy hwin basis
      initialCode candidates,
    profiledOpenFixedCoordinateSidewiseBank_commonMove A strategy hwin basis
      initialCode candidates⟩

/-! ## Runtime coordinate-selection boundary -/

/-- On a process-one local candidate set, all live right-active possibilities
carry the same right coordinate.  This is the exact homogeneity needed if the
runtime implementation selects one bank component rather than consuming the
whole bank extensionally. -/
def ProfiledOpenFixedRightCoordinateHomogeneous
    (candidates : Finset (CoordinateTaggedCandidate A initialCode)) : Prop :=
  ∀ left ∈ candidates,
    ProfiledOpenFixedCoordinateTaggedLive A strategy hwin basis initialCode
        left.2 left.1 →
      left.2 ∈ left.1.2.1 →
        ∀ right ∈ candidates,
          ProfiledOpenFixedCoordinateTaggedLive A strategy hwin basis
              initialCode right.2 right.1 →
            right.2 ∈ right.1.2.1 → left.1.1.1 = right.1.1.1

/-- Process-two mirror. -/
def ProfiledOpenFixedLeftCoordinateHomogeneous
    (candidates : Finset (CoordinateTaggedCandidate A initialCode)) : Prop :=
  ∀ left ∈ candidates,
    ProfiledOpenFixedCoordinateTaggedLive A strategy hwin basis initialCode
        left.2 left.1 →
      left.2 ∈ left.1.2.2 →
        ∀ right ∈ candidates,
          ProfiledOpenFixedCoordinateTaggedLive A strategy hwin basis
              initialCode right.2 right.1 →
            right.2 ∈ right.1.2.2 → left.1.1.2 = right.1.1.2

/-- The explicit local-summary/runtime-selection residual.  It is not a
consequence of candidate-wide common table validity and must be preserved by
the concrete process-local summary transition, unless the eventual bank
consumer avoids component selection altogether. -/
def ProfiledOpenFixedCoordinateLocallySelectable
    (candidatesOne candidatesTwo :
      Finset (CoordinateTaggedCandidate A initialCode)) : Prop :=
  ProfiledOpenFixedRightCoordinateHomogeneous A strategy hwin basis
      initialCode candidatesOne ∧
    ProfiledOpenFixedLeftCoordinateHomogeneous A strategy hwin basis
      initialCode candidatesTwo

/-! ## Exact local-fibre candidate sets are homogeneous

The following construction is the positive half of the runtime-selection
boundary.  Starting from one literal live-fresh semantic anchor, form the
finite set of all finite tagged candidates represented by a semantic point in
the anchor's exact process-local fibre.  The corresponding family coordinate
is constant on this set.  Only the forward law
`semanticTwoFibreCode_fst/snd_eq_of_rel` is used; no equality of finite images
is reflected back into an exact-view relation. -/

/-- The canonical finite tagged candidate exposed by one literal live-fresh
semantic point and one proof-side parity-control assignment. -/
noncomputable def profiledOpenFixedCoordinateCandidateOf
    (control : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
        (I := I) →
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)
    (point : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I)) :
    CoordinateTaggedCandidate A initialCode :=
  let descriptor :=
    profiledOpenFixedPinnedSemanticDescriptor A strategy hwin basis
      initialCode control point
  let family :=
    profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
      control point
  (profiledOpenFixedCoordinateTaggedFamily A initialCode family, descriptor)

/-- All finite candidates represented inside one exact process-one local
fibre.  The semantic carrier may be infinite; the image is materialized by
filtering the already finite candidate alphabet. -/
noncomputable def profiledOpenFixedRightLocalCandidates
    (control : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
        (I := I) →
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)
    (anchor : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I)) :
    Finset (CoordinateTaggedCandidate A initialCode) := by
  classical
  exact Finset.univ.filter fun candidate =>
    ∃ point : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
        (I := I),
      ProfiledOpenIndexedProcessOneLocalFibreRel A strategy hwin basis
          anchor point ∧
        candidate = profiledOpenFixedCoordinateCandidateOf A strategy hwin
          basis initialCode control point

/-- Process-two mirror. -/
noncomputable def profiledOpenFixedLeftLocalCandidates
    (control : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
        (I := I) →
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)
    (anchor : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I)) :
    Finset (CoordinateTaggedCandidate A initialCode) := by
  classical
  exact Finset.univ.filter fun candidate =>
    ∃ point : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
        (I := I),
      ProfiledOpenIndexedProcessTwoLocalFibreRel A strategy hwin basis
          anchor point ∧
        candidate = profiledOpenFixedCoordinateCandidateOf A strategy hwin
          basis initialCode control point

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Any two candidates in one exact process-one local-fibre image carry the
same right family coordinate. -/
theorem profiledOpenFixedRightLocalCandidates_coordinate_eq
    (control : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
        (I := I) →
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)
    (anchor : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I))
    {left right : CoordinateTaggedCandidate A initialCode}
    (hleft : left ∈ profiledOpenFixedRightLocalCandidates A strategy hwin
      basis initialCode control anchor)
    (hright : right ∈ profiledOpenFixedRightLocalCandidates A strategy hwin
      basis initialCode control anchor) :
    left.1.1.1 = right.1.1.1 := by
  classical
  rw [profiledOpenFixedRightLocalCandidates, Finset.mem_filter] at hleft hright
  rcases hleft.2 with ⟨leftPoint, hleftRel, rfl⟩
  rcases hright.2 with ⟨rightPoint, hrightRel, rfl⟩
  change
    (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
      control leftPoint).1 =
    (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
      control rightPoint).1
  unfold profiledOpenFixedPinnedFamilyCode
  exact
    (semanticTwoFibreCode_fst_eq_of_rel
      (profiledOpenFixedPinnedSemanticDescriptor A strategy hwin basis
        initialCode control)
      (ProfiledOpenIndexedProcessOneLocalFibreRel A strategy hwin basis)
      (ProfiledOpenIndexedProcessTwoLocalFibreRel A strategy hwin basis)
      (profiledOpenIndexedProcessOneLocalFibreRel_fibresAgree A strategy hwin
        basis) hleftRel).symm.trans
      (semanticTwoFibreCode_fst_eq_of_rel
        (profiledOpenFixedPinnedSemanticDescriptor A strategy hwin basis
          initialCode control)
        (ProfiledOpenIndexedProcessOneLocalFibreRel A strategy hwin basis)
        (ProfiledOpenIndexedProcessTwoLocalFibreRel A strategy hwin basis)
        (profiledOpenIndexedProcessOneLocalFibreRel_fibresAgree A strategy hwin
          basis) hrightRel)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Any two candidates in one exact process-two local-fibre image carry the
same left family coordinate. -/
theorem profiledOpenFixedLeftLocalCandidates_coordinate_eq
    (control : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
        (I := I) →
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)
    (anchor : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I))
    {left right : CoordinateTaggedCandidate A initialCode}
    (hleft : left ∈ profiledOpenFixedLeftLocalCandidates A strategy hwin
      basis initialCode control anchor)
    (hright : right ∈ profiledOpenFixedLeftLocalCandidates A strategy hwin
      basis initialCode control anchor) :
    left.1.1.2 = right.1.1.2 := by
  classical
  rw [profiledOpenFixedLeftLocalCandidates, Finset.mem_filter] at hleft hright
  rcases hleft.2 with ⟨leftPoint, hleftRel, rfl⟩
  rcases hright.2 with ⟨rightPoint, hrightRel, rfl⟩
  change
    (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
      control leftPoint).2 =
    (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
      control rightPoint).2
  unfold profiledOpenFixedPinnedFamilyCode
  exact
    (semanticTwoFibreCode_snd_eq_of_rel
      (profiledOpenFixedPinnedSemanticDescriptor A strategy hwin basis
        initialCode control)
      (ProfiledOpenIndexedProcessOneLocalFibreRel A strategy hwin basis)
      (ProfiledOpenIndexedProcessTwoLocalFibreRel A strategy hwin basis)
      (profiledOpenIndexedProcessTwoLocalFibreRel_fibresAgree A strategy hwin
        basis) hleftRel).symm.trans
      (semanticTwoFibreCode_snd_eq_of_rel
        (profiledOpenFixedPinnedSemanticDescriptor A strategy hwin basis
          initialCode control)
        (ProfiledOpenIndexedProcessOneLocalFibreRel A strategy hwin basis)
        (ProfiledOpenIndexedProcessTwoLocalFibreRel A strategy hwin basis)
        (profiledOpenIndexedProcessTwoLocalFibreRel_fibresAgree A strategy hwin
          basis) hrightRel)

/-- Therefore an exact process-one local-fibre candidate set is runtime
homogeneous on the coordinate selected by process one. -/
theorem profiledOpenFixedRightLocalCandidates_homogeneous
    (control : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
        (I := I) →
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)
    (anchor : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I)) :
    ProfiledOpenFixedRightCoordinateHomogeneous A strategy hwin basis
      initialCode
      (profiledOpenFixedRightLocalCandidates A strategy hwin basis initialCode
        control anchor) := by
  intro left hleft _hlive _hactive right hright _hrlive _hractive
  exact profiledOpenFixedRightLocalCandidates_coordinate_eq A strategy hwin
    basis initialCode control anchor hleft hright

/-- Process-two mirror. -/
theorem profiledOpenFixedLeftLocalCandidates_homogeneous
    (control : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
        (I := I) →
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)
    (anchor : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I)) :
    ProfiledOpenFixedLeftCoordinateHomogeneous A strategy hwin basis
      initialCode
      (profiledOpenFixedLeftLocalCandidates A strategy hwin basis initialCode
        control anchor) := by
  intro left hleft _hlive _hactive right hright _hrlive _hractive
  exact profiledOpenFixedLeftLocalCandidates_coordinate_eq A strategy hwin
    basis initialCode control anchor hleft hright

/-- Completeness of the semantic fibre enumeration is unnecessary: any
finite operational candidate set contained in one process-one exact fibre is
already homogeneous on the process-one coordinate. -/
theorem profiledOpenFixedRightCoordinateHomogeneous_of_subset_localCandidates
    (control : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
        (I := I) →
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)
    (anchor : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I))
    (candidates : Finset (CoordinateTaggedCandidate A initialCode))
    (hsubset : candidates ⊆
      profiledOpenFixedRightLocalCandidates A strategy hwin basis initialCode
        control anchor) :
    ProfiledOpenFixedRightCoordinateHomogeneous A strategy hwin basis
      initialCode candidates := by
  intro left hleft _hlive _hactive right hright _hrlive _hractive
  exact profiledOpenFixedRightLocalCandidates_coordinate_eq A strategy hwin
    basis initialCode control anchor (hsubset hleft) (hsubset hright)

/-- Process-two subset form. -/
theorem profiledOpenFixedLeftCoordinateHomogeneous_of_subset_localCandidates
    (control : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
        (I := I) →
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)
    (anchor : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I))
    (candidates : Finset (CoordinateTaggedCandidate A initialCode))
    (hsubset : candidates ⊆
      profiledOpenFixedLeftLocalCandidates A strategy hwin basis initialCode
        control anchor) :
    ProfiledOpenFixedLeftCoordinateHomogeneous A strategy hwin basis
      initialCode candidates := by
  intro left hleft _hlive _hactive right hright _hrlive _hractive
  exact profiledOpenFixedLeftLocalCandidates_coordinate_eq A strategy hwin
    basis initialCode control anchor (hsubset hleft) (hsubset hright)

/-- Two sidewise operational candidate sets are locally selectable as soon as
each is contained in the appropriate exact semantic fibre. -/
theorem profiledOpenFixedCoordinateLocallySelectable_of_subset_localCandidates
    (control : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
        (I := I) →
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)
    (anchorOne anchorTwo :
      ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis (I := I))
    (candidatesOne candidatesTwo :
      Finset (CoordinateTaggedCandidate A initialCode))
    (hsubsetOne : candidatesOne ⊆
      profiledOpenFixedRightLocalCandidates A strategy hwin basis initialCode
        control anchorOne)
    (hsubsetTwo : candidatesTwo ⊆
      profiledOpenFixedLeftLocalCandidates A strategy hwin basis initialCode
        control anchorTwo) :
    ProfiledOpenFixedCoordinateLocallySelectable A strategy hwin basis
      initialCode candidatesOne candidatesTwo := by
  exact
    ⟨profiledOpenFixedRightCoordinateHomogeneous_of_subset_localCandidates A
        strategy hwin basis initialCode control anchorOne candidatesOne
        hsubsetOne,
      profiledOpenFixedLeftCoordinateHomogeneous_of_subset_localCandidates A
        strategy hwin basis initialCode control anchorTwo candidatesTwo
        hsubsetTwo⟩

/-! ## The deliberately separate paired-provenance residual -/

/-- At one candidate, the two selected bank components really are the two
projections of one strong complete dispatcher whose family is the candidate's
family.  This is stronger than componentwise coverage and is the exact extra
fact needed by any consumer that combines both sides into one sibling round or
one joint DPA-word provenance argument. -/
def ProfiledOpenFixedCoordinatePairedProvenance
    (descriptor : CoordinateDescriptor A initialCode)
    (family : SidewiseTaggedFamily
      (ProfiledOpenFixedCoordinateSideClass A initialCode)
      (ProfiledOpenFixedCoordinateSideClass A initialCode)
      (CoordinateFamily A initialCode))
    (bank : ProfiledOpenFixedSidewisePinnedBank A initialCode
      (ProfiledOpenFixedCoordinateSideClass A initialCode)
      (ProfiledOpenFixedCoordinateSideClass A initialCode)) : Prop :=
  ∃ point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin
      basis initialCode,
    profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis initialCode point = descriptor ∧
      profiledOpenOptionalControlledFamilyOf A strategy hwin basis initialCode
          point = family.2 ∧
      let move :=
        profiledOpenOptionalFixedPinnedSemanticMoveOfWinning.{i, u, v, x, y,
          s, max i u v x y s, max i u v x y s} A strategy hwin basis
          initialCode (fun _ ↦ point.2) point.1
      move.1 = family.2 ∧
        bank.1 family.1.1 = move.rightValue A initialCode ∧
        bank.2 family.1.2 = move.leftValue A initialCode

/-- Candidate-set form of the paired-provenance residual. -/
def ProfiledOpenFixedCoordinateBankPairedProvenance
    (candidates : Finset (CoordinateTaggedCandidate A initialCode))
    (bank : ProfiledOpenFixedSidewisePinnedBank A initialCode
      (ProfiledOpenFixedCoordinateSideClass A initialCode)
      (ProfiledOpenFixedCoordinateSideClass A initialCode)) : Prop :=
  ∀ candidate ∈ candidates,
    ProfiledOpenFixedCoordinateTaggedLive A strategy hwin basis initialCode
        candidate.2 candidate.1 →
      ProfiledOpenFixedCoordinatePairedProvenance A strategy hwin basis
        initialCode candidate.2 candidate.1 bank

/-- Paired provenance is sufficient for the weak componentwise validity at
that candidate.  The converse is intentionally not claimed. -/
theorem profiledOpenFixedSidewiseCandidateValid_of_pairedProvenance
    (descriptor : CoordinateDescriptor A initialCode)
    (family : SidewiseTaggedFamily
      (ProfiledOpenFixedCoordinateSideClass A initialCode)
      (ProfiledOpenFixedCoordinateSideClass A initialCode)
      (CoordinateFamily A initialCode))
    (bank : ProfiledOpenFixedSidewisePinnedBank A initialCode
      (ProfiledOpenFixedCoordinateSideClass A initialCode)
      (ProfiledOpenFixedCoordinateSideClass A initialCode))
    (hpaired : ProfiledOpenFixedCoordinatePairedProvenance A strategy hwin
      basis initialCode descriptor family bank) :
    ProfiledOpenFixedSidewiseCandidateValid A initialCode descriptor family
      bank := by
  rcases hpaired with ⟨point, _hdescriptor, _hfamily, hmoveFamily,
    hright, hleft⟩
  constructor
  · intro hmember
    rw [hright, ProfiledOpenHiddenDescriptorPairedPinnedFamilyMove.rightValue_family,
      hmoveFamily]
    exact hmember
  · intro hmember
    rw [hleft, ProfiledOpenHiddenDescriptorPairedPinnedFamilyMove.leftValue_family,
      hmoveFamily]
    exact hmember

end

end DetParityAutomaton

end DistributedSynthesis
