/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenMixedSideQueryProvenance
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenConcretePinnedRealization
import DistributedSynthesis.Formalizations.Lemma.LemSidewiseRelationalCandidateSuccessor

/-!
# Pointed successors for the fixed sidewise pinned-bank alphabet

The fixed sidewise move is a pair of banks.  An oriented proof step must not
reconstruct a complete paired pinned move: on the right it evaluates only the
right value at the process-one class, and on the left only the left value at
the process-two class.  This file installs that interface at the relational
candidate-table boundary.

There are two deliberately explicit residuals.

* `ProfiledOpenFixedSidewiseSequentialAdjacency` says that the selected
  provenance controller is compatible with the literal semantic source on
  every active side.  Membership in the selected value's public family does
  not prove this by itself.
* `SidewiseOwnClassReadable` says that each process can compute its own bank
  class from its own finite local observation.  The proof-side actual
  candidate may not be used as a run-time bank index.

The theorem at the end proves all remaining successor plumbing from these
two semantic facts.  `IndexedLineageSide` is used only to state which
proof-side row is being checked.  It is not passed to either local class
reader and is not an observable leader or orientation bit.
-/

namespace DistributedSynthesis

universe i u v x y s oc tc lo ro

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

/-! ## A fixed query state for every one-side controller value -/

/-- A finite vector containing one right-controller query at every possible
fixed right value.  Selecting a coordinate later does not require a dependent
cast or a manufactured left controller over the same family. -/
noncomputable abbrev ProfiledOpenFixedRightPinnedBlockQueryBank :=
  ∀ value : ProfiledOpenFixedRightPinnedValue A initialCode,
    ProfiledOpenFixedRightPinnedBlockQuery A initialCode value

/-- Left mirror. -/
noncomputable abbrev ProfiledOpenFixedLeftPinnedBlockQueryBank :=
  ∀ value : ProfiledOpenFixedLeftPinnedValue A initialCode,
    ProfiledOpenFixedLeftPinnedBlockQuery A initialCode value

set_option synthInstance.maxHeartbeats 1600000 in
noncomputable instance : Fintype
    (ProfiledOpenFixedRightPinnedBlockQueryBank A initialCode) := by
  classical
  infer_instance

set_option synthInstance.maxHeartbeats 1600000 in
noncomputable instance : Fintype
    (ProfiledOpenFixedLeftPinnedBlockQueryBank A initialCode) := by
  classical
  infer_instance

/-- Both query vectors are carried symmetrically.  A proof-side oriented row
uses one coordinate; neither process is told which row the proof follows. -/
noncomputable abbrev ProfiledOpenFixedSidewisePinnedBlockQueryBank :=
  ProfiledOpenFixedRightPinnedBlockQueryBank A initialCode ×
    ProfiledOpenFixedLeftPinnedBlockQueryBank A initialCode

/-- Fixed relational query alphabet.  The first coordinate is a proof-side
lineage resolution, the second contains both controller-query vectors, and
the last is the already established finite semantic direction tag. -/
noncomputable abbrev ProfiledOpenFixedSidewisePointedQuery :=
  (IndexedLineageSide ×
      ProfiledOpenFixedSidewisePinnedBlockQueryBank A initialCode) ×
    ProfiledOpenIndexedFiniteDirectionTag A (I := I)

set_option synthInstance.maxHeartbeats 3200000 in
noncomputable instance : Fintype
    (ProfiledOpenFixedSidewisePointedQuery A initialCode) := by
  classical
  infer_instance

/-! ## Proof-side selection uses exactly one bank component -/

/-- The value and literal query selected at an oriented row. -/
noncomputable def profiledOpenFixedSidewiseActiveQuery
    {OneClass : Type oc} {TwoClass : Type tc}
    (family : SidewiseTaggedFamily OneClass TwoClass
      (ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I)
        initialCode))
    (bank : ProfiledOpenFixedSidewisePinnedBank A initialCode OneClass
      TwoClass)
    (query : ProfiledOpenFixedSidewisePointedQuery A initialCode) :
    (Sigma fun value : ProfiledOpenFixedRightPinnedValue A initialCode ↦
        ProfiledOpenFixedRightPinnedBlockQuery A initialCode value) ⊕
      (Sigma fun value : ProfiledOpenFixedLeftPinnedValue A initialCode ↦
        ProfiledOpenFixedLeftPinnedBlockQuery A initialCode value) :=
  match query.1.1 with
  | .right =>
      let value := bank.1 family.1.1
      Sum.inl ⟨value, query.1.2.1 value⟩
  | .left =>
      let value := bank.2 family.1.2
      Sum.inr ⟨value, query.1.2.2 value⟩

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledOpenFixedSidewiseActiveQuery_right
    {OneClass : Type oc} {TwoClass : Type tc}
    (family : SidewiseTaggedFamily OneClass TwoClass
      (ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I)
        initialCode))
    (bank : ProfiledOpenFixedSidewisePinnedBank A initialCode OneClass
      TwoClass)
    (queries : ProfiledOpenFixedSidewisePinnedBlockQueryBank A initialCode)
    (direction : ProfiledOpenIndexedFiniteDirectionTag A (I := I)) :
    profiledOpenFixedSidewiseActiveQuery A initialCode family bank
        ((.right, queries), direction) =
      Sum.inl ⟨bank.1 family.1.1, queries.1 (bank.1 family.1.1)⟩ :=
  rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledOpenFixedSidewiseActiveQuery_left
    {OneClass : Type oc} {TwoClass : Type tc}
    (family : SidewiseTaggedFamily OneClass TwoClass
      (ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I)
        initialCode))
    (bank : ProfiledOpenFixedSidewisePinnedBank A initialCode OneClass
      TwoClass)
    (queries : ProfiledOpenFixedSidewisePinnedBlockQueryBank A initialCode)
    (direction : ProfiledOpenIndexedFiniteDirectionTag A (I := I)) :
    profiledOpenFixedSidewiseActiveQuery A initialCode family bank
        ((.left, queries), direction) =
      Sum.inr ⟨bank.2 family.1.2, queries.2 (bank.2 family.1.2)⟩ :=
  rfl

/-! ## The operational own-class boundary -/

/-- Each fixed class must factor through the corresponding process's own
finite local observation.  No side/orientation argument is available to
either reader. -/
def SidewiseOwnClassReadable
    {Global : Type*} {OneClass : Type oc} {TwoClass : Type tc}
    {OneObservation : Type lo} {TwoObservation : Type ro}
    (oneObservation : Global → OneObservation)
    (twoObservation : Global → TwoObservation)
    (oneClass : Global → OneClass)
    (twoClass : Global → TwoClass) : Prop :=
  (∃ readOne : OneObservation → OneClass,
      ∀ candidate, readOne (oneObservation candidate) = oneClass candidate) ∧
    ∃ readTwo : TwoObservation → TwoClass,
      ∀ candidate, readTwo (twoObservation candidate) = twoClass candidate

/-- A local reader forces own-side class homogeneity on every observation
fibre.  This is the safe way to use a class-indexed bank operationally. -/
theorem sidewiseOwnClass_homogeneous_of_readable
    {Global : Type*} {OneClass : Type oc} {TwoClass : Type tc}
    {OneObservation : Type lo} {TwoObservation : Type ro}
    (oneObservation : Global → OneObservation)
    (twoObservation : Global → TwoObservation)
    (oneClass : Global → OneClass)
    (twoClass : Global → TwoClass)
    (hreadable : SidewiseOwnClassReadable oneObservation twoObservation
      oneClass twoClass) :
    (∀ left right, oneObservation left = oneObservation right →
        oneClass left = oneClass right) ∧
      ∀ left right, twoObservation left = twoObservation right →
        twoClass left = twoClass right := by
  rcases hreadable with ⟨⟨readOne, hone⟩, ⟨readTwo, htwo⟩⟩
  constructor
  · intro left right hobs
    rw [← hone left, ← hone right, hobs]
  · intro left right hobs
    rw [← htwo left, ← htwo right, hobs]

/-! ## Strong fixed-value provenance -/

set_option maxHeartbeats 1600000 in
/-- Universe-pinned right projection of the literal strong dispatcher. -/
noncomputable def profiledOpenOptionalStrongRightValue
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode) :
    ProfiledOpenFixedRightPinnedValue A initialCode :=
  let move :=
    profiledOpenOptionalFixedPinnedSemanticMoveOfWinning.{i, u, v, x, y, s,
      max i u v x y s, max i u v x y s} A strategy hwin basis initialCode
      (fun _ ↦ point.2) point.1
  move.rightValue A initialCode

set_option maxHeartbeats 1600000 in
/-- Universe-pinned left projection. -/
noncomputable def profiledOpenOptionalStrongLeftValue
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode) :
    ProfiledOpenFixedLeftPinnedValue A initialCode :=
  let move :=
    profiledOpenOptionalFixedPinnedSemanticMoveOfWinning.{i, u, v, x, y, s,
      max i u v x y s, max i u v x y s} A strategy hwin basis initialCode
      (fun _ ↦ point.2) point.1
  move.leftValue A initialCode

/-- A right fixed value is literally the right projection of one strong
optional dispatcher.  The semantic anchor is proof data; it is not stored in
the fixed value. -/
def ProfiledOpenFixedRightValueHasDispatcherProvenance
    (value : ProfiledOpenFixedRightPinnedValue A initialCode) : Prop :=
  ∃ point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode,
    value = profiledOpenOptionalStrongRightValue A strategy hwin basis
      initialCode point

/-- Left mirror. -/
def ProfiledOpenFixedLeftValueHasDispatcherProvenance
    (value : ProfiledOpenFixedLeftPinnedValue A initialCode) : Prop :=
  ∃ point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode,
    value = profiledOpenOptionalStrongLeftValue A strategy hwin basis
      initialCode point

theorem profiledOpenFixedRightValue_hasProvenance
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode) :
    ProfiledOpenFixedRightValueHasDispatcherProvenance A strategy hwin basis
      initialCode
      (profiledOpenOptionalStrongRightValue A strategy hwin basis initialCode
        point) :=
  ⟨point, rfl⟩

theorem profiledOpenFixedLeftValue_hasProvenance
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode) :
    ProfiledOpenFixedLeftValueHasDispatcherProvenance A strategy hwin basis
      initialCode
      (profiledOpenOptionalStrongLeftValue A strategy hwin basis initialCode
        point) :=
  ⟨point, rfl⟩

/-- Candidate validity strengthened only at the two coordinates actually
selected by this candidate's class tags.  Unused bank entries need no
semantic witness. -/
def ProfiledOpenFixedSidewiseProvenanceCandidateValid
    {OneClass : Type oc} {TwoClass : Type tc}
    (descriptor : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode)
    (family : SidewiseTaggedFamily OneClass TwoClass
      (ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I)
        initialCode))
    (bank : ProfiledOpenFixedSidewisePinnedBank A initialCode OneClass
      TwoClass) : Prop :=
  ProfiledOpenFixedSidewiseCandidateValid A initialCode descriptor family
      bank ∧
    (descriptor ∈ family.2.1 →
      ProfiledOpenFixedRightValueHasDispatcherProvenance A strategy hwin basis
        initialCode (bank.1 family.1.1)) ∧
    (descriptor ∈ family.2.2 →
      ProfiledOpenFixedLeftValueHasDispatcherProvenance A strategy hwin basis
        initialCode (bank.2 family.1.2))

/-! ## Semantic liveness and the exact adjacency premise -/

/-- Concrete optional liveness, enriched by an arbitrary invariant on the
sticky side tags. -/
def ProfiledOpenFixedSidewiseSemanticLive
    {OneClass : Type oc} {TwoClass : Type tc}
    (TagInvariant :
      ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode →
        SidewiseTaggedFamily OneClass TwoClass
          (ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I)
            initialCode) → Prop)
    (descriptor : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode)
    (family : SidewiseTaggedFamily OneClass TwoClass
      (ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I)
        initialCode)) : Prop :=
  ProfiledOpenOptionalPointedSemanticLive A strategy hwin basis initialCode
      descriptor family.2 ∧
    TagInvariant descriptor family

/-- The selected fixed controller must be sequentially compatible with the
literal semantic source whenever its side is active.  This is stronger than
set membership in the controller's advertised family and is the only new
semantic premise used by the successor theorem below. -/
def ProfiledOpenFixedSidewiseSequentialAdjacency
    {OneClass : Type oc} {TwoClass : Type tc}
    (RightAdjacent :
      ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin basis
          initialCode →
        ProfiledOpenFixedRightPinnedValue A initialCode → Prop)
    (LeftAdjacent :
      ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin basis
          initialCode →
        ProfiledOpenFixedLeftPinnedValue A initialCode → Prop) : Prop :=
  ∀ state
      (family : SidewiseTaggedFamily OneClass TwoClass
        (ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I)
          initialCode))
      (bank : ProfiledOpenFixedSidewisePinnedBank A initialCode OneClass
        TwoClass),
    profiledOpenOptionalControlledFamilyOf A strategy hwin basis initialCode
        state = family.2 →
    ProfiledOpenFixedSidewiseProvenanceCandidateValid A strategy hwin basis
        initialCode
        (profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy
          hwin basis initialCode state) family bank →
      ((profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy
            hwin basis initialCode state) ∈ family.2.1 →
        RightAdjacent state (bank.1 family.1.1)) ∧
      ((profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy
            hwin basis initialCode state) ∈ family.2.2 →
        LeftAdjacent state (bank.2 family.1.2))

/-- At one proof-side orientation, consume only the corresponding adjacency
coordinate.  An inactive coordinate imposes no fake semantic row. -/
def ProfiledOpenFixedActiveSequentialAdjacency
    {OneClass : Type oc} {TwoClass : Type tc}
    (RightAdjacent :
      ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin basis
          initialCode →
        ProfiledOpenFixedRightPinnedValue A initialCode → Prop)
    (LeftAdjacent :
      ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin basis
          initialCode →
        ProfiledOpenFixedLeftPinnedValue A initialCode → Prop)
    (state : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode)
    (family : SidewiseTaggedFamily OneClass TwoClass
      (ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I)
        initialCode))
    (bank : ProfiledOpenFixedSidewisePinnedBank A initialCode OneClass
      TwoClass) : IndexedLineageSide → Prop
  | .right =>
      (profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
          basis initialCode state) ∈ family.2.1 →
        RightAdjacent state (bank.1 family.1.1)
  | .left =>
      (profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
          basis initialCode state) ∈ family.2.2 →
        LeftAdjacent state (bank.2 family.1.2)

/-! ## Exact relational edge -/

/-- The concrete semantic successor ignores the controller-query vectors and
uses the already proved finite direction component. -/
noncomputable def profiledOpenFixedSidewiseSemanticNext
    (state : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode)
    (query : ProfiledOpenFixedSidewisePointedQuery A initialCode) :
    ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin basis
      initialCode :=
  profiledOpenIndexedOptionalControlledSemanticNext A strategy hwin basis
    initialCode state query.2

/-- A relational edge retains the exact semantic source family, the selected
one-side adjacency witness, and the contextual target tags. -/
def ProfiledOpenFixedSidewisePointedExactEdge
    {OneClass : Type oc} {TwoClass : Type tc}
    (TagInvariant :
      ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode →
        SidewiseTaggedFamily OneClass TwoClass
          (ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I)
            initialCode) → Prop)
    (RightAdjacent :
      ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin basis
          initialCode →
        ProfiledOpenFixedRightPinnedValue A initialCode → Prop)
    (LeftAdjacent :
      ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin basis
          initialCode →
        ProfiledOpenFixedLeftPinnedValue A initialCode → Prop)
    (targetTag :
      ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode →
        ProfiledOpenFixedSidewisePinnedBank A initialCode OneClass TwoClass →
        ProfiledOpenFixedSidewisePointedQuery A initialCode →
        ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I) initialCode →
        ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode →
        OneClass × TwoClass)
    (source : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode)
    (bank : ProfiledOpenFixedSidewisePinnedBank A initialCode OneClass
      TwoClass)
    (query : ProfiledOpenFixedSidewisePointedQuery A initialCode)
    (targetFamily : SidewiseTaggedFamily OneClass TwoClass
      (ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I)
        initialCode))
    (target : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode) : Prop :=
  ∃ state sourceFamily,
    profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis initialCode state = source ∧
    profiledOpenOptionalControlledFamilyOf A strategy hwin basis initialCode
        state = sourceFamily.2 ∧
    TagInvariant source sourceFamily ∧
    ProfiledOpenFixedSidewiseProvenanceCandidateValid A strategy hwin basis
        initialCode source sourceFamily bank ∧
    ProfiledOpenFixedActiveSequentialAdjacency A strategy hwin basis
        initialCode RightAdjacent LeftAdjacent state sourceFamily bank
        query.1.1 ∧
    profiledOpenOptionalControlledFamilyOf A strategy hwin basis initialCode
        (profiledOpenFixedSidewiseSemanticNext A strategy hwin basis
          initialCode state query) = targetFamily.2 ∧
    profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis initialCode
        (profiledOpenFixedSidewiseSemanticNext A strategy hwin basis
          initialCode state query) = target ∧
    targetFamily.1 = targetTag source bank query targetFamily.2 target

/-- Literal DPA control update used by the relational candidate table. -/
def ProfiledOpenFixedSidewiseControlStep
    (source target : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode) : Prop :=
  target.control =
    (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).step
      source.control target.code

/-! ## Complete one-step coverage -/

/-- Once active-side sequential adjacency and target-tag preservation are
proved, the fixed sidewise bank supplies the complete live successor law for
the relational candidate table.  No complete paired pinned move is
reconstructed at the edge. -/
theorem profiledOpenFixedSidewisePointed_liveSuccessorCoverage
    {OneClass : Type oc} {TwoClass : Type tc}
    (TagInvariant :
      ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode →
        SidewiseTaggedFamily OneClass TwoClass
          (ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I)
            initialCode) → Prop)
    (RightAdjacent :
      ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin basis
          initialCode →
        ProfiledOpenFixedRightPinnedValue A initialCode → Prop)
    (LeftAdjacent :
      ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin basis
          initialCode →
        ProfiledOpenFixedLeftPinnedValue A initialCode → Prop)
    (targetTag :
      ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode →
        ProfiledOpenFixedSidewisePinnedBank A initialCode OneClass TwoClass →
        ProfiledOpenFixedSidewisePointedQuery A initialCode →
        ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I) initialCode →
        ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode →
        OneClass × TwoClass)
    (hadjacent : ProfiledOpenFixedSidewiseSequentialAdjacency
      (OneClass := OneClass) (TwoClass := TwoClass) A strategy hwin basis
      initialCode RightAdjacent LeftAdjacent)
    (htag : ∀ source bank query family target,
      TagInvariant target ((targetTag source bank query family target),
        family)) :
    RelationalCandidateLiveSuccessorCoverage
      (ProfiledOpenFixedSidewiseSemanticLive A strategy hwin basis initialCode
        TagInvariant)
      (ProfiledOpenFixedSidewiseProvenanceCandidateValid A strategy hwin basis
        initialCode)
      (ProfiledOpenFixedSidewisePointedExactEdge A strategy hwin basis
        initialCode TagInvariant RightAdjacent LeftAdjacent targetTag)
      (ProfiledOpenFixedSidewiseControlStep A initialCode) := by
  intro source bank query hlive hvalid
  rcases hlive.1 with ⟨state, hsource, hsourceFamily⟩
  have hvalidState :
      ProfiledOpenFixedSidewiseProvenanceCandidateValid A strategy hwin basis
        initialCode
        (profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy
          hwin basis initialCode state) source.1 bank := by
    simpa only [hsource] using hvalid
  have hadj := hadjacent state source.1 bank hsourceFamily hvalidState
  let child := profiledOpenFixedSidewiseSemanticNext A strategy hwin basis
    initialCode state query
  let target :=
    profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
      basis initialCode child
  let family :=
    profiledOpenOptionalControlledFamilyOf A strategy hwin basis initialCode
      child
  let taggedFamily : SidewiseTaggedFamily OneClass TwoClass
      (ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I)
        initialCode) :=
    (targetTag source.2 bank query family target, family)
  refine ⟨(taggedFamily, target), ?_, ?_⟩
  · constructor
    · refine ⟨state, source.1, hsource, hsourceFamily, hlive.2, hvalid,
          ?_, rfl, rfl, rfl⟩
      cases query.1.1 with
      | right => exact hadj.1
      | left => exact hadj.2
    · change target.control =
        (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).step
          source.2.control target.code
      rw [← hsource]
      exact profiledOpenIndexedOptionalControlledSemanticNext_control A
        strategy hwin basis initialCode state query.2
  · constructor
    · exact ⟨child, rfl, rfl⟩
    · exact htag source.2 bank query family target

end

end DetParityAutomaton

end DistributedSynthesis
