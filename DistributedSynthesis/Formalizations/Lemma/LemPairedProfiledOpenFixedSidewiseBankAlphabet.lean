/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenOptionalFixedPinnedFamily
import DistributedSynthesis.Formalizations.Lemma.LemSidewiseRelationalCandidateCommonMove

/-!
# A strategy-independent fixed alphabet of sidewise pinned banks

The semantic fibre bank is a useful extraction object, but its dependent
controller types mention the realizing strategy and its semantic sources.
It therefore cannot itself be the move alphabet of the single summary
automaton quantified before the realizing strategy in `ReadbackUpgrade`.

This file defines the fixed operational codomain.  A right value is a sigma
package containing one finite public descriptor family, its finite root
record table, and its certified right pinned controller.  The left value is
the mirror.  A sidewise bank is a finite function from each process's fixed
local-class type to the corresponding fixed value.  All of these types depend
only on the objective-side finite alphabets and `initialCode`, never on a
realizing strategy.

Candidate compatibility is componentwise.  A right-active candidate need
only be covered by the right family selected at its process-one class; the
left side is checked independently.  It does not require the two selected
values to advertise one common full family.  This is precisely what the old
complete sigma move could not express.

The construction does not yet prove that a sticky class tag selects the
semantically correct values.  That is the remaining model adapter, and is
kept separate from this finite-alphabet fact.  No graph, orientation, lane,
or strict-leader bit is part of a bank index.
-/

namespace DistributedSynthesis

universe i u v x y s oc tc

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

variable (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
variable {OneClass : Type oc} {TwoClass : Type tc}

/-! ## Fixed one-side values -/

/-- One source-independent right pinned controller value.  Its family and
root-record table are finite runtime data, not semantic witnesses. -/
noncomputable def profiledOpenFixedRightPinnedValueRaw :=
  Σ family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A
      (I := I) initialCode,
    Σ expected : ProfiledOpenHiddenDescriptorRightExpected A family,
      ProfiledOpenHiddenDescriptorRightPinnedFamilyMove A family expected

/-- The raw dependent sigma acquires one phantom universe parameter from the
root-family controller interface.  Pin it once here, so every occurrence in
the operational alphabet is definitionally the same finite type. -/
noncomputable abbrev ProfiledOpenFixedRightPinnedValue :=
  profiledOpenFixedRightPinnedValueRaw.{i, u, v, x, y, s,
    max i u v x y s} A initialCode

/-- Left mirror. -/
noncomputable def profiledOpenFixedLeftPinnedValueRaw :=
  Σ family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A
      (I := I) initialCode,
    Σ expected : ProfiledOpenHiddenDescriptorLeftExpected A family,
      ProfiledOpenHiddenDescriptorLeftPinnedFamilyMove A family expected

/-- Left mirror with the same phantom universe pinned. -/
noncomputable abbrev ProfiledOpenFixedLeftPinnedValue :=
  profiledOpenFixedLeftPinnedValueRaw.{i, u, v, x, y, s,
    max i u v x y s} A initialCode

set_option synthInstance.maxHeartbeats 800000 in
noncomputable instance : Fintype
    (ProfiledOpenFixedRightPinnedValue A initialCode) := by
  classical
  change Fintype
    (Σ family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A
        (I := I) initialCode,
      Σ expected : ProfiledOpenHiddenDescriptorRightExpected A family,
        ProfiledOpenHiddenDescriptorRightPinnedFamilyMove A family expected)
  infer_instance

set_option synthInstance.maxHeartbeats 800000 in
noncomputable instance : Fintype
    (ProfiledOpenFixedLeftPinnedValue A initialCode) := by
  classical
  change Fintype
    (Σ family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A
        (I := I) initialCode,
      Σ expected : ProfiledOpenHiddenDescriptorLeftExpected A family,
        ProfiledOpenHiddenDescriptorLeftPinnedFamilyMove A family expected)
  infer_instance

/-- Forget the unused left half of a complete fixed move, retaining the
literal right controller and its root records. -/
noncomputable def ProfiledOpenHiddenDescriptorPairedPinnedFamilyMove.rightValue
    (move : ProfiledOpenHiddenDescriptorPairedPinnedFamilyMove A initialCode) :
    ProfiledOpenFixedRightPinnedValue A initialCode :=
  ⟨move.1, move.2.1, move.2.2.2.1⟩

/-- Forget the unused right half. -/
noncomputable def ProfiledOpenHiddenDescriptorPairedPinnedFamilyMove.leftValue
    (move : ProfiledOpenHiddenDescriptorPairedPinnedFamilyMove A initialCode) :
    ProfiledOpenFixedLeftPinnedValue A initialCode :=
  ⟨move.1, move.2.2.1, move.2.2.2.2⟩

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem ProfiledOpenHiddenDescriptorPairedPinnedFamilyMove.rightValue_family
    (move : ProfiledOpenHiddenDescriptorPairedPinnedFamilyMove A initialCode) :
    (move.rightValue A initialCode).1 = move.1 :=
  rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem ProfiledOpenHiddenDescriptorPairedPinnedFamilyMove.leftValue_family
    (move : ProfiledOpenHiddenDescriptorPairedPinnedFamilyMove A initialCode) :
    (move.leftValue A initialCode).1 = move.1 :=
  rfl

/-! ## The fixed sidewise bank -/

/-- One process-local value at every fixed process-one class and,
independently, one at every process-two class. -/
noncomputable abbrev ProfiledOpenFixedSidewisePinnedBank
    (OneClass : Type oc) (TwoClass : Type tc) :=
  (OneClass → ProfiledOpenFixedRightPinnedValue A initialCode) ×
    (TwoClass → ProfiledOpenFixedLeftPinnedValue A initialCode)

set_option synthInstance.maxHeartbeats 800000 in
noncomputable instance [Fintype OneClass] [Fintype TwoClass] : Fintype
    (ProfiledOpenFixedSidewisePinnedBank A initialCode OneClass TwoClass) := by
  classical
  infer_instance

/-- The sink supplies a harmless total value for unused right classes.  Its
construction may use the given winner to inhabit classified output types,
but the returned value belongs to the strategy-independent fixed type. -/
noncomputable def profiledOpenFixedDefaultRightPinnedValue
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis) :
    ProfiledOpenFixedRightPinnedValue A initialCode :=
  ⟨profiledOpenOptionalSinkFamilyCode A (I := I) initialCode,
    profiledOpenOptionalSinkRightExpected A (I := I) initialCode,
    profiledOpenOptionalSinkEmptyRightMove A strategy hwin basis initialCode⟩

/-- Harmless left-class fallback. -/
noncomputable def profiledOpenFixedDefaultLeftPinnedValue
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis) :
    ProfiledOpenFixedLeftPinnedValue A initialCode :=
  ⟨profiledOpenOptionalSinkFamilyCode A (I := I) initialCode,
    profiledOpenOptionalSinkLeftExpected A (I := I) initialCode,
    profiledOpenOptionalSinkEmptyLeftMove A strategy hwin basis initialCode⟩

/-- A total default bank used only on inactive/unattained classes. -/
noncomputable def profiledOpenFixedDefaultSidewisePinnedBank
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
  (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis) :
    ProfiledOpenFixedSidewisePinnedBank A initialCode OneClass TwoClass :=
  (fun _ ↦ profiledOpenFixedDefaultRightPinnedValue A initialCode strategy
      hwin basis,
    fun _ ↦ profiledOpenFixedDefaultLeftPinnedValue A initialCode strategy
      hwin basis)

/-! ## Componentwise candidate compatibility -/

/-- Right-local coverage of one old public family by one fixed right value. -/
def ProfiledOpenFixedRightCandidateValid
    (descriptor : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode)
    (family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I)
      initialCode)
    (move : ProfiledOpenFixedRightPinnedValue A initialCode) : Prop :=
  descriptor ∈ family.1 → descriptor ∈ move.1.1

/-- Left-local mirror. -/
def ProfiledOpenFixedLeftCandidateValid
    (descriptor : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode)
    (family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I)
      initialCode)
    (move : ProfiledOpenFixedLeftPinnedValue A initialCode) : Prop :=
  descriptor ∈ family.2 → descriptor ∈ move.1.2

/-- A fixed sidewise bank covers every active coordinate of a candidate.
The two implications are independent, so a right-only or left-only candidate
does not require an invented descriptor on the inactive side. -/
def ProfiledOpenFixedSidewiseCandidateValid
    {OneClass : Type oc} {TwoClass : Type tc}
    (descriptor : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode)
    (family : SidewiseTaggedFamily OneClass TwoClass
      (ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I)
        initialCode))
    (bank : ProfiledOpenFixedSidewisePinnedBank A initialCode OneClass
      TwoClass) : Prop :=
  ProfiledOpenFixedRightCandidateValid A initialCode descriptor family.2
      (bank.1 family.1.1) ∧
    ProfiledOpenFixedLeftCandidateValid A initialCode descriptor family.2
      (bank.2 family.1.2)

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

/-- The concrete componentwise predicate is exactly the generic sidewise
candidate predicate at the two fixed one-side alphabets. -/
theorem profiledOpenFixedSidewiseCandidateValid_eq_generic
    {OneClass : Type oc} {TwoClass : Type tc}
    (descriptor : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode)
    (family : SidewiseTaggedFamily OneClass TwoClass
      (ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I)
        initialCode))
    (bank : ProfiledOpenFixedSidewisePinnedBank A initialCode OneClass
      TwoClass) :
    ProfiledOpenFixedSidewiseCandidateValid A initialCode descriptor family
        bank ↔
      SidewiseCandidateValid
        (ProfiledOpenFixedRightCandidateValid A initialCode)
        (ProfiledOpenFixedLeftCandidateValid A initialCode)
        descriptor family bank :=
  Iff.rfl

/-- At the fixed operational alphabet, the relational-table common-move law
is equivalent to the honest per-process classwise controller obligation. -/
theorem profiledOpenFixedSidewiseCommonMoveExists_iff
    {OneClass : Type oc} {TwoClass : Type tc}
    (Live : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
        initialCode →
      ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I)
        initialCode → Prop) :
    RelationalCandidateCommonMoveExists
        (Family := SidewiseTaggedFamily OneClass TwoClass
          (ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I)
            initialCode))
        (Descriptor := ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
          initialCode)
        (Move := ProfiledOpenFixedSidewisePinnedBank A initialCode OneClass
          TwoClass)
        (fun descriptor family ↦ Live descriptor family.2)
        (ProfiledOpenFixedSidewiseCandidateValid A initialCode) ↔
      SidewiseClasswiseMovesExist
        (OneClass := OneClass) (TwoClass := TwoClass)
        (Family := ProfiledOpenIndexedHiddenDescriptorFamilyCode A
          (I := I) initialCode)
        (Descriptor := ProfiledOpenIndexedOldMoveHiddenDescriptor A
          (I := I) initialCode)
        (OneMove := ProfiledOpenFixedRightPinnedValue A initialCode)
        (TwoMove := ProfiledOpenFixedLeftPinnedValue A initialCode)
        Live
        (ProfiledOpenFixedRightCandidateValid A initialCode)
        (ProfiledOpenFixedLeftCandidateValid A initialCode) := by
  constructor
  · intro hcommon candidates hactive
    obtain ⟨bank, hbank⟩ := hcommon candidates hactive
    constructor
    · intro oneClass
      refine ⟨bank.1 oneClass, ?_⟩
      intro candidate hcandidate hlive hclass
      have hvalid := hbank candidate hcandidate hlive
      simpa only [ProfiledOpenFixedSidewiseCandidateValid, hclass] using
        hvalid.1
    · intro twoClass
      refine ⟨bank.2 twoClass, ?_⟩
      intro candidate hcandidate hlive hclass
      have hvalid := hbank candidate hcandidate hlive
      simpa only [ProfiledOpenFixedSidewiseCandidateValid, hclass] using
        hvalid.2
  · intro hclasswise candidates hactive
    obtain ⟨hone, htwo⟩ := hclasswise candidates hactive
    let oneBank : OneClass →
        ProfiledOpenFixedRightPinnedValue A initialCode := fun oneClass ↦
      Classical.choose (hone oneClass)
    let twoBank : TwoClass →
        ProfiledOpenFixedLeftPinnedValue A initialCode := fun twoClass ↦
      Classical.choose (htwo twoClass)
    refine ⟨(oneBank, twoBank), ?_⟩
    intro candidate hcandidate hlive
    constructor
    · exact Classical.choose_spec (hone candidate.1.1.1) candidate
        hcandidate hlive rfl
    · exact Classical.choose_spec (htwo candidate.1.1.2) candidate
        hcandidate hlive rfl

/-- Projecting one complete move into constant sidewise banks is valid for
every candidate covered by that move's advertised family.  This lemma is a
sanity check; the positive mixed-family construction will use nonconstant
banks. -/
theorem profiledOpenFixedSidewiseCandidateValid_of_pairedMove
    {OneClass : Type oc} {TwoClass : Type tc}
    (move : ProfiledOpenHiddenDescriptorPairedPinnedFamilyMove A initialCode)
    (descriptor : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode)
    (oneClass : OneClass) (twoClass : TwoClass) :
    ProfiledOpenFixedSidewiseCandidateValid A initialCode descriptor
      ((oneClass, twoClass), move.1)
      ((fun _ ↦ move.rightValue A initialCode),
        fun _ ↦ move.leftValue A initialCode) := by
  exact ⟨fun hmem ↦ hmem, fun hmem ↦ hmem⟩

end

end

end DetParityAutomaton

end DistributedSynthesis
