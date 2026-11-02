/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenFixedSidewiseBankAlphabet
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenFixedPinnedProvenance
import DistributedSynthesis.Formalizations.Lemma.LemSemanticChildFamilyFactorization

/-!
# Independent provenance for the two sides of a fixed pinned bank

The fixed sidewise bank may select its right and left controller values from
different semantic anchors.  This file isolates the operational fact needed
for that use: a right block evaluates only the right pinned controller, and a
left block evaluates only the left pinned controller.  Their query
reachability and semantic-table witnesses are therefore componentwise.

`ProfiledOpenFixedMixedQueryRowsFaithful` deliberately permits different
public families, expected-record tables, controllers, semantic sources, and
semantic pasts on the two sides.  The proof-side `IndexedLineageSide` case
split below does not add an observable orientation or strict-leader signal to
either process.  Sequential compatibility is a separate obligation: the
active row must install an exact opposite-side successor.  It is expressed by
the relational `ExactEdge`/successor layer, not by a joint provenance witness
for the two inactive-at-once controller coordinates.
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

variable (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))

/-! ## One-side operational queries -/

/-- The query carried by a fixed right value, without manufacturing a left
coordinate over the same family. -/
noncomputable abbrev ProfiledOpenFixedRightPinnedBlockQuery
    (value : ProfiledOpenFixedRightPinnedValue A initialCode) :=
  ProfiledOpenHiddenDescriptorRightPinnedBlockQuery A value.1 value.2.1
    value.2.2

/-- Left mirror. -/
noncomputable abbrev ProfiledOpenFixedLeftPinnedBlockQuery
    (value : ProfiledOpenFixedLeftPinnedValue A initialCode) :=
  ProfiledOpenHiddenDescriptorLeftPinnedBlockQuery A value.1 value.2.1
    value.2.2

/-- The literal response row read from one fixed right controller/query. -/
noncomputable def profiledOpenFixedRightQueryResponses
    (value : ProfiledOpenFixedRightPinnedValue A initialCode)
    (query : ProfiledOpenFixedRightPinnedBlockQuery A initialCode value)
    (descriptor : ProfiledOpenHiddenDescriptorRightCarrier A value.1) :
    ((ProfiledOpenHiddenDescriptorRightRoot A descriptor.1 × In₂) × In₁) →
      ProfiledOpenRightClassifiedOutput A :=
  fun input =>
    ((value.2.2.1.toTransitionRationalTree.labelOf query.1).2 query.2)
      ((Sigma.mk descriptor input.1.1, input.1.2), input.2)

/-- Literal left response row. -/
noncomputable def profiledOpenFixedLeftQueryResponses
    (value : ProfiledOpenFixedLeftPinnedValue A initialCode)
    (query : ProfiledOpenFixedLeftPinnedBlockQuery A initialCode value)
    (descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A value.1) :
    ((ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1 × In₁) × In₂) →
      ProfiledOpenLeftClassifiedOutput A :=
  fun input =>
    ((value.2.2.1.toTransitionRationalTree.labelOf query.1).2 query.2)
      ((Sigma.mk descriptor input.1.1, input.1.2), input.2)

/-- The right controller coordinate is reached by one actual blind-sender
word. -/
def ProfiledOpenFixedRightQueryReachable
    (value : ProfiledOpenFixedRightPinnedValue A initialCode)
    (query : ProfiledOpenFixedRightPinnedBlockQuery A initialCode value) : Prop :=
  ∃ word : List In₁,
    value.2.2.1.toTransitionRationalTree.controlAt word = query.1

/-- Left reachability. -/
def ProfiledOpenFixedLeftQueryReachable
    (value : ProfiledOpenFixedLeftPinnedValue A initialCode)
    (query : ProfiledOpenFixedLeftPinnedBlockQuery A initialCode value) : Prop :=
  ∃ word : List In₂,
    value.2.2.1.toTransitionRationalTree.controlAt word = query.1

/-- Same-controller semantic provenance for one right row. -/
def ProfiledOpenFixedRightQueryRowFaithful
    (value : ProfiledOpenFixedRightPinnedValue A initialCode)
    (query : ProfiledOpenFixedRightPinnedBlockQuery A initialCode value)
    (Allowed : ∀ descriptor :
        ProfiledOpenHiddenDescriptorRightCarrier A value.1,
      (((ProfiledOpenHiddenDescriptorRightRoot A descriptor.1 × In₂) ×
          In₁) → ProfiledOpenRightClassifiedOutput A) → Prop) : Prop :=
  ∃ word : List In₁,
    value.2.2.1.toTransitionRationalTree.controlAt word = query.1 ∧
      ∀ descriptor,
        Allowed descriptor
          (profiledOpenFixedRightQueryResponses A initialCode value query
            descriptor)

/-- Same-controller semantic provenance for one left row. -/
def ProfiledOpenFixedLeftQueryRowFaithful
    (value : ProfiledOpenFixedLeftPinnedValue A initialCode)
    (query : ProfiledOpenFixedLeftPinnedBlockQuery A initialCode value)
    (Allowed : ∀ descriptor :
        ProfiledOpenHiddenDescriptorLeftCarrier A value.1,
      (((ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1 × In₁) ×
          In₂) → ProfiledOpenLeftClassifiedOutput A) → Prop) : Prop :=
  ∃ word : List In₂,
    value.2.2.1.toTransitionRationalTree.controlAt word = query.1 ∧
      ∀ descriptor,
        Allowed descriptor
          (profiledOpenFixedLeftQueryResponses A initialCode value query
            descriptor)

/-! ## Mixed-family packaging -/

/-- The exact paired row obligation for a sidewise bank.  No common family,
controller, semantic anchor, or semantic past is a field. -/
structure ProfiledOpenFixedMixedQueryRowsFaithful
    (rightValue : ProfiledOpenFixedRightPinnedValue A initialCode)
    (rightQuery : ProfiledOpenFixedRightPinnedBlockQuery A initialCode
      rightValue)
    (leftValue : ProfiledOpenFixedLeftPinnedValue A initialCode)
    (leftQuery : ProfiledOpenFixedLeftPinnedBlockQuery A initialCode leftValue)
    (RightAllowed : ∀ descriptor :
        ProfiledOpenHiddenDescriptorRightCarrier A rightValue.1,
      (((ProfiledOpenHiddenDescriptorRightRoot A descriptor.1 × In₂) ×
          In₁) → ProfiledOpenRightClassifiedOutput A) → Prop)
    (LeftAllowed : ∀ descriptor :
        ProfiledOpenHiddenDescriptorLeftCarrier A leftValue.1,
      (((ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1 × In₁) ×
          In₂) → ProfiledOpenLeftClassifiedOutput A) → Prop) : Prop where
  right : ProfiledOpenFixedRightQueryRowFaithful A initialCode rightValue
    rightQuery RightAllowed
  left : ProfiledOpenFixedLeftQueryRowFaithful A initialCode leftValue
    leftQuery LeftAllowed

/-- The proof-side active phase asks for exactly one component of the mixed
package.  This selector is never part of either process's local state. -/
def ProfiledOpenFixedActiveQueryRowFaithful
    (rightValue : ProfiledOpenFixedRightPinnedValue A initialCode)
    (rightQuery : ProfiledOpenFixedRightPinnedBlockQuery A initialCode
      rightValue)
    (leftValue : ProfiledOpenFixedLeftPinnedValue A initialCode)
    (leftQuery : ProfiledOpenFixedLeftPinnedBlockQuery A initialCode leftValue)
    (RightAllowed : ∀ descriptor :
        ProfiledOpenHiddenDescriptorRightCarrier A rightValue.1,
      (((ProfiledOpenHiddenDescriptorRightRoot A descriptor.1 × In₂) ×
          In₁) → ProfiledOpenRightClassifiedOutput A) → Prop)
    (LeftAllowed : ∀ descriptor :
        ProfiledOpenHiddenDescriptorLeftCarrier A leftValue.1,
      (((ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1 × In₁) ×
          In₂) → ProfiledOpenLeftClassifiedOutput A) → Prop) :
    IndexedLineageSide → Prop
  | .right => ProfiledOpenFixedRightQueryRowFaithful A initialCode rightValue
      rightQuery RightAllowed
  | .left => ProfiledOpenFixedLeftQueryRowFaithful A initialCode leftValue
      leftQuery LeftAllowed

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Requiring a faithful row for either possible proof-side phase is exactly
the conjunction of the two independent one-side obligations. -/
theorem profiledOpenFixedMixedQueryRowsFaithful_iff_forall_side
    (rightValue : ProfiledOpenFixedRightPinnedValue A initialCode)
    (rightQuery : ProfiledOpenFixedRightPinnedBlockQuery A initialCode
      rightValue)
    (leftValue : ProfiledOpenFixedLeftPinnedValue A initialCode)
    (leftQuery : ProfiledOpenFixedLeftPinnedBlockQuery A initialCode leftValue)
    (RightAllowed : ∀ descriptor :
        ProfiledOpenHiddenDescriptorRightCarrier A rightValue.1,
      (((ProfiledOpenHiddenDescriptorRightRoot A descriptor.1 × In₂) ×
          In₁) → ProfiledOpenRightClassifiedOutput A) → Prop)
    (LeftAllowed : ∀ descriptor :
        ProfiledOpenHiddenDescriptorLeftCarrier A leftValue.1,
      (((ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1 × In₁) ×
          In₂) → ProfiledOpenLeftClassifiedOutput A) → Prop) :
    ProfiledOpenFixedMixedQueryRowsFaithful A initialCode rightValue rightQuery
        leftValue leftQuery RightAllowed LeftAllowed ↔
      ∀ side, ProfiledOpenFixedActiveQueryRowFaithful A initialCode rightValue
        rightQuery leftValue leftQuery RightAllowed LeftAllowed side := by
  constructor
  · intro hrows side
    cases side with
    | right => exact hrows.right
    | left => exact hrows.left
  · intro hsides
    exact ⟨hsides .right, hsides .left⟩

/-! ## Independent semantic anchors supply the mixed package -/

variable (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
variable (hwin : ∀ env : EnvironmentSequence In₁ In₂,
  A.Accepts (execution strategy env))
variable (basis : ∀ state : PairedProfiledTreeState A,
  (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)

/-- The fixed right value obtained from one literal strong extraction. -/
noncomputable def profiledOpenFixedPinnedRightValueOfWinning
    (control : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
        (I := I) →
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)
    (source : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I)) :
    ProfiledOpenFixedRightPinnedValue A initialCode :=
  ⟨profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
      control source,
    profiledOpenFixedPinnedRightExpected A strategy hwin basis initialCode
      control source,
    (profiledOpenFixedPinnedRightProvenanceMoveOfWinning A strategy hwin basis
      initialCode control source).toPinnedMove A strategy hwin basis initialCode
        control source⟩

/-- Independently extracted left value. -/
noncomputable def profiledOpenFixedPinnedLeftValueOfWinning
    (control : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
        (I := I) →
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)
    (source : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I)) :
    ProfiledOpenFixedLeftPinnedValue A initialCode :=
  ⟨profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
      control source,
    profiledOpenFixedPinnedLeftExpected A strategy hwin basis initialCode
      control source,
    (profiledOpenFixedPinnedLeftProvenanceMoveOfWinning A strategy hwin basis
      initialCode control source).toPinnedMove A strategy hwin basis initialCode
        control source⟩

/-- Every reachable query of the independently extracted right value carries
the strong semantic law of its own anchor. -/
theorem profiledOpenFixedPinnedRightValue_queryRowFaithful
    (control : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
        (I := I) →
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)
    (source : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I))
    (query : ProfiledOpenFixedRightPinnedBlockQuery A initialCode
      (profiledOpenFixedPinnedRightValueOfWinning A initialCode strategy hwin
        basis control source))
    (hreachable : ProfiledOpenFixedRightQueryReachable A initialCode
      (profiledOpenFixedPinnedRightValueOfWinning A initialCode strategy hwin
        basis control source) query) :
    ProfiledOpenFixedRightQueryRowFaithful A initialCode
      (profiledOpenFixedPinnedRightValueOfWinning A initialCode strategy hwin
        basis control source) query
      (profiledOpenFixedPinnedRightSemanticAllowed A strategy hwin basis
        initialCode control source) := by
  rcases hreachable with ⟨word, hword⟩
  refine ⟨word, hword, ?_⟩
  intro descriptor
  have hall :=
    (profiledOpenFixedPinnedRightProvenanceMoveOfWinning A strategy hwin basis
      initialCode control source).2 word query.2
  have hdescriptor := hall descriptor
  unfold profiledOpenFixedRightQueryResponses
  rw [← hword]
  exact hdescriptor

/-- Left mirror. -/
theorem profiledOpenFixedPinnedLeftValue_queryRowFaithful
    (control : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
        (I := I) →
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)
    (source : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I))
    (query : ProfiledOpenFixedLeftPinnedBlockQuery A initialCode
      (profiledOpenFixedPinnedLeftValueOfWinning A initialCode strategy hwin
        basis control source))
    (hreachable : ProfiledOpenFixedLeftQueryReachable A initialCode
      (profiledOpenFixedPinnedLeftValueOfWinning A initialCode strategy hwin
        basis control source) query) :
    ProfiledOpenFixedLeftQueryRowFaithful A initialCode
      (profiledOpenFixedPinnedLeftValueOfWinning A initialCode strategy hwin
        basis control source) query
      (profiledOpenFixedPinnedLeftSemanticAllowed A strategy hwin basis
        initialCode control source) := by
  rcases hreachable with ⟨word, hword⟩
  refine ⟨word, hword, ?_⟩
  intro descriptor
  have hall :=
    (profiledOpenFixedPinnedLeftProvenanceMoveOfWinning A strategy hwin basis
      initialCode control source).2 word query.2
  have hdescriptor := hall descriptor
  unfold profiledOpenFixedLeftQueryResponses
  rw [← hword]
  exact hdescriptor

/-- Two entirely independent anchors supply the complete mixed-family row
package.  In particular there is no premise equating `rightSource` and
`leftSource`, their controls, or their hidden semantic pasts. -/
theorem profiledOpenFixedPinnedMixedQuery_rowsFaithful
    (rightControl : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
        (I := I) →
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)
    (rightSource : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I))
    (leftControl : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
        (I := I) →
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)
    (leftSource : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I))
    (rightQuery : ProfiledOpenFixedRightPinnedBlockQuery A initialCode
      (profiledOpenFixedPinnedRightValueOfWinning A initialCode strategy hwin
        basis rightControl rightSource))
    (leftQuery : ProfiledOpenFixedLeftPinnedBlockQuery A initialCode
      (profiledOpenFixedPinnedLeftValueOfWinning A initialCode strategy hwin
        basis leftControl leftSource))
    (hright : ProfiledOpenFixedRightQueryReachable A initialCode
      (profiledOpenFixedPinnedRightValueOfWinning A initialCode strategy hwin
        basis rightControl rightSource) rightQuery)
    (hleft : ProfiledOpenFixedLeftQueryReachable A initialCode
      (profiledOpenFixedPinnedLeftValueOfWinning A initialCode strategy hwin
        basis leftControl leftSource) leftQuery) :
    ProfiledOpenFixedMixedQueryRowsFaithful A initialCode
      (profiledOpenFixedPinnedRightValueOfWinning A initialCode strategy hwin
        basis rightControl rightSource) rightQuery
      (profiledOpenFixedPinnedLeftValueOfWinning A initialCode strategy hwin
        basis leftControl leftSource) leftQuery
      (profiledOpenFixedPinnedRightSemanticAllowed A strategy hwin basis
        initialCode rightControl rightSource)
      (profiledOpenFixedPinnedLeftSemanticAllowed A strategy hwin basis
        initialCode leftControl leftSource) := by
  exact ⟨
    profiledOpenFixedPinnedRightValue_queryRowFaithful A initialCode strategy
      hwin basis rightControl rightSource rightQuery hright,
    profiledOpenFixedPinnedLeftValue_queryRowFaithful A initialCode strategy
      hwin basis leftControl leftSource leftQuery hleft⟩

end

end DetParityAutomaton

end DistributedSynthesis
