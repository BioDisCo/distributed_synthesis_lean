/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenFixedPinnedProvenance
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenPointedSupportedSuccessor

/-!
# Concrete realization of the provenance-preserving pinned move

The provenance-preserving optional dispatcher and the older weak dispatcher
have the same public family coordinate, although their rational controllers
need not be equal.  This file uses the former literally.

The operational realization predicate below deliberately asks only for the
four-way descriptor representation and for the move to come from the strong
dispatcher at that public family.  It does not select a semantic
representative of the whole two-fibre family.  That stronger selection would
reintroduce the invalid reflection from equality of finite fibre images to
the underlying exact local-view relation.

The equality to the strong dispatcher is not cosmetic: its active controller
projections are exactly the controllers covered by the arbitrary-node
`controllerFor_semantic` theorems in
`LemPairedProfiledOpenFixedPinnedProvenance`.  Those theorems cover every
monitor state at every *reachable controller node*.  Accordingly this file
retains the sender word reaching the control stored in an operational block
query and proves the semantic law for the literal emitted response row.  No
leader, orientation, or lane signal is added.
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

/-- Public-family agreement between the selected controlled move and the
single-extraction strong dispatcher.  The controlled move now uses that
dispatcher literally, so this law is definitional.  It is kept as a named
API theorem to distinguish harmless first-coordinate agreement from invalid
reflection of finite fibre images. -/
def ProfiledOpenOptionalPinnedPublicFamilyAgreement : Prop :=
  ∀ point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode,
    (profiledOpenOptionalFixedPinnedSemanticMoveOfWinning.{i, u, v, x, y, s,
      0, 0} A strategy hwin
      basis initialCode (fun _ ↦ point.2) point.1).1 =
      profiledOpenOptionalControlledFamilyOf A strategy hwin basis
        initialCode point

/-- After installing the strong dispatcher literally in the controlled move
definition, public-family agreement is definitional. -/
theorem profiledOpenOptionalPinnedPublicFamilyAgreement :
    ProfiledOpenOptionalPinnedPublicFamilyAgreement A strategy hwin basis
      initialCode := by
  intro point
  rfl

/-- A literal pinned move was produced by the strong, single-extraction
dispatcher at the advertised public family.  Consequently each active-side
projection is one of the literal controllers carrying the already proved
arbitrary-node semantic table law. -/
def ProfiledOpenOptionalPinnedMoveHasProvenance
    (family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I)
      initialCode)
    (move : ProfiledOpenHiddenDescriptorPairedPinnedFamilyMove.{i, u, v, x,
      y, s, 0, 0} A (I := I) initialCode) : Prop :=
  move.1 = family ∧
    ∃ source : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
        hwin basis initialCode,
      profiledOpenOptionalControlledFamilyOf A strategy hwin basis initialCode
          source = family ∧
        move =
          profiledOpenOptionalFixedPinnedSemanticMoveOfWinning.{i, u, v, x,
            y, s, 0, 0} A strategy hwin
            basis initialCode (fun _ ↦ source.2) source.1

/-- The strong dispatcher itself has provenance at its public family. -/
theorem profiledOpenOptionalFixedPinnedSemanticMoveOfWinning_hasProvenance
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode) :
    ProfiledOpenOptionalPinnedMoveHasProvenance A strategy hwin basis
      initialCode
      (profiledOpenOptionalControlledFamilyOf A strategy hwin basis
        initialCode point)
      (profiledOpenOptionalFixedPinnedSemanticMoveOfWinning.{i, u, v, x, y,
        s, 0, 0} A strategy hwin
        basis initialCode (fun _ ↦ point.2) point.1) := by
  refine ⟨profiledOpenOptionalPinnedPublicFamilyAgreement A strategy hwin
      basis initialCode point, point, rfl, rfl⟩

/-- Operational realization at a recovered descriptor query.  The semantic
state is used only to witness the exact descriptor and public family.  The
move itself is certified independently by its strong-dispatcher provenance,
and the descriptor is required to have the already proved four-way
representation in that family.

This is intentionally weaker than choosing one semantic state which realizes
both complete local fibres.  Such a choice is unnecessary for the later
fixed-policy parity proof and is not justified by equality of finite fibre
images. -/
def profiledOpenOptionalPinnedQueryRealizes :
    ProfiledOpenOptionalPinnedQueryRealizes A strategy hwin basis initialCode :=
  fun current family move state =>
    profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis initialCode state = current ∧
      profiledOpenOptionalControlledFamilyOf A strategy hwin basis initialCode
          state = family ∧
      ProfiledOpenOptionalControlledRepresented A initialCode current family ∧
      ProfiledOpenOptionalPinnedMoveHasProvenance A strategy hwin basis
        initialCode family move

/-- Any provenance-certified move realizes every descriptor which is live in
the pointed semantic sense.  No reflection from public-family equality to an
exact local-view relation is used: the live witness itself supplies the
descriptor/family equalities, and representation is the existing four-shape
theorem. -/
theorem profiledOpenOptionalPinnedQueryRealizes_moveValid
    (family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I)
      initialCode)
    (move : ProfiledOpenHiddenDescriptorPairedPinnedFamilyMove.{i, u, v, x,
      y, s, 0, 0} A (I := I) initialCode)
    (hprovenance : ProfiledOpenOptionalPinnedMoveHasProvenance A strategy hwin
      basis initialCode family move) :
    ProfiledOpenOptionalPointedPinnedMoveValid A strategy hwin basis
      initialCode
      (profiledOpenOptionalPinnedQueryRealizes A strategy hwin basis
        initialCode)
      family move := by
  intro current hlive
  obtain ⟨state, hdescriptor, hfamily⟩ := hlive
  refine ⟨state, ?_, hdescriptor, hfamily⟩
  refine ⟨hdescriptor, hfamily, ?_, hprovenance⟩
  simpa [hdescriptor, hfamily] using
    (profiledOpenOptionalControlledDescriptor_represented A strategy hwin
      basis initialCode state)

/-- In particular, the literal provenance-preserving move selected at a
semantic source is valid for every live descriptor of its advertised family. -/
theorem profiledOpenOptionalFixedPinnedSemanticMoveOfWinning_moveValid
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode) :
    ProfiledOpenOptionalPointedPinnedMoveValid A strategy hwin basis
      initialCode
      (profiledOpenOptionalPinnedQueryRealizes A strategy hwin basis
        initialCode)
      (profiledOpenOptionalControlledFamilyOf A strategy hwin basis
        initialCode point)
      (profiledOpenOptionalFixedPinnedSemanticMoveOfWinning.{i, u, v, x, y,
        s, 0, 0} A strategy hwin
        basis initialCode (fun _ ↦ point.2) point.1) :=
  profiledOpenOptionalPinnedQueryRealizes_moveValid A strategy hwin basis
    initialCode _ _
    (profiledOpenOptionalFixedPinnedSemanticMoveOfWinning_hasProvenance A
      strategy hwin basis initialCode point)

/-! ## Literal block-query rows -/

/-- The right receiver row emitted by a pinned union controller at the exact
finite `(controller, union-monitor)` query, restricted to one descriptor.
This is the table which the operational receive actually evaluates. -/
noncomputable def profiledOpenPinnedRightQueryResponses
    {family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I)
      initialCode}
    (move : ProfiledOpenHiddenDescriptorPairedPinnedFamilyMoveAt A family)
    (query : ProfiledOpenHiddenDescriptorPairedPinnedBlockQueryAt A family
      move)
    (descriptor : ProfiledOpenHiddenDescriptorRightCarrier A family) :
    ((ProfiledOpenHiddenDescriptorRightRoot A descriptor.1 × In₂) × In₁) →
      ProfiledOpenRightClassifiedOutput A :=
  fun input =>
    ((move.2.2.1.1.toTransitionRationalTree.labelOf query.1.1).2 query.1.2)
      ((Sigma.mk descriptor input.1.1, input.1.2), input.2)

/-- Left mirror of `profiledOpenPinnedRightQueryResponses`. -/
noncomputable def profiledOpenPinnedLeftQueryResponses
    {family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I)
      initialCode}
    (move : ProfiledOpenHiddenDescriptorPairedPinnedFamilyMoveAt A family)
    (query : ProfiledOpenHiddenDescriptorPairedPinnedBlockQueryAt A family
      move)
    (descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A family) :
    ((ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1 × In₁) × In₂) →
      ProfiledOpenLeftClassifiedOutput A :=
  fun input =>
    ((move.2.2.2.1.toTransitionRationalTree.labelOf query.2.1).2 query.2.2)
      ((Sigma.mk descriptor input.1.1, input.1.2), input.2)

/-- The right controller coordinate of a block query must be reached by an
actual blind-sender word.  `NarrowedTablesAllowed` covers all monitor states
but, correctly, only controller states reached in this way. -/
def ProfiledOpenPinnedRightQueryReachable
    {family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I)
      initialCode}
    (move : ProfiledOpenHiddenDescriptorPairedPinnedFamilyMoveAt A family)
    (query : ProfiledOpenHiddenDescriptorPairedPinnedBlockQueryAt A family
      move) : Prop :=
  ∃ word : List In₁,
    move.2.2.1.1.toTransitionRationalTree.controlAt word = query.1.1

/-- Reachability of the left blind-sender controller coordinate. -/
def ProfiledOpenPinnedLeftQueryReachable
    {family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I)
      initialCode}
    (move : ProfiledOpenHiddenDescriptorPairedPinnedFamilyMoveAt A family)
    (query : ProfiledOpenHiddenDescriptorPairedPinnedBlockQueryAt A family
      move) : Prop :=
  ∃ word : List In₂,
    move.2.2.2.1.toTransitionRationalTree.controlAt word = query.2.1

/-- The exact execution-side alignment still owed by a paired actual-query
constructor: each queried controller coordinate must be the control reached
by its actual blind-sender word.  Monitor coordinates need no extra premise,
because the strong provenance law quantifies over every monitor state. -/
def ProfiledOpenPinnedQueryExecutionAligned
    {family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I)
      initialCode}
    (move : ProfiledOpenHiddenDescriptorPairedPinnedFamilyMoveAt A family)
    (query : ProfiledOpenHiddenDescriptorPairedPinnedBlockQueryAt A family
      move) : Prop :=
  ProfiledOpenPinnedRightQueryReachable A initialCode move query ∧
    ProfiledOpenPinnedLeftQueryReachable A initialCode move query

/-! ## Same-controller row faithfulness -/

/-- Operational faithfulness of one active right query row.  The witness
retains the actual blind-sender word reaching the queried controller state;
the semantic law is asserted about the response emitted by that *same*
controller at the query's literal union-monitor state. -/
def ProfiledOpenPinnedRightQueryRowFaithful
    {family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I)
      initialCode}
    (move : ProfiledOpenHiddenDescriptorPairedPinnedFamilyMoveAt A family)
    (query : ProfiledOpenHiddenDescriptorPairedPinnedBlockQueryAt A family
      move)
    (Allowed : ∀ descriptor : ProfiledOpenHiddenDescriptorRightCarrier A
        family,
      (((ProfiledOpenHiddenDescriptorRightRoot A descriptor.1 × In₂) ×
          In₁) → ProfiledOpenRightClassifiedOutput A) → Prop) : Prop :=
  ∃ word : List In₁,
    move.2.2.1.1.toTransitionRationalTree.controlAt word = query.1.1 ∧
      ∀ descriptor,
        Allowed descriptor
          (profiledOpenPinnedRightQueryResponses A initialCode move query
            descriptor)

/-- Left mirror of `ProfiledOpenPinnedRightQueryRowFaithful`. -/
def ProfiledOpenPinnedLeftQueryRowFaithful
    {family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I)
      initialCode}
    (move : ProfiledOpenHiddenDescriptorPairedPinnedFamilyMoveAt A family)
    (query : ProfiledOpenHiddenDescriptorPairedPinnedBlockQueryAt A family
      move)
    (Allowed : ∀ descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A
        family,
      (((ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1 × In₁) ×
          In₂) → ProfiledOpenLeftClassifiedOutput A) → Prop) : Prop :=
  ∃ word : List In₂,
    move.2.2.2.1.toTransitionRationalTree.controlAt word = query.2.1 ∧
      ∀ descriptor,
        Allowed descriptor
          (profiledOpenPinnedLeftQueryResponses A initialCode move query
            descriptor)

/-- A two-live query carries two independent same-controller witnesses.  No
field asks that the existential semantic past hidden inside the right and
left `Allowed` predicates be the same. -/
structure ProfiledOpenPinnedPairedQueryRowsFaithful
    {family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I)
      initialCode}
    (move : ProfiledOpenHiddenDescriptorPairedPinnedFamilyMoveAt A family)
    (query : ProfiledOpenHiddenDescriptorPairedPinnedBlockQueryAt A family
      move)
    (RightAllowed : ∀ descriptor :
        ProfiledOpenHiddenDescriptorRightCarrier A family,
      (((ProfiledOpenHiddenDescriptorRightRoot A descriptor.1 × In₂) ×
          In₁) → ProfiledOpenRightClassifiedOutput A) → Prop)
    (LeftAllowed : ∀ descriptor :
        ProfiledOpenHiddenDescriptorLeftCarrier A family,
      (((ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1 × In₁) ×
          In₂) → ProfiledOpenLeftClassifiedOutput A) → Prop) : Prop where
  right : ProfiledOpenPinnedRightQueryRowFaithful A initialCode move query
    RightAllowed
  left : ProfiledOpenPinnedLeftQueryRowFaithful A initialCode move query
    LeftAllowed

/-- The sink shape has no active descriptor row on either side. -/
def ProfiledOpenPinnedSinkHasNoActiveRows : Prop :=
  IsEmpty
      (ProfiledOpenHiddenDescriptorRightCarrier A
        (profiledOpenOptionalSinkFamilyCode A (I := I) initialCode)) ∧
    IsEmpty
      (ProfiledOpenHiddenDescriptorLeftCarrier A
        (profiledOpenOptionalSinkFamilyCode A (I := I) initialCode))

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- The sink case of the four-way dispatcher is genuinely vacuous; it does
not manufacture a semantic source for an empty carrier. -/
theorem profiledOpenPinnedSink_hasNoActiveRows :
    ProfiledOpenPinnedSinkHasNoActiveRows A initialCode := by
  constructor
  · refine ⟨?_⟩
    rintro ⟨descriptor, hmem⟩
    simpa [profiledOpenOptionalSinkFamilyCode] using hmem
  · refine ⟨?_⟩
    rintro ⟨descriptor, hmem⟩
    simpa [profiledOpenOptionalSinkFamilyCode] using hmem

/-! ## Strong provenance at the emitted row -/

/-- Every reachable right query of the canonical right-only strong move emits
a response table with the semantic provenance of that exact descriptor. -/
theorem profiledOpenOptionalRightOnlyPinnedQuery_semantic
    (optionalControl :
      ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
          (I := I) →
        (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)
    (source : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I))
    (query : ProfiledOpenHiddenDescriptorPairedPinnedBlockQueryAt A
      (profiledOpenOptionalRightOnlyFamilyCode A strategy hwin basis
        initialCode optionalControl source)
      (profiledOpenOptionalRightOnlyPinnedSemanticMoveAtOfWinning A strategy
        hwin basis initialCode optionalControl source))
    (descriptor : ProfiledOpenHiddenDescriptorRightCarrier A
      (profiledOpenOptionalRightOnlyFamilyCode A strategy hwin basis
        initialCode optionalControl source))
    (hreachable : ProfiledOpenPinnedRightQueryReachable A initialCode
      (profiledOpenOptionalRightOnlyPinnedSemanticMoveAtOfWinning A strategy
        hwin basis initialCode optionalControl source) query) :
    profiledOpenOptionalRightOnlySemanticAllowed A strategy hwin basis
      initialCode optionalControl source descriptor
      (profiledOpenPinnedRightQueryResponses A initialCode
        (profiledOpenOptionalRightOnlyPinnedSemanticMoveAtOfWinning A strategy
          hwin basis initialCode optionalControl source) query descriptor) := by
  rcases hreachable with ⟨word, hword⟩
  have hall :=
    (profiledOpenOptionalRightOnlyPinnedProvenanceMoveOfWinning A strategy
      hwin basis initialCode optionalControl source).2 word query.1.2
  have hdescriptor := hall descriptor
  unfold profiledOpenPinnedRightQueryResponses
  rw [← hword]
  exact hdescriptor

/-- Left-only mirror: every reachable literal query row carries the strong
semantic provenance of each descriptor in the active left carrier. -/
theorem profiledOpenOptionalLeftOnlyPinnedQuery_semantic
    (optionalControl :
      ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
          (I := I) →
        (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)
    (source : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I))
    (query : ProfiledOpenHiddenDescriptorPairedPinnedBlockQueryAt A
      (profiledOpenOptionalLeftOnlyFamilyCode A strategy hwin basis
        initialCode optionalControl source)
      (profiledOpenOptionalLeftOnlyPinnedSemanticMoveAtOfWinning A strategy
        hwin basis initialCode optionalControl source))
    (descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A
      (profiledOpenOptionalLeftOnlyFamilyCode A strategy hwin basis
        initialCode optionalControl source))
    (hreachable : ProfiledOpenPinnedLeftQueryReachable A initialCode
      (profiledOpenOptionalLeftOnlyPinnedSemanticMoveAtOfWinning A strategy
        hwin basis initialCode optionalControl source) query) :
    profiledOpenOptionalLeftOnlySemanticAllowed A strategy hwin basis
      initialCode optionalControl source descriptor
      (profiledOpenPinnedLeftQueryResponses A initialCode
        (profiledOpenOptionalLeftOnlyPinnedSemanticMoveAtOfWinning A strategy
          hwin basis initialCode optionalControl source) query descriptor) := by
  rcases hreachable with ⟨word, hword⟩
  have hall :=
    (profiledOpenOptionalLeftOnlyPinnedProvenanceMoveOfWinning A strategy
      hwin basis initialCode optionalControl source).2 word query.2.2
  have hdescriptor := hall descriptor
  unfold profiledOpenPinnedLeftQueryResponses
  rw [← hword]
  exact hdescriptor

/-- Right active side of a two-live source.  The witness is the right strong
extraction; no common semantic representative with the left side is chosen. -/
theorem profiledOpenFixedPinnedRightQuery_semantic
    (control : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
        (I := I) →
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)
    (source : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I))
    (query : ProfiledOpenHiddenDescriptorPairedPinnedBlockQueryAt A
      (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
        control source)
      (profiledOpenFixedPinnedPairedProvenanceMoveAtOfWinning A strategy hwin
        basis initialCode control source))
    (descriptor : ProfiledOpenHiddenDescriptorRightCarrier A
      (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
        control source))
    (hreachable : ProfiledOpenPinnedRightQueryReachable A initialCode
      (profiledOpenFixedPinnedPairedProvenanceMoveAtOfWinning A strategy hwin
        basis initialCode control source) query) :
    profiledOpenFixedPinnedRightSemanticAllowed A strategy hwin basis
      initialCode control source descriptor
      (profiledOpenPinnedRightQueryResponses A initialCode
        (profiledOpenFixedPinnedPairedProvenanceMoveAtOfWinning A strategy hwin
          basis initialCode control source) query descriptor) := by
  rcases hreachable with ⟨word, hword⟩
  have hall :=
    (profiledOpenFixedPinnedRightProvenanceMoveOfWinning A strategy hwin basis
      initialCode control source).2 word query.1.2
  have hdescriptor := hall descriptor
  unfold profiledOpenPinnedRightQueryResponses
  rw [← hword]
  exact hdescriptor

/-- Left active side of a two-live source, proved independently from the
right witness on the literal left controller. -/
theorem profiledOpenFixedPinnedLeftQuery_semantic
    (control : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
        (I := I) →
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)
    (source : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I))
    (query : ProfiledOpenHiddenDescriptorPairedPinnedBlockQueryAt A
      (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
        control source)
      (profiledOpenFixedPinnedPairedProvenanceMoveAtOfWinning A strategy hwin
        basis initialCode control source))
    (descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A
      (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
        control source))
    (hreachable : ProfiledOpenPinnedLeftQueryReachable A initialCode
      (profiledOpenFixedPinnedPairedProvenanceMoveAtOfWinning A strategy hwin
        basis initialCode control source) query) :
    profiledOpenFixedPinnedLeftSemanticAllowed A strategy hwin basis
      initialCode control source descriptor
      (profiledOpenPinnedLeftQueryResponses A initialCode
        (profiledOpenFixedPinnedPairedProvenanceMoveAtOfWinning A strategy hwin
          basis initialCode control source) query descriptor) := by
  rcases hreachable with ⟨word, hword⟩
  have hall :=
    (profiledOpenFixedPinnedLeftProvenanceMoveOfWinning A strategy hwin basis
      initialCode control source).2 word query.2.2
  have hdescriptor := hall descriptor
  unfold profiledOpenPinnedLeftQueryResponses
  rw [← hword]
  exact hdescriptor

/-! ## The four optional shapes, packaged -/

/-- Right-only operational package: one actual word reaches the literal
query control, and every advertised right descriptor reads a strongly
semantic row from that same controller/query pair. -/
theorem profiledOpenOptionalRightOnlyPinnedQuery_rowFaithful
    (optionalControl :
      ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
          (I := I) →
        (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)
    (source : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I))
    (query : ProfiledOpenHiddenDescriptorPairedPinnedBlockQueryAt A
      (profiledOpenOptionalRightOnlyFamilyCode A strategy hwin basis
        initialCode optionalControl source)
      (profiledOpenOptionalRightOnlyPinnedSemanticMoveAtOfWinning A strategy
        hwin basis initialCode optionalControl source))
    (hreachable : ProfiledOpenPinnedRightQueryReachable A initialCode
      (profiledOpenOptionalRightOnlyPinnedSemanticMoveAtOfWinning A strategy
        hwin basis initialCode optionalControl source) query) :
    ProfiledOpenPinnedRightQueryRowFaithful A initialCode
      (profiledOpenOptionalRightOnlyPinnedSemanticMoveAtOfWinning A strategy
        hwin basis initialCode optionalControl source) query
      (profiledOpenOptionalRightOnlySemanticAllowed A strategy hwin basis
        initialCode optionalControl source) := by
  rcases hreachable with ⟨word, hword⟩
  refine ⟨word, hword, ?_⟩
  intro descriptor
  exact profiledOpenOptionalRightOnlyPinnedQuery_semantic A strategy hwin
    basis initialCode optionalControl source query descriptor ⟨word, hword⟩

/-- Left-only operational package. -/
theorem profiledOpenOptionalLeftOnlyPinnedQuery_rowFaithful
    (optionalControl :
      ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
          (I := I) →
        (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)
    (source : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I))
    (query : ProfiledOpenHiddenDescriptorPairedPinnedBlockQueryAt A
      (profiledOpenOptionalLeftOnlyFamilyCode A strategy hwin basis
        initialCode optionalControl source)
      (profiledOpenOptionalLeftOnlyPinnedSemanticMoveAtOfWinning A strategy
        hwin basis initialCode optionalControl source))
    (hreachable : ProfiledOpenPinnedLeftQueryReachable A initialCode
      (profiledOpenOptionalLeftOnlyPinnedSemanticMoveAtOfWinning A strategy
        hwin basis initialCode optionalControl source) query) :
    ProfiledOpenPinnedLeftQueryRowFaithful A initialCode
      (profiledOpenOptionalLeftOnlyPinnedSemanticMoveAtOfWinning A strategy
        hwin basis initialCode optionalControl source) query
      (profiledOpenOptionalLeftOnlySemanticAllowed A strategy hwin basis
        initialCode optionalControl source) := by
  rcases hreachable with ⟨word, hword⟩
  refine ⟨word, hword, ?_⟩
  intro descriptor
  exact profiledOpenOptionalLeftOnlyPinnedQuery_semantic A strategy hwin basis
    initialCode optionalControl source query descriptor ⟨word, hword⟩

/-- Two-live package.  The right and left witnesses remain deliberately
separate; the theorem does not merge their existential semantic pasts. -/
theorem profiledOpenFixedPinnedQuery_rowsFaithful
    (control : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
        (I := I) →
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)
    (source : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I))
    (query : ProfiledOpenHiddenDescriptorPairedPinnedBlockQueryAt A
      (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
        control source)
      (profiledOpenFixedPinnedPairedProvenanceMoveAtOfWinning A strategy hwin
        basis initialCode control source))
    (hright : ProfiledOpenPinnedRightQueryReachable A initialCode
      (profiledOpenFixedPinnedPairedProvenanceMoveAtOfWinning A strategy hwin
        basis initialCode control source) query)
    (hleft : ProfiledOpenPinnedLeftQueryReachable A initialCode
      (profiledOpenFixedPinnedPairedProvenanceMoveAtOfWinning A strategy hwin
        basis initialCode control source) query) :
    ProfiledOpenPinnedPairedQueryRowsFaithful A initialCode
      (profiledOpenFixedPinnedPairedProvenanceMoveAtOfWinning A strategy hwin
        basis initialCode control source) query
      (profiledOpenFixedPinnedRightSemanticAllowed A strategy hwin basis
        initialCode control source)
      (profiledOpenFixedPinnedLeftSemanticAllowed A strategy hwin basis
        initialCode control source) := by
  constructor
  · rcases hright with ⟨word, hword⟩
    refine ⟨word, hword, ?_⟩
    intro descriptor
    exact profiledOpenFixedPinnedRightQuery_semantic A strategy hwin basis
      initialCode control source query descriptor ⟨word, hword⟩
  · rcases hleft with ⟨word, hword⟩
    refine ⟨word, hword, ?_⟩
    intro descriptor
    exact profiledOpenFixedPinnedLeftQuery_semantic A strategy hwin basis
      initialCode control source query descriptor ⟨word, hword⟩

/-- Paired spelling using the single execution-alignment residual. -/
theorem profiledOpenFixedPinnedQuery_rowsFaithful_of_executionAligned
    (control : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
        (I := I) →
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)
    (source : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I))
    (query : ProfiledOpenHiddenDescriptorPairedPinnedBlockQueryAt A
      (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
        control source)
      (profiledOpenFixedPinnedPairedProvenanceMoveAtOfWinning A strategy hwin
        basis initialCode control source))
    (haligned : ProfiledOpenPinnedQueryExecutionAligned A initialCode
      (profiledOpenFixedPinnedPairedProvenanceMoveAtOfWinning A strategy hwin
        basis initialCode control source) query) :
    ProfiledOpenPinnedPairedQueryRowsFaithful A initialCode
      (profiledOpenFixedPinnedPairedProvenanceMoveAtOfWinning A strategy hwin
        basis initialCode control source) query
      (profiledOpenFixedPinnedRightSemanticAllowed A strategy hwin basis
        initialCode control source)
      (profiledOpenFixedPinnedLeftSemanticAllowed A strategy hwin basis
        initialCode control source) :=
  profiledOpenFixedPinnedQuery_rowsFaithful A strategy hwin basis initialCode
    control source query haligned.1 haligned.2

/-! ## Exact descriptor and public-code update -/

/-- The exact proof-side target descriptor for one represented semantic
source and one complete pinned query tag.  This definition uses the existing
indexed semantic successor; it does not combine the independent right/left
row witnesses above. -/
noncomputable def profiledOpenOptionalPinnedExactTarget
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode)
    (tag : ProfiledOpenHiddenDescriptorPairedPinnedBlockQueryTag.{i, u, v, x,
      y, s, 0, 0, 0, 0} A (I := I) initialCode) :
    ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode :=
  profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
    basis initialCode
    (profiledOpenOptionalControlledBlockQuerySemanticNext A strategy hwin
      basis initialCode point tag)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The exact target's public code is the already proved finite-direction
successor.  Thus the row-faithfulness package adds no self-referential or
joint-semantic update premise. -/
theorem profiledOpenOptionalPinnedExactTarget_code
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode)
    (tag : ProfiledOpenHiddenDescriptorPairedPinnedBlockQueryTag.{i, u, v, x,
      y, s, 0, 0, 0, 0} A (I := I) initialCode) :
    (profiledOpenOptionalPinnedExactTarget A strategy hwin basis initialCode
        point tag).code =
      profiledOpenIndexedBiBeliefNextFiniteTag A
        (point.1.state.code A strategy hwin basis)
        (point.1.state.move A strategy hwin basis) tag.2.2 := by
  exact profiledOpenOptionalControlledBlockQuerySemanticNext_code A strategy
    hwin basis initialCode point tag

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The exact target also performs the literal parity-control transition on
that finite child code. -/
theorem profiledOpenOptionalPinnedExactTarget_control
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode)
    (tag : ProfiledOpenHiddenDescriptorPairedPinnedBlockQueryTag.{i, u, v, x,
      y, s, 0, 0, 0, 0} A (I := I) initialCode) :
    (profiledOpenOptionalPinnedExactTarget A strategy hwin basis initialCode
        point tag).control =
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).step
        (profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy
          hwin basis initialCode point).control
        (profiledOpenOptionalPinnedExactTarget A strategy hwin basis
          initialCode point tag).code := by
  exact profiledOpenOptionalControlledBlockQuerySemanticNext_controlStep A
    strategy hwin basis initialCode point tag

end

end DetParityAutomaton

end DistributedSynthesis
