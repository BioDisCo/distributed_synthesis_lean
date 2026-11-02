/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemCarriedPointedSuccessorReceive
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenPointedSupportedSuccessor

/-!
# Fail-fast concrete pointed-query alignment at receives

A literal receive determines the settled history and both current inputs, but
the operational handoff needs more: the pointed query must factor through the
*finite* tuple passed to `LocalSummaryAutomaton.stepRecv`.  This file states
and proves that boundary exactly.

The tuple is ordered canonically as

```
(summary one, input one, summary two, input two).
```

Both receiving processes obtain this same tuple, with their self/other
arguments merely swapped.  `JointReceiveQueryReader.toPointed` therefore
defines one graph-blind `PointedReceiveQueryReader`; it has no graph,
orientation, lane, or strict-leader input.

For the concrete optional pinned query we then split fibre constancy into its
three literal coordinates: public family, complete pinned tag, and hidden
descriptor.  The family and tag are finite public controller data and may be
carried by the enriched wrapper.  Once their two fibre-constancy laws hold,
existence of an aligned finite reader is equivalent to constancy of exactly
the remaining descriptor

```
((indexed public code, parity control), old semantic move).
```

The final collision theorem is the fail-fast obstruction: two generated
receive occurrences with the same joint finite tuple and different actual
descriptors refute every such reader.  No hidden descriptor is installed in
either process to make the theorem true.
-/

namespace DistributedSynthesis

universe i u v x y s o q

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

/-- A generated receive by either process.  The sum tag is proof-side only;
the finite query reader below never sees it. -/
abbrev GeneratedReceiveEither
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂) :=
  Sum (GeneratedReceiveOne strategy) (GeneratedReceiveTwo strategy)

namespace GeneratedReceiveEither

variable {strategy : StrategyPair In₁ In₂ Out₁ Out₂}

def history (occurrence : GeneratedReceiveEither strategy) :
    History In₁ In₂ Graph Out₁ Out₂ :=
  match occurrence with
  | .inl receive => receive.history
  | .inr receive => receive.history

def inputOne (occurrence : GeneratedReceiveEither strategy) : In₁ :=
  match occurrence with
  | .inl receive => receive.environment.inputOne
  | .inr receive => receive.environment.inputOne

def inputTwo (occurrence : GeneratedReceiveEither strategy) : In₂ :=
  match occurrence with
  | .inl receive => receive.environment.inputTwo
  | .inr receive => receive.environment.inputTwo

end GeneratedReceiveEither

/-! ## The finite joint receive tuple -/

/-- The finite tuple available to either receiver, put in the same global
process order on both sides. -/
abbrev JointReceiveFiniteInput
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂) :=
  M.Summary .one × In₁ × M.Summary .two × In₂

noncomputable instance
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂)
    [Fintype In₁] [Fintype In₂] :
    Fintype (JointReceiveFiniteInput M) := by
  classical
  infer_instance

/-- Read the pre-round summaries and current inputs of a generated receive.
No graph field is retained. -/
def generatedReceiveEitherFiniteInput
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂)
    (occurrence : GeneratedReceiveEither strategy) :
    JointReceiveFiniteInput M :=
  (M.read (currentView Proc.one occurrence.history), occurrence.inputOne,
    M.read (currentView Proc.two occurrence.history), occurrence.inputTwo)

/-- Any value determined by settled history and both current inputs. -/
def generatedReceiveEitherSettledValue
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {Value : Type q}
    (value : History In₁ In₂ Graph Out₁ Out₂ → In₁ → In₂ →
      Value)
    (occurrence : GeneratedReceiveEither strategy) : Value :=
  value occurrence.history occurrence.inputOne occurrence.inputTwo

/-- One finite decoder of the canonically ordered joint receive tuple. -/
structure JointReceiveQueryReader
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂) (Query : Type q) where
  decode : JointReceiveFiniteInput M → Query

/-- The decoder is correct at every generated receive by either process. -/
def JointReceiveQueryReader.Correct
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {M : LocalSummaryAutomaton.{u, v, o} In₁ In₂} {Query : Type q}
    (reader : JointReceiveQueryReader M Query)
    (actual : GeneratedReceiveEither strategy → Query) : Prop :=
  ∀ occurrence,
    reader.decode (generatedReceiveEitherFiniteInput M occurrence) =
      actual occurrence

/-- Turn the canonical decoder into the self/other interface of a local
receive.  The only noncanonical PSum cases are impossible for real views and
use the supplied fallback. -/
def JointReceiveQueryReader.toPointed
    {M : LocalSummaryAutomaton.{u, v, o} In₁ In₂} {Query : Type q}
    (reader : JointReceiveQueryReader M Query) (fallback : Query) :
    PointedReceiveQueryReader M Query where
  recv
    | .one, one, .inl inputOne, two, .inr inputTwo =>
        reader.decode (one, inputOne, two, inputTwo)
    | .two, two, .inr inputTwo, one, .inl inputOne =>
        reader.decode (one, inputOne, two, inputTwo)
    | _, _, _, _, _ => fallback

@[simp] theorem JointReceiveQueryReader.toPointed_recv_one
    {M : LocalSummaryAutomaton.{u, v, o} In₁ In₂} {Query : Type q}
    (reader : JointReceiveQueryReader M Query) (fallback : Query)
    (one : M.Summary .one) (inputOne : In₁)
    (two : M.Summary .two) (inputTwo : In₂) :
    (reader.toPointed fallback).recv .one one (.inl inputOne) two
        (.inr inputTwo) =
      reader.decode (one, inputOne, two, inputTwo) :=
  rfl

@[simp] theorem JointReceiveQueryReader.toPointed_recv_two
    {M : LocalSummaryAutomaton.{u, v, o} In₁ In₂} {Query : Type q}
    (reader : JointReceiveQueryReader M Query) (fallback : Query)
    (two : M.Summary .two) (inputTwo : In₂)
    (one : M.Summary .one) (inputOne : In₁) :
    (reader.toPointed fallback).recv .two two (.inr inputTwo) one
        (.inl inputOne) =
      reader.decode (one, inputOne, two, inputTwo) :=
  rfl

/-- The exact finite-summary recovery criterion.  Literal full-view recovery
does not prove the right side: it uses a strictly finer source query. -/
theorem exists_correctJointReceiveQueryReader_iff_fibreConstant
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂)
    {Query : Type q} (fallback : Query)
    (actual : GeneratedReceiveEither strategy → Query) :
    (∃ reader : JointReceiveQueryReader M Query, reader.Correct actual) ↔
      QueryFibreConstant (generatedReceiveEitherFiniteInput M) actual := by
  constructor
  · rintro ⟨reader, hreader⟩ left right hvisible
    calc
      actual left = reader.decode (generatedReceiveEitherFiniteInput M left) :=
        (hreader left).symm
      _ = reader.decode (generatedReceiveEitherFiniteInput M right) :=
        congrArg reader.decode hvisible
      _ = actual right := hreader right
  · intro hconstant
    obtain ⟨decodeOption, hdecode⟩ :=
      (queryFibreConstant_iff_partialFactorizes
        (generatedReceiveEitherFiniteInput M) actual).mp hconstant
    let reader : JointReceiveQueryReader M Query :=
      ⟨fun input => (decodeOption input).getD fallback⟩
    refine ⟨reader, ?_⟩
    intro occurrence
    have h := hdecode occurrence
    simp only [reader]
    rw [h]
    rfl

/-- A correct canonical reader gives `PointedReceiveQueryAligned` at an
actual process-one receive, using only the two pre-round finite summaries and
the two current inputs. -/
theorem JointReceiveQueryReader.aligned_generatedReceiveOne
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {M : LocalSummaryAutomaton.{u, v, o} In₁ In₂} {Query : Type q}
    (reader : JointReceiveQueryReader M Query) (fallback : Query)
    (actual : GeneratedReceiveEither strategy → Query)
    (hcorrect : reader.Correct actual)
    (occurrence : GeneratedReceiveOne strategy) :
    PointedReceiveQueryAligned (reader.toPointed fallback) .one
      (M.read (currentView Proc.one occurrence.history))
      (.inl occurrence.environment.inputOne)
      (M.read (currentView Proc.two occurrence.history))
      (.inr occurrence.environment.inputTwo)
      (actual (.inl occurrence)) := by
  exact hcorrect (.inl occurrence)

/-- Process-two mirror.  It evaluates the same canonical tuple even though
self and other arrive in the opposite order. -/
theorem JointReceiveQueryReader.aligned_generatedReceiveTwo
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {M : LocalSummaryAutomaton.{u, v, o} In₁ In₂} {Query : Type q}
    (reader : JointReceiveQueryReader M Query) (fallback : Query)
    (actual : GeneratedReceiveEither strategy → Query)
    (hcorrect : reader.Correct actual)
    (occurrence : GeneratedReceiveTwo strategy) :
    PointedReceiveQueryAligned (reader.toPointed fallback) .two
      (M.read (currentView Proc.two occurrence.history))
      (.inr occurrence.environment.inputTwo)
      (M.read (currentView Proc.one occurrence.history))
      (.inl occurrence.environment.inputOne)
      (actual (.inr occurrence)) := by
  exact hcorrect (.inr occurrence)

/-! ## Concrete optional pinned-query coordinate audit -/

namespace DetParityAutomaton

variable {I : Type i}
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

/-- The actual pointed query is a function only of settled data.  In
particular it has no current graph argument. -/
noncomputable def profiledOpenOptionalPinnedSettledReceiveQuery
    (semantic : History In₁ In₂ Graph Out₁ Out₂ → In₁ → In₂ →
      ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin basis
        initialCode)
    (tag : History In₁ In₂ Graph Out₁ Out₂ → In₁ → In₂ →
      ProfiledOpenOptionalControlledPinnedTag A initialCode)
    (history : History In₁ In₂ Graph Out₁ Out₂)
    (inputOne : In₁) (inputTwo : In₂) :
    ProfiledOpenOptionalControlledPinnedPointedQuery A initialCode :=
  profiledOpenOptionalControlledPinnedSemanticQuery A strategy hwin basis
    initialCode (semantic history inputOne inputTwo)
    (tag history inputOne inputTwo)

/-- The actual query on a generated receive by either process. -/
noncomputable def profiledOpenOptionalPinnedActualReceiveQuery
    (semantic : History In₁ In₂ Graph Out₁ Out₂ → In₁ → In₂ →
      ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin basis
        initialCode)
    (tag : History In₁ In₂ Graph Out₁ Out₂ → In₁ → In₂ →
      ProfiledOpenOptionalControlledPinnedTag A initialCode) :
    GeneratedReceiveEither strategy →
      ProfiledOpenOptionalControlledPinnedPointedQuery A initialCode :=
  generatedReceiveEitherSettledValue
    (profiledOpenOptionalPinnedSettledReceiveQuery A strategy hwin basis
      initialCode semantic tag)

/-- Full-query constancy on the fibres of one chosen finite summary
automaton. -/
def ProfiledOpenOptionalPinnedReceiveQueryFibreConstant
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂)
    (semantic : History In₁ In₂ Graph Out₁ Out₂ → In₁ → In₂ →
      ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin basis
        initialCode)
    (tag : History In₁ In₂ Graph Out₁ Out₂ → In₁ → In₂ →
      ProfiledOpenOptionalControlledPinnedTag A initialCode) : Prop :=
  QueryFibreConstant (generatedReceiveEitherFiniteInput M)
    (profiledOpenOptionalPinnedActualReceiveQuery A strategy hwin basis
      initialCode semantic tag)

/-- Coordinatewise family constancy. -/
def ProfiledOpenOptionalPinnedReceiveFamilyFibreConstant
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂)
    (semantic : History In₁ In₂ Graph Out₁ Out₂ → In₁ → In₂ →
      ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin basis
        initialCode)
    (tag : History In₁ In₂ Graph Out₁ Out₂ → In₁ → In₂ →
      ProfiledOpenOptionalControlledPinnedTag A initialCode) : Prop :=
  QueryFibreConstant (generatedReceiveEitherFiniteInput M)
    (fun occurrence =>
      (profiledOpenOptionalPinnedActualReceiveQuery A strategy hwin basis
        initialCode semantic tag occurrence).family)

/-- Coordinatewise pinned-tag constancy. -/
def ProfiledOpenOptionalPinnedReceiveTagFibreConstant
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂)
    (semantic : History In₁ In₂ Graph Out₁ Out₂ → In₁ → In₂ →
      ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin basis
        initialCode)
    (tag : History In₁ In₂ Graph Out₁ Out₂ → In₁ → In₂ →
      ProfiledOpenOptionalControlledPinnedTag A initialCode) : Prop :=
  QueryFibreConstant (generatedReceiveEitherFiniteInput M)
    (fun occurrence =>
      (profiledOpenOptionalPinnedActualReceiveQuery A strategy hwin basis
        initialCode semantic tag occurrence).tag)

/-- The smallest unresolved coordinate after the finite public family and
pinned tag have been carried: constancy of the actual hidden descriptor. -/
def ProfiledOpenOptionalPinnedReceiveDescriptorFibreConstant
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂)
    (semantic : History In₁ In₂ Graph Out₁ Out₂ → In₁ → In₂ →
      ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin basis
        initialCode)
    (tag : History In₁ In₂ Graph Out₁ Out₂ → In₁ → In₂ →
      ProfiledOpenOptionalControlledPinnedTag A initialCode) : Prop :=
  QueryFibreConstant (generatedReceiveEitherFiniteInput M)
    (fun occurrence =>
      (profiledOpenOptionalPinnedActualReceiveQuery A strategy hwin basis
        initialCode semantic tag occurrence).descriptor)

/-- Finest descriptor coordinate: current indexed public code. -/
def ProfiledOpenOptionalPinnedReceiveCodeFibreConstant
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂)
    (semantic : History In₁ In₂ Graph Out₁ Out₂ → In₁ → In₂ →
      ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin basis
        initialCode)
    (tag : History In₁ In₂ Graph Out₁ Out₂ → In₁ → In₂ →
      ProfiledOpenOptionalControlledPinnedTag A initialCode) : Prop :=
  QueryFibreConstant (generatedReceiveEitherFiniteInput M)
    (fun occurrence =>
      (profiledOpenOptionalPinnedActualReceiveQuery A strategy hwin basis
        initialCode semantic tag occurrence).descriptor.code)

/-- Finest descriptor coordinate: literal code-parity control. -/
def ProfiledOpenOptionalPinnedReceiveControlFibreConstant
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂)
    (semantic : History In₁ In₂ Graph Out₁ Out₂ → In₁ → In₂ →
      ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin basis
        initialCode)
    (tag : History In₁ In₂ Graph Out₁ Out₂ → In₁ → In₂ →
      ProfiledOpenOptionalControlledPinnedTag A initialCode) : Prop :=
  QueryFibreConstant (generatedReceiveEitherFiniteInput M)
    (fun occurrence =>
      (profiledOpenOptionalPinnedActualReceiveQuery A strategy hwin basis
        initialCode semantic tag occurrence).descriptor.control)

/-- Finest descriptor coordinate: the old finite semantic move identity.
This is not the newly selected pinned family move stored in the public tag. -/
def ProfiledOpenOptionalPinnedReceiveOldMoveFibreConstant
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂)
    (semantic : History In₁ In₂ Graph Out₁ Out₂ → In₁ → In₂ →
      ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin basis
        initialCode)
    (tag : History In₁ In₂ Graph Out₁ Out₂ → In₁ → In₂ →
      ProfiledOpenOptionalControlledPinnedTag A initialCode) : Prop :=
  QueryFibreConstant (generatedReceiveEitherFiniteInput M)
    (fun occurrence =>
      (profiledOpenOptionalPinnedActualReceiveQuery A strategy hwin basis
        initialCode semantic tag occurrence).descriptor.moveIdentity)

/-- The descriptor residual itself splits into three ordinary finite
coordinates.  This pinpoints a future collision without treating the whole
dependent query as opaque. -/
theorem
    profiledOpenOptionalPinnedReceiveDescriptorFibreConstant_iff_coordinates
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂)
    (semantic : History In₁ In₂ Graph Out₁ Out₂ → In₁ → In₂ →
      ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin basis
        initialCode)
    (tag : History In₁ In₂ Graph Out₁ Out₂ → In₁ → In₂ →
      ProfiledOpenOptionalControlledPinnedTag A initialCode) :
    ProfiledOpenOptionalPinnedReceiveDescriptorFibreConstant A strategy hwin
        basis initialCode M semantic tag ↔
      ProfiledOpenOptionalPinnedReceiveCodeFibreConstant A strategy hwin basis
          initialCode M semantic tag ∧
        ProfiledOpenOptionalPinnedReceiveControlFibreConstant A strategy hwin
            basis initialCode M semantic tag ∧
          ProfiledOpenOptionalPinnedReceiveOldMoveFibreConstant A strategy hwin
            basis initialCode M semantic tag := by
  constructor
  · intro hdescriptor
    refine ⟨?_, ?_, ?_⟩ <;> intro left right hvisible
    · exact congrArg HiddenCodeControlDescriptor.code
        (hdescriptor left right hvisible)
    · exact congrArg HiddenCodeControlDescriptor.control
        (hdescriptor left right hvisible)
    · exact congrArg HiddenCodeControlDescriptor.moveIdentity
        (hdescriptor left right hvisible)
  · rintro ⟨hcode, hcontrol, hmove⟩ left right hvisible
    apply Prod.ext
    · apply Prod.ext
      · exact hcode left right hvisible
      · exact hcontrol left right hvisible
    · exact hmove left right hvisible

/-- Full pointed-query constancy is exactly coordinatewise constancy. -/
theorem profiledOpenOptionalPinnedReceiveQueryFibreConstant_iff_coordinates
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂)
    (semantic : History In₁ In₂ Graph Out₁ Out₂ → In₁ → In₂ →
      ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin basis
        initialCode)
    (tag : History In₁ In₂ Graph Out₁ Out₂ → In₁ → In₂ →
      ProfiledOpenOptionalControlledPinnedTag A initialCode) :
    ProfiledOpenOptionalPinnedReceiveQueryFibreConstant A strategy hwin basis
        initialCode M semantic tag ↔
      ProfiledOpenOptionalPinnedReceiveFamilyFibreConstant A strategy hwin basis
          initialCode M semantic tag ∧
        ProfiledOpenOptionalPinnedReceiveDescriptorFibreConstant A strategy hwin
            basis initialCode M semantic tag ∧
          ProfiledOpenOptionalPinnedReceiveTagFibreConstant A strategy hwin basis
            initialCode M semantic tag := by
  constructor
  · intro hfull
    refine ⟨?_, ?_, ?_⟩ <;>
      intro left right hvisible
    · exact congrArg
        ProfiledOpenOptionalControlledPinnedPointedQuery.family
        (hfull left right hvisible)
    · exact congrArg
        ProfiledOpenOptionalControlledPinnedPointedQuery.descriptor
        (hfull left right hvisible)
    · exact congrArg
        ProfiledOpenOptionalControlledPinnedPointedQuery.tag
        (hfull left right hvisible)
  · rintro ⟨hfamily, hdescriptor, htag⟩ left right hvisible
    have hf := hfamily left right hvisible
    have hd := hdescriptor left right hvisible
    have ht := htag left right hvisible
    cases hleft :
        profiledOpenOptionalPinnedActualReceiveQuery A strategy hwin basis
          initialCode semantic tag left with
    | mk leftFamily leftDescriptor leftTag =>
      cases hright :
          profiledOpenOptionalPinnedActualReceiveQuery A strategy hwin basis
            initialCode semantic tag right with
      | mk rightFamily rightDescriptor rightTag =>
        simp only [hleft, hright] at hf hd ht ⊢
        cases hf
        cases hd
        cases ht
        rfl

/-- After public family and pinned-tag recovery, an aligned concrete reader
exists iff the hidden descriptor is constant on the same finite fibres. -/
theorem exists_profiledOpenOptionalPinnedReceiveQueryReader_iff_descriptor
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂)
    (semantic : History In₁ In₂ Graph Out₁ Out₂ → In₁ → In₂ →
      ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin basis
        initialCode)
    (tag : History In₁ In₂ Graph Out₁ Out₂ → In₁ → In₂ →
      ProfiledOpenOptionalControlledPinnedTag A initialCode)
    (fallback : ProfiledOpenOptionalControlledPinnedPointedQuery A initialCode)
    (hfamily : ProfiledOpenOptionalPinnedReceiveFamilyFibreConstant A strategy
      hwin basis initialCode M semantic tag)
    (htag : ProfiledOpenOptionalPinnedReceiveTagFibreConstant A strategy hwin
      basis initialCode M semantic tag) :
    (∃ reader : JointReceiveQueryReader M
        (ProfiledOpenOptionalControlledPinnedPointedQuery A initialCode),
      reader.Correct
        (profiledOpenOptionalPinnedActualReceiveQuery A strategy hwin basis
          initialCode semantic tag)) ↔
      ProfiledOpenOptionalPinnedReceiveDescriptorFibreConstant A strategy hwin
        basis initialCode M semantic tag := by
  rw [exists_correctJointReceiveQueryReader_iff_fibreConstant M fallback]
  constructor
  · intro hfull
    exact
      (profiledOpenOptionalPinnedReceiveQueryFibreConstant_iff_coordinates A
        strategy hwin basis initialCode M semantic tag).mp hfull |>.2.1
  · intro hdescriptor
    exact
      (profiledOpenOptionalPinnedReceiveQueryFibreConstant_iff_coordinates A
        strategy hwin basis initialCode M semantic tag).mpr
        ⟨hfamily, hdescriptor, htag⟩

/-- Positive spelling of the iff: descriptor fibre constancy constructs one
canonical graph-blind `PointedReceiveQueryReader`, and that same reader is
aligned at every generated receive on both sides. -/
theorem exists_alignedProfiledOpenOptionalPinnedPointedReader_of_descriptor
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂)
    (semantic : History In₁ In₂ Graph Out₁ Out₂ → In₁ → In₂ →
      ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin basis
        initialCode)
    (tag : History In₁ In₂ Graph Out₁ Out₂ → In₁ → In₂ →
      ProfiledOpenOptionalControlledPinnedTag A initialCode)
    (fallback : ProfiledOpenOptionalControlledPinnedPointedQuery A initialCode)
    (hfamily : ProfiledOpenOptionalPinnedReceiveFamilyFibreConstant A strategy
      hwin basis initialCode M semantic tag)
    (htag : ProfiledOpenOptionalPinnedReceiveTagFibreConstant A strategy hwin
      basis initialCode M semantic tag)
    (hdescriptor :
      ProfiledOpenOptionalPinnedReceiveDescriptorFibreConstant A strategy hwin
        basis initialCode M semantic tag) :
    ∃ reader : JointReceiveQueryReader M
        (ProfiledOpenOptionalControlledPinnedPointedQuery A initialCode),
      reader.Correct
          (profiledOpenOptionalPinnedActualReceiveQuery A strategy hwin basis
            initialCode semantic tag) ∧
        (∀ occurrence : GeneratedReceiveOne strategy,
          PointedReceiveQueryAligned (reader.toPointed fallback) .one
            (M.read (currentView Proc.one occurrence.history))
            (.inl occurrence.environment.inputOne)
            (M.read (currentView Proc.two occurrence.history))
            (.inr occurrence.environment.inputTwo)
            (profiledOpenOptionalPinnedActualReceiveQuery A strategy hwin basis
              initialCode semantic tag (.inl occurrence))) ∧
        (∀ occurrence : GeneratedReceiveTwo strategy,
          PointedReceiveQueryAligned (reader.toPointed fallback) .two
            (M.read (currentView Proc.two occurrence.history))
            (.inr occurrence.environment.inputTwo)
            (M.read (currentView Proc.one occurrence.history))
            (.inl occurrence.environment.inputOne)
            (profiledOpenOptionalPinnedActualReceiveQuery A strategy hwin basis
              initialCode semantic tag (.inr occurrence))) := by
  obtain ⟨reader, hcorrect⟩ :=
    (exists_profiledOpenOptionalPinnedReceiveQueryReader_iff_descriptor A
      strategy hwin basis initialCode M semantic tag fallback hfamily htag).mpr
      hdescriptor
  refine ⟨reader, hcorrect, ?_, ?_⟩
  · intro occurrence
    exact reader.aligned_generatedReceiveOne fallback _ hcorrect occurrence
  · intro occurrence
    exact reader.aligned_generatedReceiveTwo fallback _ hcorrect occurrence

/-- Exact concrete fail-fast witness: equal finite receive tuples but distinct
actual descriptors refute every aligned reader, even though literal full
views may distinguish the occurrences. -/
theorem no_profiledOpenOptionalPinnedReceiveQueryReader_of_descriptorCollision
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂)
    (semantic : History In₁ In₂ Graph Out₁ Out₂ → In₁ → In₂ →
      ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin basis
        initialCode)
    (tag : History In₁ In₂ Graph Out₁ Out₂ → In₁ → In₂ →
      ProfiledOpenOptionalControlledPinnedTag A initialCode)
    (left right : GeneratedReceiveEither strategy)
    (hvisible : generatedReceiveEitherFiniteInput M left =
      generatedReceiveEitherFiniteInput M right)
    (hdescriptor :
      (profiledOpenOptionalPinnedActualReceiveQuery A strategy hwin basis
          initialCode semantic tag left).descriptor ≠
        (profiledOpenOptionalPinnedActualReceiveQuery A strategy hwin basis
          initialCode semantic tag right).descriptor) :
    ¬ ∃ reader : JointReceiveQueryReader M
        (ProfiledOpenOptionalControlledPinnedPointedQuery A initialCode),
      reader.Correct
        (profiledOpenOptionalPinnedActualReceiveQuery A strategy hwin basis
          initialCode semantic tag) := by
  rintro ⟨reader, hreader⟩
  apply hdescriptor
  apply congrArg ProfiledOpenOptionalControlledPinnedPointedQuery.descriptor
  calc
    profiledOpenOptionalPinnedActualReceiveQuery A strategy hwin basis
        initialCode semantic tag left =
      reader.decode (generatedReceiveEitherFiniteInput M left) :=
        (hreader left).symm
    _ = reader.decode (generatedReceiveEitherFiniteInput M right) :=
      congrArg reader.decode hvisible
    _ = profiledOpenOptionalPinnedActualReceiveQuery A strategy hwin basis
        initialCode semantic tag right := hreader right

/-! ## Present end-to-end receipt carrier specialization -/

open PairedStrategyMemory
open PairedStrategyMemory.PairedInitialProfiledRationalPackage

/-- The exact residual on the repository's current finite receipt carrier.
It does not assert the law; it gives it a concrete, inspectable type. -/
noncomputable abbrev
    ProfiledOpenOptionalEndToEndReceiveDescriptorFibreConstant
    (package : PairedInitialProfiledRationalPackage A)
    (initialOne : EndToEndFamilyReceiptOneSummary A package)
    (initialTwo : EndToEndFamilyReceiptTwoSummary A package)
    (semantic : History In₁ In₂ Graph Out₁ Out₂ → In₁ → In₂ →
      ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin basis
        initialCode)
    (tag : History In₁ In₂ Graph Out₁ Out₂ → In₁ → In₂ →
      ProfiledOpenOptionalControlledPinnedTag A initialCode) :=
  ProfiledOpenOptionalPinnedReceiveDescriptorFibreConstant A strategy hwin
    basis initialCode
    (endToEndFamilyReceiptSummaryAutomaton A package initialOne initialTwo
      (endToEndFamilyReceiptSyncOrActivateReceivePairTable A package))
    semantic tag

end

end DetParityAutomaton

end DistributedSynthesis
