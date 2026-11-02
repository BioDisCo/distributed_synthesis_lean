/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenWitnessedFixedPolicyTable

/-!
# Proof-erased roots for witnessed re-anchored rows

The source-aware table retains a live finite candidate and selects one finite
sidewise bank.  On an active side, candidate validity supplies a re-anchored
query at the literal source descriptor.  This file projects that witness to
the only dependent data needed to evaluate the selected receiver row: a
family member and one canonical root of that member.

The canonical root is not an arbitrary inhabitant.  We open
`ProfiledOpenFixedRightReanchoredQuery.semantic` (or its left mirror), select
its semantic lane, and transport `lane.realization.pivot` through the
propositionally equal classified move with
`profiledOpenHiddenDescriptorRightRootOfEq` (respectively the left map).

The runtime carrier is a finite sigma pair.  All semantic lanes, states,
move equalities, and re-anchoring witnesses occur only in a `Prop` subtype
proof and are erased.  The epoch-entry row remains an explicit argument of
the physical evaluator and is therefore sticky for the whole block; it is
never recomputed from a later physical receipt.  The combined existence
statement is also a proposition, so it does not install a runtime
orientation or strict-leader field.
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

variable [Fintype I] [Inhabited I]
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

/-! ## Finite dependent member/root carriers -/

/-- A right family member paired with a root of precisely that member. -/
abbrev ProfiledOpenFixedRightDependentMemberRoot
    (value : ProfiledOpenFixedRightPinnedValue A initialCode) :=
  Sigma fun member : ProfiledOpenHiddenDescriptorRightCarrier A value.1 ↦
    ProfiledOpenHiddenDescriptorRightRoot A member.1

/-- Left mirror. -/
abbrev ProfiledOpenFixedLeftDependentMemberRoot
    (value : ProfiledOpenFixedLeftPinnedValue A initialCode) :=
  Sigma fun member : ProfiledOpenHiddenDescriptorLeftCarrier A value.1 ↦
    ProfiledOpenHiddenDescriptorLeftRoot A member.1

set_option synthInstance.maxHeartbeats 1600000 in
noncomputable instance profiledOpenFixedRightDependentMemberRoot_fintype
    (value : ProfiledOpenFixedRightPinnedValue A initialCode) :
    Fintype (ProfiledOpenFixedRightDependentMemberRoot A initialCode value) :=
  Fintype.ofFinite _

set_option synthInstance.maxHeartbeats 1600000 in
noncomputable instance profiledOpenFixedLeftDependentMemberRoot_fintype
    (value : ProfiledOpenFixedLeftPinnedValue A initialCode) :
    Fintype (ProfiledOpenFixedLeftDependentMemberRoot A initialCode value) :=
  Fintype.ofFinite _

/-! ## The erased semantic-root predicates -/

/-- A dependent right member/root pair is the literal pivot projection of a
re-anchored semantic row at `current`. -/
def ProfiledOpenFixedRightReanchoredPivotRoot
    (current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode)
    (value : ProfiledOpenFixedRightPinnedValue A initialCode)
    (query : ProfiledOpenFixedRightPinnedBlockQuery A initialCode value)
    (memberRoot : ProfiledOpenFixedRightDependentMemberRoot A initialCode
      value) : Prop :=
  ∃ witness : ProfiledOpenFixedRightReanchoredQuery A strategy hwin basis
      initialCode current value query,
    witness.member = memberRoot.1 ∧
      ∃ lane : ProfiledOpenIndexedRightSemanticLane A strategy hwin basis
          (I := I),
        ∃ _hright : witness.state.1.state.right = some lane,
          ∃ _hdescriptor :
              profiledOpenIndexedOptionalControlledSemanticDescriptor A
                  strategy hwin basis initialCode witness.state =
                memberRoot.1.1,
            let table := ((lane.realization.coherentTable A).table
              |>.toClassified A lane.source)
            ∃ hmove : memberRoot.1.1.moveIdentity.1 =
                ProfiledOpenClassifiedMove.right lane.source table,
              memberRoot.2 =
                  profiledOpenHiddenDescriptorRightRootOfEq A
                    memberRoot.1.1 lane.source table hmove
                    lane.realization.pivot ∧
                ProfiledOpenRightSemanticTableAllowed A lane.source strategy
                  hwin lane.realization.entry basis (fun input ↦
                    profiledOpenFixedRightQueryResponses A initialCode value
                      query memberRoot.1
                      ((profiledOpenHiddenDescriptorRightRootOfEq A
                          memberRoot.1.1 lane.source table hmove input.1.1,
                        input.1.2), input.2))

/-- Left mirror. -/
def ProfiledOpenFixedLeftReanchoredPivotRoot
    (current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode)
    (value : ProfiledOpenFixedLeftPinnedValue A initialCode)
    (query : ProfiledOpenFixedLeftPinnedBlockQuery A initialCode value)
    (memberRoot : ProfiledOpenFixedLeftDependentMemberRoot A initialCode
      value) : Prop :=
  ∃ witness : ProfiledOpenFixedLeftReanchoredQuery A strategy hwin basis
      initialCode current value query,
    witness.member = memberRoot.1 ∧
      ∃ lane : ProfiledOpenIndexedLeftSemanticLane A strategy hwin basis
          (I := I),
        ∃ _hleft : witness.state.1.state.left = some lane,
          ∃ _hdescriptor :
              profiledOpenIndexedOptionalControlledSemanticDescriptor A
                  strategy hwin basis initialCode witness.state =
                memberRoot.1.1,
            let table := ((lane.realization.coherentTable A).table
              |>.toClassified A lane.source)
            ∃ hmove : memberRoot.1.1.moveIdentity.2 =
                ProfiledOpenClassifiedMove.left lane.source table,
              memberRoot.2 =
                  profiledOpenHiddenDescriptorLeftRootOfEq A
                    memberRoot.1.1 lane.source table hmove
                    lane.realization.pivot ∧
                ProfiledOpenLeftSemanticTableAllowed A lane.source strategy
                  hwin lane.realization.entry basis (fun input ↦
                    profiledOpenFixedLeftQueryResponses A initialCode value
                      query memberRoot.1
                      ((profiledOpenHiddenDescriptorLeftRootOfEq A
                          memberRoot.1.1 lane.source table hmove input.1.1,
                        input.1.2), input.2))

/-- The finite right member/root pair, refined only by an erased semantic
projection proof. -/
abbrev ProfiledOpenFixedRightReanchoredRowEvaluation
    (current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode)
    (value : ProfiledOpenFixedRightPinnedValue A initialCode)
    (query : ProfiledOpenFixedRightPinnedBlockQuery A initialCode value) :=
  { memberRoot : ProfiledOpenFixedRightDependentMemberRoot A initialCode value
    // ProfiledOpenFixedRightReanchoredPivotRoot A strategy hwin basis
      initialCode current value query memberRoot }

/-- Left mirror. -/
abbrev ProfiledOpenFixedLeftReanchoredRowEvaluation
    (current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode)
    (value : ProfiledOpenFixedLeftPinnedValue A initialCode)
    (query : ProfiledOpenFixedLeftPinnedBlockQuery A initialCode value) :=
  { memberRoot : ProfiledOpenFixedLeftDependentMemberRoot A initialCode value
    // ProfiledOpenFixedLeftReanchoredPivotRoot A strategy hwin basis
      initialCode current value query memberRoot }

set_option synthInstance.maxHeartbeats 1600000 in
noncomputable instance profiledOpenFixedRightReanchoredRowEvaluation_fintype
    (current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode)
    (value : ProfiledOpenFixedRightPinnedValue A initialCode)
    (query : ProfiledOpenFixedRightPinnedBlockQuery A initialCode value) :
    Fintype (ProfiledOpenFixedRightReanchoredRowEvaluation A strategy hwin
      basis initialCode current value query) :=
  Fintype.ofFinite _

set_option synthInstance.maxHeartbeats 1600000 in
noncomputable instance profiledOpenFixedLeftReanchoredRowEvaluation_fintype
    (current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode)
    (value : ProfiledOpenFixedLeftPinnedValue A initialCode)
    (query : ProfiledOpenFixedLeftPinnedBlockQuery A initialCode value) :
    Fintype (ProfiledOpenFixedLeftReanchoredRowEvaluation A strategy hwin
      basis initialCode current value query) :=
  Fintype.ofFinite _

/-! ## Extraction from the existing re-anchored semantic witnesses -/

omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂] in
/-- The semantic lane's pivot supplies a finite dependent right member/root
pair.  This first form remains in `Prop`, so opening the semantic existential
does not perform a large elimination. -/
theorem nonempty_profiledOpenFixedRightReanchoredRowEvaluationOfWitness
    {current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode}
    {value : ProfiledOpenFixedRightPinnedValue A initialCode}
    {query : ProfiledOpenFixedRightPinnedBlockQuery A initialCode value}
    (witness : ProfiledOpenFixedRightReanchoredQuery A strategy hwin basis
      initialCode current value query) :
    Nonempty (ProfiledOpenFixedRightReanchoredRowEvaluation A strategy hwin
      basis initialCode current value query) := by
  rcases witness.semantic with
    ⟨lane, hright, hdescriptor, hmove, hsemantic⟩
  let table := ((lane.realization.coherentTable A).table
    |>.toClassified A lane.source)
  let root := profiledOpenHiddenDescriptorRightRootOfEq A witness.member.1
    lane.source table hmove lane.realization.pivot
  refine ⟨⟨⟨witness.member, root⟩, ?_⟩⟩
  refine ⟨witness, rfl, lane, hright, hdescriptor, ?_⟩
  exact ⟨hmove, rfl, hsemantic⟩

/-- Noncomputably erase the proof-only semantic lane and retain only its
finite dependent member/root pair. -/
noncomputable def profiledOpenFixedRightReanchoredRowEvaluationOfWitness
    {current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode}
    {value : ProfiledOpenFixedRightPinnedValue A initialCode}
    {query : ProfiledOpenFixedRightPinnedBlockQuery A initialCode value}
    (witness : ProfiledOpenFixedRightReanchoredQuery A strategy hwin basis
      initialCode current value query) :
    ProfiledOpenFixedRightReanchoredRowEvaluation A strategy hwin basis
      initialCode current value query :=
  Classical.choice
    (nonempty_profiledOpenFixedRightReanchoredRowEvaluationOfWitness A
      strategy hwin basis initialCode witness)

omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂] in
/-- Left proposition-level pivot projection. -/
theorem nonempty_profiledOpenFixedLeftReanchoredRowEvaluationOfWitness
    {current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode}
    {value : ProfiledOpenFixedLeftPinnedValue A initialCode}
    {query : ProfiledOpenFixedLeftPinnedBlockQuery A initialCode value}
    (witness : ProfiledOpenFixedLeftReanchoredQuery A strategy hwin basis
      initialCode current value query) :
    Nonempty (ProfiledOpenFixedLeftReanchoredRowEvaluation A strategy hwin
      basis initialCode current value query) := by
  rcases witness.semantic with
    ⟨lane, hleft, hdescriptor, hmove, hsemantic⟩
  let table := ((lane.realization.coherentTable A).table
    |>.toClassified A lane.source)
  let root := profiledOpenHiddenDescriptorLeftRootOfEq A witness.member.1
    lane.source table hmove lane.realization.pivot
  refine ⟨⟨⟨witness.member, root⟩, ?_⟩⟩
  refine ⟨witness, rfl, lane, hleft, hdescriptor, ?_⟩
  exact ⟨hmove, rfl, hsemantic⟩

/-- Left proof-erased finite projection. -/
noncomputable def profiledOpenFixedLeftReanchoredRowEvaluationOfWitness
    {current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode}
    {value : ProfiledOpenFixedLeftPinnedValue A initialCode}
    {query : ProfiledOpenFixedLeftPinnedBlockQuery A initialCode value}
    (witness : ProfiledOpenFixedLeftReanchoredQuery A strategy hwin basis
      initialCode current value query) :
    ProfiledOpenFixedLeftReanchoredRowEvaluation A strategy hwin basis
      initialCode current value query :=
  Classical.choice
    (nonempty_profiledOpenFixedLeftReanchoredRowEvaluationOfWitness A
      strategy hwin basis initialCode witness)

/-! ## Row evaluation keeps the epoch-entry row explicit -/

/-- Classified right receiver output at the projected semantic pivot. -/
noncomputable def profiledOpenFixedRightReanchoredClassifiedOutput
    {current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode}
    {value : ProfiledOpenFixedRightPinnedValue A initialCode}
    {query : ProfiledOpenFixedRightPinnedBlockQuery A initialCode value}
    (evaluation : ProfiledOpenFixedRightReanchoredRowEvaluation A strategy
      hwin basis initialCode current value query)
    (inputOne : In₁) (inputTwo : In₂) :
    ProfiledOpenRightClassifiedOutput A :=
  profiledOpenFixedRightQueryResponses A initialCode value query
    evaluation.1.1 ((evaluation.1.2, inputTwo), inputOne)

/-- The physical informed output is selected by the sticky epoch-entry row,
not by a receipt from the current or preceding physical round. -/
noncomputable def profiledOpenFixedRightReanchoredReceiverOutput
    {current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode}
    {value : ProfiledOpenFixedRightPinnedValue A initialCode}
    {query : ProfiledOpenFixedRightPinnedBlockQuery A initialCode value}
    (evaluation : ProfiledOpenFixedRightReanchoredRowEvaluation A strategy
      hwin basis initialCode current value query)
    (entryRow : PairedEntryRow) (inputOne : In₁) (inputTwo : In₂) : Out₂ :=
  pairedRightInformedForRow entryRow
    (profiledOpenFixedRightReanchoredClassifiedOutput A strategy hwin basis
      initialCode evaluation inputOne inputTwo).1.physical

/-- Left classified evaluation. -/
noncomputable def profiledOpenFixedLeftReanchoredClassifiedOutput
    {current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode}
    {value : ProfiledOpenFixedLeftPinnedValue A initialCode}
    {query : ProfiledOpenFixedLeftPinnedBlockQuery A initialCode value}
    (evaluation : ProfiledOpenFixedLeftReanchoredRowEvaluation A strategy hwin
      basis initialCode current value query)
    (inputOne : In₁) (inputTwo : In₂) :
    ProfiledOpenLeftClassifiedOutput A :=
  profiledOpenFixedLeftQueryResponses A initialCode value query evaluation.1.1
    ((evaluation.1.2, inputOne), inputTwo)

/-- Left sticky-row physical projection. -/
noncomputable def profiledOpenFixedLeftReanchoredReceiverOutput
    {current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode}
    {value : ProfiledOpenFixedLeftPinnedValue A initialCode}
    {query : ProfiledOpenFixedLeftPinnedBlockQuery A initialCode value}
    (evaluation : ProfiledOpenFixedLeftReanchoredRowEvaluation A strategy hwin
      basis initialCode current value query)
    (entryRow : PairedEntryRow) (inputOne : In₁) (inputTwo : In₂) : Out₁ :=
  pairedLeftInformedForRow entryRow
    (profiledOpenFixedLeftReanchoredClassifiedOutput A strategy hwin basis
      initialCode evaluation inputOne inputTwo).1.physical

/-! ## Source-aware witnessed candidate projection -/

private abbrev WitnessedEncodedCandidate :=
  RelationalFamilyCandidate
    (ProfiledOpenWitnessedTableFamily A initialCode)
    (ProfiledOpenWitnessedTableDescriptor A initialCode)

private abbrev WitnessedEncodedLive :=
  SourceAwareRelationalLive
    (ProfiledOpenWitnessedTableBaseLive A strategy hwin basis initialCode)

private abbrev WitnessedEncodedValid :=
  SourceAwareRelationalCandidateValid
    (ProfiledOpenWitnessedTableBaseValid A strategy hwin basis initialCode)

/-- The exact extra premise needed to project an active root.  Reachability
of a controller query alone does not imply this membership: optional
semantic states may be one-sided or sink-shaped. -/
def ProfiledOpenWitnessedSourceActiveForQuery
    (source : WitnessedEncodedCandidate A initialCode)
    (query : ProfiledOpenWitnessedTableQuery A initialCode) : Prop :=
  match query.1.1.1 with
  | .right => source.2.2 ∈ source.1.2.1
  | .left => source.2.2 ∈ source.1.2.2

/-- Right-side source-aware projection.  `hlive` is retained at the model
boundary to record that `source` is the distinguished real candidate; the
actual root construction uses the stronger per-member row law in `hvalid`. -/
noncomputable def profiledOpenWitnessedRightReanchoredRowEvaluation
    (source : WitnessedEncodedCandidate A initialCode)
    (bank : ProfiledOpenWitnessedTableBank A initialCode)
    (query : ProfiledOpenWitnessedTableQuery A initialCode)
    (_hlive : WitnessedEncodedLive A strategy hwin basis initialCode source.2
      source.1)
    (hvalid : WitnessedEncodedValid A strategy hwin basis initialCode source.2
      source.1 bank)
    (hactive : source.2.2 ∈ source.1.2.1) :
    ProfiledOpenFixedRightReanchoredRowEvaluation A strategy hwin basis
      initialCode source.2.2 (bank.1 source.1.1.1)
        (query.1.1.2.1 (bank.1 source.1.1.1)) := by
  let value := bank.1 source.1.1.1
  let selected := query.1.1.2.1 value
  have hmember : source.2.2 ∈ value.1.1 := hvalid.2.1.1 hactive
  have hrows : ProfiledOpenFixedRightValueHasReanchoredRows A strategy hwin
      basis initialCode value := hvalid.2.2.1 hactive
  have hreachable : ProfiledOpenFixedRightQueryReachable A initialCode value
      selected := query.2.1 value
  let witness := Classical.choice
    (hrows source.2.2 hmember selected hreachable)
  exact profiledOpenFixedRightReanchoredRowEvaluationOfWitness A strategy hwin
    basis initialCode witness

/-- Left mirror. -/
noncomputable def profiledOpenWitnessedLeftReanchoredRowEvaluation
    (source : WitnessedEncodedCandidate A initialCode)
    (bank : ProfiledOpenWitnessedTableBank A initialCode)
    (query : ProfiledOpenWitnessedTableQuery A initialCode)
    (_hlive : WitnessedEncodedLive A strategy hwin basis initialCode source.2
      source.1)
    (hvalid : WitnessedEncodedValid A strategy hwin basis initialCode source.2
      source.1 bank)
    (hactive : source.2.2 ∈ source.1.2.2) :
    ProfiledOpenFixedLeftReanchoredRowEvaluation A strategy hwin basis
      initialCode source.2.2 (bank.2 source.1.1.2)
        (query.1.1.2.2 (bank.2 source.1.1.2)) := by
  let value := bank.2 source.1.1.2
  let selected := query.1.1.2.2 value
  have hmember : source.2.2 ∈ value.1.2 := hvalid.2.1.2 hactive
  have hrows : ProfiledOpenFixedLeftValueHasReanchoredRows A strategy hwin
      basis initialCode value := hvalid.2.2.2 hactive
  have hreachable : ProfiledOpenFixedLeftQueryReachable A initialCode value
      selected := query.2.2 value
  let witness := Classical.choice
    (hrows source.2.2 hmember selected hreachable)
  exact profiledOpenFixedLeftReanchoredRowEvaluationOfWitness A strategy hwin
    basis initialCode witness

omit [Inhabited I] in
/-- Shape-free, proof-only existence of the appropriate active projection.
The match is eliminated inside `Prop`; no process state gains the selected
side. -/
theorem exists_profiledOpenWitnessedActiveReanchoredRowEvaluation
    (source : WitnessedEncodedCandidate A initialCode)
    (bank : ProfiledOpenWitnessedTableBank A initialCode)
    (query : ProfiledOpenWitnessedTableQuery A initialCode)
    (hlive : WitnessedEncodedLive A strategy hwin basis initialCode source.2
      source.1)
    (hvalid : WitnessedEncodedValid A strategy hwin basis initialCode source.2
      source.1 bank)
    (hactive : ProfiledOpenWitnessedSourceActiveForQuery A initialCode source
      query) :
    match query.1.1.1 with
    | .right => Nonempty
        (ProfiledOpenFixedRightReanchoredRowEvaluation A strategy hwin basis
          initialCode source.2.2 (bank.1 source.1.1.1)
            (query.1.1.2.1 (bank.1 source.1.1.1)))
    | .left => Nonempty
        (ProfiledOpenFixedLeftReanchoredRowEvaluation A strategy hwin basis
          initialCode source.2.2 (bank.2 source.1.1.2)
            (query.1.1.2.2 (bank.2 source.1.1.2))) := by
  split
  next hright =>
    have hactiveRight : source.2.2 ∈ source.1.2.1 := by
      simpa [ProfiledOpenWitnessedSourceActiveForQuery, hright] using hactive
    exact ⟨profiledOpenWitnessedRightReanchoredRowEvaluation A strategy hwin
      basis initialCode source bank query hlive hvalid hactiveRight⟩
  next hleft =>
    have hactiveLeft : source.2.2 ∈ source.1.2.2 := by
      simpa [ProfiledOpenWitnessedSourceActiveForQuery, hleft] using hactive
    exact ⟨profiledOpenWitnessedLeftReanchoredRowEvaluation A strategy hwin
      basis initialCode source bank query hlive hvalid hactiveLeft⟩

end

end DetParityAutomaton

end DistributedSynthesis
