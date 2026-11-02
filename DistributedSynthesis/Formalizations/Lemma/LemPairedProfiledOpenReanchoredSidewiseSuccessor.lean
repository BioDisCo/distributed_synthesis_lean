/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenFixedSidewisePointedSuccessor

/-!
# Re-anchoring an active side inside a selected fixed fibre

A sidewise bank value need not have been extracted at the literal semantic
state represented by the current candidate.  What its public active fibre
does provide is stronger and sufficient for a relational proof: every member
descriptor has a canonical semantic witness inside the value's own anchor
fibre.  The exact thread may reselect that witness before taking the next
oriented step.

This file performs the shape-sensitive part of that construction.  Active
right membership eliminates the sink and left-only dispatcher shapes; the
right-only and both shapes use their existing canonical fibre-member
constructors.  The selected controller row is proved semantic for that very
member.  The left theorem is symmetric.

All case distinctions and re-anchored witnesses are proof-side.  No process
receives a lane, graph, orientation, strict-leader flag, descriptor, or bank
class.
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

variable (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
variable (hwin : ∀ env : EnvironmentSequence In₁ In₂,
  A.Accepts (execution strategy env))
variable (basis : ∀ state : PairedProfiledTreeState A,
  (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
variable (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))

noncomputable local instance reanchoredDescriptorDecidableEq :
    DecidableEq
      (ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode) :=
  Classical.decEq _

private abbrev ReanchoredDescriptor :=
  ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode

/-! ## A uniform semantic law tied to the re-anchored state -/

/-- A right response row is semantic for the literal active lane of the
given re-anchored optional state. -/
def ProfiledOpenFixedRightReanchoredSemanticAllowed
    (state : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode)
    {value : ProfiledOpenFixedRightPinnedValue A initialCode}
    (member : ProfiledOpenHiddenDescriptorRightCarrier A value.1)
    (responses :
      ((ProfiledOpenHiddenDescriptorRightRoot A member.1 × In₂) × In₁) →
        ProfiledOpenRightClassifiedOutput A) : Prop :=
  ∃ lane : ProfiledOpenIndexedRightSemanticLane A strategy hwin basis
      (I := I),
    ∃ hright : state.1.state.right = some lane,
    ∃ hdescriptor :
      profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
          basis initialCode state = member.1,
    let table := ((lane.realization.coherentTable A).table
      |>.toClassified A lane.source)
    ∃ hmove : member.1.moveIdentity.1 =
        ProfiledOpenClassifiedMove.right lane.source table,
      ProfiledOpenRightSemanticTableAllowed A lane.source strategy hwin
        lane.realization.entry basis (fun input ↦
          responses
            ((profiledOpenHiddenDescriptorRightRootOfEq A member.1 lane.source
                table hmove input.1.1,
              input.1.2), input.2))

/-- Left mirror. -/
def ProfiledOpenFixedLeftReanchoredSemanticAllowed
    (state : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode)
    {value : ProfiledOpenFixedLeftPinnedValue A initialCode}
    (member : ProfiledOpenHiddenDescriptorLeftCarrier A value.1)
    (responses :
      ((ProfiledOpenHiddenDescriptorLeftRoot A member.1 × In₁) × In₂) →
        ProfiledOpenLeftClassifiedOutput A) : Prop :=
  ∃ lane : ProfiledOpenIndexedLeftSemanticLane A strategy hwin basis
      (I := I),
    ∃ hleft : state.1.state.left = some lane,
    ∃ hdescriptor :
      profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
          basis initialCode state = member.1,
    let table := ((lane.realization.coherentTable A).table
      |>.toClassified A lane.source)
    ∃ hmove : member.1.moveIdentity.2 =
        ProfiledOpenClassifiedMove.left lane.source table,
      ProfiledOpenLeftSemanticTableAllowed A lane.source strategy hwin
        lane.realization.entry basis (fun input ↦
          responses
            ((profiledOpenHiddenDescriptorLeftRootOfEq A member.1 lane.source
                table hmove input.1.1,
              input.1.2), input.2))

/-! ## The exact one-side re-anchoring packages -/

/-- A reachable right query, re-anchored at a semantic state whose descriptor
is exactly the requested current descriptor and whose literal emitted row is
semantic there. -/
structure ProfiledOpenFixedRightReanchoredQuery
    (current : ReanchoredDescriptor A initialCode)
    (value : ProfiledOpenFixedRightPinnedValue A initialCode)
    (query : ProfiledOpenFixedRightPinnedBlockQuery A initialCode value) where
  state : ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin
    basis initialCode
  member : ProfiledOpenHiddenDescriptorRightCarrier A value.1
  member_eq : member.1 = current
  state_descriptor :
    profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
      basis initialCode state = current
  reachable : ProfiledOpenFixedRightQueryReachable A initialCode value query
  semantic : ProfiledOpenFixedRightReanchoredSemanticAllowed A strategy hwin
    basis initialCode state member
      (profiledOpenFixedRightQueryResponses A initialCode value query member)

/-- Left mirror. -/
structure ProfiledOpenFixedLeftReanchoredQuery
    (current : ReanchoredDescriptor A initialCode)
    (value : ProfiledOpenFixedLeftPinnedValue A initialCode)
    (query : ProfiledOpenFixedLeftPinnedBlockQuery A initialCode value) where
  state : ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin
    basis initialCode
  member : ProfiledOpenHiddenDescriptorLeftCarrier A value.1
  member_eq : member.1 = current
  state_descriptor :
    profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
      basis initialCode state = current
  reachable : ProfiledOpenFixedLeftQueryReachable A initialCode value query
  semantic : ProfiledOpenFixedLeftReanchoredSemanticAllowed A strategy hwin
    basis initialCode state member
      (profiledOpenFixedLeftQueryResponses A initialCode value query member)

/-! ## Shape elimination for one explicit provenance bank -/

/-- Right projection of one explicitly retained optional provenance bank. -/
noncomputable def profiledOpenOptionalStrongRightValueOfBank
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode)
    (bank : ProfiledOpenIndexedOptionalSourceFibreProvenanceBank A strategy
      hwin basis
      (profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
        initialCode (fun _ ↦ point.2)) point.1) :
    ProfiledOpenFixedRightPinnedValue A initialCode :=
  let move :=
    profiledOpenOptionalFixedPinnedSemanticMoveOfBank.{i, u, v, x, y, s,
      max i u v x y s, max i u v x y s} A strategy hwin basis initialCode
      (fun _ ↦ point.2) point.1 bank
  move.rightValue A initialCode

/-- Left projection. -/
noncomputable def profiledOpenOptionalStrongLeftValueOfBank
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode)
    (bank : ProfiledOpenIndexedOptionalSourceFibreProvenanceBank A strategy
      hwin basis
      (profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
        initialCode (fun _ ↦ point.2)) point.1) :
    ProfiledOpenFixedLeftPinnedValue A initialCode :=
  let move :=
    profiledOpenOptionalFixedPinnedSemanticMoveOfBank.{i, u, v, x, y, s,
      max i u v x y s, max i u v x y s} A strategy hwin basis initialCode
      (fun _ ↦ point.2) point.1 bank
  move.leftValue A initialCode

set_option maxHeartbeats 3200000 in
/-- Active right membership constructs the exact semantic fibre member and
proves the selected row semantic at that same re-anchored state. -/
noncomputable def profiledOpenOptionalStrongRightValueOfBank_reanchor
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode)
    (bank : ProfiledOpenIndexedOptionalSourceFibreProvenanceBank A strategy
      hwin basis
      (profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
        initialCode (fun _ ↦ point.2)) point.1)
    (current : ReanchoredDescriptor A initialCode)
    (hmember : current ∈
      (profiledOpenOptionalStrongRightValueOfBank A strategy hwin basis
        initialCode point bank).1.1)
    (query : ProfiledOpenFixedRightPinnedBlockQuery A initialCode
      (profiledOpenOptionalStrongRightValueOfBank A strategy hwin basis
        initialCode point bank))
    (hreachable : ProfiledOpenFixedRightQueryReachable A initialCode
      (profiledOpenOptionalStrongRightValueOfBank A strategy hwin basis
        initialCode point bank) query) :
    ProfiledOpenFixedRightReanchoredQuery A strategy hwin basis initialCode
      current
      (profiledOpenOptionalStrongRightValueOfBank A strategy hwin basis
        initialCode point bank) query := by
  cases bank with
  | sink hright hleft =>
      simp [profiledOpenOptionalStrongRightValueOfBank,
        profiledOpenOptionalFixedPinnedSemanticMoveOfBank,
        profiledOpenOptionalSinkFamilyCode] at hmember
  | leftOnly lane hright hleft move =>
      simp only [profiledOpenOptionalStrongRightValueOfBank,
        profiledOpenOptionalFixedPinnedSemanticMoveOfBank,
        ProfiledOpenHiddenDescriptorPairedPinnedFamilyMove.rightValue_family]
        at hmember
      have hempty :
          (profiledOpenOptionalLeftOnlyFamilyCode A strategy hwin basis
            initialCode (fun _ ↦ point.2)
            (point.1.toLeftOnly A strategy hwin basis lane hright hleft)).1 =
            ∅ :=
        profiledOpenOptionalLeftOnlyFamilyCode_right A strategy hwin basis
          initialCode (fun _ ↦ point.2)
          (point.1.toLeftOnly A strategy hwin basis lane hright hleft)
      rw [hempty] at hmember
      exact (by simpa using hmember : False).elim
  | rightOnly lane hright hleft move =>
      let control := fun _ : ProfiledOpenIndexedCorrelatedSemanticState A
        strategy hwin basis (I := I) ↦ point.2
      let source := point.1.toRightOnly A strategy hwin basis lane hright hleft
      let member : ProfiledOpenHiddenDescriptorRightCarrier A
          (profiledOpenOptionalRightOnlyFamilyCode A strategy hwin basis
            initialCode control source) := ⟨current, hmember⟩
      let reanchored := profiledOpenOptionalRightOnlyPoint A strategy hwin basis
        initialCode control source member
      let state : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
          hwin basis initialCode := (reanchored.optional, point.2)
      refine {
        state := state
        member := member
        member_eq := rfl
        state_descriptor := ?_
        reachable := hreachable
        semantic := ?_ }
      · exact profiledOpenOptionalRightOnlyPoint_descriptor A strategy hwin
          basis initialCode control source member
      · rcases hreachable with ⟨word, hword⟩
        refine ⟨reanchored.lane, reanchored.right_eq,
          profiledOpenOptionalRightOnlyPoint_descriptor A strategy hwin basis
            initialCode control source member, ?_⟩
        let table := ((reanchored.lane.realization.coherentTable A).table
          |>.toClassified A reanchored.lane.source)
        let hmove := profiledOpenOptionalRightOnlyPoint_moveIdentity A strategy
          hwin basis initialCode control source member
        refine ⟨hmove, ?_⟩
        have hall :=
          (profiledOpenOptionalRightOnlyPinnedProvenanceMoveOfWinning A
            strategy hwin basis initialCode control source).2 word query.2
        have hsemantic := hall member
        unfold profiledOpenFixedRightQueryResponses
        rw [← hword]
        exact hsemantic
  | both rightLane leftLane hright hleft move =>
      let control := fun _ : ProfiledOpenFixedPinnedSemanticPoint A strategy
        hwin basis (I := I) ↦ point.2
      let source := point.1.toLiveFresh A strategy hwin basis rightLane
        leftLane hright hleft
      let member : ProfiledOpenHiddenDescriptorRightCarrier A
          (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
            control source) := ⟨current, hmember⟩
      let reanchored := profiledOpenFixedPinnedRightPoint A strategy hwin basis
        initialCode control source member
      let state : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
          hwin basis initialCode :=
        (ProfiledOpenIndexedOptionalFreshSemanticPoint.ofLiveFresh A strategy
          hwin basis reanchored, point.2)
      refine {
        state := state
        member := member
        member_eq := rfl
        state_descriptor := ?_
        reachable := hreachable
        semantic := ?_ }
      · exact profiledOpenFixedPinnedRightPoint_descriptor A strategy hwin
          basis initialCode control source member
      · rcases hreachable with ⟨word, hword⟩
        refine ⟨reanchored.rightLane, reanchored.right_eq,
          profiledOpenFixedPinnedRightPoint_descriptor A strategy hwin basis
            initialCode control source member, ?_⟩
        let table := ((reanchored.rightLane.realization.coherentTable A).table
          |>.toClassified A reanchored.rightLane.source)
        let hmove := profiledOpenFixedPinnedRightPoint_moveIdentity A strategy
          hwin basis initialCode control source member
        refine ⟨hmove, ?_⟩
        have hall :=
          (profiledOpenFixedPinnedRightProvenanceMoveOfWinning A strategy hwin
            basis initialCode control source).2 word query.2
        have hsemantic := hall member
        unfold profiledOpenFixedRightQueryResponses
        rw [← hword]
        exact hsemantic

set_option maxHeartbeats 3200000 in
/-- Active left membership constructs the symmetric exact semantic fibre
member and proves the selected row semantic at that re-anchored state. -/
noncomputable def profiledOpenOptionalStrongLeftValueOfBank_reanchor
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode)
    (bank : ProfiledOpenIndexedOptionalSourceFibreProvenanceBank A strategy
      hwin basis
      (profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
        initialCode (fun _ ↦ point.2)) point.1)
    (current : ReanchoredDescriptor A initialCode)
    (hmember : current ∈
      (profiledOpenOptionalStrongLeftValueOfBank A strategy hwin basis
        initialCode point bank).1.2)
    (query : ProfiledOpenFixedLeftPinnedBlockQuery A initialCode
      (profiledOpenOptionalStrongLeftValueOfBank A strategy hwin basis
        initialCode point bank))
    (hreachable : ProfiledOpenFixedLeftQueryReachable A initialCode
      (profiledOpenOptionalStrongLeftValueOfBank A strategy hwin basis
        initialCode point bank) query) :
    ProfiledOpenFixedLeftReanchoredQuery A strategy hwin basis initialCode
      current
      (profiledOpenOptionalStrongLeftValueOfBank A strategy hwin basis
        initialCode point bank) query := by
  cases bank with
  | sink hright hleft =>
      simp [profiledOpenOptionalStrongLeftValueOfBank,
        profiledOpenOptionalFixedPinnedSemanticMoveOfBank,
        profiledOpenOptionalSinkFamilyCode] at hmember
  | rightOnly lane hright hleft move =>
      simp only [profiledOpenOptionalStrongLeftValueOfBank,
        profiledOpenOptionalFixedPinnedSemanticMoveOfBank,
        ProfiledOpenHiddenDescriptorPairedPinnedFamilyMove.leftValue_family]
        at hmember
      have hempty :
          (profiledOpenOptionalRightOnlyFamilyCode A strategy hwin basis
            initialCode (fun _ ↦ point.2)
            (point.1.toRightOnly A strategy hwin basis lane hright hleft)).2 =
            ∅ :=
        profiledOpenOptionalRightOnlyFamilyCode_left A strategy hwin basis
          initialCode (fun _ ↦ point.2)
          (point.1.toRightOnly A strategy hwin basis lane hright hleft)
      rw [hempty] at hmember
      exact (by simpa using hmember : False).elim
  | leftOnly lane hright hleft move =>
      let control := fun _ : ProfiledOpenIndexedCorrelatedSemanticState A
        strategy hwin basis (I := I) ↦ point.2
      let source := point.1.toLeftOnly A strategy hwin basis lane hright hleft
      let member : ProfiledOpenHiddenDescriptorLeftCarrier A
          (profiledOpenOptionalLeftOnlyFamilyCode A strategy hwin basis
            initialCode control source) := ⟨current, hmember⟩
      let reanchored := profiledOpenOptionalLeftOnlyPoint A strategy hwin basis
        initialCode control source member
      let state : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
          hwin basis initialCode := (reanchored.optional, point.2)
      refine {
        state := state
        member := member
        member_eq := rfl
        state_descriptor := ?_
        reachable := hreachable
        semantic := ?_ }
      · exact profiledOpenOptionalLeftOnlyPoint_descriptor A strategy hwin
          basis initialCode control source member
      · rcases hreachable with ⟨word, hword⟩
        refine ⟨reanchored.lane, reanchored.left_eq,
          profiledOpenOptionalLeftOnlyPoint_descriptor A strategy hwin basis
            initialCode control source member, ?_⟩
        let table := ((reanchored.lane.realization.coherentTable A).table
          |>.toClassified A reanchored.lane.source)
        let hmove := profiledOpenOptionalLeftOnlyPoint_moveIdentity A strategy
          hwin basis initialCode control source member
        refine ⟨hmove, ?_⟩
        have hall :=
          (profiledOpenOptionalLeftOnlyPinnedProvenanceMoveOfWinning A
            strategy hwin basis initialCode control source).2 word query.2
        have hsemantic := hall member
        unfold profiledOpenFixedLeftQueryResponses
        rw [← hword]
        exact hsemantic
  | both rightLane leftLane hright hleft move =>
      let control := fun _ : ProfiledOpenFixedPinnedSemanticPoint A strategy
        hwin basis (I := I) ↦ point.2
      let source := point.1.toLiveFresh A strategy hwin basis rightLane
        leftLane hright hleft
      let member : ProfiledOpenHiddenDescriptorLeftCarrier A
          (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
            control source) := ⟨current, hmember⟩
      let reanchored := profiledOpenFixedPinnedLeftPoint A strategy hwin basis
        initialCode control source member
      let state : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
          hwin basis initialCode :=
        (ProfiledOpenIndexedOptionalFreshSemanticPoint.ofLiveFresh A strategy
          hwin basis reanchored, point.2)
      refine {
        state := state
        member := member
        member_eq := rfl
        state_descriptor := ?_
        reachable := hreachable
        semantic := ?_ }
      · exact profiledOpenFixedPinnedLeftPoint_descriptor A strategy hwin basis
          initialCode control source member
      · rcases hreachable with ⟨word, hword⟩
        refine ⟨reanchored.leftLane, reanchored.left_eq,
          profiledOpenFixedPinnedLeftPoint_descriptor A strategy hwin basis
            initialCode control source member, ?_⟩
        let table := ((reanchored.leftLane.realization.coherentTable A).table
          |>.toClassified A reanchored.leftLane.source)
        let hmove := profiledOpenFixedPinnedLeftPoint_moveIdentity A strategy
          hwin basis initialCode control source member
        refine ⟨hmove, ?_⟩
        have hall :=
          (profiledOpenFixedPinnedLeftProvenanceMoveOfWinning A strategy hwin
            basis initialCode control source).2 word query.2
        have hsemantic := hall member
        unfold profiledOpenFixedLeftQueryResponses
        rw [← hword]
        exact hsemantic

/-! ## Winning-dispatcher adapters -/

set_option maxHeartbeats 3200000 in
/-- The winning optional dispatcher is definitionally the preceding explicit
bank construction. -/
noncomputable def profiledOpenOptionalStrongRightValue_reanchor
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode)
    (current : ReanchoredDescriptor A initialCode)
    (hmember : current ∈
      (profiledOpenOptionalStrongRightValue A strategy hwin basis initialCode
        point).1.1)
    (query : ProfiledOpenFixedRightPinnedBlockQuery A initialCode
      (profiledOpenOptionalStrongRightValue A strategy hwin basis initialCode
        point))
    (hreachable : ProfiledOpenFixedRightQueryReachable A initialCode
      (profiledOpenOptionalStrongRightValue A strategy hwin basis initialCode
        point) query) :
    ProfiledOpenFixedRightReanchoredQuery A strategy hwin basis initialCode
      current
      (profiledOpenOptionalStrongRightValue A strategy hwin basis initialCode
        point) query := by
  let bank :=
    profiledOpenIndexedOptionalSourceFibreProvenanceBankOfWinning A strategy
      hwin basis
      (profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
        initialCode (fun _ ↦ point.2)) point.1
  simpa only [profiledOpenOptionalStrongRightValue,
      profiledOpenOptionalFixedPinnedSemanticMoveOfWinning,
      profiledOpenOptionalStrongRightValueOfBank] using
    (profiledOpenOptionalStrongRightValueOfBank_reanchor A strategy hwin basis
      initialCode point bank current hmember query hreachable)

set_option maxHeartbeats 3200000 in
/-- Left winning-dispatcher adapter. -/
noncomputable def profiledOpenOptionalStrongLeftValue_reanchor
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode)
    (current : ReanchoredDescriptor A initialCode)
    (hmember : current ∈
      (profiledOpenOptionalStrongLeftValue A strategy hwin basis initialCode
        point).1.2)
    (query : ProfiledOpenFixedLeftPinnedBlockQuery A initialCode
      (profiledOpenOptionalStrongLeftValue A strategy hwin basis initialCode
        point))
    (hreachable : ProfiledOpenFixedLeftQueryReachable A initialCode
      (profiledOpenOptionalStrongLeftValue A strategy hwin basis initialCode
        point) query) :
    ProfiledOpenFixedLeftReanchoredQuery A strategy hwin basis initialCode
      current
      (profiledOpenOptionalStrongLeftValue A strategy hwin basis initialCode
        point) query := by
  let bank :=
    profiledOpenIndexedOptionalSourceFibreProvenanceBankOfWinning A strategy
      hwin basis
      (profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
        initialCode (fun _ ↦ point.2)) point.1
  simpa only [profiledOpenOptionalStrongLeftValue,
      profiledOpenOptionalFixedPinnedSemanticMoveOfWinning,
      profiledOpenOptionalStrongLeftValueOfBank] using
    (profiledOpenOptionalStrongLeftValueOfBank_reanchor A strategy hwin basis
      initialCode point bank current hmember query hreachable)

/-- Existential fixed-value provenance is enough to produce a re-anchored
witness.  The result is kept in `Nonempty`, so the proof-side existential is
never eliminated into runtime controller data. -/
theorem profiledOpenFixedRightValue_reanchor_of_provenance
    (value : ProfiledOpenFixedRightPinnedValue A initialCode)
    (hprovenance : ProfiledOpenFixedRightValueHasDispatcherProvenance A
      strategy hwin basis initialCode value)
    (current : ReanchoredDescriptor A initialCode)
    (hmember : current ∈ value.1.1)
    (query : ProfiledOpenFixedRightPinnedBlockQuery A initialCode value)
    (hreachable : ProfiledOpenFixedRightQueryReachable A initialCode value
      query) :
    Nonempty
      (ProfiledOpenFixedRightReanchoredQuery A strategy hwin basis initialCode
        current value query) := by
  rcases hprovenance with ⟨point, rfl⟩
  exact ⟨profiledOpenOptionalStrongRightValue_reanchor A strategy hwin basis
    initialCode point current hmember query hreachable⟩

/-- Left existential-provenance adapter. -/
theorem profiledOpenFixedLeftValue_reanchor_of_provenance
    (value : ProfiledOpenFixedLeftPinnedValue A initialCode)
    (hprovenance : ProfiledOpenFixedLeftValueHasDispatcherProvenance A
      strategy hwin basis initialCode value)
    (current : ReanchoredDescriptor A initialCode)
    (hmember : current ∈ value.1.2)
    (query : ProfiledOpenFixedLeftPinnedBlockQuery A initialCode value)
    (hreachable : ProfiledOpenFixedLeftQueryReachable A initialCode value
      query) :
    Nonempty
      (ProfiledOpenFixedLeftReanchoredQuery A strategy hwin basis initialCode
        current value query) := by
  rcases hprovenance with ⟨point, rfl⟩
  exact ⟨profiledOpenOptionalStrongLeftValue_reanchor A strategy hwin basis
    initialCode point current hmember query hreachable⟩

/-! ## General per-member provenance (the adapter-facing interface) -/

/-- A fixed right value has semantic provenance at every advertised member
and every reachable literal controller query.  Unlike
`HasDispatcherProvenance`, this does not require the entire fixed value to be
the projection of one optional four-shape dispatcher. -/
def ProfiledOpenFixedRightValueHasReanchoredRows
    (value : ProfiledOpenFixedRightPinnedValue A initialCode) : Prop :=
  ∀ (current : ReanchoredDescriptor A initialCode), current ∈ value.1.1 →
    ∀ query : ProfiledOpenFixedRightPinnedBlockQuery A initialCode value,
      ProfiledOpenFixedRightQueryReachable A initialCode value query →
        Nonempty
          (ProfiledOpenFixedRightReanchoredQuery A strategy hwin basis
            initialCode current value query)

/-- Left mirror. -/
def ProfiledOpenFixedLeftValueHasReanchoredRows
    (value : ProfiledOpenFixedLeftPinnedValue A initialCode) : Prop :=
  ∀ (current : ReanchoredDescriptor A initialCode), current ∈ value.1.2 →
    ∀ query : ProfiledOpenFixedLeftPinnedBlockQuery A initialCode value,
      ProfiledOpenFixedLeftQueryReachable A initialCode value query →
        Nonempty
          (ProfiledOpenFixedLeftReanchoredQuery A strategy hwin basis
            initialCode current value query)

/-- The old single-dispatcher predicate is one sufficient source of the
general right per-member law. -/
theorem profiledOpenFixedRightValue_hasReanchoredRows_of_provenance
    (value : ProfiledOpenFixedRightPinnedValue A initialCode)
    (hprovenance : ProfiledOpenFixedRightValueHasDispatcherProvenance A
      strategy hwin basis initialCode value) :
    ProfiledOpenFixedRightValueHasReanchoredRows A strategy hwin basis
      initialCode value := by
  intro current hmember query hreachable
  exact profiledOpenFixedRightValue_reanchor_of_provenance A strategy hwin
    basis initialCode value hprovenance current hmember query hreachable

/-- Left old-to-general adapter. -/
theorem profiledOpenFixedLeftValue_hasReanchoredRows_of_provenance
    (value : ProfiledOpenFixedLeftPinnedValue A initialCode)
    (hprovenance : ProfiledOpenFixedLeftValueHasDispatcherProvenance A
      strategy hwin basis initialCode value) :
    ProfiledOpenFixedLeftValueHasReanchoredRows A strategy hwin basis
      initialCode value := by
  intro current hmember query hreachable
  exact profiledOpenFixedLeftValue_reanchor_of_provenance A strategy hwin basis
    initialCode value hprovenance current hmember query hreachable

/-- Candidate validity at the exact interface consumed by re-anchored
successor coverage.  Each selected active value may come from a different
construction; no common optional-dispatcher preimage is requested. -/
def ProfiledOpenFixedSidewiseReanchoredCandidateValid
    {OneClass : Type oc} {TwoClass : Type tc}
    (descriptor : ReanchoredDescriptor A initialCode)
    (family : SidewiseTaggedFamily OneClass TwoClass
      (ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I)
        initialCode))
    (bank : ProfiledOpenFixedSidewisePinnedBank A initialCode OneClass
      TwoClass) : Prop :=
  ProfiledOpenFixedSidewiseCandidateValid A initialCode descriptor family
      bank ∧
    (descriptor ∈ family.2.1 →
      ProfiledOpenFixedRightValueHasReanchoredRows A strategy hwin basis
        initialCode (bank.1 family.1.1)) ∧
    (descriptor ∈ family.2.2 →
      ProfiledOpenFixedLeftValueHasReanchoredRows A strategy hwin basis
        initialCode (bank.2 family.1.2))

/-- Compatibility with the earlier, stronger candidate predicate. -/
theorem profiledOpenFixedSidewiseReanchoredCandidateValid_of_provenance
    {OneClass : Type oc} {TwoClass : Type tc}
    (descriptor : ReanchoredDescriptor A initialCode)
    (family : SidewiseTaggedFamily OneClass TwoClass
      (ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I)
        initialCode))
    (bank : ProfiledOpenFixedSidewisePinnedBank A initialCode OneClass
      TwoClass)
    (hvalid : ProfiledOpenFixedSidewiseProvenanceCandidateValid A strategy hwin
      basis initialCode descriptor family bank) :
    ProfiledOpenFixedSidewiseReanchoredCandidateValid A strategy hwin basis
      initialCode descriptor family bank := by
  refine ⟨hvalid.1, ?_, ?_⟩
  · intro hactive
    exact profiledOpenFixedRightValue_hasReanchoredRows_of_provenance A strategy
      hwin basis initialCode _ (hvalid.2.1 hactive)
  · intro hactive
    exact profiledOpenFixedLeftValue_hasReanchoredRows_of_provenance A strategy
      hwin basis initialCode _ (hvalid.2.2 hactive)

/-! ## Reachable finite query alphabet -/

/-- Every controller coordinate in both symmetric query vectors is reached by
an actual blind-sender word.  This restricts only rational-tree controls; it
does not expose a side, class, graph, or leader flag. -/
def ProfiledOpenFixedSidewisePointedQueryReachable
    (query : ProfiledOpenFixedSidewisePointedQuery A initialCode) : Prop :=
  (∀ value : ProfiledOpenFixedRightPinnedValue A initialCode,
      ProfiledOpenFixedRightQueryReachable A initialCode value
        (query.1.2.1 value)) ∧
    (∀ value : ProfiledOpenFixedLeftPinnedValue A initialCode,
      ProfiledOpenFixedLeftQueryReachable A initialCode value
        (query.1.2.2 value))

/-- The honest finite query alphabet used by the re-anchored edge.  Although
reachability is stated with an existential word, this is a subtype of an
already finite raw alphabet, hence remains finite noncomputably. -/
noncomputable abbrev ProfiledOpenFixedSidewiseReachablePointedQuery :=
  { query : ProfiledOpenFixedSidewisePointedQuery A initialCode //
    ProfiledOpenFixedSidewisePointedQueryReachable A initialCode query }

set_option synthInstance.maxHeartbeats 3200000 in
noncomputable instance : Fintype
    (ProfiledOpenFixedSidewiseReachablePointedQuery A initialCode) :=
  Fintype.ofFinite _

/-- Canonical reachable right query: the rational controller and pinned union
monitor are both read at the empty word/node. -/
noncomputable def profiledOpenFixedRightInitialReachableQuery
    (value : ProfiledOpenFixedRightPinnedValue A initialCode) :
    ProfiledOpenFixedRightPinnedBlockQuery A initialCode value :=
  (value.2.2.1.toTransitionRationalTree.controlAt [],
    (ProfiledOpenHiddenDescriptorRightPinnedUnionMonitor A value.1
      value.2.1).initial)

/-- Left empty-word query. -/
noncomputable def profiledOpenFixedLeftInitialReachableQuery
    (value : ProfiledOpenFixedLeftPinnedValue A initialCode) :
    ProfiledOpenFixedLeftPinnedBlockQuery A initialCode value :=
  (value.2.2.1.toTransitionRationalTree.controlAt [],
    (ProfiledOpenHiddenDescriptorLeftPinnedUnionMonitor A value.1
      value.2.1).initial)

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenFixedRightInitialReachableQuery_reachable
    (value : ProfiledOpenFixedRightPinnedValue A initialCode) :
    ProfiledOpenFixedRightQueryReachable A initialCode value
      (profiledOpenFixedRightInitialReachableQuery A initialCode value) :=
  ⟨[], rfl⟩

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenFixedLeftInitialReachableQuery_reachable
    (value : ProfiledOpenFixedLeftPinnedValue A initialCode) :
    ProfiledOpenFixedLeftQueryReachable A initialCode value
      (profiledOpenFixedLeftInitialReachableQuery A initialCode value) :=
  ⟨[], rfl⟩

/-- A harmless finite direction tag.  Nonemptiness of the lineage index is
the only extra assumption: the tag uses the sink move on both shadows. -/
noncomputable def profiledOpenFixedSidewiseDefaultDirection
    [Inhabited I] : ProfiledOpenIndexedFiniteDirectionTag A (I := I) :=
  ⟨(.sink, .sink),
    { rightPivot := (default, .first)
      rightControl := PUnit.unit
      rightInput := (default, default)
      leftPivot := (default, .first)
      leftControl := PUnit.unit
      leftInput := (default, default) }⟩

/-- Canonical raw query whose every fixed-value coordinate is reached at the
empty sender word. -/
noncomputable def profiledOpenFixedSidewiseInitialReachableRawQuery
    [Inhabited I] : ProfiledOpenFixedSidewisePointedQuery A initialCode :=
  ((.right,
      (profiledOpenFixedRightInitialReachableQuery A initialCode,
        profiledOpenFixedLeftInitialReachableQuery A initialCode)),
    profiledOpenFixedSidewiseDefaultDirection A (I := I))

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenFixedSidewiseInitialReachableRawQuery_reachable
    [Inhabited I] :
    ProfiledOpenFixedSidewisePointedQueryReachable A initialCode
      (profiledOpenFixedSidewiseInitialReachableRawQuery A initialCode) := by
  constructor
  · intro value
    exact profiledOpenFixedRightInitialReachableQuery_reachable A initialCode
      value
  · intro value
    exact profiledOpenFixedLeftInitialReachableQuery_reachable A initialCode
      value

/-- The generic relational table's nonempty-query requirement is therefore
available under the honest minimal assumption that the lineage index is
nonempty. -/
noncomputable instance [Inhabited I] : Inhabited
    (ProfiledOpenFixedSidewiseReachablePointedQuery A initialCode) :=
  ⟨⟨profiledOpenFixedSidewiseInitialReachableRawQuery A initialCode,
    profiledOpenFixedSidewiseInitialReachableRawQuery_reachable A initialCode⟩⟩

/-! ## Re-anchored exact edge -/

/-- The proof-side step state is either reselected inside the active fixed
value's semantic fibre, or is the original semantic state when the selected
side is inactive.  The active disjunct retains the literal row-faithfulness
witness proved above. -/
def ProfiledOpenFixedSidewiseReanchoredStep
    {OneClass : Type oc} {TwoClass : Type tc}
    (sourceState : ProfiledOpenIndexedOptionalControlledSemanticState A
      strategy hwin basis initialCode)
    (sourceFamily : SidewiseTaggedFamily OneClass TwoClass
      (ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I)
        initialCode))
    (bank : ProfiledOpenFixedSidewisePinnedBank A initialCode OneClass
      TwoClass)
    (query : ProfiledOpenFixedSidewisePointedQuery A initialCode)
    (stepState : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode) : Prop :=
  match query.1.1 with
  | .right =>
      ((profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy
            hwin basis initialCode sourceState) ∈ sourceFamily.2.1 ∧
        ∃ witness : ProfiledOpenFixedRightReanchoredQuery A strategy hwin
            basis initialCode
            (profiledOpenIndexedOptionalControlledSemanticDescriptor A
              strategy hwin basis initialCode sourceState)
            (bank.1 sourceFamily.1.1)
            (query.1.2.1 (bank.1 sourceFamily.1.1)),
          witness.state = stepState) ∨
      ((profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy
            hwin basis initialCode sourceState) ∉ sourceFamily.2.1 ∧
        stepState = sourceState)
  | .left =>
      ((profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy
            hwin basis initialCode sourceState) ∈ sourceFamily.2.2 ∧
        ∃ witness : ProfiledOpenFixedLeftReanchoredQuery A strategy hwin
            basis initialCode
            (profiledOpenIndexedOptionalControlledSemanticDescriptor A
              strategy hwin basis initialCode sourceState)
            (bank.2 sourceFamily.1.2)
            (query.1.2.2 (bank.2 sourceFamily.1.2)),
          witness.state = stepState) ∨
      ((profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy
            hwin basis initialCode sourceState) ∉ sourceFamily.2.2 ∧
        stepState = sourceState)

/-- Exact relational edge after proof-side re-anchoring.  The original live
state supplies only the contextual source family and tags.  The semantic
child is taken from `stepState`, which has the same exact descriptor but may
be a different history inside the selected fixed value's fibre. -/
def ProfiledOpenFixedSidewiseReanchoredExactEdge
    {OneClass : Type oc} {TwoClass : Type tc}
    (TagInvariant :
      ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode →
        SidewiseTaggedFamily OneClass TwoClass
          (ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I)
            initialCode) → Prop)
    (targetTag :
      ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode →
        ProfiledOpenFixedSidewisePinnedBank A initialCode OneClass TwoClass →
        ProfiledOpenFixedSidewiseReachablePointedQuery A initialCode →
        ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I) initialCode →
        ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode →
        OneClass × TwoClass)
    (source : ReanchoredDescriptor A initialCode)
    (bank : ProfiledOpenFixedSidewisePinnedBank A initialCode OneClass
      TwoClass)
    (query : ProfiledOpenFixedSidewiseReachablePointedQuery A initialCode)
    (targetFamily : SidewiseTaggedFamily OneClass TwoClass
      (ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I)
        initialCode))
    (target : ReanchoredDescriptor A initialCode) : Prop :=
  ∃ sourceState sourceFamily stepState,
    profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis initialCode sourceState = source ∧
    profiledOpenOptionalControlledFamilyOf A strategy hwin basis initialCode
        sourceState = sourceFamily.2 ∧
    TagInvariant source sourceFamily ∧
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
    targetFamily.1 = targetTag source bank query targetFamily.2 target

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Candidate validity plus reachable query alignment chooses an exact
same-descriptor step state.  This is the point at which re-anchoring replaces
the earlier `SequentialAdjacency` premise. -/
theorem exists_profiledOpenFixedSidewiseReanchoredStep
    {OneClass : Type oc} {TwoClass : Type tc}
    (sourceState : ProfiledOpenIndexedOptionalControlledSemanticState A
      strategy hwin basis initialCode)
    (sourceFamily : SidewiseTaggedFamily OneClass TwoClass
      (ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I)
        initialCode))
    (bank : ProfiledOpenFixedSidewisePinnedBank A initialCode OneClass
      TwoClass)
    (query : ProfiledOpenFixedSidewiseReachablePointedQuery A initialCode)
    (hvalid : ProfiledOpenFixedSidewiseReanchoredCandidateValid A strategy
      hwin basis initialCode
      (profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis initialCode sourceState) sourceFamily bank) :
    ∃ stepState,
      ProfiledOpenFixedSidewiseReanchoredStep A strategy hwin basis initialCode
          sourceState sourceFamily bank query.1 stepState ∧
        profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy
          hwin basis initialCode stepState =
            profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy
              hwin basis initialCode sourceState := by
  rcases query with ⟨query, hreachable⟩
  cases hside : query.1.1 with
  | right =>
      by_cases hactive :
        profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy
            hwin basis initialCode sourceState ∈ sourceFamily.2.1
      · let value := bank.1 sourceFamily.1.1
        let selected := query.1.2.1 value
        have hmember :
            profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy
                hwin basis initialCode sourceState ∈ value.1.1 :=
          hvalid.1.1 hactive
        have hrows :
            ProfiledOpenFixedRightValueHasReanchoredRows A strategy hwin basis
              initialCode value :=
          hvalid.2.1 hactive
        have hquery : ProfiledOpenFixedRightQueryReachable A initialCode value
            selected :=
          hreachable.1 value
        rcases hrows
            (profiledOpenIndexedOptionalControlledSemanticDescriptor A
              strategy hwin basis initialCode sourceState)
            hmember selected hquery with ⟨witness⟩
        refine ⟨witness.state, ?_, witness.state_descriptor⟩
        simp only [ProfiledOpenFixedSidewiseReanchoredStep, hside]
        exact Or.inl ⟨hactive, witness, rfl⟩
      · refine ⟨sourceState, ?_, rfl⟩
        simp only [ProfiledOpenFixedSidewiseReanchoredStep, hside]
        exact Or.inr ⟨hactive, trivial⟩
  | left =>
      by_cases hactive :
        profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy
            hwin basis initialCode sourceState ∈ sourceFamily.2.2
      · let value := bank.2 sourceFamily.1.2
        let selected := query.1.2.2 value
        have hmember :
            profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy
                hwin basis initialCode sourceState ∈ value.1.2 :=
          hvalid.1.2 hactive
        have hrows :
            ProfiledOpenFixedLeftValueHasReanchoredRows A strategy hwin basis
              initialCode value :=
          hvalid.2.2 hactive
        have hquery : ProfiledOpenFixedLeftQueryReachable A initialCode value
            selected :=
          hreachable.2 value
        rcases hrows
            (profiledOpenIndexedOptionalControlledSemanticDescriptor A
              strategy hwin basis initialCode sourceState)
            hmember selected hquery with ⟨witness⟩
        refine ⟨witness.state, ?_, witness.state_descriptor⟩
        simp only [ProfiledOpenFixedSidewiseReanchoredStep, hside]
        exact Or.inl ⟨hactive, witness, rfl⟩
      · refine ⟨sourceState, ?_, rfl⟩
        simp only [ProfiledOpenFixedSidewiseReanchoredStep, hside]
        exact Or.inr ⟨hactive, trivial⟩

/-- Complete live successor coverage on the reachable finite query alphabet.
There is no `SequentialAdjacency` hypothesis: active rows are re-anchored from
the generalized per-member provenance carried by candidate validity, while
inactive rows keep the original semantic state. -/
theorem profiledOpenFixedSidewiseReanchored_liveSuccessorCoverage
    {OneClass : Type oc} {TwoClass : Type tc}
    (TagInvariant :
      ReanchoredDescriptor A initialCode →
        SidewiseTaggedFamily OneClass TwoClass
          (ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I)
            initialCode) → Prop)
    (targetTag :
      ReanchoredDescriptor A initialCode →
        ProfiledOpenFixedSidewisePinnedBank A initialCode OneClass TwoClass →
        ProfiledOpenFixedSidewiseReachablePointedQuery A initialCode →
        ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I) initialCode →
        ReanchoredDescriptor A initialCode → OneClass × TwoClass)
    (htag : ∀ source bank query family target,
      TagInvariant target
        ((targetTag source bank query family target), family)) :
    RelationalCandidateLiveSuccessorCoverage
      (ProfiledOpenFixedSidewiseSemanticLive A strategy hwin basis initialCode
        TagInvariant)
      (ProfiledOpenFixedSidewiseReanchoredCandidateValid A strategy hwin basis
        initialCode)
      (ProfiledOpenFixedSidewiseReanchoredExactEdge A strategy hwin basis
        initialCode TagInvariant targetTag)
      (ProfiledOpenFixedSidewiseControlStep A initialCode) := by
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
    · exact ⟨sourceState, source.1, stepState, hsource, hsourceFamily,
        hlive.2, hvalid, hstep, hstepSource, rfl, rfl, rfl⟩
    · change target.control =
        (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).step
          source.2.control target.code
      rw [← hstepSource]
      exact profiledOpenIndexedOptionalControlledSemanticNext_control A
        strategy hwin basis initialCode stepState query.1.2
  · constructor
    · exact ⟨child, rfl, rfl⟩
    · exact htag source.2 bank query family target

end

end DetParityAutomaton

end DistributedSynthesis
