/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenProvenanceFiniteDelayedActiveFork
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenReanchoredEvaluationOneRoundTrace
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenProvenanceDistinguishedSemanticEpochParity

/-!
# Installing the retained boundary root in a witnessed physical overlay

The delayed strict-close fork already identifies the exact classified child
root which survives root deduplication.  This file installs that root, rather
than an independently selected semantic pivot, in the first witnessed row of
the next physical epoch.

The installation is proof-side.  It does not expose the selected side,
lineage, root, or row to either process.  The semantic row law is obtained from
the complete per-member `HasReanchoredRows` interface; no equality between the
retained root and a within-block semantic pivot is asserted.
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
variable (codePolicy : ProfiledOpenIndexedProvenanceCodeRationalPolicy A
  strategy hwin basis initialCode)

variable {initialState : PairedProfiledTreeState A}
variable (fixedPolicy :
  (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)
variable (point : ProfiledOpenIndexedOptionalControlledSemanticState A
  strategy hwin basis initialCode)
variable (initialRoot : ProfiledFixedPolicyRoot A fixedPolicy)
variable (package : ProfiledOpenProvenancePolicyFixedTablePackage A strategy
  hwin basis initialCode codePolicy fixedPolicy point initialRoot)

private abbrev BoundaryState :=
  ProfiledOpenProvenancePolicyDistinguishedState A strategy hwin basis
    initialCode codePolicy fixedPolicy point initialRoot package

private abbrev BoundaryQuery :=
  ProfiledOpenWitnessedTableQuery.{i, u, v, x, y, s,
    max i u v x y s, max i u v x y s} A initialCode

/-! ## Active semantic slots are represented in the advertised family -/

section
omit [Inhabited I]

/-- An exact active right slot of a witnessed semantic representative places
its descriptor in the right half of that representative's public family. -/
theorem profiledOpenOptionalControlledDescriptor_mem_right_of_slot_eq_some
    (semantic : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode)
    (lineage : I) (root : ProfiledOpenRightRoot A)
    (hslot :
      (profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis initialCode semantic).code.rightSlots lineage =
          some (.right root)) :
    profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis initialCode semantic ∈
      (profiledOpenOptionalControlledFamilyOf A strategy hwin basis initialCode
        semantic).1 := by
  classical
  cases hright : semantic.1.state.right with
  | none =>
      simp only [profiledOpenIndexedOptionalControlledSemanticDescriptor_code]
        at hslot
      change
        (semantic.1.state.right.slots A strategy hwin basis) lineage =
          some (.right root) at hslot
      simp [hright, ProfiledOpenIndexedRightSemanticShadow.slots] at hslot
  | some rightLane =>
      cases hleft : semantic.1.state.left with
      | none =>
          rw [profiledOpenOptionalControlledFamilyOf_eq_rightOnly A strategy
            hwin basis initialCode semantic rightLane hright hleft]
          exact
            (profiledOpenRightOnlyDescriptor_mem_family A strategy hwin basis
              (profiledOpenOptionalFixedSemanticDescriptor A strategy hwin
                basis initialCode (fun _ ↦ semantic.2))
              (semantic.1.toRightOnly A strategy hwin basis rightLane hright
                hleft)).1
      | some leftLane =>
          rw [profiledOpenOptionalControlledFamilyOf_eq_both A strategy hwin
            basis initialCode semantic rightLane leftLane hright hleft]
          exact
            (profiledOpenSourceFibreCurrent_mem_both A strategy hwin basis
              (profiledOpenFixedPinnedSemanticDescriptor A strategy hwin basis
                initialCode (fun _ ↦ semantic.2))
              (semantic.1.toLiveFresh A strategy hwin basis rightLane leftLane
                hright hleft)).1

/-- Left mirror of the active-family membership bridge. -/
theorem profiledOpenOptionalControlledDescriptor_mem_left_of_slot_eq_some
    (semantic : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode)
    (lineage : I) (root : ProfiledOpenLeftRoot A)
    (hslot :
      (profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis initialCode semantic).code.leftSlots lineage =
          some (.left root)) :
    profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis initialCode semantic ∈
      (profiledOpenOptionalControlledFamilyOf A strategy hwin basis initialCode
        semantic).2 := by
  classical
  cases hleft : semantic.1.state.left with
  | none =>
      simp only [profiledOpenIndexedOptionalControlledSemanticDescriptor_code]
        at hslot
      change
        (semantic.1.state.left.slots A strategy hwin basis) lineage =
          some (.left root) at hslot
      simp [hleft, ProfiledOpenIndexedLeftSemanticShadow.slots] at hslot
  | some leftLane =>
      cases hright : semantic.1.state.right with
      | none =>
          rw [profiledOpenOptionalControlledFamilyOf_eq_leftOnly A strategy
            hwin basis initialCode semantic leftLane hright hleft]
          exact
            (profiledOpenLeftOnlyDescriptor_mem_family A strategy hwin basis
              (profiledOpenOptionalFixedSemanticDescriptor A strategy hwin
                basis initialCode (fun _ ↦ semantic.2))
              (semantic.1.toLeftOnly A strategy hwin basis leftLane hright
                hleft)).2
      | some rightLane =>
          rw [profiledOpenOptionalControlledFamilyOf_eq_both A strategy hwin
            basis initialCode semantic rightLane leftLane hright hleft]
          exact
            (profiledOpenSourceFibreCurrent_mem_both A strategy hwin basis
              (profiledOpenFixedPinnedSemanticDescriptor A strategy hwin basis
                initialCode (fun _ ↦ semantic.2))
              (semantic.1.toLiveFresh A strategy hwin basis rightLane leftLane
                hright hleft)).2

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Semantic right slots contain only right classified roots. -/
theorem exists_profiledOpenOptionalControlled_rightRoot_of_slot_eq_some
    (semantic : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode)
    (lineage : I) (anchor : ProfiledOpenClassifiedAnchor A)
    (hslot :
      (profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis initialCode semantic).code.rightSlots lineage = some anchor) :
    ∃ root : ProfiledOpenRightRoot A, anchor = .right root := by
  simp only [profiledOpenIndexedOptionalControlledSemanticDescriptor_code]
    at hslot
  change (semantic.1.state.right.slots A strategy hwin basis) lineage =
    some anchor at hslot
  cases hright : semantic.1.state.right with
  | none =>
      simp [hright, ProfiledOpenIndexedRightSemanticShadow.slots] at hslot
  | some lane =>
      cases hmember : lane.memberAt lineage with
      | none =>
          simp [hright, hmember,
            ProfiledOpenIndexedRightSemanticShadow.slots] at hslot
      | some member =>
          refine ⟨member.1, ?_⟩
          simpa [hright, hmember,
            ProfiledOpenIndexedRightSemanticShadow.slots] using hslot.symm

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Semantic left slots contain only left classified roots. -/
theorem exists_profiledOpenOptionalControlled_leftRoot_of_slot_eq_some
    (semantic : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode)
    (lineage : I) (anchor : ProfiledOpenClassifiedAnchor A)
    (hslot :
      (profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis initialCode semantic).code.leftSlots lineage = some anchor) :
    ∃ root : ProfiledOpenLeftRoot A, anchor = .left root := by
  simp only [profiledOpenIndexedOptionalControlledSemanticDescriptor_code]
    at hslot
  change (semantic.1.state.left.slots A strategy hwin basis) lineage =
    some anchor at hslot
  cases hleft : semantic.1.state.left with
  | none =>
      simp [hleft, ProfiledOpenIndexedLeftSemanticShadow.slots] at hslot
  | some lane =>
      cases hmember : lane.memberAt lineage with
      | none =>
          simp [hleft, hmember,
            ProfiledOpenIndexedLeftSemanticShadow.slots] at hslot
      | some member =>
          refine ⟨member.1, ?_⟩
          simpa [hleft, hmember,
            ProfiledOpenIndexedLeftSemanticShadow.slots] using hslot.symm

end

/-- A right slot of the current distinguished candidate has the expected
classified constructor. -/
theorem
    exists_profiledOpenProvenancePolicyDistinguished_rightRoot_of_slot_eq_some
    (current : BoundaryState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (lineage : I) (anchor : ProfiledOpenClassifiedAnchor A)
    (hslot :
      (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package
          current).code.rightSlots lineage = some anchor) :
    ∃ root : ProfiledOpenRightRoot A, anchor = .right root := by
  have hall :=
    profiledOpenProvenancePolicyDistinguished_mem_live_valid A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package current
  rcases hall.2.1.2.1.2 with
    ⟨semantic, hdescriptor, _hfamily, _htag⟩
  apply exists_profiledOpenOptionalControlled_rightRoot_of_slot_eq_some A
    strategy hwin basis initialCode semantic lineage anchor
  rw [hdescriptor]
  exact hslot

/-- Left constructor mirror. -/
theorem
    exists_profiledOpenProvenancePolicyDistinguished_leftRoot_of_slot_eq_some
    (current : BoundaryState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (lineage : I) (anchor : ProfiledOpenClassifiedAnchor A)
    (hslot :
      (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package
          current).code.leftSlots lineage = some anchor) :
    ∃ root : ProfiledOpenLeftRoot A, anchor = .left root := by
  have hall :=
    profiledOpenProvenancePolicyDistinguished_mem_live_valid A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package current
  rcases hall.2.1.2.1.2 with
    ⟨semantic, hdescriptor, _hfamily, _htag⟩
  apply exists_profiledOpenOptionalControlled_leftRoot_of_slot_eq_some A
    strategy hwin basis initialCode semantic lineage anchor
  rw [hdescriptor]
  exact hslot

/-! ## Exact retained-root overlay installation -/

/-- A right active slot of the finite distinguished candidate can be installed
as the literal member/root of a witnessed overlay.  The final existential is
the transport-free root equation used by physical epoch concatenation. -/
theorem exists_profiledOpenProvenancePolicyRightRoundOverlayOfExactSlot
    (current : BoundaryState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (query : BoundaryQuery A initialCode)
    (lineage : I) (root : ProfiledOpenRightRoot A)
    (row : PairedEntryRow)
    (hslot :
      (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package
          current).code.rightSlots lineage = some (.right root)) :
    ∃ overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode,
      overlay.member.1 =
          profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
            basis initialCode codePolicy fixedPolicy point initialRoot package
              current ∧
        overlay.entryRow = row ∧
        (∃ (source : ProfiledOpenRightViewClass A)
            (table : ProfiledOpenRightClassifiedTable A source)
            (hmove : overlay.member.1.moveIdentity.1 =
              ProfiledOpenClassifiedMove.right source table),
          (profiledOpenHiddenDescriptorRightRootToEq A overlay.member.1 source
            table hmove overlay.root).1 = root) ∧
        overlay.SemanticallyReanchored A strategy hwin basis initialCode ∧
        ProfiledOpenFixedRightValueHasReanchoredRows A strategy hwin basis
          initialCode overlay.value := by
  classical
  let actual :=
    profiledOpenProvenancePolicyDistinguishedActual A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current
  let descriptor :=
    profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current
  let bank :=
    profiledOpenProvenancePolicyDistinguishedBank A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current
  have hall :=
    profiledOpenProvenancePolicyDistinguished_mem_live_valid A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package current
  have hlive : ProfiledOpenProvenancePolicyEncodedLive A strategy hwin basis
      initialCode codePolicy actual.2 actual.1 := hall.2.1
  have hvalid : ProfiledOpenProvenancePolicyEncodedValid A strategy hwin basis
      initialCode actual.2 actual.1 bank := hall.2.2
  rcases hlive.2.1.2 with ⟨semantic, hdescriptor, hfamily, _htag⟩
  have hsemanticSlot :
      (profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis initialCode semantic).code.rightSlots lineage =
          some (.right root) := by
    rw [hdescriptor]
    exact hslot
  have hsemanticMember :=
    profiledOpenOptionalControlledDescriptor_mem_right_of_slot_eq_some A
      strategy hwin basis initialCode semantic lineage root hsemanticSlot
  have hactive : descriptor ∈ actual.1.2.1 := by
    change actual.2.2 ∈ actual.1.2.1
    rw [← hdescriptor, ← hfamily]
    exact hsemanticMember
  let value := bank.1 actual.1.1.1
  have hmember : descriptor ∈ value.1.1 := hvalid.2.1.1 hactive
  have hrows : ProfiledOpenFixedRightValueHasReanchoredRows A strategy hwin
      basis initialCode value := hvalid.2.2.1 hactive
  let selectedQuery := query.1.1.2.1 value
  have hreachable : ProfiledOpenFixedRightQueryReachable A initialCode value
      selectedQuery := query.2.1 value
  have hfinite : ProfiledOpenIndexedBiBeliefValid A descriptor.code
      descriptor.moveIdentity := hlive.2.2.2.1.1
  cases hmove : descriptor.moveIdentity.1 with
  | sink =>
      have hempty := hfinite.1
      rw [hmove] at hempty
      have hrootMem : ProfiledOpenClassifiedAnchor.right root ∈
          profiledOpenIndexedSlotRoots A descriptor.code.rightSlots := by
        simp only [profiledOpenIndexedSlotRoots, Finset.mem_biUnion,
          Finset.mem_univ, true_and]
        refine ⟨lineage, ?_⟩
        rw [hslot]
        exact Finset.mem_singleton_self _
      rw [hempty] at hrootMem
      simpa using hrootMem
  | left source table =>
      have hfalse := hfinite.1
      rw [hmove] at hfalse
      exact False.elim hfalse
  | right source table =>
      have hrightValid := hfinite.1
      rw [hmove] at hrightValid
      have hrootMem : root ∈ source.1 :=
        profiledOpenIndexedRightSlot_root_mem_source_of_laneValid A
          descriptor.code source table lineage root hrightValid hslot
      let member : ProfiledOpenHiddenDescriptorRightCarrier A value.1 :=
        ⟨descriptor, hmember⟩
      let retainedRoot : ProfiledOpenHiddenDescriptorRightRoot A member.1 :=
        profiledOpenHiddenDescriptorRightRootOfEq A descriptor source table
          hmove ⟨root, hrootMem⟩
      let overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode :=
        { value := value
          query := selectedQuery
          reachable := hreachable
          member := member
          root := retainedRoot
          entryRow := row }
      have hsemantic : overlay.SemanticallyReanchored A strategy hwin basis
          initialCode := by
        refine ⟨descriptor, ?_⟩
        exact
          profiledOpenFixedRightReanchoredRetainedRoot_of_hasReanchoredRows A
            strategy hwin basis initialCode value hrows member retainedRoot
              selectedQuery hreachable
      refine ⟨overlay, rfl, rfl, ?_, hsemantic, hrows⟩
      refine ⟨source, table, hmove, ?_⟩
      exact congrArg Subtype.val
        (profiledOpenHiddenDescriptorRightRootToEq_rootOfEq A descriptor source
          table hmove ⟨root, hrootMem⟩)

/-- Left exact retained-root installation. -/
theorem exists_profiledOpenProvenancePolicyLeftRoundOverlayOfExactSlot
    (current : BoundaryState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (query : BoundaryQuery A initialCode)
    (lineage : I) (root : ProfiledOpenLeftRoot A)
    (row : PairedEntryRow)
    (hslot :
      (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package
          current).code.leftSlots lineage = some (.left root)) :
    ∃ overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode,
      overlay.member.1 =
          profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
            basis initialCode codePolicy fixedPolicy point initialRoot package
              current ∧
        overlay.entryRow = row ∧
        (∃ (source : ProfiledOpenLeftViewClass A)
            (table : ProfiledOpenLeftClassifiedTable A source)
            (hmove : overlay.member.1.moveIdentity.2 =
              ProfiledOpenClassifiedMove.left source table),
          (profiledOpenHiddenDescriptorLeftRootToEq A overlay.member.1 source
            table hmove overlay.root).1 = root) ∧
        overlay.SemanticallyReanchored A strategy hwin basis initialCode ∧
        ProfiledOpenFixedLeftValueHasReanchoredRows A strategy hwin basis
          initialCode overlay.value := by
  classical
  let actual :=
    profiledOpenProvenancePolicyDistinguishedActual A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current
  let descriptor :=
    profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current
  let bank :=
    profiledOpenProvenancePolicyDistinguishedBank A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current
  have hall :=
    profiledOpenProvenancePolicyDistinguished_mem_live_valid A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package current
  have hlive : ProfiledOpenProvenancePolicyEncodedLive A strategy hwin basis
      initialCode codePolicy actual.2 actual.1 := hall.2.1
  have hvalid : ProfiledOpenProvenancePolicyEncodedValid A strategy hwin basis
      initialCode actual.2 actual.1 bank := hall.2.2
  rcases hlive.2.1.2 with ⟨semantic, hdescriptor, hfamily, _htag⟩
  have hsemanticSlot :
      (profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis initialCode semantic).code.leftSlots lineage =
          some (.left root) := by
    rw [hdescriptor]
    exact hslot
  have hsemanticMember :=
    profiledOpenOptionalControlledDescriptor_mem_left_of_slot_eq_some A
      strategy hwin basis initialCode semantic lineage root hsemanticSlot
  have hactive : descriptor ∈ actual.1.2.2 := by
    change actual.2.2 ∈ actual.1.2.2
    rw [← hdescriptor, ← hfamily]
    exact hsemanticMember
  let value := bank.2 actual.1.1.2
  have hmember : descriptor ∈ value.1.2 := hvalid.2.1.2 hactive
  have hrows : ProfiledOpenFixedLeftValueHasReanchoredRows A strategy hwin
      basis initialCode value := hvalid.2.2.2 hactive
  let selectedQuery := query.1.1.2.2 value
  have hreachable : ProfiledOpenFixedLeftQueryReachable A initialCode value
      selectedQuery := query.2.2 value
  have hfinite : ProfiledOpenIndexedBiBeliefValid A descriptor.code
      descriptor.moveIdentity := hlive.2.2.2.1.1
  cases hmove : descriptor.moveIdentity.2 with
  | sink =>
      have hempty := hfinite.2.1
      rw [hmove] at hempty
      have hrootMem : ProfiledOpenClassifiedAnchor.left root ∈
          profiledOpenIndexedSlotRoots A descriptor.code.leftSlots := by
        simp only [profiledOpenIndexedSlotRoots, Finset.mem_biUnion,
          Finset.mem_univ, true_and]
        refine ⟨lineage, ?_⟩
        rw [hslot]
        exact Finset.mem_singleton_self _
      rw [hempty] at hrootMem
      simpa using hrootMem
  | right source table =>
      have hfalse := hfinite.2.1
      rw [hmove] at hfalse
      exact False.elim hfalse
  | left source table =>
      have hleftValid := hfinite.2.1
      rw [hmove] at hleftValid
      have hrootMem : root ∈ source.1 :=
        profiledOpenIndexedLeftSlot_root_mem_source_of_laneValid A
          descriptor.code source table lineage root hleftValid hslot
      let member : ProfiledOpenHiddenDescriptorLeftCarrier A value.1 :=
        ⟨descriptor, hmember⟩
      let retainedRoot : ProfiledOpenHiddenDescriptorLeftRoot A member.1 :=
        profiledOpenHiddenDescriptorLeftRootOfEq A descriptor source table
          hmove ⟨root, hrootMem⟩
      let overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode :=
        { value := value
          query := selectedQuery
          reachable := hreachable
          member := member
          root := retainedRoot
          entryRow := row }
      have hsemantic : overlay.SemanticallyReanchored A strategy hwin basis
          initialCode := by
        refine ⟨descriptor, ?_⟩
        exact
          profiledOpenFixedLeftReanchoredRetainedRoot_of_hasReanchoredRows A
            strategy hwin basis initialCode value hrows member retainedRoot
              selectedQuery hreachable
      refine ⟨overlay, rfl, rfl, ?_, hsemantic, hrows⟩
      refine ⟨source, table, hmove, ?_⟩
      exact congrArg Subtype.val
        (profiledOpenHiddenDescriptorLeftRootToEq_rootOfEq A descriptor source
          table hmove ⟨root, hrootMem⟩)

/-! ## Side-generic boundary installation -/

/-- Exact public signature of a witnessed overlay installed at a classified
boundary anchor.  Besides the root and sticky-row equations, the proposition
stores precisely the two semantic facts needed to iterate the physical
overlay: a retained-root start witness and the complete per-member row law. -/
def ProfiledOpenProvenancePolicyBoundaryOverlayInstalledAt
    (current : BoundaryState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (side : IndexedLineageSide) (anchor : ProfiledOpenClassifiedAnchor A)
    (row : PairedEntryRow) : Prop :=
  match side with
  | .right =>
      ∃ (root : ProfiledOpenRightRoot A)
          (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode),
        anchor = .right root ∧
          overlay.member.1 =
            profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
              basis initialCode codePolicy fixedPolicy point initialRoot package
                current ∧
          overlay.entryRow = row ∧
          (∃ (source : ProfiledOpenRightViewClass A)
              (table : ProfiledOpenRightClassifiedTable A source)
              (hmove : overlay.member.1.moveIdentity.1 =
                ProfiledOpenClassifiedMove.right source table),
            (profiledOpenHiddenDescriptorRightRootToEq A overlay.member.1
              source table hmove overlay.root).1 = root) ∧
          overlay.SemanticallyReanchored A strategy hwin basis initialCode ∧
          ProfiledOpenFixedRightValueHasReanchoredRows A strategy hwin basis
            initialCode overlay.value
  | .left =>
      ∃ (root : ProfiledOpenLeftRoot A)
          (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode),
        anchor = .left root ∧
          overlay.member.1 =
            profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
              basis initialCode codePolicy fixedPolicy point initialRoot package
                current ∧
          overlay.entryRow = row ∧
          (∃ (source : ProfiledOpenLeftViewClass A)
              (table : ProfiledOpenLeftClassifiedTable A source)
              (hmove : overlay.member.1.moveIdentity.2 =
                ProfiledOpenClassifiedMove.left source table),
            (profiledOpenHiddenDescriptorLeftRootToEq A overlay.member.1
              source table hmove overlay.root).1 = root) ∧
          overlay.SemanticallyReanchored A strategy hwin basis initialCode ∧
          ProfiledOpenFixedLeftValueHasReanchoredRows A strategy hwin basis
            initialCode overlay.value

/-- Any exact active slot of a finite distinguished state can be installed
with an arbitrary requested sticky row.  No dynamically selected query pivot
or child-root equality is needed. -/
theorem
    profiledOpenProvenancePolicyBoundaryOverlayInstalledAt_of_slot_eq_some
    (current : BoundaryState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (query : BoundaryQuery A initialCode)
    (side : IndexedLineageSide) (lineage : I)
    (anchor : ProfiledOpenClassifiedAnchor A) (row : PairedEntryRow)
    (hslot : profiledOpenIndexedBiBeliefCurrentSlots A side
      (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package
          current).code lineage = some anchor) :
    ProfiledOpenProvenancePolicyBoundaryOverlayInstalledAt A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package current
        side anchor row := by
  cases side with
  | right =>
      have hrightSlot :
          (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
            basis initialCode codePolicy fixedPolicy point initialRoot package
              current).code.rightSlots lineage = some anchor := by
        exact hslot
      obtain ⟨root, hanchor⟩ :=
        exists_profiledOpenProvenancePolicyDistinguished_rightRoot_of_slot_eq_some
          A strategy hwin basis initialCode codePolicy fixedPolicy point
            initialRoot package current lineage anchor hrightSlot
      have hslotRoot :
          (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
            basis initialCode codePolicy fixedPolicy point initialRoot package
              current).code.rightSlots lineage = some (.right root) := by
        rw [← hanchor]
        exact hrightSlot
      obtain ⟨overlay, hmember, hrow, hroot, hsemantic, hrows⟩ :=
        exists_profiledOpenProvenancePolicyRightRoundOverlayOfExactSlot A
          strategy hwin basis initialCode codePolicy fixedPolicy point
            initialRoot package current query lineage root row hslotRoot
      exact ⟨root, overlay, hanchor, hmember, hrow, hroot, hsemantic, hrows⟩
  | left =>
      have hleftSlot :
          (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
            basis initialCode codePolicy fixedPolicy point initialRoot package
              current).code.leftSlots lineage = some anchor := by
        exact hslot
      obtain ⟨root, hanchor⟩ :=
        exists_profiledOpenProvenancePolicyDistinguished_leftRoot_of_slot_eq_some
          A strategy hwin basis initialCode codePolicy fixedPolicy point
            initialRoot package current lineage anchor hleftSlot
      have hslotRoot :
          (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
            basis initialCode codePolicy fixedPolicy point initialRoot package
              current).code.leftSlots lineage = some (.left root) := by
        rw [← hanchor]
        exact hleftSlot
      obtain ⟨overlay, hmember, hrow, hroot, hsemantic, hrows⟩ :=
        exists_profiledOpenProvenancePolicyLeftRoundOverlayOfExactSlot A
          strategy hwin basis initialCode codePolicy fixedPolicy point
            initialRoot package current query lineage root row hslotRoot
      exact ⟨root, overlay, hanchor, hmember, hrow, hroot, hsemantic, hrows⟩

/-- A root-aligned active pivot installs a witnessed overlay at exactly its
stored classified root and exactly its sticky row. -/
theorem
    profiledOpenProvenancePolicyBoundaryOverlayInstalledAt_of_rootAligned
    (current : BoundaryState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (query : BoundaryQuery A initialCode)
    (side : IndexedLineageSide) (anchor : ProfiledOpenClassifiedAnchor A)
    (aligned : ProfiledOpenProvenancePolicyRootAlignedActivePivotAt A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
        current side anchor) :
    ProfiledOpenProvenancePolicyBoundaryOverlayInstalledAt A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package current
        side anchor aligned.activePivot.pivot.2 := by
  cases side with
  | right =>
      have hslot :
          (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
            basis initialCode codePolicy fixedPolicy point initialRoot package
              current).code.rightSlots aligned.activePivot.pivot.1 =
            some anchor := by
        exact aligned.root_eq
      obtain ⟨root, hanchor⟩ :=
        exists_profiledOpenProvenancePolicyDistinguished_rightRoot_of_slot_eq_some
          A strategy hwin basis initialCode codePolicy fixedPolicy point
            initialRoot package current aligned.activePivot.pivot.1 anchor hslot
      have hslotRoot :
          (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
            basis initialCode codePolicy fixedPolicy point initialRoot package
              current).code.rightSlots aligned.activePivot.pivot.1 =
            some (.right root) := by
        rw [← hanchor]
        exact hslot
      obtain ⟨overlay, hmember, hrow, hroot, hsemantic, hrows⟩ :=
        exists_profiledOpenProvenancePolicyRightRoundOverlayOfExactSlot A
          strategy hwin basis initialCode codePolicy fixedPolicy point
            initialRoot package current query aligned.activePivot.pivot.1 root
              aligned.activePivot.pivot.2 hslotRoot
      exact ⟨root, overlay, hanchor, hmember, hrow, hroot, hsemantic, hrows⟩
  | left =>
      have hslot :
          (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
            basis initialCode codePolicy fixedPolicy point initialRoot package
              current).code.leftSlots aligned.activePivot.pivot.1 =
            some anchor := by
        exact aligned.root_eq
      obtain ⟨root, hanchor⟩ :=
        exists_profiledOpenProvenancePolicyDistinguished_leftRoot_of_slot_eq_some
          A strategy hwin basis initialCode codePolicy fixedPolicy point
            initialRoot package current aligned.activePivot.pivot.1 anchor hslot
      have hslotRoot :
          (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
            basis initialCode codePolicy fixedPolicy point initialRoot package
              current).code.leftSlots aligned.activePivot.pivot.1 =
            some (.left root) := by
        rw [← hanchor]
        exact hslot
      obtain ⟨overlay, hmember, hrow, hroot, hsemantic, hrows⟩ :=
        exists_profiledOpenProvenancePolicyLeftRoundOverlayOfExactSlot A
          strategy hwin basis initialCode codePolicy fixedPolicy point
            initialRoot package current query aligned.activePivot.pivot.1 root
              aligned.activePivot.pivot.2 hslotRoot
      exact ⟨root, overlay, hanchor, hmember, hrow, hroot, hsemantic, hrows⟩

/-! ## Fixed persistent-lineage installation -/

/-- The exact target root of the fixed persistent lineage is installable at
the positive-time distinguished state with the first sticky row.  This uses
the target slot itself and does not identify it with a separately selected
active-pivot child. -/
theorem
    profiledOpenProvenancePolicyDistinguishedTargetRootAt_overlayInstalledFirst
    (query : Nat → BoundaryQuery A initialCode)
    (halternates :
      ProfiledOpenProvenancePolicyDistinguishedQueryAlternates A initialCode
        query)
    (lineage : I)
    (hlineage : ∀ n,
      profiledOpenIndexedBiBeliefCurrentSlots A (query n).1.1.1
        (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
          (profiledOpenProvenancePolicyDistinguishedStateAt A strategy hwin
            basis initialCode codePolicy fixedPolicy point initialRoot package
              query n)).code lineage ≠ none)
    (n : Nat) :
    let current :=
      profiledOpenProvenancePolicyDistinguishedStateAt A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package query
          (n + 1)
    let root :=
      profiledOpenProvenancePolicyDistinguishedTargetRootAt A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package query
          lineage hlineage n
    ProfiledOpenProvenancePolicyBoundaryOverlayInstalledAt A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package current
        (query n).1.1.1.other root .first := by
  let current :=
    profiledOpenProvenancePolicyDistinguishedStateAt A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package query (n + 1)
  let root :=
    profiledOpenProvenancePolicyDistinguishedTargetRootAt A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package query lineage
        hlineage n
  apply
    profiledOpenProvenancePolicyBoundaryOverlayInstalledAt_of_slot_eq_some A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
        package current (query (n + 1)) (query n).1.1.1.other lineage root
          .first
  exact
    profiledOpenProvenancePolicyDistinguishedTargetRootAt_targetSlot A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
        query halternates lineage hlineage n

/-- The same installed anchor has exactly the block-minimum priority of the
semantic epoch selected for that fixed lineage. -/
theorem
    profiledOpenProvenancePolicyDistinguishedTargetRootAt_overlayPriority_eq_epoch
    (query : Nat → BoundaryQuery A initialCode)
    (halternates :
      ProfiledOpenProvenancePolicyDistinguishedQueryAlternates A initialCode
        query)
    (lineage : I)
    (hlineage : ∀ n,
      profiledOpenIndexedBiBeliefCurrentSlots A (query n).1.1.1
        (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
          (profiledOpenProvenancePolicyDistinguishedStateAt A strategy hwin
            basis initialCode codePolicy fixedPolicy point initialRoot package
              query n)).code lineage ≠ none)
    (n : Nat) :
    let current :=
      profiledOpenProvenancePolicyDistinguishedStateAt A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package query
          (n + 1)
    let root :=
      profiledOpenProvenancePolicyDistinguishedTargetRootAt A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package query
          lineage hlineage n
    let epoch :=
      profiledOpenProvenancePolicyDistinguishedSemanticEpochAt A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package query
          halternates lineage hlineage n
    ProfiledOpenProvenancePolicyBoundaryOverlayInstalledAt A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package
          current (query n).1.1.1.other root .first ∧
      profiledOpenIndexedRootPriority A root =
        A.priority
          (blockMinState A
            (entryState (A := A)
              (PairedStrategyMemory.selectedHistory epoch.sourceMemory
                epoch.direction))
            (PairedStrategyMemory.selectedBlockWord epoch.sourceMemory
              epoch.direction)) := by
  let current :=
    profiledOpenProvenancePolicyDistinguishedStateAt A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package query (n + 1)
  let root :=
    profiledOpenProvenancePolicyDistinguishedTargetRootAt A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package query lineage
        hlineage n
  let epoch :=
    profiledOpenProvenancePolicyDistinguishedSemanticEpochAt A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package query
        halternates lineage hlineage n
  refine ⟨?_, ?_⟩
  · exact
      profiledOpenProvenancePolicyDistinguishedTargetRootAt_overlayInstalledFirst
        A strategy hwin basis initialCode codePolicy fixedPolicy point
          initialRoot package query halternates lineage hlineage n
  · exact epoch.block_min_eq.symm

/-- Public chosen-lineage form: the anchor installed at positive time is the
same root whose priority is the packaged semantic epoch priority term. -/
theorem
    profiledOpenProvenancePolicyDistinguishedSemanticEpochPriority_overlayInstalledFirst
    (query : Nat → BoundaryQuery A initialCode)
    (halternates :
      ProfiledOpenProvenancePolicyDistinguishedQueryAlternates A initialCode
        query)
    (hsemantic :
      ProfiledOpenProvenancePolicyDistinguishedSemanticEpochBlockMinParity A
        strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
          package query halternates)
    (n : Nat) :
    let lineage := Classical.choose hsemantic
    let hlineage := Classical.choose (Classical.choose_spec hsemantic)
    let current :=
      profiledOpenProvenancePolicyDistinguishedStateAt A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package query
          (n + 1)
    let root :=
      profiledOpenProvenancePolicyDistinguishedTargetRootAt A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package query
          lineage hlineage n
    ProfiledOpenProvenancePolicyBoundaryOverlayInstalledAt A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package
          current (query n).1.1.1.other root .first ∧
      profiledOpenIndexedRootPriority A root =
        profiledOpenProvenancePolicyDistinguishedSemanticEpochPriority A
          strategy hwin basis initialCode codePolicy fixedPolicy point
            initialRoot package query halternates hsemantic n := by
  let lineage := Classical.choose hsemantic
  let hlineage := Classical.choose (Classical.choose_spec hsemantic)
  have hresult :=
    profiledOpenProvenancePolicyDistinguishedTargetRootAt_overlayPriority_eq_epoch
      A strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
        package query halternates lineage hlineage n
  refine ⟨hresult.1, ?_⟩
  simpa only [
    profiledOpenProvenancePolicyDistinguishedSemanticEpochPriority,
    lineage, hlineage] using hresult.2

/-! ## The delayed strict-close boundary -/

/-- The middle state of the safe delayed fork installs the exact strict-close
child anchor in the next witnessed overlay, with the sticky first row.  This
is the boundary equation needed for epoch concatenation; it deliberately says
nothing about equality with a within-block distinguished pivot. -/
theorem
    profiledOpenProvenancePolicyFiniteDelayedBoundary_middleOverlayInstalledFirst
    (source : BoundaryState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (prefixQuery fullQuery : BoundaryQuery A initialCode)
    (oldSide : IndexedLineageSide)
    (sourcePivot : ProfiledOpenProvenancePolicyActivePivotAt A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package source
        oldSide)
    (strictPrefix : List (ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂)))
    (lastStrict : ProfiledOpenPhysicalStrictLetter (I := I)
      (In₁ := In₁) (In₂ := In₂))
    (bothInputOne : In₁) (bothInputTwo : In₂) :
    let fork :=
      profiledOpenProvenancePolicyFiniteDelayedBoundaryForkOfActivePivot A
        strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
          package source prefixQuery fullQuery oldSide sourcePivot strictPrefix
            lastStrict bothInputOne bothInputTwo
    let anchor :=
      profiledOpenProvenancePolicyPhysicalSelectedChildAnchor A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package source
          oldSide sourcePivot strictPrefix lastStrict.inputOne
            lastStrict.inputTwo
    ProfiledOpenProvenancePolicyBoundaryOverlayInstalledAt A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package
        fork.middle oldSide.other anchor .first := by
  let fork :=
    profiledOpenProvenancePolicyFiniteDelayedBoundaryForkOfActivePivot A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
        package source prefixQuery fullQuery oldSide sourcePivot strictPrefix
          lastStrict bothInputOne bothInputTwo
  let anchor :=
    profiledOpenProvenancePolicyPhysicalSelectedChildAnchor A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package source
        oldSide sourcePivot strictPrefix lastStrict.inputOne lastStrict.inputTwo
  let aligned :=
    profiledOpenProvenancePolicyFiniteDelayedBoundaryMiddleRootPivot A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
        source prefixQuery oldSide sourcePivot strictPrefix lastStrict
  have hinstall :=
    profiledOpenProvenancePolicyBoundaryOverlayInstalledAt_of_rootAligned A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
        package fork.middle fork.zeroOpenQuery oldSide.other anchor aligned
  simpa only [aligned,
    profiledOpenProvenancePolicyPhysicalClosingQuery_nextRootPivot_row] using
      hinstall

end

end DetParityAutomaton

end DistributedSynthesis
