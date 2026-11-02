/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenProvenanceBoundaryOverlayInstall

/-!
# Controller data of an exact-slot boundary overlay

The basic exact-slot installer retains the descriptor, classified root, and
sticky row needed by the parity argument.  A finite receipt frontier also has
to know that the installed overlay uses the distinguished state's literal
bank component and the supplied streaming query's literal coordinate.

This file repeats the constructive installer with those two equations exposed.
They are unconditional consequences of the construction; no output-homogeneity
or query-alignment premise is added.
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

private abbrev ExactSlotState :=
  ProfiledOpenProvenancePolicyDistinguishedState A strategy hwin basis
    initialCode codePolicy fixedPolicy point initialRoot package

private abbrev ExactSlotQuery :=
  ProfiledOpenWitnessedTableQuery.{i, u, v, x, y, s,
    max i u v x y s, max i u v x y s} A initialCode

/-! ## Right exact-slot data -/

/-- The exact right-slot installer, exposing the two controller coordinates
that were definitionally chosen in its construction. -/
theorem
    exists_profiledOpenProvenancePolicyRightRoundOverlayOfExactSlot_withData
    (current : ExactSlotState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (query : ExactSlotQuery A initialCode)
    (lineage : I) (root : ProfiledOpenRightRoot A)
    (row : PairedEntryRow)
    (hslot :
      (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package
          current).code.rightSlots lineage = some (.right root)) :
    ∃ overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode,
      overlay.value =
          (profiledOpenProvenancePolicyDistinguishedBank A strategy hwin basis
            initialCode codePolicy fixedPolicy point initialRoot package
              current).1
            (profiledOpenProvenancePolicyDistinguishedActual A strategy hwin
              basis initialCode codePolicy fixedPolicy point initialRoot
                package current).1.1.1 ∧
        overlay.query = query.1.1.2.1 overlay.value ∧
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
      refine ⟨overlay, rfl, rfl, rfl, rfl, ?_, hsemantic, hrows⟩
      refine ⟨source, table, hmove, ?_⟩
      exact congrArg Subtype.val
        (profiledOpenHiddenDescriptorRightRootToEq_rootOfEq A descriptor source
          table hmove ⟨root, hrootMem⟩)

/-! ## Left exact-slot data -/

/-- Left mirror, with the selected left bank value and query coordinate
exposed definitionally. -/
theorem
    exists_profiledOpenProvenancePolicyLeftRoundOverlayOfExactSlot_withData
    (current : ExactSlotState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (query : ExactSlotQuery A initialCode)
    (lineage : I) (root : ProfiledOpenLeftRoot A)
    (row : PairedEntryRow)
    (hslot :
      (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package
          current).code.leftSlots lineage = some (.left root)) :
    ∃ overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode,
      overlay.value =
          (profiledOpenProvenancePolicyDistinguishedBank A strategy hwin basis
            initialCode codePolicy fixedPolicy point initialRoot package
              current).2
            (profiledOpenProvenancePolicyDistinguishedActual A strategy hwin
              basis initialCode codePolicy fixedPolicy point initialRoot
                package current).1.1.2 ∧
        overlay.query = query.1.1.2.2 overlay.value ∧
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
      refine ⟨overlay, rfl, rfl, rfl, rfl, ?_, hsemantic, hrows⟩
      refine ⟨source, table, hmove, ?_⟩
      exact congrArg Subtype.val
        (profiledOpenHiddenDescriptorLeftRootToEq_rootOfEq A descriptor source
          table hmove ⟨root, hrootMem⟩)

end

end DetParityAutomaton

end DistributedSynthesis
