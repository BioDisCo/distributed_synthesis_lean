/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenProvenanceBoundaryOverlayInstall

/-!
# Installing the source of the persistent lineage

The persistent-lineage monitor observes normalized child slots.  Before a
physical overlay can be compared with that monitor, one must recover the row
that produced the normalized target and install the *source* root with this
same row.  Root deduplication does not obstruct this step: a retained slot at
one lineage came from the raw child code at that very lineage.

This file proves exactly that unconditional part of the physical seam.  It
does not identify the certificate emitted by an independently re-anchored
fixed response table with the child of the finite direction tag.  That is a
separate cross-interface equality, not a consequence of root installation.
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

private abbrev SourceOverlayState :=
  ProfiledOpenProvenancePolicyDistinguishedState A strategy hwin basis
    initialCode codePolicy fixedPolicy point initialRoot package

private abbrev SourceOverlayQuery :=
  ProfiledOpenWitnessedTableQuery.{i, u, v, x, y, s,
    max i u v x y s, max i u v x y s} A initialCode

/-! ## Recovering the exact pre-dedup row -/

/-- The normalized target of the fixed persistent lineage was already
produced by the raw child code at the same lineage.  The existential row is
the row that must remain sticky in the source overlay. -/
theorem
    profiledOpenProvenancePolicyDistinguishedTargetRootAt_exists_rawSourceRow
    (query : Nat → SourceOverlayQuery A initialCode)
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
        initialCode codePolicy fixedPolicy point initialRoot package query n
    let descriptor :=
      profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package
          current
    let direction := profiledOpenIndexedRawDirectionOfFiniteTag A
      descriptor.code descriptor.moveIdentity (query n).1.2
    let targetRoot :=
      profiledOpenProvenancePolicyDistinguishedTargetRootAt A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package query
          lineage hlineage n
    ∃ row : PairedEntryRow,
      match (query n).1.1.1 with
      | .right =>
          profiledOpenIndexedRightRawChildCode A descriptor.code
            descriptor.moveIdentity direction lineage = some (row, targetRoot)
      | .left =>
          profiledOpenIndexedLeftRawChildCode A descriptor.code
            descriptor.moveIdentity direction lineage = some (row, targetRoot) := by
  let current :=
    profiledOpenProvenancePolicyDistinguishedStateAt A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package query n
  let descriptor :=
    profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current
  let direction := profiledOpenIndexedRawDirectionOfFiniteTag A
    descriptor.code descriptor.moveIdentity (query n).1.2
  let targetRoot :=
    profiledOpenProvenancePolicyDistinguishedTargetRootAt A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package query lineage
        hlineage n
  have htarget :=
    profiledOpenProvenancePolicyDistinguishedTargetRootAt_targetSlot A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
        query halternates lineage hlineage n
  have hnext :=
    profiledOpenProvenancePolicyDistinguishedDescriptorAt_code_succ A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
        query n
  have hslot :
      profiledOpenIndexedBiBeliefCurrentSlots A (query n).1.1.1.other
          (profiledOpenIndexedBiBeliefNext A descriptor.code
            descriptor.moveIdentity direction) lineage =
        some targetRoot := by
    rw [← profiledOpenIndexedBiBeliefNextFiniteTag]
    rw [← hnext]
    exact htarget
  cases hside : (query n).1.1.1 with
  | right =>
      let raw := profiledOpenIndexedRightRawChildCode A descriptor.code
        descriptor.moveIdentity direction
      have hroot : raw.deduplicateRoots.rootSlots lineage =
          some targetRoot := by
        simpa only [hside, IndexedLineageSide.other,
          profiledOpenIndexedBiBeliefCurrentSlots_left,
          profiledOpenIndexedBiBeliefNext_leftSlots,
          profiledOpenIndexedRightChildCode, raw] using hslot
      rw [IndexedLineageChildCode.rootSlots_eq_some_iff] at hroot
      obtain ⟨row, hrow⟩ := hroot
      refine ⟨row, ?_⟩
      simpa only [hside, raw] using
        (raw.eq_of_deduplicateRoots_eq_some lineage row targetRoot hrow)
  | left =>
      let raw := profiledOpenIndexedLeftRawChildCode A descriptor.code
        descriptor.moveIdentity direction
      have hroot : raw.deduplicateRoots.rootSlots lineage =
          some targetRoot := by
        simpa only [hside, IndexedLineageSide.other,
          profiledOpenIndexedBiBeliefCurrentSlots_right,
          profiledOpenIndexedBiBeliefNext_rightSlots,
          profiledOpenIndexedLeftChildCode, raw] using hslot
      rw [IndexedLineageChildCode.rootSlots_eq_some_iff] at hroot
      obtain ⟨row, hrow⟩ := hroot
      refine ⟨row, ?_⟩
      simpa only [hside, raw] using
        (raw.eq_of_deduplicateRoots_eq_some lineage row targetRoot hrow)

/-! ## Installing the persistent source with that row -/

/-- Maximal unconditional source-side seam.  At every epoch there is an
exact current root of the persistent lineage and an exact raw row producing
the chosen normalized target.  The current root is installable in a witnessed
overlay with precisely that row.

The theorem intentionally stops before equating the fixed overlay response's
certificate with `targetRoot`: the former is selected by the fixed query-bank
coordinate, while the latter is computed by the finite direction tag. -/
theorem
    exists_profiledOpenProvenancePolicyDistinguished_sourceOverlayForTarget
    (query : Nat → SourceOverlayQuery A initialCode)
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
        initialCode codePolicy fixedPolicy point initialRoot package query n
    let descriptor :=
      profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package
          current
    let side := (query n).1.1.1
    let direction := profiledOpenIndexedRawDirectionOfFiniteTag A
      descriptor.code descriptor.moveIdentity (query n).1.2
    let targetRoot :=
      profiledOpenProvenancePolicyDistinguishedTargetRootAt A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package query
          lineage hlineage n
    ∃ sourceRoot : ProfiledOpenClassifiedAnchor A,
      ∃ row : PairedEntryRow,
        profiledOpenIndexedBiBeliefCurrentSlots A side descriptor.code lineage =
            some sourceRoot ∧
          (match side with
          | .right =>
              profiledOpenIndexedRightRawChildCode A descriptor.code
                descriptor.moveIdentity direction lineage =
                  some (row, targetRoot)
          | .left =>
              profiledOpenIndexedLeftRawChildCode A descriptor.code
                descriptor.moveIdentity direction lineage =
                  some (row, targetRoot)) ∧
          ProfiledOpenProvenancePolicyBoundaryOverlayInstalledAt A strategy
            hwin basis initialCode codePolicy fixedPolicy point initialRoot
              package current side sourceRoot row := by
  let current :=
    profiledOpenProvenancePolicyDistinguishedStateAt A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package query n
  let descriptor :=
    profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current
  let side := (query n).1.1.1
  let direction := profiledOpenIndexedRawDirectionOfFiniteTag A
    descriptor.code descriptor.moveIdentity (query n).1.2
  let targetRoot :=
    profiledOpenProvenancePolicyDistinguishedTargetRootAt A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package query lineage
        hlineage n
  obtain ⟨sourceRoot, hsource⟩ :=
    Option.ne_none_iff_exists'.mp (hlineage n)
  obtain ⟨row, hraw⟩ :=
    profiledOpenProvenancePolicyDistinguishedTargetRootAt_exists_rawSourceRow A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
        package query halternates lineage hlineage n
  refine ⟨sourceRoot, row, hsource, hraw, ?_⟩
  exact
    profiledOpenProvenancePolicyBoundaryOverlayInstalledAt_of_slot_eq_some A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
        package current (query n) side lineage sourceRoot row hsource

end

end DetParityAutomaton

end DistributedSynthesis
