/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenWitnessedCodePolicyAlignment
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenWitnessedPhysicalRoundAdapter
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenPolicyAlignedEpochPriority

/-!
# Physical rows for the provenance-aligned code policy

The policy-retagged candidate table strengthens the old witnessed liveness
invariant with reachability and move realization for one rational code policy.
The physical row evaluator needs only the old witnessed component.  This file
records the forgetful map and uses it to connect a table built with the new
liveness and retagged edge to the existing right- and left-row evaluators.

Retagging happens only after the literal physical edge has been taken.  The
target representative may therefore have a different public family and move,
but it has exactly the physical child's `(code, control)`.  The final theorem
uses that equality to transport the already-proved target-slot block-minimum
law.  No runtime controller learns a side, strict leader, lineage, or hidden
bit; all selections in this file remain proof data.
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

private abbrev ProvenanceFamily :=
  ProfiledOpenWitnessedTableFamily A initialCode

private abbrev ProvenanceBaseDescriptor :=
  ProfiledOpenWitnessedTableBaseDescriptor A initialCode

private abbrev ProvenanceDescriptor :=
  ProfiledOpenWitnessedTableDescriptor A initialCode

private abbrev ProvenanceCandidate :=
  ProfiledOpenWitnessedEncodedCandidate A initialCode

private abbrev ProvenanceBank :=
  ProfiledOpenWitnessedTableBank A initialCode

private abbrev ProvenanceQuery :=
  ProfiledOpenWitnessedTableQuery A initialCode

private abbrev ProvenanceEncodedLive :=
  SourceAwareRelationalLive
    (ProfiledOpenProvenancePolicyBaseLive A strategy hwin basis initialCode
      codePolicy)

private abbrev ProvenanceEncodedValid :=
  SourceAwareRelationalCandidateValid
    (ProfiledOpenWitnessedTableBaseValid A strategy hwin basis initialCode)

private abbrev ProvenanceEncodedEdge :=
  sourceAwareRelationalExactEdge
    (ProfiledOpenProvenancePolicyRetaggedExactEdge A strategy hwin basis
      initialCode codePolicy)

private abbrev ProvenanceEncodedControlStep :=
  sourceAwareRelationalControlStep
    (Family := ProvenanceFamily A initialCode)
    (ProfiledOpenWitnessedTableControlStep A initialCode)

/-! ## The policy-aligned fixed table -/

variable {initialState : PairedProfiledTreeState A}
variable (tablePolicy :
  (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)

/-- The old finite rational table interface, instantiated with policy-live
candidates and policy-retagged exact edges.  The table policy and code policy
are intentionally distinct: the former extracts a finite common-bank table,
whereas the latter supplies the anti-mosaic parity path. -/
abbrev ProfiledOpenProvenancePolicyFixedTablePackage
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode)
    (initialRoot : ProfiledFixedPolicyRoot A tablePolicy) :=
  FixedPolicyRelationalCandidateTablePackage A tablePolicy
    (ProvenanceEncodedLive A strategy hwin basis initialCode codePolicy)
    (ProvenanceEncodedValid A strategy hwin basis initialCode)
    (ProvenanceEncodedEdge A strategy hwin basis initialCode codePolicy)
    (ProvenanceEncodedControlStep A initialCode)
    initialRoot
    (sourceAwareRelationalCandidatesEncode
      (profiledOpenActiveLaneWitnessedInitialCandidateSet A strategy hwin basis
        initialCode point))
    (sourceAwareRelationalCandidateEncode
      (profiledOpenActiveLaneWitnessedInitialCandidate A strategy hwin basis
        initialCode point))

/-- Once the installed initial point is reachable and realizes the code
policy's root move, the generic table extraction applies with the retagged
edge.  The decoded exact thread therefore uses the policy-aligned edge at
every completed direction. -/
theorem exists_profiledOpenProvenancePolicyFixedTable
    (policyState : ProfiledOpenIndexedProvenanceCodePolicyState A strategy
      hwin basis initialCode)
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode)
    (hdescriptor :
      profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis initialCode point = (policyState, move))
    (hreachable : SourceFreeBeliefCodeParityRationalPolicy.Reachable
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode)
      initialCode
      (ProfiledOpenIndexedProvenanceValid A strategy hwin basis)
      (profiledOpenIndexedBiBeliefNextFiniteTag A) codePolicy policyState)
    (hmove : ProfiledOpenIndexedProvenanceCodePolicyMoveRealizesAt A strategy
      hwin basis initialCode codePolicy policyState move)
    (initialRoot : ProfiledFixedPolicyRoot A tablePolicy)
    (hinitialRoot : initialRoot.state A tablePolicy = tablePolicy.run []) :
    ∃ package : ProfiledOpenProvenancePolicyFixedTablePackage A strategy
        hwin basis initialCode codePolicy tablePolicy point initialRoot,
      ∀ query : Nat → ProvenanceQuery A initialCode,
        Nonempty
          (SourceAwareRelationalFamilyExactThread
            (ProfiledOpenProvenancePolicyRetaggedExactEdge A strategy hwin
              basis initialCode codePolicy)
            (ProfiledOpenWitnessedTableControlStep A initialCode)
            (profiledOpenActiveLaneWitnessedInitialCandidateSet A strategy
              hwin basis initialCode point)
            (package.branch.moveAt query) query) := by
  let initial :=
    profiledOpenActiveLaneWitnessedInitialCandidateSet A strategy hwin basis
      initialCode point
  let actual :=
    profiledOpenActiveLaneWitnessedInitialCandidate A strategy hwin basis
      initialCode point
  have hmem : sourceAwareRelationalCandidateEncode actual ∈
      sourceAwareRelationalCandidatesEncode initial :=
    mem_sourceAwareRelationalCandidatesEncode initial actual
      (profiledOpenActiveLaneWitnessedInitialCandidate_mem A strategy hwin
        basis initialCode point)
  have hlive : ProvenanceEncodedLive A strategy hwin basis initialCode
      codePolicy (sourceAwareRelationalCandidateEncode actual).2
        (sourceAwareRelationalCandidateEncode actual).1 := by
    refine ⟨rfl, ?_⟩
    exact profiledOpenProvenancePolicy_initialCandidate_live A strategy hwin
      basis initialCode codePolicy policyState move point hdescriptor
      hreachable hmove
  obtain ⟨package, hthreads⟩ :=
    exists_fixedPolicyRelationalCandidateTable A tablePolicy
      (ProvenanceEncodedLive A strategy hwin basis initialCode codePolicy)
      (ProvenanceEncodedValid A strategy hwin basis initialCode)
      (ProvenanceEncodedEdge A strategy hwin basis initialCode codePolicy)
      (ProvenanceEncodedControlStep A initialCode)
      initialRoot hinitialRoot
      (sourceAwareRelationalCandidatesEncode initial)
      (sourceAwareRelationalCandidateEncode actual) hmem hlive
      (profiledOpenProvenancePolicyRetagged_encodedLiveSuccessorCoverage A
        strategy hwin basis initialCode codePolicy)
      (profiledOpenProvenancePolicy_encodedCommonMoveExists A strategy hwin
        basis initialCode codePolicy)
  refine ⟨package, ?_⟩
  intro query
  obtain ⟨thread⟩ := hthreads query
  exact ⟨sourceAwareRelationalFamilyExactThreadDecode
    (ProfiledOpenProvenancePolicyRetaggedExactEdge A strategy hwin basis
      initialCode codePolicy)
    (ProfiledOpenWitnessedTableControlStep A initialCode) initial
    (package.branch.moveAt query) query thread⟩

/-- Root-specialized one-arrow constructor.  The provenance rational policy
already supplies an installed semantic representative of its root, so no
additional semantic candidate is required from the caller. -/
theorem exists_profiledOpenProvenancePolicyFixedTable_of_root
    (initialRoot : ProfiledFixedPolicyRoot A tablePolicy)
    (hinitialRoot : initialRoot.state A tablePolicy = tablePolicy.run []) :
    ∃ point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
        hwin basis initialCode,
      ∃ package : ProfiledOpenProvenancePolicyFixedTablePackage A strategy
          hwin basis initialCode codePolicy tablePolicy point initialRoot,
        ∀ query : Nat → ProvenanceQuery A initialCode,
          Nonempty
            (SourceAwareRelationalFamilyExactThread
              (ProfiledOpenProvenancePolicyRetaggedExactEdge A strategy hwin
                basis initialCode codePolicy)
              (ProfiledOpenWitnessedTableControlStep A initialCode)
              (profiledOpenActiveLaneWitnessedInitialCandidateSet A strategy
                hwin basis initialCode point)
              (package.branch.moveAt query) query) := by
  obtain ⟨move, point, hmove, hdescriptor, _hcandidate, _hlive⟩ :=
    exists_profiledOpenIndexedProvenanceCodePolicyInitialCandidate A strategy
      hwin basis initialCode codePolicy
  have hrun := profiledOpenIndexedProvenanceCodePolicy_run_nil A strategy hwin
    basis initialCode codePolicy
  have hdescriptor' :
      profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
          basis initialCode point = (codePolicy.run [], move) := by
    simpa only [hrun] using hdescriptor
  obtain ⟨package, hthreads⟩ :=
    exists_profiledOpenProvenancePolicyFixedTable A strategy hwin basis
      initialCode codePolicy tablePolicy (codePolicy.run []) move point
      hdescriptor' ⟨[], rfl⟩ hmove initialRoot hinitialRoot
  exact ⟨point, package, hthreads⟩

/-! ## Forgetting only the proof-strengthening -/

omit [Inhabited I] in
/-- Policy liveness contains the old witnessed liveness needed by physical
row projection.  This is the only coercion required by the row evaluator. -/
theorem profiledOpenProvenancePolicy_encodedLive_to_witnessed
    {descriptor : ProvenanceDescriptor A initialCode}
    {family : ProvenanceFamily A initialCode}
    (hlive : ProvenanceEncodedLive A strategy hwin basis initialCode codePolicy
      descriptor family) :
    SourceAwareRelationalLive
      (ProfiledOpenWitnessedTableBaseLive A strategy hwin basis initialCode)
      descriptor family := by
  exact ⟨hlive.1, hlive.2.1⟩

/-- Right physical-row projection from a policy-live source. -/
noncomputable def profiledOpenProvenancePolicyRightRowEvaluation
    (source : ProvenanceCandidate A initialCode)
    (bank : ProvenanceBank A initialCode)
    (query : ProvenanceQuery A initialCode)
    (hlive : ProvenanceEncodedLive A strategy hwin basis initialCode codePolicy
      source.2 source.1)
    (hvalid : ProvenanceEncodedValid A strategy hwin basis initialCode
      source.2 source.1 bank)
    (hactive : source.2.2 ∈ source.1.2.1) :
    ProfiledOpenFixedRightReanchoredRowEvaluation A strategy hwin basis
      initialCode source.2.2 (bank.1 source.1.1.1)
        (query.1.1.2.1 (bank.1 source.1.1.1)) :=
  profiledOpenWitnessedRightReanchoredRowEvaluation A strategy hwin basis
    initialCode source bank query
      (profiledOpenProvenancePolicy_encodedLive_to_witnessed A strategy hwin
        basis initialCode codePolicy hlive)
      hvalid hactive

/-- Left physical-row projection from a policy-live source. -/
noncomputable def profiledOpenProvenancePolicyLeftRowEvaluation
    (source : ProvenanceCandidate A initialCode)
    (bank : ProvenanceBank A initialCode)
    (query : ProvenanceQuery A initialCode)
    (hlive : ProvenanceEncodedLive A strategy hwin basis initialCode codePolicy
      source.2 source.1)
    (hvalid : ProvenanceEncodedValid A strategy hwin basis initialCode
      source.2 source.1 bank)
    (hactive : source.2.2 ∈ source.1.2.2) :
    ProfiledOpenFixedLeftReanchoredRowEvaluation A strategy hwin basis
      initialCode source.2.2 (bank.2 source.1.1.2)
        (query.1.1.2.2 (bank.2 source.1.1.2)) :=
  profiledOpenWitnessedLeftReanchoredRowEvaluation A strategy hwin basis
    initialCode source bank query
      (profiledOpenProvenancePolicy_encodedLive_to_witnessed A strategy hwin
        basis initialCode codePolicy hlive)
      hvalid hactive

/-- The right overlay constructor can be used unchanged on a policy-live
candidate. -/
noncomputable def profiledOpenProvenancePolicyRightRoundOverlayOfSource
    (source : ProvenanceCandidate A initialCode)
    (bank : ProvenanceBank A initialCode)
    (query : ProvenanceQuery A initialCode)
    (hlive : ProvenanceEncodedLive A strategy hwin basis initialCode codePolicy
      source.2 source.1)
    (hvalid : ProvenanceEncodedValid A strategy hwin basis initialCode
      source.2 source.1 bank)
    (hactive : source.2.2 ∈ source.1.2.1)
    (entryRow : PairedEntryRow) :
    ProfiledOpenWitnessedRightRoundOverlay A initialCode :=
  profiledOpenWitnessedRightRoundOverlayOfSource A strategy hwin basis
    initialCode source bank query
      (profiledOpenProvenancePolicy_encodedLive_to_witnessed A strategy hwin
        basis initialCode codePolicy hlive)
      hvalid hactive entryRow

/-- Left overlay mirror. -/
noncomputable def profiledOpenProvenancePolicyLeftRoundOverlayOfSource
    (source : ProvenanceCandidate A initialCode)
    (bank : ProvenanceBank A initialCode)
    (query : ProvenanceQuery A initialCode)
    (hlive : ProvenanceEncodedLive A strategy hwin basis initialCode codePolicy
      source.2 source.1)
    (hvalid : ProvenanceEncodedValid A strategy hwin basis initialCode
      source.2 source.1 bank)
    (hactive : source.2.2 ∈ source.1.2.2)
    (entryRow : PairedEntryRow) :
    ProfiledOpenWitnessedLeftRoundOverlay A initialCode :=
  profiledOpenWitnessedLeftRoundOverlayOfSource A strategy hwin basis
    initialCode source bank query
      (profiledOpenProvenancePolicy_encodedLive_to_witnessed A strategy hwin
        basis initialCode codePolicy hlive)
      hvalid hactive entryRow

/-- Direct right-row adapter for the distinguished cursor of a table built
with the new liveness and retagged edge. -/
noncomputable def profiledOpenProvenancePolicyRightRoundOverlayOfCursor
    {point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode}
    {initialRoot : ProfiledFixedPolicyRoot A tablePolicy}
    (package : ProfiledOpenProvenancePolicyFixedTablePackage A strategy hwin
      basis initialCode codePolicy tablePolicy point initialRoot)
    (cursor : package.branch.Cursor)
    (query : ProvenanceQuery A initialCode)
    (hactive : cursor.actual.2.2 ∈ cursor.actual.1.2.1)
    (entryRow : PairedEntryRow) :
    ProfiledOpenWitnessedRightRoundOverlay A initialCode :=
  profiledOpenProvenancePolicyRightRoundOverlayOfSource A strategy hwin basis
    initialCode codePolicy cursor.actual (cursor.move package.branch) query
      cursor.actual_live (cursor.move_valid_actual package.branch) hactive
      entryRow

/-- Direct left-row adapter for the distinguished cursor. -/
noncomputable def profiledOpenProvenancePolicyLeftRoundOverlayOfCursor
    {point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode}
    {initialRoot : ProfiledFixedPolicyRoot A tablePolicy}
    (package : ProfiledOpenProvenancePolicyFixedTablePackage A strategy hwin
      basis initialCode codePolicy tablePolicy point initialRoot)
    (cursor : package.branch.Cursor)
    (query : ProvenanceQuery A initialCode)
    (hactive : cursor.actual.2.2 ∈ cursor.actual.1.2.2)
    (entryRow : PairedEntryRow) :
    ProfiledOpenWitnessedLeftRoundOverlay A initialCode :=
  profiledOpenProvenancePolicyLeftRoundOverlayOfSource A strategy hwin basis
    initialCode codePolicy cursor.actual (cursor.move package.branch) query
      cursor.actual_live (cursor.move_valid_actual package.branch) hactive
      entryRow

/-! ## Retagged targets preserve the physical priority calculation -/

omit [Inhabited I] in
/-- The target-slot block-minimum theorem survives policy retagging.  The
literal physical child supplies the strategy block; equality of target
`(code, control)` transports the requested slot to that child. -/
theorem exists_profiledOpenProvenancePolicyEpochMemoryStep_of_targetSlot
    {sourceFamily : ProvenanceFamily A initialCode}
    {source : ProvenanceBaseDescriptor A initialCode}
    {bank : ProvenanceBank A initialCode}
    {query : ProvenanceQuery A initialCode}
    {targetFamily : ProvenanceFamily A initialCode}
    {target : ProvenanceBaseDescriptor A initialCode}
    (hedge : ProfiledOpenProvenancePolicyRetaggedExactEdge A strategy hwin
      basis initialCode codePolicy sourceFamily source bank query targetFamily
        target)
    (side : IndexedLineageSide) (lineage : I)
    (root : ProfiledOpenClassifiedAnchor A)
    (hside : side = query.1.1.1.other)
    (hslot : profiledOpenIndexedBiBeliefCurrentSlots A side target.code
      lineage = some root) :
    ∃ sourceMemory targetMemory : PairedStrategyMemory A strategy,
      ∃ direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂),
        PairedStrategyMemory.DirectionCompatible (A := A) sourceMemory
            direction ∧
          targetMemory = sourceMemory.step (A := A) direction ∧
          pairedEntryPriority A targetMemory.toTreeState =
              profiledOpenIndexedRootPriority A root ∧
          A.priority
              (blockMinState A
                (entryState (A := A)
                  (PairedStrategyMemory.selectedHistory sourceMemory
                    direction))
                (PairedStrategyMemory.selectedBlockWord sourceMemory
                  direction)) =
            profiledOpenIndexedRootPriority A root := by
  obtain ⟨physicalTarget, hphysical, hstate⟩ :=
    profiledOpenProvenancePolicyRetaggedExactEdge_state_eq_physical A strategy
      hwin basis initialCode codePolicy hedge
  have hcode : target.code = physicalTarget.2.code :=
    congrArg Prod.fst hstate
  have hphysicalSlot :
      profiledOpenIndexedBiBeliefCurrentSlots A side physicalTarget.2.code
        lineage = some root := by
    rw [← hcode]
    exact hslot
  exact exists_profiledOpenWitnessedEpochMemoryStep_of_targetSlot A strategy
    hwin basis initialCode hphysical side lineage root hside hphysicalSlot

end

end DetParityAutomaton

end DistributedSynthesis
