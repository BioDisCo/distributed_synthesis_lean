/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenProvenanceCodePolicyInstall
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenWitnessedSemanticControlBridge
import DistributedSynthesis.Formalizations.Lemma.LemSourceFreeBeliefCodePolicyPathAcceptance

/-!
# Installing one coherent code policy in the witnessed candidate thread

The literal semantic child of a witnessed re-anchored edge has the right
successor belief code and DPA control, but its newly computed move and public
family need not be those selected by one accepting rational code policy.
Requiring the two semantic points to have the same family would be the false
fibre-functionality shortcut.

This file implements the safe boundary retagging instead.  The current
installed semantic point supplies the physical row and its literal child
supplies the next `(code, control)`.  At the completed finite direction, the
provenance-strengthened rational policy installs an independently witnessed
semantic representative with exactly that `(code, control)` and the policy's
next move.  The representative carries its own literal finite family and tag.

Thus every exact candidate thread projects to one literal path of the same
rational policy.  Its positive-time code word is accepted.  No process is
told the active side, strict leader, lineage, or which semantic witness was
used; all representatives below occur only under `Prop`.
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

private abbrev PolicyDescriptor :=
  ProfiledOpenWitnessedTableBaseDescriptor A initialCode

private abbrev PolicyFamily :=
  ProfiledOpenWitnessedTableFamily A initialCode

private abbrev PolicyCandidate :=
  ProfiledOpenWitnessedTableCandidate A initialCode

private abbrev PolicyBank :=
  ProfiledOpenWitnessedTableBank A initialCode

private abbrev PolicyQuery :=
  ProfiledOpenWitnessedTableQuery A initialCode

private abbrev PolicyState :=
  ProfiledOpenIndexedProvenanceCodePolicyState A strategy hwin basis
    initialCode

private abbrev PolicyPoint :=
  ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin basis
    initialCode

/-! ## The policy-indexed candidate invariant -/

/-- A witnessed candidate is policy-live when its `(code, control)` is one
reachable state of the selected code policy and its installed move realizes
that policy state.  The ordinary witnessed liveness component retains the
literal semantic family/tag provenance used for physical row evaluation. -/
def ProfiledOpenProvenancePolicyBaseLive
    (descriptor : PolicyDescriptor A initialCode)
    (family : PolicyFamily A initialCode) : Prop :=
  ProfiledOpenWitnessedTableBaseLive A strategy hwin basis initialCode
      descriptor family ∧
    SourceFreeBeliefCodeParityRationalPolicy.Reachable
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode)
      initialCode
      (ProfiledOpenIndexedProvenanceValid A strategy hwin basis)
      (profiledOpenIndexedBiBeliefNextFiniteTag A) codePolicy descriptor.1 ∧
    ProfiledOpenIndexedProvenanceCodePolicyMoveRealizesAt A strategy hwin
      basis initialCode codePolicy descriptor.1 descriptor.2

omit [Inhabited I] in
/-- The initial candidate of an installed policy representative is
policy-live whenever its policy state is reachable and its move realizes that
state. -/
theorem profiledOpenProvenancePolicy_initialCandidate_live
    (state : PolicyState A strategy hwin basis initialCode)
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (point : PolicyPoint A strategy hwin basis initialCode)
    (hdescriptor :
      profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis initialCode point = (state, move))
    (hreachable : SourceFreeBeliefCodeParityRationalPolicy.Reachable
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode)
      initialCode
      (ProfiledOpenIndexedProvenanceValid A strategy hwin basis)
      (profiledOpenIndexedBiBeliefNextFiniteTag A) codePolicy state)
    (hmove : ProfiledOpenIndexedProvenanceCodePolicyMoveRealizesAt A strategy
      hwin basis initialCode codePolicy state move) :
    ProfiledOpenProvenancePolicyBaseLive A strategy hwin basis initialCode
      codePolicy
      (profiledOpenActiveLaneWitnessedInitialCandidate A strategy hwin basis
        initialCode point).2
      (profiledOpenActiveLaneWitnessedInitialCandidate A strategy hwin basis
        initialCode point).1 := by
  refine ⟨profiledOpenActiveLaneWitnessedInitialCandidate_live A strategy
      hwin basis initialCode point, ?_, ?_⟩
  · simpa only [profiledOpenActiveLaneWitnessedInitialCandidate,
      hdescriptor] using hreachable
  · simpa only [profiledOpenActiveLaneWitnessedInitialCandidate,
      hdescriptor] using hmove

/-! ## The retagged completed-direction edge -/

/-- A completed-direction edge first takes one ordinary witnessed physical
edge to a literal semantic child.  It then installs the policy-selected
successor representative.  Only `(code, control)` is identified across this
retagging; the target keeps its own honest family and class-pair tag.

The source and target realization fields make policy coherence intrinsic to
an exact thread, rather than an external property which could be lost by
candidate selection. -/
def ProfiledOpenProvenancePolicyRetaggedExactEdge
    (sourceFamily : PolicyFamily A initialCode)
    (source : PolicyDescriptor A initialCode)
    (bank : PolicyBank A initialCode)
    (query : PolicyQuery A initialCode)
    (targetFamily : PolicyFamily A initialCode)
    (target : PolicyDescriptor A initialCode) : Prop :=
  ∃ physicalTarget : PolicyCandidate A initialCode,
    ProfiledOpenFixedSidewiseWitnessedReanchoredExactEdge A strategy hwin
        basis initialCode sourceFamily source bank query physicalTarget.1
          physicalTarget.2 ∧
      target.1 = physicalTarget.2.1 ∧
      target.1 = codePolicy.successor source.1 query.1.2 ∧
      ProfiledOpenIndexedProvenanceCodePolicyMoveRealizesAt A strategy hwin
        basis initialCode codePolicy source.1 source.2 ∧
      ProfiledOpenIndexedProvenanceCodePolicyMoveRealizesAt A strategy hwin
        basis initialCode codePolicy target.1 target.2 ∧
      ∃ targetPoint : PolicyPoint A strategy hwin basis initialCode,
        profiledOpenActiveLaneWitnessedInitialCandidate A strategy hwin basis
          initialCode targetPoint = (targetFamily, target)

section
omit [Inhabited I]

/-- The retagged edge retains the objective-relevant result of the literal
physical edge. -/
theorem profiledOpenProvenancePolicyRetaggedExactEdge_state_eq_physical
    {sourceFamily : PolicyFamily A initialCode}
    {source : PolicyDescriptor A initialCode}
    {bank : PolicyBank A initialCode}
    {query : PolicyQuery A initialCode}
    {targetFamily : PolicyFamily A initialCode}
    {target : PolicyDescriptor A initialCode}
    (hedge : ProfiledOpenProvenancePolicyRetaggedExactEdge A strategy hwin
      basis initialCode codePolicy sourceFamily source bank query targetFamily
        target) :
    ∃ physicalTarget : PolicyCandidate A initialCode,
      ProfiledOpenFixedSidewiseWitnessedReanchoredExactEdge A strategy hwin
          basis initialCode sourceFamily source bank query physicalTarget.1
            physicalTarget.2 ∧
        target.1 = physicalTarget.2.1 := by
  rcases hedge with ⟨physicalTarget, hphysical, hstate, _⟩
  exact ⟨physicalTarget, hphysical, hstate⟩

/-- Every retagged edge follows the same rational code-policy successor. -/
theorem profiledOpenProvenancePolicyRetaggedExactEdge_policySuccessor
    {sourceFamily : PolicyFamily A initialCode}
    {source : PolicyDescriptor A initialCode}
    {bank : PolicyBank A initialCode}
    {query : PolicyQuery A initialCode}
    {targetFamily : PolicyFamily A initialCode}
    {target : PolicyDescriptor A initialCode}
    (hedge : ProfiledOpenProvenancePolicyRetaggedExactEdge A strategy hwin
      basis initialCode codePolicy sourceFamily source bank query targetFamily
        target) :
    target.1 = codePolicy.successor source.1 query.1.2 := by
  rcases hedge with
    ⟨_physicalTarget, _hphysical, _hphysicalState, hsuccessor, _⟩
  exact hsuccessor

/-- Both ends of a retagged edge carry the move selected by the same code
policy at their respective finite states. -/
theorem profiledOpenProvenancePolicyRetaggedExactEdge_realizes
    {sourceFamily : PolicyFamily A initialCode}
    {source : PolicyDescriptor A initialCode}
    {bank : PolicyBank A initialCode}
    {query : PolicyQuery A initialCode}
    {targetFamily : PolicyFamily A initialCode}
    {target : PolicyDescriptor A initialCode}
    (hedge : ProfiledOpenProvenancePolicyRetaggedExactEdge A strategy hwin
      basis initialCode codePolicy sourceFamily source bank query targetFamily
        target) :
    ProfiledOpenIndexedProvenanceCodePolicyMoveRealizesAt A strategy hwin
        basis initialCode codePolicy source.1 source.2 ∧
      ProfiledOpenIndexedProvenanceCodePolicyMoveRealizesAt A strategy hwin
        basis initialCode codePolicy target.1 target.2 := by
  rcases hedge with
    ⟨_physicalTarget, _hphysical, _hphysicalState, _hsuccessor,
      hsource, htarget, _⟩
  exact ⟨hsource, htarget⟩

end

/-! ## Pointwise coverage -/

omit [Inhabited I] in
/-- The policy-indexed live invariant has complete successor coverage.  This
is the central installation theorem: the old edge supplies the physical
child, while provenance rationalization supplies the independently retagged
policy successor. -/
theorem profiledOpenProvenancePolicyRetagged_liveSuccessorCoverage :
    EncodedSourceAwareRelationalCandidateLiveSuccessorCoverage
      (ProfiledOpenProvenancePolicyBaseLive A strategy hwin basis initialCode
        codePolicy)
      (ProfiledOpenWitnessedTableBaseValid A strategy hwin basis initialCode)
      (ProfiledOpenProvenancePolicyRetaggedExactEdge A strategy hwin basis
        initialCode codePolicy)
      (ProfiledOpenWitnessedTableControlStep A initialCode) := by
  intro source bank query hlive hvalid
  obtain ⟨physicalTarget, hphysicalEdge, hphysicalControl,
      _hphysicalLive⟩ :=
    profiledOpenFixedSidewiseWitnessedReanchored_liveSuccessorCoverage A
      strategy hwin basis initialCode source bank query hlive.1 hvalid
  obtain ⟨targetMove, targetPoint, htargetRealizes,
      htargetDescriptor, hpolicySuccessor⟩ :=
    exists_profiledOpenIndexedProvenanceCodePolicySuccessorInstalledCandidate
      A strategy hwin basis initialCode codePolicy source.2.1 hlive.2.1
        source.2.2 hlive.2.2 query.1.2
  let targetCandidate : PolicyCandidate A initialCode :=
    profiledOpenActiveLaneWitnessedInitialCandidate A strategy hwin basis
      initialCode targetPoint
  have htargetState : targetCandidate.2.1 =
      codePolicy.successor source.2.1 query.1.2 := by
    exact congrArg Prod.fst htargetDescriptor
  have htargetMove : targetCandidate.2.2 = targetMove := by
    exact congrArg Prod.snd htargetDescriptor
  obtain ⟨physicalSource, hphysicalSourceDescriptor, hphysicalCode,
      hphysicalControlEq⟩ :=
    profiledOpenFixedSidewiseWitnessedReanchoredExactEdge_code_control A
      strategy hwin basis initialCode hphysicalEdge
  have hsourceCode : physicalSource.1.state.code A strategy hwin basis =
      source.2.code := by
    exact congrArg
      (fun descriptor : PolicyDescriptor A initialCode ↦ descriptor.code)
      hphysicalSourceDescriptor
  have hsourceMove : physicalSource.1.state.move A strategy hwin basis =
      source.2.moveIdentity := by
    exact congrArg
      (fun descriptor : PolicyDescriptor A initialCode ↦
        descriptor.moveIdentity) hphysicalSourceDescriptor
  have hphysicalCodeFormula : physicalTarget.2.code =
      profiledOpenIndexedBiBeliefNextFiniteTag A source.2.code
        source.2.moveIdentity query.1.2 := by
    rw [← hphysicalCode]
    change
      (profiledOpenIndexedCorrelatedFiniteTagNext A strategy hwin basis
          physicalSource.1.state query.1.2).code A strategy hwin basis = _
    rw [profiledOpenIndexedCorrelatedFiniteTagNext_code A strategy hwin basis,
      hsourceCode, hsourceMove]
  have htargetStatePhysical : targetCandidate.2.1 = physicalTarget.2.1 := by
    rw [htargetState, hpolicySuccessor]
    apply Prod.ext
    · exact hphysicalCodeFormula.symm
    · change
        (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).step
            source.2.control
            (profiledOpenIndexedBiBeliefNextFiniteTag A source.2.code
              source.2.moveIdentity query.1.2) =
          physicalTarget.2.control
      change physicalTarget.2.control =
          (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).step
            source.2.control physicalTarget.2.code at hphysicalControl
      calc
        _ = (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).step
            source.2.control physicalTarget.2.code := by
          rw [hphysicalCodeFormula]
        _ = physicalTarget.2.control := hphysicalControl.symm
  have htargetReachable :=
    profiledOpenIndexedProvenanceCodePolicy_successor_reachable A strategy
      hwin basis initialCode codePolicy source.2.1 hlive.2.1 query.1.2
  refine ⟨targetCandidate, ?_, ?_, ?_⟩
  · refine ⟨physicalTarget, hphysicalEdge, htargetStatePhysical,
      htargetState, hlive.2.2, ?_, targetPoint, rfl⟩
    simpa only [htargetState, htargetMove] using htargetRealizes
  · change targetCandidate.2.control =
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).step
        source.2.control targetCandidate.2.code
    have htargetCodePhysical' := congrArg Prod.fst htargetStatePhysical
    have htargetControlPhysical' := congrArg Prod.snd htargetStatePhysical
    change targetCandidate.2.1.2 =
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).step
        source.2.1.2 targetCandidate.2.1.1
    rw [htargetCodePhysical', htargetControlPhysical']
    exact hphysicalControl
  · exact profiledOpenProvenancePolicy_initialCandidate_live A strategy hwin
      basis initialCode codePolicy (codePolicy.successor source.2.1 query.1.2)
        targetMove targetPoint htargetDescriptor htargetReachable
        (by simpa only [htargetState, htargetMove] using htargetRealizes)

/-! ## Common banks and the source-aware table interface -/

section
omit [Inhabited I]

/-- Strengthening liveness with policy coherence does not change the
candidate-wide common-bank construction. -/
theorem profiledOpenProvenancePolicy_commonMoveExists :
    RelationalCandidateCommonMoveExists
      (ProfiledOpenProvenancePolicyBaseLive A strategy hwin basis initialCode
        codePolicy)
      (ProfiledOpenWitnessedTableBaseValid A strategy hwin basis
        initialCode) := by
  intro candidates hactive
  have hbaseActive : RelationalCandidateSetActive
      (ProfiledOpenWitnessedTableBaseLive A strategy hwin basis initialCode)
      candidates := by
    rcases hactive with ⟨candidate, hcandidate, hlive⟩
    exact ⟨candidate, hcandidate, hlive.1⟩
  obtain ⟨bank, hbank⟩ :=
    profiledOpenActiveLaneWitnessed_commonMoveExists A strategy hwin basis
      initialCode candidates hbaseActive
  exact ⟨bank, fun candidate hcandidate hlive ↦
    hbank candidate hcandidate hlive.1⟩

/-- Source-aware encoding of policy-retagged coverage. -/
theorem
    profiledOpenProvenancePolicyRetagged_encodedLiveSuccessorCoverage :
    RelationalCandidateLiveSuccessorCoverage
      (SourceAwareRelationalLive
        (ProfiledOpenProvenancePolicyBaseLive A strategy hwin basis
          initialCode codePolicy))
      (SourceAwareRelationalCandidateValid
        (ProfiledOpenWitnessedTableBaseValid A strategy hwin basis
          initialCode))
      (sourceAwareRelationalExactEdge
        (ProfiledOpenProvenancePolicyRetaggedExactEdge A strategy hwin basis
          initialCode codePolicy))
      (sourceAwareRelationalControlStep
        (ProfiledOpenWitnessedTableControlStep A initialCode)) := by
  exact relationalCandidateLiveSuccessorCoverage_sourceAware
    (ProfiledOpenProvenancePolicyBaseLive A strategy hwin basis initialCode
      codePolicy)
    (ProfiledOpenWitnessedTableBaseValid A strategy hwin basis initialCode)
    (ProfiledOpenProvenancePolicyRetaggedExactEdge A strategy hwin basis
      initialCode codePolicy)
    (ProfiledOpenWitnessedTableControlStep A initialCode)
    (profiledOpenProvenancePolicyRetagged_liveSuccessorCoverage A strategy
      hwin basis initialCode codePolicy)

/-- Source-aware encoding of the policy-indexed common-bank theorem. -/
theorem profiledOpenProvenancePolicy_encodedCommonMoveExists :
    RelationalCandidateCommonMoveExists
      (SourceAwareRelationalLive
        (ProfiledOpenProvenancePolicyBaseLive A strategy hwin basis
          initialCode codePolicy))
      (SourceAwareRelationalCandidateValid
        (ProfiledOpenWitnessedTableBaseValid A strategy hwin basis
          initialCode)) := by
  exact relationalCandidateCommonMoveExists_sourceAware
    (ProfiledOpenProvenancePolicyBaseLive A strategy hwin basis initialCode
      codePolicy)
    (ProfiledOpenWitnessedTableBaseValid A strategy hwin basis initialCode)
    (profiledOpenProvenancePolicy_commonMoveExists A strategy hwin basis
      initialCode codePolicy)

end

/-! ## Exact threads are accepted policy paths -/

/-- A source-aware exact thread for the policy-retagged completed-direction
edge. -/
abbrev ProfiledOpenProvenancePolicyExactThread
    (initial : Finset (PolicyCandidate A initialCode))
    (move : Nat → PolicyBank A initialCode)
    (query : Nat → PolicyQuery A initialCode) :=
  SourceAwareRelationalFamilyExactThread
    (ProfiledOpenProvenancePolicyRetaggedExactEdge A strategy hwin basis
      initialCode codePolicy)
    (ProfiledOpenWitnessedTableControlStep A initialCode) initial move query

/-- The policy path carried by an exact retagged candidate thread. -/
def profiledOpenProvenancePolicyPathOfExactThread
    {initial : Finset (PolicyCandidate A initialCode)}
    {move : Nat → PolicyBank A initialCode}
    {query : Nat → PolicyQuery A initialCode}
    (thread : ProfiledOpenProvenancePolicyExactThread A strategy hwin basis
      initialCode codePolicy initial move query)
    (hinitial : (thread.candidate 0).2.1 = codePolicy.run []) :
    SourceFreeBeliefCodeParityPolicyPath
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode)
      initialCode
      (ProfiledOpenIndexedProvenanceValid A strategy hwin basis)
      (profiledOpenIndexedBiBeliefNextFiniteTag A) codePolicy where
  state := fun n ↦ (thread.candidate n).2.1
  direction := fun n ↦ (query n).1.2
  initial := hinitial
  successor := fun n ↦
    profiledOpenProvenancePolicyRetaggedExactEdge_policySuccessor A strategy
      hwin basis initialCode codePolicy (thread.exact n)

omit [Inhabited I] in
/-- The child-code word of the exact candidate thread is definitionally the
positive-time state word of its rational policy path. -/
theorem profiledOpenProvenancePolicyPathOfExactThread_childCodeWord
    {initial : Finset (PolicyCandidate A initialCode)}
    {move : Nat → PolicyBank A initialCode}
    {query : Nat → PolicyQuery A initialCode}
    (thread : ProfiledOpenProvenancePolicyExactThread A strategy hwin basis
      initialCode codePolicy initial move query)
    (hinitial : (thread.candidate 0).2.1 = codePolicy.run []) :
    (profiledOpenProvenancePolicyPathOfExactThread A strategy hwin basis
        initialCode codePolicy thread hinitial).childCodeWord
          (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode)
          initialCode
          (ProfiledOpenIndexedProvenanceValid A strategy hwin basis)
          (profiledOpenIndexedBiBeliefNextFiniteTag A) codePolicy =
      (fun n ↦ (thread.candidate (n + 1)).2.code) := by
  rfl

omit [Inhabited I] in
/-- Anti-mosaic endpoint: every exact retagged thread starting at the policy
root produces an accepted indexed-belief code word. -/
theorem profiledOpenProvenancePolicyExactThread_accepts
    {initial : Finset (PolicyCandidate A initialCode)}
    {move : Nat → PolicyBank A initialCode}
    {query : Nat → PolicyQuery A initialCode}
    (thread : ProfiledOpenProvenancePolicyExactThread A strategy hwin basis
      initialCode codePolicy initial move query)
    (hinitial : (thread.candidate 0).2.1 = codePolicy.run []) :
    (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).Accepts
      (fun n ↦ (thread.candidate (n + 1)).2.code) := by
  let path := profiledOpenProvenancePolicyPathOfExactThread A strategy hwin
    basis initialCode codePolicy thread hinitial
  simpa only [path,
    profiledOpenProvenancePolicyPathOfExactThread_childCodeWord] using
      (path.accepts
        (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode) initialCode
        (ProfiledOpenIndexedProvenanceValid A strategy hwin basis)
        (profiledOpenIndexedBiBeliefNextFiniteTag A) codePolicy)

/-! ## One finite table carrying the installed policy path -/

variable {initialState : PairedProfiledTreeState A}

/-- The old fixed-policy parity monitor and the new provenance code policy
are independent finite coordinates of one table.  The candidate relation is
the retagged edge above, so its distinguished branch is now simultaneously a
physical witnessed branch and one coherent accepting code-policy path. -/
abbrev ProfiledOpenProvenancePolicyRetaggedTablePackage
    (fixedPolicy :
      (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)
    (initialRoot : ProfiledFixedPolicyRoot A fixedPolicy)
    (point : PolicyPoint A strategy hwin basis initialCode) :=
  FixedPolicyRelationalCandidateTablePackage A fixedPolicy
    (SourceAwareRelationalLive
      (ProfiledOpenProvenancePolicyBaseLive A strategy hwin basis initialCode
        codePolicy))
    (SourceAwareRelationalCandidateValid
      (ProfiledOpenWitnessedTableBaseValid A strategy hwin basis initialCode))
    (sourceAwareRelationalExactEdge
      (ProfiledOpenProvenancePolicyRetaggedExactEdge A strategy hwin basis
        initialCode codePolicy))
    (sourceAwareRelationalControlStep
      (ProfiledOpenWitnessedTableControlStep A initialCode))
    initialRoot
    (sourceAwareRelationalCandidatesEncode
      (profiledOpenActiveLaneWitnessedInitialCandidateSet A strategy hwin basis
        initialCode point))
    (sourceAwareRelationalCandidateEncode
      (profiledOpenActiveLaneWitnessedInitialCandidate A strategy hwin basis
        initialCode point))

/-- One accepted distinguished thread returned by the finite table.  The
acceptance proof refers to the exact child-code word carried by `thread`; it
is not inherited from a disconnected monitor word. -/
structure ProfiledOpenProvenancePolicyAcceptedExactThread
    (initial : Finset (PolicyCandidate A initialCode))
    (move : Nat → PolicyBank A initialCode)
    (query : Nat → PolicyQuery A initialCode) where
  thread : ProfiledOpenProvenancePolicyExactThread A strategy hwin basis
    initialCode codePolicy initial move query
  initial_state : (thread.candidate 0).2.1 = codePolicy.run []
  accepts : (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).Accepts
    (fun n ↦ (thread.candidate (n + 1)).2.code)

/-- End-to-end finite table specialization.  The installed root is selected
from the strengthened policy itself.  Every query word has a nonempty exact
distinguished thread, and that very thread's child-code word is accepted.

This theorem is unconditional: policy provenance, retagged successor
coverage, and the common bank were all constructed above. -/
theorem exists_profiledOpenProvenancePolicyRetaggedFixedPolicyTable
    (fixedPolicy :
      (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)
    (initialRoot : ProfiledFixedPolicyRoot A fixedPolicy)
    (hinitialRoot : initialRoot.state A fixedPolicy = fixedPolicy.run []) :
    ∃ point : PolicyPoint A strategy hwin basis initialCode,
      ∃ package : ProfiledOpenProvenancePolicyRetaggedTablePackage A
          strategy hwin basis initialCode codePolicy fixedPolicy initialRoot
            point,
        ∀ query : Nat → PolicyQuery A initialCode,
          Nonempty
            (ProfiledOpenProvenancePolicyAcceptedExactThread A strategy hwin
              basis initialCode codePolicy
              (profiledOpenActiveLaneWitnessedInitialCandidateSet A strategy
                hwin basis initialCode point)
              (package.branch.moveAt query) query) := by
  have hrootReachable :
      SourceFreeBeliefCodeParityRationalPolicy.Reachable
        (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode)
        initialCode
        (ProfiledOpenIndexedProvenanceValid A strategy hwin basis)
        (profiledOpenIndexedBiBeliefNextFiniteTag A) codePolicy
        (codePolicy.run []) :=
    ⟨[], rfl⟩
  obtain ⟨rootMove, point, hrootMove, hpointDescriptor, _hcandidate,
      _hbaseLive⟩ :=
    exists_profiledOpenIndexedProvenanceCodePolicyInstalledCandidate A
      strategy hwin basis initialCode codePolicy (codePolicy.run [])
        hrootReachable
  let initial :=
    profiledOpenActiveLaneWitnessedInitialCandidateSet A strategy hwin basis
      initialCode point
  let actual :=
    profiledOpenActiveLaneWitnessedInitialCandidate A strategy hwin basis
      initialCode point
  have hactualMem : actual ∈ initial := by
    exact profiledOpenActiveLaneWitnessedInitialCandidate_mem A strategy hwin
      basis initialCode point
  have hactualLive :
      ProfiledOpenProvenancePolicyBaseLive A strategy hwin basis initialCode
        codePolicy actual.2 actual.1 := by
    exact profiledOpenProvenancePolicy_initialCandidate_live A strategy hwin
      basis initialCode codePolicy (codePolicy.run []) rootMove point
        hpointDescriptor hrootReachable hrootMove
  have hencodedMem : sourceAwareRelationalCandidateEncode actual ∈
      sourceAwareRelationalCandidatesEncode initial :=
    mem_sourceAwareRelationalCandidatesEncode initial actual hactualMem
  have hencodedLive : SourceAwareRelationalLive
      (ProfiledOpenProvenancePolicyBaseLive A strategy hwin basis initialCode
        codePolicy)
      (sourceAwareRelationalCandidateEncode actual).2
      (sourceAwareRelationalCandidateEncode actual).1 :=
    ⟨rfl, hactualLive⟩
  obtain ⟨package, hthreads⟩ :=
    exists_fixedPolicyRelationalCandidateTable A fixedPolicy
      (SourceAwareRelationalLive
        (ProfiledOpenProvenancePolicyBaseLive A strategy hwin basis
          initialCode codePolicy))
      (SourceAwareRelationalCandidateValid
        (ProfiledOpenWitnessedTableBaseValid A strategy hwin basis
          initialCode))
      (sourceAwareRelationalExactEdge
        (ProfiledOpenProvenancePolicyRetaggedExactEdge A strategy hwin basis
          initialCode codePolicy))
      (sourceAwareRelationalControlStep
        (ProfiledOpenWitnessedTableControlStep A initialCode))
      initialRoot hinitialRoot
      (sourceAwareRelationalCandidatesEncode initial)
      (sourceAwareRelationalCandidateEncode actual) hencodedMem hencodedLive
      (profiledOpenProvenancePolicyRetagged_encodedLiveSuccessorCoverage A
        strategy hwin basis initialCode codePolicy)
      (profiledOpenProvenancePolicy_encodedCommonMoveExists A strategy hwin
        basis initialCode codePolicy)
  refine ⟨point, package, ?_⟩
  intro query
  obtain ⟨encodedThread⟩ := hthreads query
  let thread := sourceAwareRelationalFamilyExactThreadDecode
    (ProfiledOpenProvenancePolicyRetaggedExactEdge A strategy hwin basis
      initialCode codePolicy)
    (ProfiledOpenWitnessedTableControlStep A initialCode) initial
    (package.branch.moveAt query) query encodedThread
  have hzero : thread.candidate 0 = actual := by
    have hinitial := thread.initial_mem
    simpa only [initial,
      profiledOpenActiveLaneWitnessedInitialCandidateSet,
      Finset.mem_singleton] using hinitial
  have hinitialState : (thread.candidate 0).2.1 = codePolicy.run [] := by
    rw [hzero]
    exact congrArg Prod.fst hpointDescriptor
  refine ⟨⟨thread, hinitialState, ?_⟩⟩
  exact profiledOpenProvenancePolicyExactThread_accepts A strategy hwin basis
    initialCode codePolicy thread hinitialState

/-! ## Explicit finite recurrence of the retagged table -/

/-- The complete finite public recurrence state. -/
abbrev ProfiledOpenProvenancePolicyRetaggedBranchState
    (fixedPolicy :
      (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)
    (point : PolicyPoint A strategy hwin basis initialCode)
    (initialRoot : ProfiledFixedPolicyRoot A fixedPolicy)
    (package : ProfiledOpenProvenancePolicyRetaggedTablePackage A strategy hwin
      basis initialCode codePolicy fixedPolicy initialRoot point) :=
  package.table.toTransitionRationalTree.Control ×
    Finset (RelationalFamilyCandidate
      (ProfiledOpenWitnessedTableFamily A initialCode)
      (ProfiledOpenWitnessedTableDescriptor A initialCode))

/-- Initial finite recurrence state of the retagged table. -/
noncomputable def profiledOpenProvenancePolicyRetaggedBranchInitial
    (fixedPolicy :
      (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)
    (point : PolicyPoint A strategy hwin basis initialCode)
    (initialRoot : ProfiledFixedPolicyRoot A fixedPolicy)
    (package : ProfiledOpenProvenancePolicyRetaggedTablePackage A strategy hwin
      basis initialCode codePolicy fixedPolicy initialRoot point) :
    ProfiledOpenProvenancePolicyRetaggedBranchState A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package :=
  (package.table.toTransitionRationalTree.initial,
    sourceAwareRelationalCandidatesEncode
      (profiledOpenActiveLaneWitnessedInitialCandidateSet A strategy hwin basis
        initialCode point))

/-- Total one-query recurrence.  `none` is only the generic unreachable
completion; the distinguished branch label theorem below rules it out. -/
noncomputable def profiledOpenProvenancePolicyRetaggedBranchStep
    (fixedPolicy :
      (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)
    (point : PolicyPoint A strategy hwin basis initialCode)
    (initialRoot : ProfiledFixedPolicyRoot A fixedPolicy)
    (package : ProfiledOpenProvenancePolicyRetaggedTablePackage A strategy hwin
      basis initialCode codePolicy fixedPolicy initialRoot point)
    (current : ProfiledOpenProvenancePolicyRetaggedBranchState A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package)
    (query : PolicyQuery A initialCode) :
    ProfiledOpenProvenancePolicyRetaggedBranchState A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package :=
  match package.table.toTransitionRationalTree.labelOf current.1 with
  | none => current
  | some bank =>
      let nextCandidates := relationalFamilySaturation
        (sourceAwareRelationalExactEdge
          (ProfiledOpenProvenancePolicyRetaggedExactEdge A strategy hwin basis
            initialCode codePolicy))
        (sourceAwareRelationalControlStep
          (ProfiledOpenWitnessedTableControlStep A initialCode))
        current.2 bank query
      (package.table.toTransitionRationalTree.step current.1
        (query, nextCandidates), nextCandidates)

/-- Public recurrence state reached by the distinguished branch at depth
`n`. -/
noncomputable def profiledOpenProvenancePolicyRetaggedBranchStateAt
    (fixedPolicy :
      (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)
    (point : PolicyPoint A strategy hwin basis initialCode)
    (initialRoot : ProfiledFixedPolicyRoot A fixedPolicy)
    (package : ProfiledOpenProvenancePolicyRetaggedTablePackage A strategy hwin
      basis initialCode codePolicy fixedPolicy initialRoot point)
    (query : Nat → PolicyQuery A initialCode) (n : Nat) :
    ProfiledOpenProvenancePolicyRetaggedBranchState A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package :=
  (package.table.toTransitionRationalTree.controlAt
      (package.branch.cursorAt query n).node,
    (package.branch.cursorAt query n).candidates)

/-- The distinguished recurrence always reads its genuine common bank. -/
theorem profiledOpenProvenancePolicyRetaggedBranchStateAt_label
    (fixedPolicy :
      (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)
    (point : PolicyPoint A strategy hwin basis initialCode)
    (initialRoot : ProfiledFixedPolicyRoot A fixedPolicy)
    (package : ProfiledOpenProvenancePolicyRetaggedTablePackage A strategy hwin
      basis initialCode codePolicy fixedPolicy initialRoot point)
    (query : Nat → PolicyQuery A initialCode) (n : Nat) :
    package.table.toTransitionRationalTree.labelOf
        (profiledOpenProvenancePolicyRetaggedBranchStateAt A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
          query n).1 =
      some (package.branch.moveAt query n) := by
  change package.table.toTransitionRationalTree.labeledTree
      (package.branch.cursorAt query n).node =
    some (package.branch.moveAt query n)
  rw [← package.branch_tree_eq]
  exact RelationalCandidateTreeBranchPackage.Cursor.tree_eq_some_move
    package.branch (package.branch.cursorAt query n)

@[simp] theorem profiledOpenProvenancePolicyRetaggedBranchStateAt_zero
    (fixedPolicy :
      (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)
    (point : PolicyPoint A strategy hwin basis initialCode)
    (initialRoot : ProfiledFixedPolicyRoot A fixedPolicy)
    (package : ProfiledOpenProvenancePolicyRetaggedTablePackage A strategy hwin
      basis initialCode codePolicy fixedPolicy initialRoot point)
    (query : Nat → PolicyQuery A initialCode) :
    profiledOpenProvenancePolicyRetaggedBranchStateAt A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package query 0 =
      profiledOpenProvenancePolicyRetaggedBranchInitial A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package := by
  rfl

/-- The explicit public state follows the retagged recurrence exactly. -/
theorem profiledOpenProvenancePolicyRetaggedBranchStateAt_succ
    (fixedPolicy :
      (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)
    (point : PolicyPoint A strategy hwin basis initialCode)
    (initialRoot : ProfiledFixedPolicyRoot A fixedPolicy)
    (package : ProfiledOpenProvenancePolicyRetaggedTablePackage A strategy hwin
      basis initialCode codePolicy fixedPolicy initialRoot point)
    (query : Nat → PolicyQuery A initialCode) (n : Nat) :
    profiledOpenProvenancePolicyRetaggedBranchStateAt A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package query
          (n + 1) =
      profiledOpenProvenancePolicyRetaggedBranchStep A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package
        (profiledOpenProvenancePolicyRetaggedBranchStateAt A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
          query n) (query n) := by
  rw [profiledOpenProvenancePolicyRetaggedBranchStep,
    profiledOpenProvenancePolicyRetaggedBranchStateAt_label]
  apply Prod.ext
  · simp only [profiledOpenProvenancePolicyRetaggedBranchStateAt,
      RelationalCandidateTreeBranchPackage.cursorAt,
      RelationalCandidateTreeBranchPackage.Cursor.step]
    rw [TransitionRationalTree.controlAt_append]
    rfl
  · rfl

/-- Candidate-set projection of the explicit state. -/
theorem profiledOpenProvenancePolicyRetaggedBranchStateAt_candidates
    (fixedPolicy :
      (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)
    (point : PolicyPoint A strategy hwin basis initialCode)
    (initialRoot : ProfiledFixedPolicyRoot A fixedPolicy)
    (package : ProfiledOpenProvenancePolicyRetaggedTablePackage A strategy hwin
      basis initialCode codePolicy fixedPolicy initialRoot point)
    (query : Nat → PolicyQuery A initialCode) (n : Nat) :
    (profiledOpenProvenancePolicyRetaggedBranchStateAt A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package query n).2 =
      (package.branch.cursorAt query n).candidates :=
  rfl

end

end DetParityAutomaton

end DistributedSynthesis
