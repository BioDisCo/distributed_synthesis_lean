/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFixedPolicyRelationalCandidateTable
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenReanchoredSidewiseSuccessor

/-!
# The re-anchored sidewise bank feeds the fixed-policy candidate table

This file is the final generic adapter between the shape-free sidewise-bank
construction and `exists_fixedPolicyRelationalCandidateTable`.  Re-anchoring
already supplies exact, control-correct, live successor coverage.  Therefore
the only remaining move-side premise is the candidate-wide common-bank law.

The law is stated over the complete public candidate set.  Its witness is one
fixed symmetric bank, not a selected semantic source, hidden optional shape,
orientation, lane, or strict-leader signal.  All semantic witnesses below are
proof-side only.
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

variable {OneClass : Type oc} {TwoClass : Type tc}
variable [Fintype OneClass] [Fintype TwoClass]

variable {initialState : PairedProfiledTreeState A}
variable (policy :
  (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)

private abbrev TableDescriptor :=
  ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode

private abbrev TableFamily :=
  SidewiseTaggedFamily OneClass TwoClass
    (ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I) initialCode)

private abbrev TableMove :=
  ProfiledOpenFixedSidewisePinnedBank A initialCode OneClass TwoClass

private abbrev TableQuery :=
  ProfiledOpenFixedSidewiseReachablePointedQuery A initialCode

/-! ## Canonical proof-side class tagging -/

/-- A tagged family carries exactly the two shape-free classes assigned to
its retained descriptor and public family.  In the concrete instantiation
`classOf` is obtained from an attained semantic representative and defaults
only off the live fragment.

Although the target tag is generated proof-side, it becomes public table
state.  Consequently the concrete `classOf` must be the projected
shape-free class, never an optional-shape, orientation, or leader test. -/
def ProfiledOpenShapeFreeClassTagInvariant
    (classOf : TableDescriptor A initialCode →
      ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I) initialCode →
      OneClass × TwoClass)
    (descriptor : TableDescriptor A initialCode)
    (family : TableFamily A initialCode (OneClass := OneClass)
      (TwoClass := TwoClass)) : Prop :=
  family.1 = classOf descriptor family.2

/-- Canonical contextual target tag.  It ignores the source controller and
query and tags the literal retained target family/descriptor pair. -/
def profiledOpenShapeFreeClassTargetTag
    (classOf : TableDescriptor A initialCode →
      ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I) initialCode →
      OneClass × TwoClass)
    (_source : TableDescriptor A initialCode)
    (_bank : TableMove A initialCode (OneClass := OneClass)
      (TwoClass := TwoClass))
    (_query : TableQuery A initialCode)
    (family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I)
      initialCode)
    (target : TableDescriptor A initialCode) : OneClass × TwoClass :=
  classOf target family

omit [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    [Fintype OneClass] [Fintype TwoClass] in
theorem profiledOpenShapeFreeClassTargetTag_invariant
    (classOf : TableDescriptor A initialCode →
      ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I) initialCode →
      OneClass × TwoClass)
    (source : TableDescriptor A initialCode)
    (bank : TableMove A initialCode (OneClass := OneClass)
      (TwoClass := TwoClass))
    (query : TableQuery A initialCode)
    (family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I)
      initialCode)
    (target : TableDescriptor A initialCode) :
    ProfiledOpenShapeFreeClassTagInvariant A initialCode classOf target
      ((profiledOpenShapeFreeClassTargetTag A initialCode classOf source bank
        query family target), family) :=
  rfl

/-!
The theorem deliberately accepts the common-bank law at exactly the
strength produced by the shape-free extraction.  It does not ask for a
chosen hidden source or a reflection theorem from equal public classes back
to equal semantic views.
-/

/-- Re-anchored coverage and one shape-free common bank are precisely the
inputs needed by the fixed-policy relational candidate table. -/
theorem exists_profiledOpenShapeFreeFixedPolicyRelationalCandidateTable
    (TagInvariant : TableDescriptor A initialCode →
      TableFamily A initialCode (OneClass := OneClass)
        (TwoClass := TwoClass) → Prop)
    (targetTag :
      TableDescriptor A initialCode →
      TableMove A initialCode (OneClass := OneClass) (TwoClass := TwoClass) →
      TableQuery A initialCode →
      ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I) initialCode →
      TableDescriptor A initialCode → OneClass × TwoClass)
    (htag : ∀ source bank query family target,
      TagInvariant target
        ((targetTag source bank query family target), family))
    (common : RelationalCandidateCommonMoveExists
      (ProfiledOpenFixedSidewiseSemanticLive A strategy hwin basis initialCode
        TagInvariant)
      (ProfiledOpenFixedSidewiseReanchoredCandidateValid A strategy hwin basis
        initialCode))
    (initialRoot : ProfiledFixedPolicyRoot A policy)
    (hinitial : initialRoot.state A policy = policy.run [])
    (initial : Finset (RelationalFamilyCandidate
      (TableFamily A initialCode (OneClass := OneClass) (TwoClass := TwoClass))
      (TableDescriptor A initialCode)))
    (initialActual : RelationalFamilyCandidate
      (TableFamily A initialCode (OneClass := OneClass) (TwoClass := TwoClass))
      (TableDescriptor A initialCode))
    (hinitialMem : initialActual ∈ initial)
    (hinitialLive :
      ProfiledOpenFixedSidewiseSemanticLive A strategy hwin basis initialCode
        TagInvariant initialActual.2 initialActual.1) :
    ∃ package : FixedPolicyRelationalCandidateTablePackage A policy
        (ProfiledOpenFixedSidewiseSemanticLive A strategy hwin basis
          initialCode TagInvariant)
        (ProfiledOpenFixedSidewiseReanchoredCandidateValid A strategy hwin
          basis initialCode)
        (ProfiledOpenFixedSidewiseReanchoredExactEdge A strategy hwin basis
          initialCode TagInvariant targetTag)
        (ProfiledOpenFixedSidewiseControlStep A initialCode)
        initialRoot initial initialActual,
      ∀ query : Nat → TableQuery A initialCode,
        Nonempty (RelationalFamilyExactThread
          (ProfiledOpenFixedSidewiseReanchoredExactEdge A strategy hwin basis
            initialCode TagInvariant targetTag)
          (ProfiledOpenFixedSidewiseControlStep A initialCode)
          initial (package.branch.moveAt query) query) := by
  apply exists_fixedPolicyRelationalCandidateTable A policy
    (ProfiledOpenFixedSidewiseSemanticLive A strategy hwin basis initialCode
      TagInvariant)
    (ProfiledOpenFixedSidewiseReanchoredCandidateValid A strategy hwin basis
      initialCode)
    (ProfiledOpenFixedSidewiseReanchoredExactEdge A strategy hwin basis
      initialCode TagInvariant targetTag)
    (ProfiledOpenFixedSidewiseControlStep A initialCode)
    initialRoot hinitial initial initialActual hinitialMem hinitialLive
  · exact profiledOpenFixedSidewiseReanchored_liveSuccessorCoverage A
      strategy hwin basis initialCode TagInvariant targetTag htag
  · exact common

/-- Canonical-tag specialization.  Once the shape-free construction supplies
`classOf` and the corresponding candidate-wide common bank, no separate
target-tag preservation theorem remains: it is definitional. -/
theorem exists_profiledOpenShapeFreeFixedPolicyRelationalCandidateTable_of_classTag
    (classOf : TableDescriptor A initialCode →
      ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I) initialCode →
      OneClass × TwoClass)
    (common : RelationalCandidateCommonMoveExists
      (ProfiledOpenFixedSidewiseSemanticLive A strategy hwin basis initialCode
        (ProfiledOpenShapeFreeClassTagInvariant A initialCode classOf))
      (ProfiledOpenFixedSidewiseReanchoredCandidateValid A strategy hwin basis
        initialCode))
    (initialRoot : ProfiledFixedPolicyRoot A policy)
    (hinitial : initialRoot.state A policy = policy.run [])
    (initial : Finset (RelationalFamilyCandidate
      (TableFamily A initialCode (OneClass := OneClass) (TwoClass := TwoClass))
      (TableDescriptor A initialCode)))
    (initialActual : RelationalFamilyCandidate
      (TableFamily A initialCode (OneClass := OneClass) (TwoClass := TwoClass))
      (TableDescriptor A initialCode))
    (hinitialMem : initialActual ∈ initial)
    (hinitialLive :
      ProfiledOpenFixedSidewiseSemanticLive A strategy hwin basis initialCode
        (ProfiledOpenShapeFreeClassTagInvariant A initialCode classOf)
        initialActual.2 initialActual.1) :
    ∃ package : FixedPolicyRelationalCandidateTablePackage A policy
        (ProfiledOpenFixedSidewiseSemanticLive A strategy hwin basis
          initialCode
          (ProfiledOpenShapeFreeClassTagInvariant A initialCode classOf))
        (ProfiledOpenFixedSidewiseReanchoredCandidateValid A strategy hwin
          basis initialCode)
        (ProfiledOpenFixedSidewiseReanchoredExactEdge A strategy hwin basis
          initialCode
          (ProfiledOpenShapeFreeClassTagInvariant A initialCode classOf)
          (profiledOpenShapeFreeClassTargetTag A initialCode classOf))
        (ProfiledOpenFixedSidewiseControlStep A initialCode)
        initialRoot initial initialActual,
      ∀ query : Nat → TableQuery A initialCode,
        Nonempty (RelationalFamilyExactThread
          (ProfiledOpenFixedSidewiseReanchoredExactEdge A strategy hwin basis
            initialCode
            (ProfiledOpenShapeFreeClassTagInvariant A initialCode classOf)
            (profiledOpenShapeFreeClassTargetTag A initialCode classOf))
          (ProfiledOpenFixedSidewiseControlStep A initialCode)
          initial (package.branch.moveAt query) query) := by
  exact exists_profiledOpenShapeFreeFixedPolicyRelationalCandidateTable A
    strategy hwin basis initialCode policy
    (ProfiledOpenShapeFreeClassTagInvariant A initialCode classOf)
    (profiledOpenShapeFreeClassTargetTag A initialCode classOf)
    (profiledOpenShapeFreeClassTargetTag_invariant A initialCode classOf)
    common initialRoot hinitial initial initialActual hinitialMem hinitialLive

end

end DetParityAutomaton

end DistributedSynthesis
