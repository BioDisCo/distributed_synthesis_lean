/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenShapeFreeFixedPolicyTable

/-!
# Initial candidate for the shape-free fixed-policy table

An explicit optional controlled semantic state already contains all data
needed to start the relational candidate table.  Its literal descriptor and
public two-fibre family form one candidate; the proof-side shape-free class
map supplies only the public sticky tags.  The canonical initial candidate
set is the singleton containing that candidate.

No graph shape, orientation, active lane, or strict-leader bit is inspected
by these definitions.  The only semantic witness is retained in proofs of
liveness and is not part of the finite public candidate.

The final section constructs the initial `ProfiledFixedPolicyRoot` directly
when a rational policy is typed at a recurrent right or left root.  In that
case the policy's accepting-run root equation supplies both reachability and
the equation at the empty word.  Thus no extra initial-orientation premise is
needed after the exceptional finite prefix has selected a recurrent child.
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

private abbrev InitialDescriptor :=
  ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode

private abbrev InitialRawFamily :=
  ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I) initialCode

private abbrev InitialTaggedFamily :=
  SidewiseTaggedFamily OneClass TwoClass
    (InitialRawFamily A initialCode)

private abbrev InitialCandidate :=
  RelationalFamilyCandidate
    (InitialTaggedFamily A initialCode (OneClass := OneClass)
      (TwoClass := TwoClass))
    (InitialDescriptor A initialCode)

/-! ## The canonical singleton -/

/-- The tagged family of one explicit semantic state.  `classOf` is applied
only to the state's already finite descriptor and public family. -/
noncomputable def profiledOpenShapeFreeInitialTaggedFamily
    (classOf : InitialDescriptor A initialCode →
      InitialRawFamily A initialCode → OneClass × TwoClass)
    (state : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode) :
    InitialTaggedFamily A initialCode (OneClass := OneClass)
      (TwoClass := TwoClass) :=
  let descriptor :=
    profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
      basis initialCode state
  let family :=
    profiledOpenOptionalControlledFamilyOf A strategy hwin basis initialCode
      state
  (classOf descriptor family, family)

/-- The literal candidate represented by one explicit semantic state. -/
noncomputable def profiledOpenShapeFreeInitialCandidate
    (classOf : InitialDescriptor A initialCode →
      InitialRawFamily A initialCode → OneClass × TwoClass)
    (state : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode) :
    InitialCandidate A initialCode (OneClass := OneClass)
      (TwoClass := TwoClass) :=
  (profiledOpenShapeFreeInitialTaggedFamily A strategy hwin basis initialCode
      classOf state,
    profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
      basis initialCode state)

/-- The canonical initial public candidate set contains no speculative
members: it is the singleton of the actual initial candidate. -/
noncomputable def profiledOpenShapeFreeInitialCandidateSet
    (classOf : InitialDescriptor A initialCode →
      InitialRawFamily A initialCode → OneClass × TwoClass)
    (state : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode) :
    Finset (InitialCandidate A initialCode (OneClass := OneClass)
      (TwoClass := TwoClass)) :=
  {profiledOpenShapeFreeInitialCandidate A strategy hwin basis initialCode
    classOf state}

omit [Inhabited I] [Fintype OneClass] [Fintype TwoClass] in
@[simp] theorem profiledOpenShapeFreeInitialCandidate_mem
    (classOf : InitialDescriptor A initialCode →
      InitialRawFamily A initialCode → OneClass × TwoClass)
    (state : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode) :
    profiledOpenShapeFreeInitialCandidate A strategy hwin basis initialCode
        classOf state ∈
      profiledOpenShapeFreeInitialCandidateSet A strategy hwin basis
        initialCode classOf state := by
  classical
  simp only [profiledOpenShapeFreeInitialCandidateSet, Finset.mem_singleton]

omit [Inhabited I] [Fintype OneClass] [Fintype TwoClass] in
/-- The explicit semantic state proves both semantic liveness and the
canonical shape-free class-tag invariant for its singleton candidate. -/
theorem profiledOpenShapeFreeInitialCandidate_live
    (classOf : InitialDescriptor A initialCode →
      InitialRawFamily A initialCode → OneClass × TwoClass)
    (state : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode) :
    ProfiledOpenFixedSidewiseSemanticLive A strategy hwin basis initialCode
      (ProfiledOpenShapeFreeClassTagInvariant A initialCode classOf)
      (profiledOpenShapeFreeInitialCandidate A strategy hwin basis initialCode
        classOf state).2
      (profiledOpenShapeFreeInitialCandidate A strategy hwin basis initialCode
        classOf state).1 := by
  refine ⟨?_, ?_⟩
  · exact ⟨state, rfl, rfl⟩
  · rfl

/-! ## One-arrow initialization of the existing table theorem -/

variable {initialState : PairedProfiledTreeState A}
variable (policy :
  (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)

/-- Once the common shape-free bank and one recurrent policy root are
available, an explicit semantic state discharges every initial-candidate
argument of the fixed-policy table theorem. -/
theorem exists_profiledOpenShapeFreeFixedPolicyRelationalCandidateTable_of_initialState
    (classOf : InitialDescriptor A initialCode →
      InitialRawFamily A initialCode → OneClass × TwoClass)
    (common : RelationalCandidateCommonMoveExists
      (ProfiledOpenFixedSidewiseSemanticLive A strategy hwin basis initialCode
        (ProfiledOpenShapeFreeClassTagInvariant A initialCode classOf))
      (ProfiledOpenFixedSidewiseReanchoredCandidateValid A strategy hwin basis
        initialCode))
    (state : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode)
    (initialRoot : ProfiledFixedPolicyRoot A policy)
    (hinitialRoot : initialRoot.state A policy = policy.run []) :
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
        initialRoot
        (profiledOpenShapeFreeInitialCandidateSet A strategy hwin basis
          initialCode classOf state)
        (profiledOpenShapeFreeInitialCandidate A strategy hwin basis
          initialCode classOf state),
      ∀ query : Nat →
          ProfiledOpenFixedSidewiseReachablePointedQuery A initialCode,
        Nonempty (RelationalFamilyExactThread
          (ProfiledOpenFixedSidewiseReanchoredExactEdge A strategy hwin basis
            initialCode
            (ProfiledOpenShapeFreeClassTagInvariant A initialCode classOf)
            (profiledOpenShapeFreeClassTargetTag A initialCode classOf))
          (ProfiledOpenFixedSidewiseControlStep A initialCode)
          (profiledOpenShapeFreeInitialCandidateSet A strategy hwin basis
            initialCode classOf state)
          (package.branch.moveAt query) query) := by
  apply exists_profiledOpenShapeFreeFixedPolicyRelationalCandidateTable_of_classTag
    A strategy hwin basis initialCode policy classOf common initialRoot
      hinitialRoot
      (profiledOpenShapeFreeInitialCandidateSet A strategy hwin basis
        initialCode classOf state)
      (profiledOpenShapeFreeInitialCandidate A strategy hwin basis initialCode
        classOf state)
  · exact profiledOpenShapeFreeInitialCandidate_mem A strategy hwin basis
      initialCode classOf state
  · exact profiledOpenShapeFreeInitialCandidate_live A strategy hwin basis
      initialCode classOf state

/-! ## Canonical recurrent policy roots -/

/-- If the policy automaton starts at a right recurrent state, its canonical
fixed-policy root is obtained without an additional reachability choice. -/
noncomputable def profiledFixedPolicyInitialRightRoot
    (live : (((A.State × A.State) × A.State) ×
      RightInitialActionProfile
        (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂)))
    (rightPolicy :
      (pairedProfiledEntryRunAutomaton A (.inr (.inl live)))
        |>.RationalTransitionPolicy) :
    ProfiledFixedPolicyRoot A rightPolicy :=
  .right ⟨live, ⟨[], rightPolicy.accepts.1.1⟩⟩

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁]
    [DecidableEq In₂] in
@[simp] theorem profiledFixedPolicyInitialRightRoot_state
    (live : (((A.State × A.State) × A.State) ×
      RightInitialActionProfile
        (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂)))
    (rightPolicy :
      (pairedProfiledEntryRunAutomaton A (.inr (.inl live)))
        |>.RationalTransitionPolicy) :
    (profiledFixedPolicyInitialRightRoot A live rightPolicy).state A
        rightPolicy = rightPolicy.run [] := by
  exact rightPolicy.accepts.1.1.symm

/-- Process-swapped recurrent initial root. -/
noncomputable def profiledFixedPolicyInitialLeftRoot
    (live : (((A.State × A.State) × A.State) ×
      LeftInitialActionProfile
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)))
    (leftPolicy :
      (pairedProfiledEntryRunAutomaton A (.inr (.inr live)))
        |>.RationalTransitionPolicy) :
    ProfiledFixedPolicyRoot A leftPolicy :=
  .left ⟨live, ⟨[], leftPolicy.accepts.1.1⟩⟩

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁]
    [DecidableEq In₂] in
@[simp] theorem profiledFixedPolicyInitialLeftRoot_state
    (live : (((A.State × A.State) × A.State) ×
      LeftInitialActionProfile
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)))
    (leftPolicy :
      (pairedProfiledEntryRunAutomaton A (.inr (.inr live)))
        |>.RationalTransitionPolicy) :
    (profiledFixedPolicyInitialLeftRoot A live leftPolicy).state A leftPolicy =
      leftPolicy.run [] := by
  exact leftPolicy.accepts.1.1.symm

end

end DetParityAutomaton

end DistributedSynthesis
