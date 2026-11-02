/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshPhaseActivatedRecurrentHandoff
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointUnitCanonicalMemberTraceAlignment
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointUnitPersistentStrictAcceptance

/-!
# The activated recurrent trace remains in one literal child

The retained stage used by the one-way activation names one dependent child.
The exact pair theorem enters the indexed recurrent kernel at that child, and
the existing indexed-to-fixed-policy simulation preserves it under every
subsequent physical round.  This file packages those two facts as a trace
invariant.

The child and its fixed-policy comparison state are proof-side witnesses.
No endpoint receives a child key, graph, orientation, hierarchy side, leader
bit, history, or semantic view.
-/

namespace DistributedSynthesis

universe u v x y s c

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

private abbrev CommonPoint :=
  ProfiledRawJointGuardedCommonSemanticPoint A strategy

private abbrev CrossValid :=
  ProfiledRawJointGuardedCommonLiteralCrossExtraValid A strategy hwin

namespace ProfiledRawJointGuardedCommonDecoratedPolicyPackage

variable {initial : CommonPoint A strategy}

private abbrev Package :=
  ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy hwin initial
    (CrossValid A strategy hwin)

private abbrev TaggedChild (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamTaggedChildCode A strategy hwin
    package

private abbrev TaggedKernel (package : Package A strategy hwin
    (initial := initial)) :=
  package.literalRightSeamTaggedExecutableKernel A strategy hwin

private abbrev UnitAdapter
    (package : Package A strategy hwin (initial := initial))
    (key : TaggedChild A strategy hwin package) :=
  profiledRawJointUnitPolicyDummyExceptionalAdapter A strategy
    (package.literalRightSeamTaggedChildSource A strategy hwin key)
    (package.literalRightSeamTaggedChildPolicy A strategy hwin key)
    (package.literalRightSeamTaggedChildControllerBank A strategy hwin key)
    (InitialOne := Unit) (InitialTwo := Unit)
    (ExceptionalOne := Unit) (ExceptionalTwo := Unit)

private abbrev UnitKernel
    (package : Package A strategy hwin (initial := initial))
    (key : TaggedChild A strategy hwin package) :=
  profiledRawJointUnitPolicyLeaderFreeKernel A strategy
    (package.literalRightSeamTaggedChildSource A strategy hwin key)
    (package.literalRightSeamTaggedChildPolicy A strategy hwin key)
    (package.literalRightSeamTaggedChildControllerBank A strategy hwin key)
    (UnitAdapter A strategy hwin package key)

/-! ## Every freshly advanced receiver carries a policy edge -/

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- The total fallback of a right receiver is itself an exact checked edge. -/
theorem profiledRawJointUnitPolicyFallbackLeft_alternatingStep
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy
      (initial.code A) policy) :
    ProfiledRawJointUnitFixedPolicyRoot.AlternatingStep A policy (.inl source)
      (.inr (profiledRawJointUnitPolicyFallbackLeft A strategy initial policy
        bank source)) := by
  let target := profiledRawJointUnitPolicyFallbackLeft A strategy initial
    policy bank source
  have hstage :
      (stepProfiledRawJointUnitRightPolicyReceiverFor A strategy initial policy
        bank source
          (profiledRawJointUnitRightPolicyFiniteStateAfter A strategy initial
            policy bank source []).1 .first
          (profiledRawJointUnitRightPolicyFiniteStateAfter A strategy initial
            policy bank source []).2 default).2.2 = some target := by
    exact (Classical.choose_spec
      (profiledRawJointUnitRightPolicy_real_close_stages_exact A strategy
        initial policy bank source .first [] default)).1
  exact .rightToLeft source target
    (profiledRawJointUnitRightPolicyReceiverFor_allowed_of_staged A strategy
      initial policy bank source
        (profiledRawJointUnitRightPolicyFiniteStateAfter A strategy initial
          policy bank source []).1 .first
        (profiledRawJointUnitRightPolicyFiniteStateAfter A strategy initial
          policy bank source []).2 default target hstage)

/-- Any actual continuation of a right receiver exposes an alternating edge. -/
theorem profiledRawJointUnitPolicyRightReceiverTarget_after_continue_step
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (receiver : ProfiledRawJointUnitRightPolicyReceiverControl A strategy
      initial policy)
    (owner : ProfiledRawJointUnitRightPolicyOwnerControl A strategy initial
      policy bank) (move : In₂ × In₁) :
    ProfiledRawJointUnitFixedPolicyRoot.AlternatingStep A policy
      (.inl receiver.1)
      (.inr (profiledRawJointUnitPolicyRightReceiverTarget A strategy initial
        policy bank
          (continueProfiledRawJointUnitRightPolicyReceiver A strategy initial
            policy bank receiver owner move).2)) := by
  let ownerFor := profiledRawJointUnitRightPolicyOwnerControlFor A strategy
    initial policy bank receiver owner
  let result := stepProfiledRawJointUnitRightPolicyReceiverFor A strategy
    initial policy bank receiver.1 ownerFor receiver.2.1 receiver.2.2.1 move
  change ProfiledRawJointUnitFixedPolicyRoot.AlternatingStep A policy
    (.inl receiver.1)
    (.inr (result.2.2.getD
      (profiledRawJointUnitPolicyFallbackLeft A strategy initial policy bank
        receiver.1)))
  cases htarget : result.2.2 with
  | none =>
      simpa [htarget] using
        profiledRawJointUnitPolicyFallbackLeft_alternatingStep A strategy
          initial policy bank receiver.1
  | some target =>
      have hallowed :=
        profiledRawJointUnitRightPolicyReceiverFor_allowed_of_staged A strategy
          initial policy bank receiver.1 ownerFor receiver.2.1 receiver.2.2.1
            move target htarget
      simpa [htarget] using
        (ProfiledRawJointUnitFixedPolicyRoot.AlternatingStep.rightToLeft
          receiver.1 target hallowed)

/-- Mirror fallback edge for a left receiver. -/
theorem profiledRawJointUnitPolicyFallbackRight_alternatingStep
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy
      (initial.code A) policy) :
    ProfiledRawJointUnitFixedPolicyRoot.AlternatingStep A policy (.inr source)
      (.inl (profiledRawJointUnitPolicyFallbackRight A strategy initial policy
        bank source)) := by
  let target := profiledRawJointUnitPolicyFallbackRight A strategy initial
    policy bank source
  have hstage :
      (stepProfiledRawJointUnitLeftPolicyReceiverFor A strategy initial policy
        bank source
          (profiledRawJointUnitLeftPolicyFiniteStateAfter A strategy initial
            policy bank source []).1 .first
          (profiledRawJointUnitLeftPolicyFiniteStateAfter A strategy initial
            policy bank source []).2 default).2.2 = some target := by
    exact (Classical.choose_spec
      (profiledRawJointUnitLeftPolicy_real_close_stages_exact A strategy
        initial policy bank source .first [] default)).1
  exact .leftToRight source target
    (profiledRawJointUnitLeftPolicyReceiverFor_allowed_of_staged A strategy
      initial policy bank source
        (profiledRawJointUnitLeftPolicyFiniteStateAfter A strategy initial
          policy bank source []).1 .first
        (profiledRawJointUnitLeftPolicyFiniteStateAfter A strategy initial
          policy bank source []).2 default target hstage)

/-- Any actual continuation of a left receiver exposes its alternating edge. -/
theorem profiledRawJointUnitPolicyLeftReceiverTarget_after_continue_step
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (receiver : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy
      initial policy)
    (owner : ProfiledRawJointUnitLeftPolicyOwnerControl A strategy initial
      policy bank) (move : In₁ × In₂) :
    ProfiledRawJointUnitFixedPolicyRoot.AlternatingStep A policy
      (.inr receiver.1)
      (.inl (profiledRawJointUnitPolicyLeftReceiverTarget A strategy initial
        policy bank
          (continueProfiledRawJointUnitLeftPolicyReceiver A strategy initial
            policy bank receiver owner move).2)) := by
  let ownerFor := profiledRawJointUnitLeftPolicyOwnerControlFor A strategy
    initial policy bank receiver owner
  let result := stepProfiledRawJointUnitLeftPolicyReceiverFor A strategy
    initial policy bank receiver.1 ownerFor receiver.2.1 receiver.2.2.1 move
  change ProfiledRawJointUnitFixedPolicyRoot.AlternatingStep A policy
    (.inr receiver.1)
    (.inl (result.2.2.getD
      (profiledRawJointUnitPolicyFallbackRight A strategy initial policy bank
        receiver.1)))
  cases htarget : result.2.2 with
  | none =>
      simpa [htarget] using
        profiledRawJointUnitPolicyFallbackRight_alternatingStep A strategy
          initial policy bank receiver.1
  | some target =>
      have hallowed :=
        profiledRawJointUnitLeftPolicyReceiverFor_allowed_of_staged A strategy
          initial policy bank receiver.1 ownerFor receiver.2.1 receiver.2.2.1
            move target htarget
      simpa [htarget] using
        (ProfiledRawJointUnitFixedPolicyRoot.AlternatingStep.leftToRight
          receiver.1 target hallowed)

/-- Continuing a left block appends its checked receiver edge to an existing
finite policy prefix. -/
theorem profiledRawJointUnitPolicyLeftReceiverTarget_after_continue_reachable
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (receiver : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy
      initial policy)
    (owner : ProfiledRawJointUnitLeftPolicyOwnerControl A strategy initial
      policy bank) (move : In₁ × In₂)
    (reachable :
      ProfiledRawJointUnitFixedPolicyRoot.AlternatingPrefix.Reachable
        (policy := policy) A seed (.inr receiver.1)) :
    ProfiledRawJointUnitFixedPolicyRoot.AlternatingPrefix.Reachable
      (policy := policy) A seed
        (.inl (profiledRawJointUnitPolicyLeftReceiverTarget A strategy initial
          policy bank
            (continueProfiledRawJointUnitLeftPolicyReceiver A strategy initial
              policy bank receiver owner move).2)) :=
  reachable.snoc A
    (profiledRawJointUnitPolicyLeftReceiverTarget_after_continue_step A
      strategy initial policy bank receiver owner move)

/-- Continuing a right block appends its checked receiver edge to an existing
finite policy prefix. -/
theorem profiledRawJointUnitPolicyRightReceiverTarget_after_continue_reachable
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (receiver : ProfiledRawJointUnitRightPolicyReceiverControl A strategy
      initial policy)
    (owner : ProfiledRawJointUnitRightPolicyOwnerControl A strategy initial
      policy bank) (move : In₂ × In₁)
    (reachable :
      ProfiledRawJointUnitFixedPolicyRoot.AlternatingPrefix.Reachable
        (policy := policy) A seed (.inl receiver.1)) :
    ProfiledRawJointUnitFixedPolicyRoot.AlternatingPrefix.Reachable
      (policy := policy) A seed
        (.inr (profiledRawJointUnitPolicyRightReceiverTarget A strategy initial
          policy bank
            (continueProfiledRawJointUnitRightPolicyReceiver A strategy initial
              policy bank receiver owner move).2)) :=
  reachable.snoc A
    (profiledRawJointUnitPolicyRightReceiverTarget_after_continue_step A
      strategy initial policy bank receiver owner move)

/-- Starting a left block and consuming its first round exposes the next edge. -/
theorem profiledRawJointUnitPolicyLeftReceiverTarget_after_start_step
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (receiver : ProfiledRawJointUnitRightPolicyReceiverControl A strategy
      initial policy) (move : In₁ × In₂) :
    ProfiledRawJointUnitFixedPolicyRoot.AlternatingStep A policy
      (.inr (profiledRawJointUnitPolicyStartLeftReceiver A strategy initial
        policy bank receiver move).2.1)
      (.inl (profiledRawJointUnitPolicyLeftReceiverTarget A strategy initial
        policy bank
          (profiledRawJointUnitPolicyStartLeftReceiver A strategy initial
            policy bank receiver move).2)) := by
  simpa [profiledRawJointUnitPolicyStartLeftReceiver,
    profiledRawJointUnitRestartLeft] using
      profiledRawJointUnitPolicyLeftReceiverTarget_after_continue_step A
        strategy initial policy bank
        (initialProfiledRawJointUnitLeftPolicyReceiver A strategy initial
          policy
          (profiledRawJointUnitPolicyRightReceiverTarget A strategy initial
            policy bank receiver) receiver.2.1)
        (initialProfiledRawJointUnitLeftPolicyOwner A strategy initial policy
          bank
          (profiledRawJointUnitPolicyRightReceiverTarget A strategy initial
            policy bank receiver)) move

/-- Right-start mirror of the preceding edge theorem. -/
theorem profiledRawJointUnitPolicyRightReceiverTarget_after_start_step
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (receiver : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy
      initial policy) (move : In₂ × In₁) :
    ProfiledRawJointUnitFixedPolicyRoot.AlternatingStep A policy
      (.inl (profiledRawJointUnitPolicyStartRightReceiver A strategy initial
        policy bank receiver move).2.1)
      (.inr (profiledRawJointUnitPolicyRightReceiverTarget A strategy initial
        policy bank
          (profiledRawJointUnitPolicyStartRightReceiver A strategy initial
            policy bank receiver move).2)) := by
  simpa [profiledRawJointUnitPolicyStartRightReceiver,
    profiledRawJointUnitRestartRight] using
      profiledRawJointUnitPolicyRightReceiverTarget_after_continue_step A
        strategy initial policy bank
        (initialProfiledRawJointUnitRightPolicyReceiver A strategy initial
          policy
          (profiledRawJointUnitPolicyLeftReceiverTarget A strategy initial
            policy bank receiver) receiver.2.1)
        (initialProfiledRawJointUnitRightPolicyOwner A strategy initial policy
          bank
          (profiledRawJointUnitPolicyLeftReceiverTarget A strategy initial
            policy bank receiver)) move

/-- Starting a left block extends reachability from the right receiver's
current staged target to the new left receiver's staged target. -/
theorem profiledRawJointUnitPolicyLeftReceiverTarget_after_start_reachable
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (receiver : ProfiledRawJointUnitRightPolicyReceiverControl A strategy
      initial policy) (move : In₁ × In₂)
    (reachable :
      ProfiledRawJointUnitFixedPolicyRoot.AlternatingPrefix.Reachable
        (policy := policy) A seed
          (.inr (profiledRawJointUnitPolicyRightReceiverTarget A strategy
            initial policy bank receiver))) :
    ProfiledRawJointUnitFixedPolicyRoot.AlternatingPrefix.Reachable
      (policy := policy) A seed
        (.inl (profiledRawJointUnitPolicyLeftReceiverTarget A strategy initial
          policy bank
            (profiledRawJointUnitPolicyStartLeftReceiver A strategy initial
              policy bank receiver move).2)) := by
  apply reachable.snoc
  simpa [profiledRawJointUnitPolicyStartLeftReceiver,
    profiledRawJointUnitRestartLeft] using
      profiledRawJointUnitPolicyLeftReceiverTarget_after_start_step A strategy
        initial policy bank receiver move

/-- Starting a right block extends reachability from the left receiver's
current staged target to the new right receiver's staged target. -/
theorem profiledRawJointUnitPolicyRightReceiverTarget_after_start_reachable
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (receiver : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy
      initial policy) (move : In₂ × In₁)
    (reachable :
      ProfiledRawJointUnitFixedPolicyRoot.AlternatingPrefix.Reachable
        (policy := policy) A seed
          (.inl (profiledRawJointUnitPolicyLeftReceiverTarget A strategy
            initial policy bank receiver))) :
    ProfiledRawJointUnitFixedPolicyRoot.AlternatingPrefix.Reachable
      (policy := policy) A seed
        (.inr (profiledRawJointUnitPolicyRightReceiverTarget A strategy initial
          policy bank
            (profiledRawJointUnitPolicyStartRightReceiver A strategy initial
              policy bank receiver move).2)) := by
  apply reachable.snoc
  simpa [profiledRawJointUnitPolicyStartRightReceiver,
    profiledRawJointUnitRestartRight] using
      profiledRawJointUnitPolicyRightReceiverTarget_after_start_step A strategy
        initial policy bank receiver move

end

private abbrev OnePending (package : Package A strategy hwin
    (initial := initial)) :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (ProfiledRawJointGuardedCommonLiteralCombinedFreshOneShared A strategy hwin
      package)
    (ProfiledRawJointGuardedCommonLiteralCombinedFreshOnePayload A strategy
      hwin package)

private abbrev TwoPending (package : Package A strategy hwin
    (initial := initial)) :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoShared A strategy hwin
      package)
    (ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoPayload A strategy
      hwin package)

private abbrev OneRecurrent (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamOneControl A strategy hwin
    package

private abbrev TwoRecurrent (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamTwoControl A strategy hwin
    package

private abbrev OneControl (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralCombinedFreshOneControl A strategy hwin
    package (OneRecurrent A strategy hwin package)

private abbrev TwoControl (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoControl A strategy hwin
    package (TwoRecurrent A strategy hwin package)

/-! ## Output-independent same-child witnesses -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The recurrent relation is structural in the two Moore outputs. -/
theorem profiledRawJointIndexedPolicyRecurrentAt_reoutput
    {ChildCode : Type c}
    {source : ChildCode → ProfiledRawJointOneSidedSemanticState A strategy
      (I := Unit)}
    {policy : (key : ChildCode) →
      ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
        (source key).code}
    {bank : (key : ChildCode) → ProfiledRawJointUnitPolicyControllerBank A
      strategy (source key) (policy key)}
    {InitialOne InitialTwo ExceptionalOne ExceptionalTwo : Type}
    {key : ChildCode}
    {indexedControls :
      (ProfiledRawJointIndexedPolicyOneControl A strategy ChildCode source
          policy bank InitialOne ExceptionalOne × Out₁) ×
        (ProfiledRawJointIndexedPolicyTwoControl A strategy ChildCode source
          policy bank InitialTwo ExceptionalTwo × Out₂)}
    {unitControls :
      (ProfiledRawJointUnitPolicyOneControl A strategy (source key) (policy key)
          (bank key) InitialOne ExceptionalOne × Out₁) ×
        (ProfiledRawJointUnitPolicyTwoControl A strategy (source key) (policy key)
          (bank key) InitialTwo ExceptionalTwo × Out₂)}
    (recurrent : ProfiledRawJointIndexedPolicyRecurrentAt A strategy ChildCode
      source policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo
        key indexedControls unitControls)
    (outputOne : Out₁) (outputTwo : Out₂) :
    ProfiledRawJointIndexedPolicyRecurrentAt A strategy ChildCode source policy
      bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo key
      ((indexedControls.1.1, outputOne), (indexedControls.2.1, outputTwo))
      ((unitControls.1.1, outputOne), (unitControls.2.1, outputTwo)) := by
  cases recurrent <;> constructor

/-- A same-child witness is structural: its two stored Moore outputs may be
replaced together by arbitrary new values. -/
noncomputable def LiteralRightSeamTaggedSameChildAt.reoutput
    (package : Package A strategy hwin (initial := initial))
    {tagged : (TaggedKernel A strategy hwin package).globalMachine.State}
    (same : package.LiteralRightSeamTaggedSameChildAt A strategy hwin tagged)
    (outputOne : Out₁) (outputTwo : Out₂) :
    package.LiteralRightSeamTaggedSameChildAt A strategy hwin
      ((tagged.1.1, outputOne), (tagged.2.1, outputTwo)) := by
  exact ⟨same.key,
    ((same.unitState.1.1, outputOne), (same.unitState.2.1, outputTwo)),
    profiledRawJointIndexedPolicyRecurrentAt_reoutput A strategy
      same.recurrent outputOne outputTwo⟩

/-! ## Finite accepted-policy lineage of every live receiver -/

/-- All macro sources and staged targets visible in a recurrent Unit state
remain finitely reachable from one fixed policy root.  Matched states also
record the common source used by their owner and receiver controls. -/
def LiteralRightSeamTaggedSameChildAt.PolicyReachableFrom
    (package : Package A strategy hwin (initial := initial))
    {tagged : (TaggedKernel A strategy hwin package).globalMachine.State}
    (same : package.LiteralRightSeamTaggedSameChildAt A strategy hwin tagged)
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy
      ((package.literalRightSeamTaggedChildSource A strategy hwin
        same.key).code A)
      (package.literalRightSeamTaggedChildPolicy A strategy hwin same.key)) :
    Prop :=
  let source := package.literalRightSeamTaggedChildSource A strategy hwin
    same.key
  let policy := package.literalRightSeamTaggedChildPolicy A strategy hwin
    same.key
  let bank := package.literalRightSeamTaggedChildControllerBank A strategy hwin
    same.key
  match same.unitState.1.1, same.unitState.2.1 with
  | .rightOwner _ owner, .rightReceiver _ right =>
      owner.1 = right.1 ∧
      ProfiledRawJointUnitFixedPolicyRoot.AlternatingPrefix.Reachable
        (policy := policy) A seed (.inl right.1) ∧
      ProfiledRawJointUnitFixedPolicyRoot.AlternatingPrefix.Reachable
        (policy := policy) A seed
          (.inr (profiledRawJointUnitPolicyRightReceiverTarget A strategy
            source policy bank right))
  | .leftReceiver _ left, .leftOwner _ owner =>
      left.1 = owner.1 ∧
      ProfiledRawJointUnitFixedPolicyRoot.AlternatingPrefix.Reachable
        (policy := policy) A seed (.inr left.1) ∧
      ProfiledRawJointUnitFixedPolicyRoot.AlternatingPrefix.Reachable
        (policy := policy) A seed
          (.inl (profiledRawJointUnitPolicyLeftReceiverTarget A strategy
            source policy bank left))
  | .leftReceiver _ left, .rightReceiver _ right =>
      ProfiledRawJointUnitFixedPolicyRoot.AlternatingPrefix.Reachable
        (policy := policy) A seed (.inr left.1) ∧
      ProfiledRawJointUnitFixedPolicyRoot.AlternatingPrefix.Reachable
        (policy := policy) A seed
          (.inl (profiledRawJointUnitPolicyLeftReceiverTarget A strategy
            source policy bank left)) ∧
      ProfiledRawJointUnitFixedPolicyRoot.AlternatingPrefix.Reachable
        (policy := policy) A seed (.inl right.1) ∧
      ProfiledRawJointUnitFixedPolicyRoot.AlternatingPrefix.Reachable
        (policy := policy) A seed
          (.inr (profiledRawJointUnitPolicyRightReceiverTarget A strategy
            source policy bank right))
  | _, _ => False

/-- The accepted activation root and all finite descendants currently exposed
by the selected fixed-child carrier. -/
structure LiteralRightSeamTaggedSameChildAt.AcceptedPolicyLineage
    (package : Package A strategy hwin (initial := initial))
    {tagged : (TaggedKernel A strategy hwin package).globalMachine.State}
    (same : package.LiteralRightSeamTaggedSameChildAt A strategy hwin tagged) :
    Type (max u v x y s) where
  seed : ProfiledRawJointUnitFixedPolicyRoot A strategy
    ((package.literalRightSeamTaggedChildSource A strategy hwin same.key).code
      A)
    (package.literalRightSeamTaggedChildPolicy A strategy hwin same.key)
  seed_state : ProfiledRawJointUnitFixedPolicyRoot.state A
      (package.literalRightSeamTaggedChildPolicy A strategy hwin same.key)
      seed =
    (package.literalRightSeamTaggedChildPolicy A strategy hwin same.key).run []
  reachable : same.PolicyReachableFrom A strategy hwin package seed

/-- Replacing Moore outputs leaves the policy-lineage proposition unchanged. -/
theorem LiteralRightSeamTaggedSameChildAt.PolicyReachableFrom.reoutput
    (package : Package A strategy hwin (initial := initial))
    {tagged : (TaggedKernel A strategy hwin package).globalMachine.State}
    (same : package.LiteralRightSeamTaggedSameChildAt A strategy hwin tagged)
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy
      ((package.literalRightSeamTaggedChildSource A strategy hwin
        same.key).code A)
      (package.literalRightSeamTaggedChildPolicy A strategy hwin same.key))
    (reachable : same.PolicyReachableFrom A strategy hwin package seed)
    (outputOne : Out₁) (outputTwo : Out₂) :
    (same.reoutput A strategy hwin package outputOne outputTwo
      ).PolicyReachableFrom A strategy hwin package seed := by
  revert seed
  generalize hindexed : tagged = indexedState at same ⊢
  rintro seed reachable
  rcases same with ⟨key, unitState, recurrent⟩
  subst indexedState
  cases recurrent <;> exact reachable

set_option maxHeartbeats 800000 in
/-- One recurrent physical transition preserves the finite policy ancestry of
both live orientations and refreshes each visible receiver target by one
checked alternating edge. -/
theorem LiteralRightSeamTaggedSameChildAt.PolicyReachableFrom.advance
    (package : Package A strategy hwin (initial := initial))
    {tagged : (TaggedKernel A strategy hwin package).globalMachine.State}
    (same : package.LiteralRightSeamTaggedSameChildAt A strategy hwin tagged)
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy
      ((package.literalRightSeamTaggedChildSource A strategy hwin
        same.key).code A)
      (package.literalRightSeamTaggedChildPolicy A strategy hwin same.key))
    (reachable : same.PolicyReachableFrom A strategy hwin package seed)
    (round : EnvironmentRound In₁ In₂) :
    (same.advance A strategy hwin package round).PolicyReachableFrom A strategy
      hwin package seed := by
  unfold LiteralRightSeamTaggedSameChildAt.PolicyReachableFrom at reachable ⊢
  revert seed
  generalize hindexed : tagged = indexedState at same ⊢
  rintro seed reachable
  rcases same with ⟨key, unitState, recurrent⟩
  subst indexedState
  rcases round with ⟨inputOne, inputTwo, graph⟩
  cases recurrent <;> cases graph <;>
    simp [LiteralRightSeamTaggedSameChildAt.advance,
      FinitePairedPhysicalController.advanceControls,
      ProfiledRawJointLeaderFreeKernel.physicalController,
      profiledRawJointIndexedPolicyLeaderFreeKernel,
      profiledRawJointUnitPolicyLeaderFreeKernel,
      profiledRawJointUnitPolicyStartLeftReceiver,
      profiledRawJointUnitPolicyStartRightReceiver,
      profiledRawJointUnitRestartLeft,
      profiledRawJointUnitRestartRight] at reachable ⊢ <;>
    aesop (config := { warnOnNonterminal := false }) (add safe forward
      [ProfiledRawJointUnitFixedPolicyRoot.AlternatingPrefix.Reachable.snoc,
       profiledRawJointUnitPolicyFallbackLeft_alternatingStep,
       profiledRawJointUnitPolicyRightReceiverTarget_after_continue_step,
       profiledRawJointUnitPolicyFallbackRight_alternatingStep,
       profiledRawJointUnitPolicyLeftReceiverTarget_after_continue_step,
       profiledRawJointUnitPolicyLeftReceiverTarget_after_continue_reachable,
       profiledRawJointUnitPolicyRightReceiverTarget_after_continue_reachable,
       profiledRawJointUnitPolicyLeftReceiverTarget_after_start_step,
       profiledRawJointUnitPolicyRightReceiverTarget_after_start_step,
       profiledRawJointUnitPolicyLeftReceiverTarget_after_start_reachable,
       profiledRawJointUnitPolicyRightReceiverTarget_after_start_reachable]) <;>
    first
    | apply
        profiledRawJointUnitPolicyLeftReceiverTarget_after_continue_reachable
          A strategy
      assumption
    | apply
        profiledRawJointUnitPolicyRightReceiverTarget_after_continue_reachable
          A strategy
      assumption

/-- Replacing Moore outputs preserves the accepted policy seed together with
the finite ancestry of every live macro and staged target. -/
noncomputable def
    LiteralRightSeamTaggedSameChildAt.AcceptedPolicyLineage.reoutput
    (package : Package A strategy hwin (initial := initial))
    {tagged : (TaggedKernel A strategy hwin package).globalMachine.State}
    {same : package.LiteralRightSeamTaggedSameChildAt A strategy hwin tagged}
    (lineage : same.AcceptedPolicyLineage A strategy hwin package)
    (outputOne : Out₁) (outputTwo : Out₂) :
    (same.reoutput A strategy hwin package outputOne outputTwo
      ).AcceptedPolicyLineage A strategy hwin package where
  seed := lineage.seed
  seed_state := lineage.seed_state
  reachable :=
    LiteralRightSeamTaggedSameChildAt.PolicyReachableFrom.reoutput A strategy
      hwin package same lineage.seed lineage.reachable outputOne outputTwo

/-- One recurrent physical round preserves the accepted seed and extends the
finite ancestry precisely at the newly staged receiver targets. -/
noncomputable def
    LiteralRightSeamTaggedSameChildAt.AcceptedPolicyLineage.advance
    (package : Package A strategy hwin (initial := initial))
    {tagged : (TaggedKernel A strategy hwin package).globalMachine.State}
    {same : package.LiteralRightSeamTaggedSameChildAt A strategy hwin tagged}
    (lineage : same.AcceptedPolicyLineage A strategy hwin package)
    (round : EnvironmentRound In₁ In₂) :
    (same.advance A strategy hwin package round).AcceptedPolicyLineage A
      strategy hwin package where
  seed := lineage.seed
  seed_state := lineage.seed_state
  reachable :=
    LiteralRightSeamTaggedSameChildAt.PolicyReachableFrom.advance A strategy
      hwin package same lineage.seed lineage.reachable round

/-! ## The canonical activation row remains `.first` -/

/-- Same-child recurrent row invariant.  In a matched state only the live
receiver row matters; in a cross state both receiver rows do.  Exceptional
shapes are impossible under `same.recurrent` and are assigned `False`. -/
def LiteralRightSeamTaggedSameChildAt.RowsFirst
    (package : Package A strategy hwin (initial := initial))
    {tagged : (TaggedKernel A strategy hwin package).globalMachine.State}
    (same : package.LiteralRightSeamTaggedSameChildAt A strategy hwin tagged) :
    Prop :=
  match same.unitState.1.1, same.unitState.2.1 with
  | .rightOwner _ _, .rightReceiver _ receiver => receiver.2.1 = .first
  | .leftReceiver _ receiver, .leftOwner _ _ => receiver.2.1 = .first
  | .leftReceiver _ left, .rightReceiver _ right =>
      left.2.1 = .first ∧ right.2.1 = .first
  | _, _ => False

/-- Replacing the two Moore outputs does not affect receiver rows. -/
theorem LiteralRightSeamTaggedSameChildAt.RowsFirst.reoutput
    (package : Package A strategy hwin (initial := initial))
    {tagged : (TaggedKernel A strategy hwin package).globalMachine.State}
    (same : package.LiteralRightSeamTaggedSameChildAt A strategy hwin tagged)
    (rows : same.RowsFirst A strategy hwin package)
    (outputOne : Out₁) (outputTwo : Out₂) :
    (same.reoutput A strategy hwin package outputOne outputTwo).RowsFirst A
      strategy hwin package := by
  generalize hindexed : tagged = indexedState at same rows ⊢
  rcases same with ⟨key, unitState, recurrent⟩
  subst indexedState
  cases recurrent <;> exact rows

/-- Every recurrent fixed-child transition preserves the canonical first
receiver row.  This includes `.both`: both retained receivers keep their
already selected row. -/
theorem LiteralRightSeamTaggedSameChildAt.RowsFirst.advance
    (package : Package A strategy hwin (initial := initial))
    {tagged : (TaggedKernel A strategy hwin package).globalMachine.State}
    (same : package.LiteralRightSeamTaggedSameChildAt A strategy hwin tagged)
    (rows : same.RowsFirst A strategy hwin package)
    (round : EnvironmentRound In₁ In₂) :
    (same.advance A strategy hwin package round).RowsFirst A strategy hwin
      package := by
  unfold LiteralRightSeamTaggedSameChildAt.RowsFirst at rows ⊢
  generalize hindexed : tagged = indexedState at same rows ⊢
  rcases same with ⟨key, unitState, recurrent⟩
  subst indexedState
  rcases round with ⟨inputOne, inputTwo, graph⟩
  cases recurrent <;> cases graph <;>
    simp [LiteralRightSeamTaggedSameChildAt.RowsFirst,
      LiteralRightSeamTaggedSameChildAt.advance,
      FinitePairedPhysicalController.advanceControls,
      ProfiledRawJointLeaderFreeKernel.physicalController,
      profiledRawJointIndexedPolicyLeaderFreeKernel,
      profiledRawJointUnitPolicyLeaderFreeKernel,
      profiledRawJointUnitPolicyStartLeftReceiver,
      profiledRawJointUnitPolicyStartRightReceiver,
      profiledRawJointUnitRestartLeft,
      profiledRawJointUnitRestartRight,
      initialProfiledRawJointUnitLeftPolicyReceiver,
      initialProfiledRawJointUnitRightPolicyReceiver,
      continueProfiledRawJointUnitLeftPolicyReceiver,
      continueProfiledRawJointUnitRightPolicyReceiver] at rows ⊢ <;>
    aesop

set_option maxHeartbeats 800000 in
/-- One strict-right transition from any recurrent fixed-child shape ends in
a matched-right state.  The preserved row invariant identifies its receiver
row as `.first`. -/
theorem LiteralRightSeamTaggedSameChildAt.advance_right_matchedRight
    (package : Package A strategy hwin (initial := initial))
    {tagged : (TaggedKernel A strategy hwin package).globalMachine.State}
    (same : package.LiteralRightSeamTaggedSameChildAt A strategy hwin tagged)
    (rows : same.RowsFirst A strategy hwin package)
    (input : In₁ × In₂) :
    let next := same.advance A strategy hwin package
      ⟨input.1, input.2, .right⟩
    let source := package.literalRightSeamTaggedChildSource A strategy hwin
      next.key
    let policy := package.literalRightSeamTaggedChildPolicy A strategy hwin
      next.key
    let bank := package.literalRightSeamTaggedChildControllerBank A strategy
      hwin next.key
    let adapter := UnitAdapter A strategy hwin package next.key
    ∃ owner : ProfiledRawJointUnitRightPolicyOwnerControl A strategy source
        policy bank,
      ∃ right : ProfiledRawJointUnitRightPolicyReceiverControl A strategy
          source policy,
        ∃ outputOne : Out₁, ∃ outputTwo : Out₂,
          next.unitState =
              profiledRawJointUnitMatchedRightState A strategy source policy
                bank adapter owner right outputOne outputTwo ∧
            right.2.1 = .first := by
  dsimp only
  generalize htagged : tagged = indexedState at same rows ⊢
  rcases same with ⟨key, unitState, recurrent⟩
  subst indexedState
  cases recurrent <;>
    simp [LiteralRightSeamTaggedSameChildAt.advance,
      LiteralRightSeamTaggedSameChildAt.RowsFirst,
      FinitePairedPhysicalController.advanceControls,
      ProfiledRawJointLeaderFreeKernel.physicalController,
      profiledRawJointIndexedPolicyLeaderFreeKernel,
      profiledRawJointUnitPolicyLeaderFreeKernel,
      profiledRawJointUnitPolicyStartRightReceiver,
      profiledRawJointUnitRestartRight,
      initialProfiledRawJointUnitRightPolicyReceiver,
      continueProfiledRawJointUnitRightPolicyReceiver,
      profiledRawJointUnitMatchedRightState] at rows ⊢ <;>
    aesop

/-- The strict-right shape theorem in a form that keeps the original round
term, avoiding transports in later state-indexed recurrence proofs. -/
theorem LiteralRightSeamTaggedSameChildAt.advance_matchedRight_of_graph_right
    (package : Package A strategy hwin (initial := initial))
    {tagged : (TaggedKernel A strategy hwin package).globalMachine.State}
    (same : package.LiteralRightSeamTaggedSameChildAt A strategy hwin tagged)
    (rows : same.RowsFirst A strategy hwin package)
    (round : EnvironmentRound In₁ In₂) (hgraph : round.graph = .right) :
    let next := same.advance A strategy hwin package round
    let source := package.literalRightSeamTaggedChildSource A strategy hwin
      next.key
    let policy := package.literalRightSeamTaggedChildPolicy A strategy hwin
      next.key
    let bank := package.literalRightSeamTaggedChildControllerBank A strategy
      hwin next.key
    let adapter := UnitAdapter A strategy hwin package next.key
    ∃ owner : ProfiledRawJointUnitRightPolicyOwnerControl A strategy source
        policy bank,
      ∃ right : ProfiledRawJointUnitRightPolicyReceiverControl A strategy
          source policy,
        ∃ outputOne : Out₁, ∃ outputTwo : Out₂,
          next.unitState =
              profiledRawJointUnitMatchedRightState A strategy source policy
                bank adapter owner right outputOne outputTwo ∧
            right.2.1 = .first := by
  rcases round with ⟨inputOne, inputTwo, graph⟩
  dsimp only at hgraph ⊢
  subst graph
  exact same.advance_right_matchedRight A strategy hwin package rows
    (inputOne, inputTwo)

/-! ## Arbitrary finite suffixes -/

/-- The selected fixed child can be followed through an arbitrary finite
physical suffix.  Its index is the literal rerooted tagged-kernel state. -/
noncomputable def LiteralRightSeamTaggedSameChildAt.trace
    (package : Package A strategy hwin (initial := initial))
    {tagged : (TaggedKernel A strategy hwin package).globalMachine.State}
    (same : package.LiteralRightSeamTaggedSameChildAt A strategy hwin tagged)
    (env : EnvironmentSequence In₁ In₂) : ∀ n : Nat,
    package.LiteralRightSeamTaggedSameChildAt A strategy hwin
      (((TaggedKernel A strategy hwin package).globalMachine.reroot tagged
        ).globalStateTrace env n) := by
  intro n
  induction n with
  | zero =>
      simpa [FiniteGlobalRoundMachine.reroot] using same
  | succ n ih =>
      rw [FiniteGlobalRoundMachine.globalStateTrace_succ]
      simpa [ProfiledRawJointLeaderFreeKernel.globalMachine,
        FiniteGlobalRoundMachine.reroot] using
          ih.advance A strategy hwin package (env n)

/-- The canonical receiver row follows the same arbitrary finite suffix. -/
theorem LiteralRightSeamTaggedSameChildAt.RowsFirst.trace
    (package : Package A strategy hwin (initial := initial))
    {tagged : (TaggedKernel A strategy hwin package).globalMachine.State}
    (same : package.LiteralRightSeamTaggedSameChildAt A strategy hwin tagged)
    (rows : same.RowsFirst A strategy hwin package)
    (env : EnvironmentSequence In₁ In₂) : ∀ n : Nat,
    (same.trace A strategy hwin package env n).RowsFirst A strategy hwin
      package := by
  intro n
  induction n with
  | zero =>
      simpa [LiteralRightSeamTaggedSameChildAt.trace] using rows
  | succ n ih =>
      simpa [LiteralRightSeamTaggedSameChildAt.trace] using
        (LiteralRightSeamTaggedSameChildAt.RowsFirst.advance A strategy hwin
          package (same.trace A strategy hwin package env n) ih (env n))

/-- The accepted seed and finite ancestry follow the same arbitrary physical
suffix.  This is the policy-lineage counterpart of the structural same-child
trace above. -/
noncomputable def
    LiteralRightSeamTaggedSameChildAt.AcceptedPolicyLineage.trace
    (package : Package A strategy hwin (initial := initial))
    {tagged : (TaggedKernel A strategy hwin package).globalMachine.State}
    {same : package.LiteralRightSeamTaggedSameChildAt A strategy hwin tagged}
    (lineage : same.AcceptedPolicyLineage A strategy hwin package)
    (env : EnvironmentSequence In₁ In₂) : ∀ n : Nat,
    (same.trace A strategy hwin package env n).AcceptedPolicyLineage A
      strategy hwin package := by
  intro n
  induction n with
  | zero =>
      simpa [LiteralRightSeamTaggedSameChildAt.trace] using lineage
  | succ n ih =>
      simpa [LiteralRightSeamTaggedSameChildAt.trace] using
        ih.advance A strategy hwin package (env n)

/-- The pair reconstructed from a retained stage is already one fixed-child
comparison state before the activating round. -/
noncomputable def literalRightSeamStageMatched_sameChild
    (package : Package A strategy hwin (initial := initial))
    (stage : ProfiledRawJointGuardedCommonLiteralRightSeamStage A strategy hwin
      package)
    (outputOne : Out₁) (outputTwo : Out₂) :
    let matched := package.literalRightSeamStageMatched A strategy hwin stage
    package.LiteralRightSeamTaggedSameChildAt A strategy hwin
      ((matched.1, outputOne), (matched.2, outputTwo)) := by
  dsimp only
  let unitState :
      (UnitKernel A strategy hwin package stage.child).globalMachine.State :=
    (((.rightOwner ()
        (package.literalRightSeamStageInitialRightOwner A strategy hwin
          stage)), outputOne),
      ((.rightReceiver ()
        (package.literalRightSeamStageInitialRightReceiver A strategy hwin
          stage)), outputTwo))
  exact ⟨stage.child, unitState,
    package.literalRightSeamStageMatched_recurrentAt A strategy hwin stage
      outputOne outputTwo⟩

/-- A stage returned by the finite child inspector is rooted at the initial
state of that child's selected accepting policy.  This is the provenance fact
that an arbitrary inhabitant of the stage type would not provide. -/
theorem literalRightSeamStageOfChild_root_state
    (package : Package A strategy hwin (initial := initial))
    (row : PairedEntryRow)
    (child : TaggedChild A strategy hwin package)
    (stage : ProfiledRawJointGuardedCommonLiteralRightSeamStage A strategy hwin
      package)
    (hstage : package.literalRightSeamStageOfChild A strategy hwin row child =
      some stage) :
    ProfiledRawJointUnitFixedPolicyRoot.state A
        (package.literalRightSeamTaggedChildPolicy A strategy hwin stage.child)
        (.inl stage.root) =
      (package.literalRightSeamTaggedChildPolicy A strategy hwin
        stage.child).run [] := by
  classical
  simp only [literalRightSeamStageOfChild] at hstage
  split at hstage
  · have hstageEq := Option.some.inj hstage
    subst stage
    rfl
  · contradiction

/-- A stage whose root is certified as the selected policy's initial state
starts the fixed-child comparison with an accepted seed and with both
initially visible roots in its finite alternating lineage. -/
noncomputable def
    literalRightSeamStageMatched_acceptedPolicyLineage_of_root_state
    (package : Package A strategy hwin (initial := initial))
    (stage : ProfiledRawJointGuardedCommonLiteralRightSeamStage A strategy hwin
      package)
    (hroot :
      ProfiledRawJointUnitFixedPolicyRoot.state A
          (package.literalRightSeamTaggedChildPolicy A strategy hwin
            stage.child)
          (.inl stage.root) =
        (package.literalRightSeamTaggedChildPolicy A strategy hwin
          stage.child).run [])
    (outputOne : Out₁) (outputTwo : Out₂) :
    let same := package.literalRightSeamStageMatched_sameChild A strategy hwin
      stage outputOne outputTwo
    same.AcceptedPolicyLineage A strategy hwin package := by
  dsimp only
  let same := package.literalRightSeamStageMatched_sameChild A strategy hwin
    stage outputOne outputTwo
  let source := package.literalRightSeamTaggedChildSource A strategy hwin
    stage.child
  let policy := package.literalRightSeamTaggedChildPolicy A strategy hwin
    stage.child
  let bank := package.literalRightSeamTaggedChildControllerBank A strategy
    hwin stage.child
  let seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (source.code A)
      policy := .inl stage.root
  refine ⟨seed, hroot, ?_⟩
  unfold LiteralRightSeamTaggedSameChildAt.PolicyReachableFrom
  dsimp [same, seed, literalRightSeamStageMatched_sameChild,
    literalRightSeamStageMatched,
    literalRightSeamStageInitialRightOwner,
    literalRightSeamStageInitialRightReceiver,
    initialProfiledRawJointUnitRightPolicyOwner,
    initialProfiledRawJointUnitRightPolicyReceiver,
    profiledRawJointUnitPolicyRightReceiverTarget]
  refine ⟨rfl,
    ProfiledRawJointUnitFixedPolicyRoot.AlternatingPrefix.reachable_refl A,
    ?_⟩
  exact
    ProfiledRawJointUnitFixedPolicyRoot.AlternatingPrefix.Reachable.snoc A
      (ProfiledRawJointUnitFixedPolicyRoot.AlternatingPrefix.reachable_refl A)
      (profiledRawJointUnitPolicyFallbackLeft_alternatingStep A strategy
        source policy bank stage.root)

/-- Every honestly inspected stage satisfies the root-state premise of the
preceding constructor. -/
noncomputable def
    literalRightSeamStageOfChild_matched_acceptedPolicyLineage
    (package : Package A strategy hwin (initial := initial))
    (row : PairedEntryRow)
    (child : TaggedChild A strategy hwin package)
    (stage : ProfiledRawJointGuardedCommonLiteralRightSeamStage A strategy hwin
      package)
    (hstage : package.literalRightSeamStageOfChild A strategy hwin row child =
      some stage)
    (outputOne : Out₁) (outputTwo : Out₂) :
    let same := package.literalRightSeamStageMatched_sameChild A strategy hwin
      stage outputOne outputTwo
    same.AcceptedPolicyLineage A strategy hwin package := by
  exact
    package.literalRightSeamStageMatched_acceptedPolicyLineage_of_root_state A
      strategy hwin stage
      (package.literalRightSeamStageOfChild_root_state A strategy hwin row
        child stage hstage)
      outputOne outputTwo

/-- For an exact table-emitted stage, the fixed-child comparison starts at
the genuinely accepted root of that child's selected policy.  Its initially
empty receiver has only the certified fallback target, which is one literal
alternating edge from that root. -/
noncomputable def
    literalRightSeamExactStageAt_matched_acceptedPolicyLineage
    (package : Package A strategy hwin (initial := initial))
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (sourceRow entryRow : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) (outputOne : Out₁) (outputTwo : Out₂) :
    let stage := package.literalRightSeamExactStageAt A strategy hwin key
      sourceRow entryRow past input
    let same := package.literalRightSeamStageMatched_sameChild A strategy hwin
      stage outputOne outputTwo
    same.AcceptedPolicyLineage A strategy hwin package := by
  let stage := package.literalRightSeamExactStageAt A strategy hwin key
    sourceRow entryRow past input
  exact
    package.literalRightSeamStageOfChild_matched_acceptedPolicyLineage A
      strategy hwin entryRow
      (package.literalRightSeamTaggedTarget A strategy hwin key sourceRow past
        input)
      stage
      (package.literalRightSeamStageOfChild_exactAt A strategy hwin key
        sourceRow entryRow past input)
      outputOne outputTwo

/-- The exact strict-right activation step already carries a same-child
witness, before any relay flushing is considered. -/
noncomputable def literalRightSeamStage_after_strictRight_sameChild
    (package : Package A strategy hwin (initial := initial))
    (stage : ProfiledRawJointGuardedCommonLiteralRightSeamStage A strategy hwin
      package)
    (outputOne : Out₁) (outputTwo : Out₂) (input : In₁ × In₂) :
    let matched := package.literalRightSeamStageMatched A strategy hwin stage
    let tagged :=
      (TaggedKernel A strategy hwin package).physicalController.advanceControls
        ((matched.1, outputOne), (matched.2, outputTwo))
        ⟨input.1, input.2, .right⟩
    package.LiteralRightSeamTaggedSameChildAt A strategy hwin tagged := by
  dsimp only
  let matched := package.literalRightSeamStageMatched A strategy hwin stage
  let unitStart :
      (UnitKernel A strategy hwin package stage.child).globalMachine.State :=
    (((.rightOwner ()
        (package.literalRightSeamStageInitialRightOwner A strategy hwin stage)),
        outputOne),
      ((.rightReceiver ()
        (package.literalRightSeamStageInitialRightReceiver A strategy hwin
          stage)), outputTwo))
  let unitFinal :=
    (UnitKernel A strategy hwin package stage.child).physicalController
      |>.advanceControls unitStart ⟨input.1, input.2, .right⟩
  refine ⟨stage.child, unitFinal, ?_⟩
  exact package.literalRightSeamStage_after_strictRight_recurrentAt A strategy
    hwin stage outputOne outputTwo input

/-! ## Accepted-stage provenance in the pending controller -/

/-- Every stage refreshed by the restarted right receiver is rooted at the
initial state of its selected accepting policy. -/
theorem literalRightSeamBranchRestartedReceiverRecv_stage_root_state
    (package : Package A strategy hwin (initial := initial))
    (receiver :
      ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A
        strategy hwin package)
    (own : In₁) (delivered : In₂)
    (stage : ProfiledRawJointGuardedCommonLiteralRightSeamStage A strategy hwin
      package)
    (hstage :
      (package.literalRightSeamBranchRestartedReceiverRecv A strategy hwin
        receiver own delivered).2.2.2.2 = some stage) :
    ProfiledRawJointUnitFixedPolicyRoot.state A
        (package.literalRightSeamTaggedChildPolicy A strategy hwin stage.child)
        (.inl stage.root) =
      (package.literalRightSeamTaggedChildPolicy A strategy hwin
        stage.child).run [] := by
  let result := package.literalRightSeamBranchRestartedReceiverRecv A strategy
    hwin receiver own delivered
  apply package.literalRightSeamStageOfChild_root_state A strategy hwin .first
    (package.literalRightSeamBranchChild A strategy hwin receiver result.1.2)
      stage
  rw [← package.literalRightSeamBranchRestartedReceiverRecv_stage A strategy
    hwin receiver own delivered]
  exact hstage

/-- The right stage currently selected by process one's pending member, when
present, has honest accepted-policy provenance. -/
def LiteralCombinedFreshOneSelectedStageAccepted
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package) : Prop :=
  ∀ stage : ProfiledRawJointGuardedCommonLiteralRightSeamStage A strategy hwin
      package,
    (package.literalCombinedFreshOneReceiver A strategy hwin one.1
      one.2.1).2.2.2 = some stage →
      ProfiledRawJointUnitFixedPolicyRoot.state A
          (package.literalRightSeamTaggedChildPolicy A strategy hwin
            stage.child)
          (.inl stage.root) =
        (package.literalRightSeamTaggedChildPolicy A strategy hwin
          stage.child).run []

/-- The common pending root contains no selected stage. -/
theorem literalCombinedFreshOneSelectedStageAccepted_initial
    (package : Package A strategy hwin (initial := initial)) :
    package.LiteralCombinedFreshOneSelectedStageAccepted A strategy hwin
      (package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin) := by
  intro stage hstage
  simp [literalCombinedFreshPendingOnlyInitialOne,
    literalCombinedFreshPendingOnlyInitialOneShared,
    literalCrossCombinedFreshOneSharedAt,
    literalCombinedFreshOneReceiver, FiniteDelayedFork.candidate,
    literalRightSeamStagedReceiverInitial]
    at hstage

/-- A blind process-one transition retains the selected receiver and hence
its accepted-stage provenance. -/
theorem LiteralCombinedFreshOneSelectedStageAccepted.noRecv
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package)
    (accepted :
      package.LiteralCombinedFreshOneSelectedStageAccepted A strategy hwin one)
    (input : In₁) :
    package.LiteralCombinedFreshOneSelectedStageAccepted A strategy hwin
      (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
        (package.literalCombinedFreshOnePendingStep A strategy hwin) one
          input).1 := by
  intro stage hstage
  apply accepted stage
  exact hstage

/-- The open branch of a process-one receive stores the freshly inspected
stage and therefore has accepted-policy provenance. -/
theorem literalCombinedFreshOneSelectedStageAccepted_after_openRecvOne
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package) (own : In₁)
    (two : TwoPending A strategy hwin package) (delivered : In₂) :
    package.LiteralCombinedFreshOneSelectedStageAccepted A strategy hwin
      (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one own two
        delivered).1.openControl := by
  intro stage hstage
  change
    (package.literalCombinedFreshOneReceiver A strategy hwin false
      (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one own two
        delivered).1.openControl.2.1).2.2.2 = some stage at hstage
  rw [package.literalCombinedFreshPhaseLiveRecvOne_open_receiver A strategy
    hwin] at hstage
  exact package.literalRightSeamBranchRestartedReceiverRecv_stage_root_state A
    strategy hwin _ _ _ stage hstage

/-- The closed branch of a process-one receive is a fresh stage-free root. -/
theorem literalCombinedFreshOneSelectedStageAccepted_after_closedRecvOne
    (package : Package A strategy hwin (initial := initial))
    (one : OnePending A strategy hwin package) (own : In₁)
    (two : TwoPending A strategy hwin package) (delivered : In₂) :
    package.LiteralCombinedFreshOneSelectedStageAccepted A strategy hwin
      (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one own two
        delivered).1.closedControl := by
  intro stage hstage
  change
    (package.literalCombinedFreshOneReceiver A strategy hwin true
      (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one own two
        delivered).1.closedControl.2.1).2.2.2 = some stage at hstage
  rw [package.literalCombinedFreshPhaseLiveRecvOne_closed_receiver A strategy
    hwin] at hstage
  simp [literalRightSeamStagedReceiverInitial] at hstage

/-! ## Pending or one fixed child -/

/-- Strengthening of the pending/recurrent shape invariant.  In the recurrent
case it retains an actual fixed child comparison state. -/
inductive LiteralCombinedFreshPhaseActivatedSameChildSelected
    (package : Package A strategy hwin (initial := initial)) :
    OneControl A strategy hwin package →
      TwoControl A strategy hwin package → Type (max u v x y s)
  | pending (one : OnePending A strategy hwin package)
      (two : TwoPending A strategy hwin package)
      (structural :
        package.LiteralCombinedFreshPhaseLiveStructuralSelected A strategy
          hwin one two)
      (ready_eq :
        package.literalCombinedFreshRightActivationReadyOne A strategy hwin
            one =
          package.literalCombinedFreshRightActivationReadyTwo A strategy hwin
            two one)
      (stageAccepted :
        package.LiteralCombinedFreshOneSelectedStageAccepted A strategy hwin
          one) :
      LiteralCombinedFreshPhaseActivatedSameChildSelected package
        (.inl one) (.inl two)
  | recurrent (one : OneRecurrent A strategy hwin package)
      (two : TwoRecurrent A strategy hwin package)
      (same : package.LiteralRightSeamTaggedSameChildAt A strategy hwin
        ((one, default), (two, default)))
      (rowsFirst : same.RowsFirst A strategy hwin package)
      (lineage : same.AcceptedPolicyLineage A strategy hwin package) :
      LiteralCombinedFreshPhaseActivatedSameChildSelected package
        (.inr one) (.inr two)

/-- The common root starts in the pending branch. -/
noncomputable def literalCombinedFreshPhaseActivatedSameChildSelected_initial
    (package : Package A strategy hwin (initial := initial)) :
    package.LiteralCombinedFreshPhaseActivatedSameChildSelected A strategy hwin
      (.inl (package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin))
      (.inl (package.literalCombinedFreshPendingOnlyInitialTwo A strategy
        hwin)) :=
  .pending _ _
    (package.literalCombinedFreshPhaseLiveStructuralSelected_initial A strategy
      hwin)
    ((package.literalCombinedFreshRightActivationReady_initial A strategy
      hwin).1.trans
        (package.literalCombinedFreshRightActivationReady_initial A strategy
          hwin).2.symm)
    (package.literalCombinedFreshOneSelectedStageAccepted_initial A strategy
      hwin)

/-! ## One-round preservation -/

/-- A strict-right round either remains pending or performs the exact
stage-selected activation. -/
noncomputable def
    LiteralCombinedFreshPhaseActivatedSameChildSelected.strictRight
    (package : Package A strategy hwin (initial := initial))
    {one : OneControl A strategy hwin package}
    {two : TwoControl A strategy hwin package}
    (sameSelected :
      package.LiteralCombinedFreshPhaseActivatedSameChildSelected A strategy
        hwin one two)
    (input : In₁ × In₂) :
    package.LiteralCombinedFreshPhaseActivatedSameChildSelected A strategy hwin
      (package.literalCombinedFreshPhaseActivatedNoRecvOne A strategy hwin one
        input.1).1
      (package.literalCombinedFreshPhaseActivatedOpenRecvTwo A strategy hwin
        two input.2 one input.1).1 := by
  cases sameSelected with
  | pending one two structural readyEq stageAccepted =>
      cases hreadyOne :
        package.literalCombinedFreshRightActivationReadyOne A strategy hwin one
      · have hreadyTwo :
            package.literalCombinedFreshRightActivationReadyTwo A strategy hwin
              two one = false := by
          rw [← readyEq]
          exact hreadyOne
        let oneNext : OnePending A strategy hwin package :=
          (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
            (package.literalCombinedFreshOnePendingStep A strategy hwin)
            one input.1).1
        let twoNext : TwoPending A strategy hwin package :=
          (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two
            input.2 one input.1).1.openControl
        simpa [literalCombinedFreshPhaseActivatedNoRecvOne,
          literalCombinedFreshPhaseActivatedOpenRecvTwo, hreadyOne,
          hreadyTwo, oneNext, twoNext] using
            (LiteralCombinedFreshPhaseActivatedSameChildSelected.pending
              (package := package) oneNext twoNext
              (package.literalCombinedFreshPhaseLiveStructuralSelected_strictRight
                A strategy hwin one two structural input)
              (package.literalCombinedFreshRightActivationReady_eq_of_phase_eq
                A strategy hwin oneNext twoNext rfl)
              (stageAccepted.noRecv A strategy hwin package one input.1))
      · have hreadyTwo :
            package.literalCombinedFreshRightActivationReadyTwo A strategy hwin
              two one = true := by
          rw [← readyEq]
          exact hreadyOne
        cases hstage :
          (package.literalCombinedFreshOneReceiver A strategy hwin one.1
            one.2.1).2.2.2 with
        | none =>
            simp [literalCombinedFreshRightActivationReadyOne,
              literalCombinedFreshRightFreshStageReady, hstage] at hreadyOne
        | some stage =>
            have hreadyOneParts := hreadyOne
            simp [literalCombinedFreshRightActivationReadyOne,
              literalCombinedFreshRightFreshStageReady, hstage] at hreadyOneParts
            have hreadyTwoParts := hreadyTwo
            simp [literalCombinedFreshRightActivationReadyTwo,
              literalCombinedFreshRightFreshStageReady, hstage] at hreadyTwoParts
            have hphaseOne : one.2.1.1.2 = true := by
              exact hreadyOneParts.1
            have hrow : stage.row = .first := by
              exact hreadyOneParts.2
            have hphaseTwo : two.2.1.1.2 = true := by
              exact hreadyTwoParts.1
            have hswitch :=
              package.literalCombinedFreshPhaseActivated_switch_exact_pair A
                strategy hwin one two stage hstage hrow hphaseOne hphaseTwo
                  input
            rw [hswitch.1, hswitch.2]
            let hsame :=
              package.literalRightSeamStage_after_strictRight_sameChild A
                strategy hwin stage (default : Out₁) (default : Out₂) input
            let hnormalized := hsame.reoutput A strategy hwin package
              (default : Out₁) (default : Out₂)
            have hsameRows : hsame.RowsFirst A strategy hwin package := by
              change stage.row = .first
              exact hrow
            let hnormalizedRows :=
              LiteralRightSeamTaggedSameChildAt.RowsFirst.reoutput A strategy
                hwin package hsame hsameRows (default : Out₁) (default : Out₂)
            let hmatched :=
              package.literalRightSeamStageMatched_sameChild A strategy hwin
                stage (default : Out₁) (default : Out₂)
            let hmatchedLineage :=
              package.literalRightSeamStageMatched_acceptedPolicyLineage_of_root_state
                A strategy hwin stage (stageAccepted stage hstage)
                  (default : Out₁) (default : Out₂)
            let hsameLineage :
                hsame.AcceptedPolicyLineage A strategy hwin package := by
              simpa [hmatched, hsame,
                literalRightSeamStage_after_strictRight_sameChild,
                LiteralRightSeamTaggedSameChildAt.advance] using
                  hmatchedLineage.advance A strategy hwin package
                    ⟨input.1, input.2, .right⟩
            let hnormalizedLineage :=
              hsameLineage.reoutput A strategy hwin package
                (default : Out₁) (default : Out₂)
            simpa [hsame, hnormalized, hnormalizedRows, hnormalizedLineage,
              TaggedKernel,
              FinitePairedPhysicalController.advanceControls,
              ProfiledRawJointLeaderFreeKernel.physicalController,
              profiledRawJointIndexedPolicyLeaderFreeKernel] using
                (LiteralCombinedFreshPhaseActivatedSameChildSelected.recurrent
                  (package := package) _ _ hnormalized hnormalizedRows
                    hnormalizedLineage)
  | recurrent one two same rowsFirst lineage =>
      let advanced := same.advance A strategy hwin package
        ⟨input.1, input.2, .right⟩
      let normalized := advanced.reoutput A strategy hwin package
        (default : Out₁) (default : Out₂)
      let advancedRows :=
        LiteralRightSeamTaggedSameChildAt.RowsFirst.advance A strategy hwin
          package same rowsFirst ⟨input.1, input.2, .right⟩
      let normalizedRows :=
        LiteralRightSeamTaggedSameChildAt.RowsFirst.reoutput A strategy hwin
          package advanced advancedRows (default : Out₁) (default : Out₂)
      let advancedLineage := lineage.advance A strategy hwin package
        ⟨input.1, input.2, .right⟩
      let normalizedLineage := advancedLineage.reoutput A strategy hwin package
        (default : Out₁) (default : Out₂)
      simpa [advanced, normalized, advancedRows, normalizedRows,
        advancedLineage, normalizedLineage,
        TaggedKernel, literalCombinedFreshPhaseActivatedNoRecvOne,
        literalCombinedFreshPhaseActivatedOpenRecvTwo,
        FinitePairedPhysicalController.advanceControls,
        ProfiledRawJointLeaderFreeKernel.physicalController,
        profiledRawJointIndexedPolicyLeaderFreeKernel] using
          (LiteralCombinedFreshPhaseActivatedSameChildSelected.recurrent
            (package := package) _ _ normalized normalizedRows
              normalizedLineage)

/-- A strict-left round cannot activate the right-stage kernel; after
activation it preserves the already selected child. -/
noncomputable def
    LiteralCombinedFreshPhaseActivatedSameChildSelected.strictLeft
    (package : Package A strategy hwin (initial := initial))
    {one : OneControl A strategy hwin package}
    {two : TwoControl A strategy hwin package}
    (sameSelected :
      package.LiteralCombinedFreshPhaseActivatedSameChildSelected A strategy
        hwin one two)
    (input : In₁ × In₂) :
    package.LiteralCombinedFreshPhaseActivatedSameChildSelected A strategy hwin
      (package.literalCombinedFreshPhaseActivatedOpenRecvOne A strategy hwin
        one input.1 two input.2).1
      (package.literalCombinedFreshPhaseActivatedNoRecvTwo A strategy hwin two
        input.2).1 := by
  cases sameSelected with
  | pending one two structural _ _ =>
      let oneNext : OnePending A strategy hwin package :=
        (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
          input.1 two input.2).1.openControl
      let twoNext : TwoPending A strategy hwin package :=
        (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
          (package.literalCombinedFreshTwoPendingStep A strategy hwin) two
            input.2).1
      simpa [literalCombinedFreshPhaseActivatedOpenRecvOne,
        literalCombinedFreshPhaseActivatedNoRecvTwo, oneNext, twoNext] using
          (LiteralCombinedFreshPhaseActivatedSameChildSelected.pending
            (package := package) oneNext twoNext
            (package.literalCombinedFreshPhaseLiveStructuralSelected_strictLeft
              A strategy hwin one two structural input)
            (package.literalCombinedFreshRightActivationReady_eq_of_phase_eq
              A strategy hwin oneNext twoNext rfl)
            (package.literalCombinedFreshOneSelectedStageAccepted_after_openRecvOne
              A strategy hwin one input.1 two input.2))
  | recurrent one two same rowsFirst lineage =>
      let advanced := same.advance A strategy hwin package
        ⟨input.1, input.2, .left⟩
      let normalized := advanced.reoutput A strategy hwin package
        (default : Out₁) (default : Out₂)
      let advancedRows :=
        LiteralRightSeamTaggedSameChildAt.RowsFirst.advance A strategy hwin
          package same rowsFirst ⟨input.1, input.2, .left⟩
      let normalizedRows :=
        LiteralRightSeamTaggedSameChildAt.RowsFirst.reoutput A strategy hwin
          package advanced advancedRows (default : Out₁) (default : Out₂)
      let advancedLineage := lineage.advance A strategy hwin package
        ⟨input.1, input.2, .left⟩
      let normalizedLineage := advancedLineage.reoutput A strategy hwin package
        (default : Out₁) (default : Out₂)
      simpa [advanced, normalized, advancedRows, normalizedRows,
        advancedLineage, normalizedLineage,
        TaggedKernel, literalCombinedFreshPhaseActivatedOpenRecvOne,
        literalCombinedFreshPhaseActivatedNoRecvTwo,
        FinitePairedPhysicalController.advanceControls,
        ProfiledRawJointLeaderFreeKernel.physicalController,
        profiledRawJointIndexedPolicyLeaderFreeKernel] using
          (LiteralCombinedFreshPhaseActivatedSameChildSelected.recurrent
            (package := package) _ _ normalized normalizedRows
              normalizedLineage)

/-- A simultaneous close remains pending or preserves the already selected
child. -/
noncomputable def LiteralCombinedFreshPhaseActivatedSameChildSelected.both
    (package : Package A strategy hwin (initial := initial))
    {one : OneControl A strategy hwin package}
    {two : TwoControl A strategy hwin package}
    (sameSelected :
      package.LiteralCombinedFreshPhaseActivatedSameChildSelected A strategy
        hwin one two)
    (input : In₁ × In₂) :
    package.LiteralCombinedFreshPhaseActivatedSameChildSelected A strategy hwin
      (package.literalCombinedFreshPhaseActivatedClose A strategy hwin one
        input.1 two input.2).1
      (package.literalCombinedFreshPhaseActivatedClose A strategy hwin one
        input.1 two input.2).2 := by
  cases sameSelected with
  | pending one two structural _ _ =>
      let oneNext : OnePending A strategy hwin package :=
        (package.literalCombinedFreshPhaseLiveRecvOne A strategy hwin one
          input.1 two input.2).1.closedControl
      let twoNext : TwoPending A strategy hwin package :=
        (package.literalCombinedFreshPhaseLiveRecvTwo A strategy hwin two
          input.2 one input.1).1.closedControl
      have hready := package.literalCombinedFreshRightActivationReady_after_both
        A strategy hwin one two input
      simpa [literalCombinedFreshPhaseActivatedClose, oneNext, twoNext] using
        (LiteralCombinedFreshPhaseActivatedSameChildSelected.pending
          (package := package) oneNext twoNext
          (package.literalCombinedFreshPhaseLiveStructuralSelected_both A
            strategy hwin one two structural input)
          (hready.1.trans hready.2.symm)
          (package.literalCombinedFreshOneSelectedStageAccepted_after_closedRecvOne
            A strategy hwin one input.1 two input.2))
  | recurrent one two same rowsFirst lineage =>
      let advanced := same.advance A strategy hwin package
        ⟨input.1, input.2, .both⟩
      let normalized := advanced.reoutput A strategy hwin package
        (default : Out₁) (default : Out₂)
      let advancedRows :=
        LiteralRightSeamTaggedSameChildAt.RowsFirst.advance A strategy hwin
          package same rowsFirst ⟨input.1, input.2, .both⟩
      let normalizedRows :=
        LiteralRightSeamTaggedSameChildAt.RowsFirst.reoutput A strategy hwin
          package advanced advancedRows (default : Out₁) (default : Out₂)
      let advancedLineage := lineage.advance A strategy hwin package
        ⟨input.1, input.2, .both⟩
      let normalizedLineage := advancedLineage.reoutput A strategy hwin package
        (default : Out₁) (default : Out₂)
      simpa [advanced, normalized, advancedRows, normalizedRows,
        advancedLineage, normalizedLineage,
        TaggedKernel, literalCombinedFreshPhaseActivatedClose,
        FinitePairedPhysicalController.advanceControls,
        ProfiledRawJointLeaderFreeKernel.physicalController,
        profiledRawJointIndexedPolicyLeaderFreeKernel] using
          (LiteralCombinedFreshPhaseActivatedSameChildSelected.recurrent
            (package := package) _ _ normalized normalizedRows
              normalizedLineage)

/-! ## The semantic trace -/

/-- Every recurrent state of the canonical semantic trace retains the fixed
child selected at its unique activation. -/
noncomputable def
    literalCombinedFreshPhaseActivatedSemanticTrace_sameChildSelected
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) : ∀ n : Nat,
    package.LiteralCombinedFreshPhaseActivatedSameChildSelected A strategy hwin
      (package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy hwin
        env n).1
      (package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy hwin
        env n).2 := by
  intro n
  induction n with
  | zero =>
      exact package.literalCombinedFreshPhaseActivatedSameChildSelected_initial
        A strategy hwin
  | succ n ih =>
      cases hgraph : (env n).graph with
      | right =>
          simpa only [literalCombinedFreshPhaseActivatedSemanticTrace,
            FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
            hgraph] using ih.strictRight A strategy hwin package
              ((env n).inputOne, (env n).inputTwo)
      | left =>
          simpa only [literalCombinedFreshPhaseActivatedSemanticTrace,
            FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
            hgraph] using ih.strictLeft A strategy hwin package
              ((env n).inputOne, (env n).inputTwo)
      | both =>
          simpa only [literalCombinedFreshPhaseActivatedSemanticTrace,
            FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
            hgraph] using ih.both A strategy hwin package
              ((env n).inputOne, (env n).inputTwo)

/-- The canonical recurrent trace packages the same-child witness, its
preserved first-row proof, and its accepted-policy lineage together. -/
noncomputable def
    literalCombinedFreshPhaseActivatedSemanticTrace_sameChildAtFullData
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : OneRecurrent A strategy hwin package)
    (two : TwoRecurrent A strategy hwin package)
    (htrace :
      package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy hwin
        env n = (.inr one, .inr two))
    (outputOne : Out₁) (outputTwo : Out₂) :
    PSigma (fun same :
        package.LiteralRightSeamTaggedSameChildAt A strategy hwin
          ((one, outputOne), (two, outputTwo)) ↦
      PSigma (fun _ : same.RowsFirst A strategy hwin package ↦
        same.AcceptedPolicyLineage A strategy hwin package)) := by
  have hinvariant :=
    package.literalCombinedFreshPhaseActivatedSemanticTrace_sameChildSelected
      A strategy hwin env n
  rw [htrace] at hinvariant
  cases hinvariant with
  | recurrent _ _ same rowsFirst lineage =>
      let reoutput := same.reoutput A strategy hwin package outputOne outputTwo
      exact ⟨reoutput, ⟨
        LiteralRightSeamTaggedSameChildAt.RowsFirst.reoutput A strategy hwin
          package same rowsFirst outputOne outputTwo,
        lineage.reoutput A strategy hwin package outputOne outputTwo⟩⟩

/-- Projection retaining the older same-child/row interface.  It is defined
from the full datum so later lineage users refer to the identical dependent
same-child witness. -/
noncomputable def
    literalCombinedFreshPhaseActivatedSemanticTrace_sameChildAtData
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : OneRecurrent A strategy hwin package)
    (two : TwoRecurrent A strategy hwin package)
    (htrace :
      package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy hwin
        env n = (.inr one, .inr two))
    (outputOne : Out₁) (outputTwo : Out₂) :
    { same : package.LiteralRightSeamTaggedSameChildAt A strategy hwin
        ((one, outputOne), (two, outputTwo)) //
      same.RowsFirst A strategy hwin package } := by
  let full :=
    package.literalCombinedFreshPhaseActivatedSemanticTrace_sameChildAtFullData
      A strategy hwin env n one two htrace outputOne outputTwo
  exact ⟨full.1, full.2.1⟩

/-- Concrete recurrent presentation of the trace, with arbitrary requested
Moore outputs, yields the exact same-child witness needed by the physical
flush handoff. -/
noncomputable def
    literalCombinedFreshPhaseActivatedSemanticTrace_sameChildAt
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : OneRecurrent A strategy hwin package)
    (two : TwoRecurrent A strategy hwin package)
    (htrace :
      package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy hwin
        env n = (.inr one, .inr two))
    (outputOne : Out₁) (outputTwo : Out₂) :
    package.LiteralRightSeamTaggedSameChildAt A strategy hwin
      ((one, outputOne), (two, outputTwo)) :=
  (package.literalCombinedFreshPhaseActivatedSemanticTrace_sameChildAtData A
    strategy hwin env n one two htrace outputOne outputTwo).1

/-- The canonical semantic trace also exposes the preserved `.first` receiver
row at every recurrent cut. -/
theorem literalCombinedFreshPhaseActivatedSemanticTrace_sameChildAt_rowsFirst
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : OneRecurrent A strategy hwin package)
    (two : TwoRecurrent A strategy hwin package)
    (htrace :
      package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy hwin
        env n = (.inr one, .inr two))
    (outputOne : Out₁) (outputTwo : Out₂) :
    (package.literalCombinedFreshPhaseActivatedSemanticTrace_sameChildAt A
      strategy hwin env n one two htrace outputOne outputTwo).RowsFirst A
        strategy hwin package :=
  (package.literalCombinedFreshPhaseActivatedSemanticTrace_sameChildAtData A
    strategy hwin env n one two htrace outputOne outputTwo).2

/-- Every recurrent semantic state retains a genuinely accepted policy seed
and finite ancestry for all of its currently exposed fixed-child roots. -/
noncomputable def
    literalCombinedFreshPhaseActivatedSemanticTrace_sameChildAt_lineage
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : OneRecurrent A strategy hwin package)
    (two : TwoRecurrent A strategy hwin package)
    (htrace :
      package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy hwin
        env n = (.inr one, .inr two))
    (outputOne : Out₁) (outputTwo : Out₂) :
    (package.literalCombinedFreshPhaseActivatedSemanticTrace_sameChildAt A
      strategy hwin env n one two htrace outputOne outputTwo
      ).AcceptedPolicyLineage A strategy hwin package :=
  (package.literalCombinedFreshPhaseActivatedSemanticTrace_sameChildAtFullData
    A strategy hwin env n one two htrace outputOne outputTwo).2.2

/-! ## Automatic physical-flush handoff -/

/-- The same-child premise of the two-round physical flush is supplied
automatically by the semantic trace invariant. -/
noncomputable def
    LiteralCombinedFreshPhaseActivatedLeftRightFlushWitness.sameChildOfSemantic
    (package : Package A strategy hwin (initial := initial))
    {env : EnvironmentSequence In₁ In₂} {n : Nat}
    {one : OneRecurrent A strategy hwin package}
    {two : TwoRecurrent A strategy hwin package}
    (flush :
      package.LiteralCombinedFreshPhaseActivatedLeftRightFlushWitness A
        strategy hwin env n one two)
    (hsemantic :
      package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy hwin
        env n = (.inr one, .inr two)) :
    package.LiteralRightSeamTaggedSameChildAt A strategy hwin flush.tagged :=
  flush.sameChild A strategy hwin package
    (package.literalCombinedFreshPhaseActivatedSemanticTrace_sameChildAt A
      strategy hwin env n one two hsemantic
      ((package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
        hwin).globalMachine.globalStateTrace env n).1.2
      ((package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
        hwin).globalMachine.globalStateTrace env n).2.2)

set_option maxHeartbeats 800000 in
/-- The two-round relay flush preserves the same-child witness, its first-row
invariant, and its accepted-policy lineage simultaneously.  Bundling these
dependent data is essential: reconstructing the same-child witness a second
time produces a propositionally equal but not definitionally identical index
for the row and lineage proofs. -/
noncomputable def
    LiteralCombinedFreshPhaseActivatedLeftRightFlushWitness.sameChildOfSemanticFullData
    (package : Package A strategy hwin (initial := initial))
    {env : EnvironmentSequence In₁ In₂} {n : Nat}
    {one : OneRecurrent A strategy hwin package}
    {two : TwoRecurrent A strategy hwin package}
    (flush :
      package.LiteralCombinedFreshPhaseActivatedLeftRightFlushWitness A
        strategy hwin env n one two)
    (hsemantic :
      package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy hwin
        env n = (.inr one, .inr two)) :
    PSigma (fun same :
        package.LiteralRightSeamTaggedSameChildAt A strategy hwin
          flush.tagged ↦
      PSigma (fun _ : same.RowsFirst A strategy hwin package ↦
        same.AcceptedPolicyLineage A strategy hwin package)) := by
  let actual :=
    package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
      hwin
  let atStart :=
    package.literalCombinedFreshPhaseActivatedSemanticTrace_sameChildAt A
      strategy hwin env n one two hsemantic
      (actual.globalMachine.globalStateTrace env n).1.2
      (actual.globalMachine.globalStateTrace env n).2.2
  let lineageStart :=
    package.literalCombinedFreshPhaseActivatedSemanticTrace_sameChildAt_lineage
      A strategy hwin env n one two hsemantic
      (actual.globalMachine.globalStateTrace env n).1.2
      (actual.globalMachine.globalStateTrace env n).2.2
  let afterOne := atStart.advance A strategy hwin package (env n)
  let rowsStart :=
    package.literalCombinedFreshPhaseActivatedSemanticTrace_sameChildAt_rowsFirst
      A strategy hwin env n one two hsemantic
      (actual.globalMachine.globalStateTrace env n).1.2
      (actual.globalMachine.globalStateTrace env n).2.2
  let rowsOne :=
    LiteralRightSeamTaggedSameChildAt.RowsFirst.advance A strategy hwin package
      atStart rowsStart (env n)
  let lineageOne := lineageStart.advance A strategy hwin package (env n)
  let afterTwo := afterOne.advance A strategy hwin package (env (n + 1))
  let rowsTwo :=
    LiteralRightSeamTaggedSameChildAt.RowsFirst.advance A strategy hwin package
      afterOne rowsOne (env (n + 1))
  let lineageTwo := lineageOne.advance A strategy hwin package (env (n + 1))
  rw [flush.descendant]
  simpa [afterOne, afterTwo,
    FiniteGlobalRoundMachine.globalStateTrace_succ, OmegaWord.drop,
    FiniteGlobalRoundMachine.reroot,
    ProfiledRawJointLeaderFreeKernel.globalMachine] using
      (PSigma.mk afterTwo (PSigma.mk rowsTwo lineageTwo))

set_option maxHeartbeats 800000 in
/-- The automatic same-child state produced by the two-round relay flush
still has the canonical `.first` receiver row. -/
theorem
    LiteralCombinedFreshPhaseActivatedLeftRightFlushWitness.sameChildOfSemantic_rowsFirst
    (package : Package A strategy hwin (initial := initial))
    {env : EnvironmentSequence In₁ In₂} {n : Nat}
    {one : OneRecurrent A strategy hwin package}
    {two : TwoRecurrent A strategy hwin package}
    (flush :
      package.LiteralCombinedFreshPhaseActivatedLeftRightFlushWitness A
        strategy hwin env n one two)
    (hsemantic :
      package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy hwin
        env n = (.inr one, .inr two)) :
    (flush.sameChildOfSemantic A strategy hwin package hsemantic).RowsFirst A
      strategy hwin package := by
  let actual :=
    package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
      hwin
  let atStart :=
    package.literalCombinedFreshPhaseActivatedSemanticTrace_sameChildAt A
      strategy hwin env n one two hsemantic
      (actual.globalMachine.globalStateTrace env n).1.2
      (actual.globalMachine.globalStateTrace env n).2.2
  have rowsStart : atStart.RowsFirst A strategy hwin package :=
    package.literalCombinedFreshPhaseActivatedSemanticTrace_sameChildAt_rowsFirst
      A strategy hwin env n one two hsemantic
        (actual.globalMachine.globalStateTrace env n).1.2
        (actual.globalMachine.globalStateTrace env n).2.2
  let afterOne := atStart.advance A strategy hwin package (env n)
  have rowsOne : afterOne.RowsFirst A strategy hwin package :=
    LiteralRightSeamTaggedSameChildAt.RowsFirst.advance A strategy hwin package
      atStart rowsStart (env n)
  let afterTwo := afterOne.advance A strategy hwin package (env (n + 1))
  have rowsTwo : afterTwo.RowsFirst A strategy hwin package :=
    LiteralRightSeamTaggedSameChildAt.RowsFirst.advance A strategy hwin package
      afterOne rowsOne (env (n + 1))
  unfold LiteralRightSeamTaggedSameChildAt.RowsFirst at rowsTwo ⊢
  simp only [
    LiteralCombinedFreshPhaseActivatedLeftRightFlushWitness.sameChildOfSemantic,
    LiteralCombinedFreshPhaseActivatedLeftRightFlushWitness.sameChild,
    LiteralRightSeamTaggedSameChildAt.unitState] at ⊢
  generalize hone : afterTwo.unitState.1.1 = finalOne at rowsTwo ⊢
  generalize htwo : afterTwo.unitState.2.1 = finalTwo at rowsTwo ⊢
  cases finalOne <;> cases finalTwo <;> exact rowsTwo

set_option maxHeartbeats 800000 in
/-- The forced left/right flush ends in a matched-right fixed-child state.
Its live receiver retains the canonical `.first` row. -/
theorem
    LiteralCombinedFreshPhaseActivatedLeftRightFlushWitness.sameChildOfSemantic_matchedRight
    (package : Package A strategy hwin (initial := initial))
    {env : EnvironmentSequence In₁ In₂} {n : Nat}
    {one : OneRecurrent A strategy hwin package}
    {two : TwoRecurrent A strategy hwin package}
    (flush :
      package.LiteralCombinedFreshPhaseActivatedLeftRightFlushWitness A
        strategy hwin env n one two)
    (hsemantic :
      package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy hwin
        env n = (.inr one, .inr two)) :
    let same := flush.sameChildOfSemantic A strategy hwin package hsemantic
    let source := package.literalRightSeamTaggedChildSource A strategy hwin
      same.key
    let policy := package.literalRightSeamTaggedChildPolicy A strategy hwin
      same.key
    let bank := package.literalRightSeamTaggedChildControllerBank A strategy
      hwin same.key
    let adapter := UnitAdapter A strategy hwin package same.key
    ∃ owner : ProfiledRawJointUnitRightPolicyOwnerControl A strategy source
        policy bank,
      ∃ right : ProfiledRawJointUnitRightPolicyReceiverControl A strategy
          source policy,
        ∃ outputOne : Out₁, ∃ outputTwo : Out₂,
          same.unitState =
              profiledRawJointUnitMatchedRightState A strategy source policy
                bank adapter owner right outputOne outputTwo ∧
            right.2.1 = .first := by
  dsimp only
  let actual :=
    package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
      hwin
  let atStart :=
    package.literalCombinedFreshPhaseActivatedSemanticTrace_sameChildAt A
      strategy hwin env n one two hsemantic
      (actual.globalMachine.globalStateTrace env n).1.2
      (actual.globalMachine.globalStateTrace env n).2.2
  have rowsStart : atStart.RowsFirst A strategy hwin package :=
    package.literalCombinedFreshPhaseActivatedSemanticTrace_sameChildAt_rowsFirst
      A strategy hwin env n one two hsemantic
        (actual.globalMachine.globalStateTrace env n).1.2
        (actual.globalMachine.globalStateTrace env n).2.2
  let afterOne := atStart.advance A strategy hwin package (env n)
  have rowsOne : afterOne.RowsFirst A strategy hwin package :=
    LiteralRightSeamTaggedSameChildAt.RowsFirst.advance A strategy hwin package
      atStart rowsStart (env n)
  have shape :=
    afterOne.advance_matchedRight_of_graph_right A strategy hwin package
      rowsOne (env (n + 1)) flush.right
  unfold LiteralCombinedFreshPhaseActivatedLeftRightFlushWitness.sameChildOfSemantic
  unfold LiteralCombinedFreshPhaseActivatedLeftRightFlushWitness.sameChild
  simpa [
    atStart, afterOne, actual] using shape

/-! ## Aligned left-headed persistent cut -/

/-- A post-flush cut at which the acknowledged controller, tagged indexed
kernel, and one fixed-child Unit kernel are all synchronized.  The Unit state
is completed matched-right, so the physical suffix starts with its required
strict-left block. -/
structure LiteralCombinedFreshPhaseActivatedPersistentLeftUnitCutWitness
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) : Type (max u v x y s) where
  start : Nat
  tagged : (TaggedKernel A strategy hwin package).globalMachine.State
  duplicate :
    package.LiteralCombinedFreshPhaseActivatedDuplicateRecurrentAt A strategy
      hwin
      ((package.literalCombinedFreshPhaseActivatedPhysicalController A
        strategy hwin).globalMachine.globalStateTrace env start)
      tagged
  same : package.LiteralRightSeamTaggedSameChildAt A strategy hwin tagged
  rowsFirst : same.RowsFirst A strategy hwin package
  lineage : same.AcceptedPolicyLineage A strategy hwin package
  left : (env start).graph = .left
  noBoth : ∀ j : Nat, (env (start + j)).graph ≠ .both
  strictRunsTerminate : OperationalStrictRunsTerminate
    (profiledRawJointPhysicalGraphTail (OmegaWord.drop env start) 0)
  owner : ProfiledRawJointUnitRightPolicyOwnerControl A strategy
    (package.literalRightSeamTaggedChildSource A strategy hwin same.key)
    (package.literalRightSeamTaggedChildPolicy A strategy hwin same.key)
    (package.literalRightSeamTaggedChildControllerBank A strategy hwin
      same.key)
  right : ProfiledRawJointUnitRightPolicyReceiverControl A strategy
    (package.literalRightSeamTaggedChildSource A strategy hwin same.key)
    (package.literalRightSeamTaggedChildPolicy A strategy hwin same.key)
  outputOne : Out₁
  outputTwo : Out₂
  unitState_eq : same.unitState =
    profiledRawJointUnitMatchedRightState A strategy
      (package.literalRightSeamTaggedChildSource A strategy hwin same.key)
      (package.literalRightSeamTaggedChildPolicy A strategy hwin same.key)
      (package.literalRightSeamTaggedChildControllerBank A strategy hwin
        same.key)
      (UnitAdapter A strategy hwin package same.key) owner right outputOne
        outputTwo
  right_row : right.2.1 = .first

/-- Persistent reversal automatically supplies an aligned left-headed Unit
cut after the relay flush.  Choosing a later right/left boundary is essential:
the immediate post-flush round need not already be left. -/
theorem
    exists_literalCombinedFreshPhaseActivatedPersistentLeftUnitCutWitness_of_persistentReversal
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂)
    (hreversal :
      PersistentStrictReversalTail (fun n ↦ (env n).graph)) :
    Nonempty
      (package.LiteralCombinedFreshPhaseActivatedPersistentLeftUnitCutWitness
        A strategy hwin env) := by
  rcases
      package.exists_literalCombinedFreshPhaseActivatedLeftRightFlushWitness_with_noBothSuffix_of_persistentReversal
        A strategy hwin env hreversal with
    ⟨n, one, two, hsemantic, ⟨⟨flush⟩, hnoBothFlush⟩⟩
  rcases hreversal.exists_adjacent_right_left_after (n + 2) with
    ⟨r, hr, hright, hleft⟩
  let k := r - (n + 2)
  have hk : n + 2 + k = r := by
    dsimp only [k]
    omega
  let tail := OmegaWord.drop env (n + 2)
  let fullZero :=
    flush.sameChildOfSemanticFullData A strategy hwin package hsemantic
  let sameZero := fullZero.1
  have rowsZero : sameZero.RowsFirst A strategy hwin package := fullZero.2.1
  let lineageZero := fullZero.2.2
  let sameBefore := sameZero.trace A strategy hwin package tail k
  have rowsBefore : sameBefore.RowsFirst A strategy hwin package :=
    LiteralRightSeamTaggedSameChildAt.RowsFirst.trace A strategy hwin package
      sameZero rowsZero tail k
  have htailRight : (tail k).graph = .right := by
    simpa [tail, OmegaWord.drop, hk] using hright
  let sameAfter := sameZero.trace A strategy hwin package tail (k + 1)
  have rowsAfter : sameAfter.RowsFirst A strategy hwin package :=
    LiteralRightSeamTaggedSameChildAt.RowsFirst.trace A strategy hwin package
      sameZero rowsZero tail (k + 1)
  let lineageAfter := lineageZero.trace A strategy hwin package tail (k + 1)
  have shapeBefore :=
    sameBefore.advance_matchedRight_of_graph_right A strategy hwin package
      rowsBefore (tail k) htailRight
  have shapeAfter :
      let source := package.literalRightSeamTaggedChildSource A strategy hwin
        sameAfter.key
      let policy := package.literalRightSeamTaggedChildPolicy A strategy hwin
        sameAfter.key
      let bank := package.literalRightSeamTaggedChildControllerBank A strategy
        hwin sameAfter.key
      let adapter := UnitAdapter A strategy hwin package sameAfter.key
      ∃ owner : ProfiledRawJointUnitRightPolicyOwnerControl A strategy source
          policy bank,
        ∃ right : ProfiledRawJointUnitRightPolicyReceiverControl A strategy
            source policy,
          ∃ outputOne : Out₁, ∃ outputTwo : Out₂,
            sameAfter.unitState =
                profiledRawJointUnitMatchedRightState A strategy source policy
                  bank adapter owner right outputOne outputTwo ∧
              right.2.1 = .first := by
    simpa [sameAfter, sameBefore,
      LiteralRightSeamTaggedSameChildAt.trace] using shapeBefore
  have duplicateAt :=
    flush.duplicate.globalStateTrace A strategy hwin package
      ((package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
        hwin).globalMachine.globalStateTrace env (n + 2))
      flush.tagged tail (k + 1)
  have actualAt :
      ((package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
        hwin).globalMachine.reroot
          ((package.literalCombinedFreshPhaseActivatedPhysicalController A
            strategy hwin).globalMachine.globalStateTrace env (n + 2))
        ).globalStateTrace tail (k + 1) =
      (package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
        hwin).globalMachine.globalStateTrace env (r + 1) := by
    rw [(package.literalCombinedFreshPhaseActivatedPhysicalController A
      strategy hwin).globalMachine.reroot_globalStateTrace_drop env (n + 2)
        (k + 1)]
    congr 1
    omega
  have duplicateAfter :
      package.LiteralCombinedFreshPhaseActivatedDuplicateRecurrentAt A strategy
        hwin
        ((package.literalCombinedFreshPhaseActivatedPhysicalController A
          strategy hwin).globalMachine.globalStateTrace env (r + 1))
        (((TaggedKernel A strategy hwin package).globalMachine.reroot
          flush.tagged).globalStateTrace tail (k + 1)) := by
    rw [actualAt] at duplicateAt
    exact duplicateAt
  have hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail (OmegaWord.drop env (r + 1)) 0) := by
    apply operationalStrictRunsTerminate_of_bothStrictDirectionsRecurrent
    constructor
    · intro start
      rcases hreversal.2.1 (r + 1 + start) with ⟨m, hm, hgraph⟩
      refine ⟨m - (r + 1), by omega, ?_⟩
      have hbase : r + 1 ≤ m := by omega
      simpa [profiledRawJointPhysicalGraphTail, OmegaWord.drop,
        Nat.add_sub_of_le hbase] using hgraph
    · intro start
      rcases hreversal.2.2 (r + 1 + start) with ⟨m, hm, hgraph⟩
      refine ⟨m - (r + 1), by omega, ?_⟩
      have hbase : r + 1 ≤ m := by omega
      simpa [profiledRawJointPhysicalGraphTail, OmegaWord.drop,
        Nat.add_sub_of_le hbase] using hgraph
  rcases shapeAfter with
    ⟨owner, right, outputOne, outputTwo, hunitState, hrightRow⟩
  refine ⟨⟨r + 1,
    ((TaggedKernel A strategy hwin package).globalMachine.reroot flush.tagged
      ).globalStateTrace tail (k + 1), duplicateAfter, sameAfter, rowsAfter,
    lineageAfter, hleft, ?_, hterm, owner, right, outputOne, outputTwo, hunitState,
    hrightRow⟩⟩
  intro j
  rw [show r + 1 + j = n + 2 + (k + 1 + j) by omega]
  exact hnoBothFlush (k + 1 + j)

/-- At the aligned cut, persistent-strict acceptance needs only a genuinely
accepted policy ancestor, its finite alternating lineage to the receiver
target, and equality of the actual DPA state with that target's first-row
entry state.  All graph and controller-shape premises are discharged by the
cut witness. -/
theorem
    LiteralCombinedFreshPhaseActivatedPersistentLeftUnitCutWitness.unit_acceptsFrom_of_policyLineage
    {package : Package A strategy hwin (initial := initial)}
    {env : EnvironmentSequence In₁ In₂}
    (cut :
      package.LiteralCombinedFreshPhaseActivatedPersistentLeftUnitCutWitness
        A strategy hwin env)
    (acceptedSeed current :
      ProfiledRawJointUnitFixedPolicyRoot A strategy
        ((package.literalRightSeamTaggedChildSource A strategy hwin
          cut.same.key).code A)
        (package.literalRightSeamTaggedChildPolicy A strategy hwin
          cut.same.key))
    (hseed :
      ProfiledRawJointUnitFixedPolicyRoot.state A
          (package.literalRightSeamTaggedChildPolicy A strategy hwin
            cut.same.key) acceptedSeed =
        (package.literalRightSeamTaggedChildPolicy A strategy hwin
          cut.same.key).run [])
    (chain :
      ProfiledRawJointUnitFixedPolicyRoot.AlternatingPrefix A
        (package.literalRightSeamTaggedChildPolicy A strategy hwin
          cut.same.key) acceptedSeed current)
    (hcurrent : current =
      .inr (profiledRawJointUnitPolicyRightReceiverTarget A strategy
        (package.literalRightSeamTaggedChildSource A strategy hwin
          cut.same.key)
        (package.literalRightSeamTaggedChildPolicy A strategy hwin
          cut.same.key)
        (package.literalRightSeamTaggedChildControllerBank A strategy hwin
          cut.same.key) cut.right))
    (hchecker :
      let actual :=
        package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
          hwin
      let actualWord := actual.globalMachine.globalMachineTraceWord
        actual.globalOutputOne actual.globalOutputTwo env
      A.run actualWord cut.start =
        current.entryStateForRow A strategy
          (package.literalRightSeamTaggedChildSource A strategy hwin
            cut.same.key)
          (package.literalRightSeamTaggedChildPolicy A strategy hwin
            cut.same.key) .first) :
    let actual :=
      package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
        hwin
    let actualWord := actual.globalMachine.globalMachineTraceWord
      actual.globalOutputOne actual.globalOutputTwo env
    let unit := UnitKernel A strategy hwin package cut.same.key
    A.AcceptsFrom (A.run actualWord cut.start)
      ((unit.globalMachine.reroot cut.same.unitState).globalMachineTraceWord
        unit.globalOutputOne unit.globalOutputTwo
        (OmegaWord.drop env cut.start)) := by
  subst current
  let source := package.literalRightSeamTaggedChildSource A strategy hwin
    cut.same.key
  let policy := package.literalRightSeamTaggedChildPolicy A strategy hwin
    cut.same.key
  let bank := package.literalRightSeamTaggedChildControllerBank A strategy hwin
    cut.same.key
  let adapter := UnitAdapter A strategy hwin package cut.same.key
  let physicalEnv := OmegaWord.drop env cut.start
  let target := profiledRawJointUnitPolicyRightReceiverTarget A strategy source
    policy bank cut.right
  have hgraph : (physicalEnv 0).graph = .left := by
    simpa [physicalEnv, OmegaWord.drop] using cut.left
  have hnoboth : ∀ j : Nat,
      profiledRawJointPhysicalGraphTail physicalEnv 0 j ≠ .both := by
    intro j
    simpa [profiledRawJointPhysicalGraphTail, physicalEnv, OmegaWord.drop]
      using cut.noBoth j
  have zeroMatched :=
    profiledRawJointUnitPersistentStrictControlAt_zero_matchedRight A strategy
      source policy bank adapter cut.owner cut.right cut.outputOne cut.outputTwo
        physicalEnv cut.strictRunsTerminate target .first hgraph rfl
          cut.right_row
  have zero :
      ProfiledRawJointUnitPersistentStrictControlAt A strategy source policy
        bank adapter cut.same.unitState physicalEnv cut.strictRunsTerminate
          .first (.inr target) 0 := by
    rw [cut.unitState_eq]
    exact zeroMatched
  exact profiledRawJointUnitPersistentStrict_acceptsFrom_of_prefix A strategy
    source policy bank adapter cut.same.unitState physicalEnv
      cut.strictRunsTerminate acceptedSeed (.inr target) hnoboth zero _ hchecker
        hseed chain

/-- Acceptance of the fixed-child Unit suffix at an aligned cut transfers
through the same-child simulation and duplicate relay, then pastes back the
finite actual prefix. -/
theorem
    LiteralCombinedFreshPhaseActivatedPersistentLeftUnitCutWitness.accepts_of_unitAcceptsFrom
    {package : Package A strategy hwin (initial := initial)}
    {env : EnvironmentSequence In₁ In₂}
    (cut :
      package.LiteralCombinedFreshPhaseActivatedPersistentLeftUnitCutWitness
        A strategy hwin env)
    (hunit :
      let actual :=
        package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
          hwin
      let actualWord := actual.globalMachine.globalMachineTraceWord
        actual.globalOutputOne actual.globalOutputTwo env
      let unit := UnitKernel A strategy hwin package cut.same.key
      A.AcceptsFrom (A.run actualWord cut.start)
        ((unit.globalMachine.reroot cut.same.unitState).globalMachineTraceWord
          unit.globalOutputOne unit.globalOutputTwo
          (OmegaWord.drop env cut.start))) :
    A.Accepts
      ((package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
        hwin).globalMachine.globalMachineTraceWord
        (package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
          hwin).globalOutputOne
        (package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
          hwin).globalOutputTwo env) := by
  let actual :=
    package.literalCombinedFreshPhaseActivatedPhysicalController A strategy hwin
  let actualWord := actual.globalMachine.globalMachineTraceWord
    actual.globalOutputOne actual.globalOutputTwo env
  have htagged :
      A.AcceptsFrom (A.run actualWord cut.start)
        (((TaggedKernel A strategy hwin package).globalMachine.reroot
          cut.tagged).globalMachineTraceWord
            (TaggedKernel A strategy hwin package).globalOutputOne
            (TaggedKernel A strategy hwin package).globalOutputTwo
            (OmegaWord.drop env cut.start)) := by
    exact (profiledRawJointIndexedPolicyRecurrentAt_acceptsFrom_iff A strategy
      (TaggedChild A strategy hwin package)
      (package.literalRightSeamTaggedChildSource A strategy hwin)
      (package.literalRightSeamTaggedChildPolicy A strategy hwin)
      (package.literalRightSeamTaggedChildControllerBank A strategy hwin)
      (package.literalRightSeamTaggedUnitAdapter A strategy hwin)
      cut.same.key (UnitAdapter A strategy hwin package cut.same.key)
      cut.tagged cut.same.unitState cut.same.recurrent
      (OmegaWord.drop env cut.start) (A.run actualWord cut.start)).mpr hunit
  exact package.literalCombinedFreshPhaseActivated_accepts_of_duplicateRecurrentAt
    A strategy hwin env cut.start cut.tagged cut.duplicate htagged

/-- The complete activated word is accepted once the three genuinely
semantic residual facts at the aligned cut are known: an accepted policy
ancestor, its finite alternating lineage to the live receiver target, and
the actual checker-state equation. -/
theorem
    LiteralCombinedFreshPhaseActivatedPersistentLeftUnitCutWitness.accepts_of_policyLineage
    {package : Package A strategy hwin (initial := initial)}
    {env : EnvironmentSequence In₁ In₂}
    (cut :
      package.LiteralCombinedFreshPhaseActivatedPersistentLeftUnitCutWitness
        A strategy hwin env)
    (acceptedSeed current :
      ProfiledRawJointUnitFixedPolicyRoot A strategy
        ((package.literalRightSeamTaggedChildSource A strategy hwin
          cut.same.key).code A)
        (package.literalRightSeamTaggedChildPolicy A strategy hwin
          cut.same.key))
    (hseed :
      ProfiledRawJointUnitFixedPolicyRoot.state A
          (package.literalRightSeamTaggedChildPolicy A strategy hwin
            cut.same.key) acceptedSeed =
        (package.literalRightSeamTaggedChildPolicy A strategy hwin
          cut.same.key).run [])
    (chain :
      ProfiledRawJointUnitFixedPolicyRoot.AlternatingPrefix A
        (package.literalRightSeamTaggedChildPolicy A strategy hwin
          cut.same.key) acceptedSeed current)
    (hcurrent : current =
      .inr (profiledRawJointUnitPolicyRightReceiverTarget A strategy
        (package.literalRightSeamTaggedChildSource A strategy hwin
          cut.same.key)
        (package.literalRightSeamTaggedChildPolicy A strategy hwin
          cut.same.key)
        (package.literalRightSeamTaggedChildControllerBank A strategy hwin
          cut.same.key) cut.right))
    (hchecker :
      let actual :=
        package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
          hwin
      let actualWord := actual.globalMachine.globalMachineTraceWord
        actual.globalOutputOne actual.globalOutputTwo env
      A.run actualWord cut.start =
        current.entryStateForRow A strategy
          (package.literalRightSeamTaggedChildSource A strategy hwin
            cut.same.key)
          (package.literalRightSeamTaggedChildPolicy A strategy hwin
            cut.same.key) .first) :
    A.Accepts
      ((package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
        hwin).globalMachine.globalMachineTraceWord
        (package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
          hwin).globalOutputOne
        (package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
          hwin).globalOutputTwo env) := by
  apply cut.accepts_of_unitAcceptsFrom A strategy hwin
  exact cut.unit_acceptsFrom_of_policyLineage A strategy hwin acceptedSeed
    current hseed chain hcurrent hchecker

/-- The accepted-lineage invariant already contains the completed
matched-right receiver target selected at the aligned cut. -/
theorem
    LiteralCombinedFreshPhaseActivatedPersistentLeftUnitCutWitness.rightTarget_reachable
    {package : Package A strategy hwin (initial := initial)}
    {env : EnvironmentSequence In₁ In₂}
    (cut :
      package.LiteralCombinedFreshPhaseActivatedPersistentLeftUnitCutWitness
        A strategy hwin env) :
    ProfiledRawJointUnitFixedPolicyRoot.AlternatingPrefix.Reachable
      (policy := package.literalRightSeamTaggedChildPolicy A strategy hwin
        cut.same.key)
      A cut.lineage.seed
      (.inr (profiledRawJointUnitPolicyRightReceiverTarget A strategy
        (package.literalRightSeamTaggedChildSource A strategy hwin
          cut.same.key)
        (package.literalRightSeamTaggedChildPolicy A strategy hwin
          cut.same.key)
        (package.literalRightSeamTaggedChildControllerBank A strategy hwin
          cut.same.key) cut.right)) := by
  have reachable := cut.lineage.reachable
  unfold LiteralRightSeamTaggedSameChildAt.PolicyReachableFrom at reachable
  rw [cut.unitState_eq] at reachable
  exact reachable.2.2

/-- At a persistent-reversal cut, accepted-policy ancestry is now automatic.
The only semantic premise left is the equality between the actual checker
state and the selected receiver target's fresh `.first` entry state. -/
theorem
    LiteralCombinedFreshPhaseActivatedPersistentLeftUnitCutWitness.accepts_of_checker
    {package : Package A strategy hwin (initial := initial)}
    {env : EnvironmentSequence In₁ In₂}
    (cut :
      package.LiteralCombinedFreshPhaseActivatedPersistentLeftUnitCutWitness
        A strategy hwin env)
    (hchecker :
      let actual :=
        package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
          hwin
      let actualWord := actual.globalMachine.globalMachineTraceWord
        actual.globalOutputOne actual.globalOutputTwo env
      let source := package.literalRightSeamTaggedChildSource A strategy hwin
        cut.same.key
      let policy := package.literalRightSeamTaggedChildPolicy A strategy hwin
        cut.same.key
      let bank := package.literalRightSeamTaggedChildControllerBank A strategy
        hwin cut.same.key
      let target := profiledRawJointUnitPolicyRightReceiverTarget A strategy
        source policy bank cut.right
      let current : ProfiledRawJointUnitFixedPolicyRoot A strategy
          (source.code A) policy := .inr target
      A.run actualWord cut.start =
        current.entryStateForRow A strategy source policy .first) :
    A.Accepts
      ((package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
        hwin).globalMachine.globalMachineTraceWord
        (package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
          hwin).globalOutputOne
        (package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
          hwin).globalOutputTwo env) := by
  rcases cut.rightTarget_reachable A strategy hwin with ⟨chain⟩
  exact cut.accepts_of_policyLineage A strategy hwin cut.lineage.seed
    (.inr (profiledRawJointUnitPolicyRightReceiverTarget A strategy
      (package.literalRightSeamTaggedChildSource A strategy hwin cut.same.key)
      (package.literalRightSeamTaggedChildPolicy A strategy hwin cut.same.key)
      (package.literalRightSeamTaggedChildControllerBank A strategy hwin
        cut.same.key) cut.right))
    cut.lineage.seed_state chain rfl hchecker

/-- Strongest automatic handoff: a state-relative acceptance proof for the
selected fixed-child suffix closes the complete activated physical word.
The accepted suffix may come from code-lineage priority pasting; no
four-regime package or row-dependent DPA restart is required. -/
theorem
    literalCombinedFreshPhaseActivated_accepts_of_leftRightFlush_unitAcceptsFrom_of_semantic
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : OneRecurrent A strategy hwin package)
    (two : TwoRecurrent A strategy hwin package)
    (hsemantic :
      package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy hwin
        env n = (.inr one, .inr two))
    (flush :
      package.LiteralCombinedFreshPhaseActivatedLeftRightFlushWitness A
        strategy hwin env n one two)
    (hunit :
      let actual :=
        package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
          hwin
      let actualWord := actual.globalMachine.globalMachineTraceWord
        actual.globalOutputOne actual.globalOutputTwo env
      let same := flush.sameChildOfSemantic A strategy hwin package hsemantic
      let unit := UnitKernel A strategy hwin package same.key
      A.AcceptsFrom (A.run actualWord (n + 2))
        (((unit.globalMachine.reroot same.unitState).globalMachineTraceWord
          unit.globalOutputOne unit.globalOutputTwo
          (OmegaWord.drop env (n + 2))))) :
    A.Accepts
      ((package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
        hwin).globalMachine.globalMachineTraceWord
        (package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
          hwin).globalOutputOne
        (package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
          hwin).globalOutputTwo env) := by
  let atStart :=
    package.literalCombinedFreshPhaseActivatedSemanticTrace_sameChildAt A
      strategy hwin env n one two hsemantic
      ((package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
        hwin).globalMachine.globalStateTrace env n).1.2
      ((package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
        hwin).globalMachine.globalStateTrace env n).2.2
  exact
    package.literalCombinedFreshPhaseActivated_accepts_of_leftRightFlush_sameChild
      A strategy hwin env n one two flush atStart (by
        simpa [atStart,
          LiteralCombinedFreshPhaseActivatedLeftRightFlushWitness.sameChildOfSemantic]
          using hunit)

/-- After the trace invariant, the only recurrent-tail premise is the actual
fixed-child physical acceptance package.  No independent same-child witness
remains. -/
theorem
    literalCombinedFreshPhaseActivated_accepts_of_leftRightFlush_physicalAcceptance_of_semantic
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : OneRecurrent A strategy hwin package)
    (two : TwoRecurrent A strategy hwin package)
    (hsemantic :
      package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy hwin
        env n = (.inr one, .inr two))
    (flush :
      package.LiteralCombinedFreshPhaseActivatedLeftRightFlushWitness A
        strategy hwin env n one two)
    (physical :
      let actual :=
        package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
          hwin
      let actualWord := actual.globalMachine.globalMachineTraceWord
        actual.globalOutputOne actual.globalOutputTwo env
      let same := flush.sameChildOfSemantic A strategy hwin package hsemantic
      let unit := UnitKernel A strategy hwin package same.key
      A.FiniteGlobalMachinePhysicalAcceptanceFrom
        (A.run actualWord (n + 2))
        (unit.globalMachine.reroot same.unitState)
        unit.globalOutputOne unit.globalOutputTwo
        (OmegaWord.drop env (n + 2))) :
    A.Accepts
      ((package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
        hwin).globalMachine.globalMachineTraceWord
        (package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
          hwin).globalOutputOne
        (package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
          hwin).globalOutputTwo env) := by
  let atStart :=
    package.literalCombinedFreshPhaseActivatedSemanticTrace_sameChildAt A
      strategy hwin env n one two hsemantic
      ((package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
        hwin).globalMachine.globalStateTrace env n).1.2
      ((package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
        hwin).globalMachine.globalStateTrace env n).2.2
  exact
    package.literalCombinedFreshPhaseActivated_accepts_of_leftRightFlush_physicalAcceptance
      A strategy hwin env n one two flush atStart (by
        simpa [atStart,
          LiteralCombinedFreshPhaseActivatedLeftRightFlushWitness.sameChildOfSemantic]
          using physical)

/-! ## Persistent-reversal branch -/

/-- Local data sufficient to accept the fixed child reached after the relay
flush.  The finite chain preserves the selected policy's accepted lineage;
the member-aware slices then determine every later checker cut state by the
canonical close induction. -/
structure LiteralCombinedFreshPhaseActivatedFixedChildMemberSuffixBookkeeping
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (one : OneRecurrent A strategy hwin package)
    (two : TwoRecurrent A strategy hwin package)
    (hsemantic :
      package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy hwin
        env n = (.inr one, .inr two))
    (flush :
      package.LiteralCombinedFreshPhaseActivatedLeftRightFlushWitness A
        strategy hwin env n one two) : Type (max u v x y s) where
  acceptedSeed :
    ProfiledRawJointUnitFixedPolicyRoot A strategy
      ((package.literalRightSeamTaggedChildSource A strategy hwin
        (flush.sameChildOfSemantic A strategy hwin package hsemantic).key).code
          A)
      (package.literalRightSeamTaggedChildPolicy A strategy hwin
        (flush.sameChildOfSemantic A strategy hwin package hsemantic).key)
  current :
    ProfiledRawJointUnitFixedPolicyRoot A strategy
      ((package.literalRightSeamTaggedChildSource A strategy hwin
        (flush.sameChildOfSemantic A strategy hwin package hsemantic).key).code
          A)
      (package.literalRightSeamTaggedChildPolicy A strategy hwin
        (flush.sameChildOfSemantic A strategy hwin package hsemantic).key)
  acceptedSeed_state :
    ProfiledRawJointUnitFixedPolicyRoot.state A
        (package.literalRightSeamTaggedChildPolicy A strategy hwin
          (flush.sameChildOfSemantic A strategy hwin package hsemantic).key)
        acceptedSeed =
      (package.literalRightSeamTaggedChildPolicy A strategy hwin
        (flush.sameChildOfSemantic A strategy hwin package hsemantic).key).run
          []
  chain :
    ProfiledRawJointUnitFixedPolicyRoot.AlternatingPrefix A
      (package.literalRightSeamTaggedChildPolicy A strategy hwin
        (flush.sameChildOfSemantic A strategy hwin package hsemantic).key)
      acceptedSeed current
  initialRow : PairedEntryRow
  memberAt : Nat → Bool
  hterm : OperationalStrictRunsTerminate
    (profiledRawJointPhysicalGraphTail (OmegaWord.drop env (n + 2)) 0)
  slices :
    let actual :=
      package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
        hwin
    let actualWord := actual.globalMachine.globalMachineTraceWord
      actual.globalOutputOne actual.globalOutputTwo env
    let same := flush.sameChildOfSemantic A strategy hwin package hsemantic
    let unit := UnitKernel A strategy hwin package same.key
    ProfiledRawJointUnitCanonicalMemberStateRelativeSliceAlignment A strategy
      (package.literalRightSeamTaggedChildSource A strategy hwin same.key)
      (package.literalRightSeamTaggedChildPolicy A strategy hwin same.key)
      (package.literalRightSeamTaggedChildControllerBank A strategy hwin
        same.key)
      (OmegaWord.drop env (n + 2)) (A.run actualWord (n + 2))
      ((unit.globalMachine.reroot same.unitState).globalMachineTraceWord
        unit.globalOutputOne unit.globalOutputTwo
        (OmegaWord.drop env (n + 2)))
      hterm current initialRow memberAt

namespace LiteralCombinedFreshPhaseActivatedFixedChildMemberSuffixBookkeeping

/-- The bookkeeping package closes the exact fixed-child suffix premise of
the phase-activated handoff. -/
theorem acceptsFrom
    {package : Package A strategy hwin (initial := initial)}
    {env : EnvironmentSequence In₁ In₂} {n : Nat}
    {one : OneRecurrent A strategy hwin package}
    {two : TwoRecurrent A strategy hwin package}
    {hsemantic :
      package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy hwin
        env n = (.inr one, .inr two)}
    {flush :
      package.LiteralCombinedFreshPhaseActivatedLeftRightFlushWitness A
        strategy hwin env n one two}
    (bookkeeping :
      package.LiteralCombinedFreshPhaseActivatedFixedChildMemberSuffixBookkeeping
        A strategy hwin env n one two hsemantic flush) :
    let actual :=
      package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
        hwin
    let actualWord := actual.globalMachine.globalMachineTraceWord
      actual.globalOutputOne actual.globalOutputTwo env
    let same := flush.sameChildOfSemantic A strategy hwin package hsemantic
    let unit := UnitKernel A strategy hwin package same.key
    A.AcceptsFrom (A.run actualWord (n + 2))
      ((unit.globalMachine.reroot same.unitState).globalMachineTraceWord
        unit.globalOutputOne unit.globalOutputTwo
        (OmegaWord.drop env (n + 2))) := by
  dsimp only
  exact bookkeeping.slices.acceptsFrom_of_prefix A strategy
    (package.literalRightSeamTaggedChildSource A strategy hwin
      (flush.sameChildOfSemantic A strategy hwin package hsemantic).key)
    (package.literalRightSeamTaggedChildPolicy A strategy hwin
      (flush.sameChildOfSemantic A strategy hwin package hsemantic).key)
    (package.literalRightSeamTaggedChildControllerBank A strategy hwin
      (flush.sameChildOfSemantic A strategy hwin package hsemantic).key)
    bookkeeping.acceptedSeed_state bookkeeping.chain

end LiteralCombinedFreshPhaseActivatedFixedChildMemberSuffixBookkeeping

/-- Persistent strict reversal automatically supplies the recurrent cut, the
two-receive physical flush, and the same-child witness.  Consequently the
only remaining premise in this graph regime is acceptance of the actual
reached fixed-child suffix from the actual post-prefix checker state. -/
theorem
    literalCombinedFreshPhaseActivated_accepts_of_persistentReversal_of_fixedChildSuffix
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂)
    (hreversal :
      PersistentStrictReversalTail (fun n ↦ (env n).graph))
    (hunit :
      ∀ (n : Nat) (one : OneRecurrent A strategy hwin package)
        (two : TwoRecurrent A strategy hwin package)
        (hsemantic :
          package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy
            hwin env n = (.inr one, .inr two))
        (flush :
          package.LiteralCombinedFreshPhaseActivatedLeftRightFlushWitness A
            strategy hwin env n one two),
        let actual :=
          package.literalCombinedFreshPhaseActivatedPhysicalController A
            strategy hwin
        let actualWord := actual.globalMachine.globalMachineTraceWord
          actual.globalOutputOne actual.globalOutputTwo env
        let same :=
          flush.sameChildOfSemantic A strategy hwin package hsemantic
        let unit := UnitKernel A strategy hwin package same.key
        A.AcceptsFrom (A.run actualWord (n + 2))
          ((unit.globalMachine.reroot same.unitState).globalMachineTraceWord
            unit.globalOutputOne unit.globalOutputTwo
            (OmegaWord.drop env (n + 2)))) :
    A.Accepts
      ((package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
        hwin).globalMachine.globalMachineTraceWord
        (package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
          hwin).globalOutputOne
        (package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
          hwin).globalOutputTwo env) := by
  rcases
      package.exists_literalCombinedFreshPhaseActivatedLeftRightFlushWitness_of_persistentReversal
        A strategy hwin env hreversal with
    ⟨n, one, two, hsemantic, ⟨flush⟩⟩
  exact
    package.literalCombinedFreshPhaseActivated_accepts_of_leftRightFlush_unitAcceptsFrom_of_semantic
      A strategy hwin env n one two hsemantic flush
        (hunit n one two hsemantic flush)

/-- Persistent reversal reduced to finite selected-policy lineage plus the
two local trace equations (open records and member-aware closing record) at
each canonical close.  Future checker entry states are no longer assumptions. -/
theorem
    literalCombinedFreshPhaseActivated_accepts_of_persistentReversal_of_memberSlices
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂)
    (hreversal :
      PersistentStrictReversalTail (fun n ↦ (env n).graph))
    (hbookkeeping :
      ∀ (n : Nat) (one : OneRecurrent A strategy hwin package)
        (two : TwoRecurrent A strategy hwin package)
        (hsemantic :
          package.literalCombinedFreshPhaseActivatedSemanticTrace A strategy
            hwin env n = (.inr one, .inr two))
        (flush :
          package.LiteralCombinedFreshPhaseActivatedLeftRightFlushWitness A
            strategy hwin env n one two),
        package.LiteralCombinedFreshPhaseActivatedFixedChildMemberSuffixBookkeeping
          A strategy hwin env n one two hsemantic flush) :
    A.Accepts
      ((package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
        hwin).globalMachine.globalMachineTraceWord
        (package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
          hwin).globalOutputOne
        (package.literalCombinedFreshPhaseActivatedPhysicalController A strategy
          hwin).globalOutputTwo env) := by
  apply
    package.literalCombinedFreshPhaseActivated_accepts_of_persistentReversal_of_fixedChildSuffix
      A strategy hwin env hreversal
  intro n one two hsemantic flush
  exact (hbookkeeping n one two hsemantic flush).acceptsFrom A strategy hwin

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
