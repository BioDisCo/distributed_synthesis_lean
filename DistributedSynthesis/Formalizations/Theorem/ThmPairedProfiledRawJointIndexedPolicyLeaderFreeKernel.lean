/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointUnitPolicyLeaderFreeKernel

/-!
# A finite indexed family of recurrent raw-joint policies

The fixed-policy leader-free kernel already supplies the exact recurrent
transition table below one rational provenance policy.  The hybrid root
construction can install any member of a finite family of such policies.
This module packages that harmless dependent indexing once and for all.

The two continuing receive transitions see controls carrying potentially
different indices because the generic physical carrier is total.  When the
indices agree we use the delivered, progressed owner exactly.  When they do
not agree, the tuple is outside the synchronized invariant; we restart a
canonical owner at the receiver's source merely to make the local function
total.  No correctness statement uses that mismatch branch.  All other
recurrent transitions already select their next policy from the receiver
whose staged target they consume.

There is no graph, orientation, or strict-leader argument anywhere in this
adapter.
-/

namespace DistributedSynthesis

universe u v x y s k i₁ i₂ e₁ e₂

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
  (ChildCode : Type k)
  (source : ChildCode →
    ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
  (policy : (key : ChildCode) →
    ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      ((source key).code A))
  (bank : (key : ChildCode) →
    ProfiledRawJointUnitPolicyControllerBank A strategy (source key)
      (policy key))

/-! ## The four dependent recurrent control families -/

abbrev ProfiledRawJointIndexedPolicyRightOwner (key : ChildCode) :=
  ProfiledRawJointUnitPolicyRightOwner A strategy (source key) (policy key)
    (bank key) ()

abbrev ProfiledRawJointIndexedPolicyLeftReceiver (key : ChildCode) :=
  ProfiledRawJointUnitPolicyLeftReceiver A strategy (source key) (policy key) ()

abbrev ProfiledRawJointIndexedPolicyRightReceiver (key : ChildCode) :=
  ProfiledRawJointUnitPolicyRightReceiver A strategy (source key) (policy key) ()

abbrev ProfiledRawJointIndexedPolicyLeftOwner (key : ChildCode) :=
  ProfiledRawJointUnitPolicyLeftOwner A strategy (source key) (policy key)
    (bank key) ()

abbrev ProfiledRawJointIndexedPolicyOneControl
    (InitialOne : Type i₁) (ExceptionalOne : Type e₁) :=
  ProfiledRawJointLeaderFreeOneControl InitialOne ExceptionalOne ChildCode
    (ProfiledRawJointIndexedPolicyRightOwner A strategy ChildCode source policy
      bank)
    (ProfiledRawJointIndexedPolicyLeftReceiver A strategy ChildCode source
      policy)

abbrev ProfiledRawJointIndexedPolicyTwoControl
    (InitialTwo : Type i₂) (ExceptionalTwo : Type e₂) :=
  ProfiledRawJointLeaderFreeTwoControl InitialTwo ExceptionalTwo ChildCode
    (ProfiledRawJointIndexedPolicyRightReceiver A strategy ChildCode source
      policy)
    (ProfiledRawJointIndexedPolicyLeftOwner A strategy ChildCode source policy
      bank)

/-! ## The finite-front adapter -/

/-- Root and exceptional maps needed above a finite indexed recurrent family.
They are executable data, not semantic hypotheses. -/
structure ProfiledRawJointIndexedPolicyExceptionalAdapter
    (InitialOne : Type i₁) (InitialTwo : Type i₂)
    (ExceptionalOne : Type e₁) (ExceptionalTwo : Type e₂) where
  initialOne : InitialOne
  initialTwo : InitialTwo
  initialOutputOne : Out₁
  initialOutputTwo : Out₂
  initialNoRecvOne : InitialOne → In₁ → Out₁ ×
    ProfiledRawJointIndexedPolicyOneControl A strategy ChildCode source policy
      bank InitialOne ExceptionalOne
  exceptionalNoRecvOne : ExceptionalOne → In₁ → Out₁ ×
    ProfiledRawJointIndexedPolicyOneControl A strategy ChildCode source policy
      bank InitialOne ExceptionalOne
  initialNoRecvTwo : InitialTwo → In₂ → Out₂ ×
    ProfiledRawJointIndexedPolicyTwoControl A strategy ChildCode source policy
      bank InitialTwo ExceptionalTwo
  exceptionalNoRecvTwo : ExceptionalTwo → In₂ → Out₂ ×
    ProfiledRawJointIndexedPolicyTwoControl A strategy ChildCode source policy
      bank InitialTwo ExceptionalTwo
  otherRecvOne :
    ProfiledRawJointIndexedPolicyOneControl A strategy ChildCode source policy
        bank InitialOne ExceptionalOne → In₁ →
      ProfiledRawJointIndexedPolicyTwoControl A strategy ChildCode source
        policy bank InitialTwo ExceptionalTwo → In₂ →
      Out₁ × ProfiledRawJointIndexedPolicyOneControl A strategy ChildCode
        source policy bank InitialOne ExceptionalOne
  otherRecvTwo :
    ProfiledRawJointIndexedPolicyTwoControl A strategy ChildCode source policy
        bank InitialTwo ExceptionalTwo → In₂ →
      ProfiledRawJointIndexedPolicyOneControl A strategy ChildCode source
        policy bank InitialOne ExceptionalOne → In₁ →
      Out₂ × ProfiledRawJointIndexedPolicyTwoControl A strategy ChildCode
        source policy bank InitialTwo ExceptionalTwo

/-! ## The two equality-sensitive continuing receives -/

/-- Continue a right receiver with the genuinely delivered owner when its
policy key agrees.  The mismatch fallback is unreachable from a synchronized
matched-right phase. -/
noncomputable def profiledRawJointIndexedPolicyContinueRightReceiver
    [DecidableEq ChildCode]
    (receiverKey rightKey : ChildCode)
    (receiver : ProfiledRawJointIndexedPolicyRightReceiver A strategy
      ChildCode source policy receiverKey)
    (owner : ProfiledRawJointIndexedPolicyRightOwner A strategy ChildCode
      source policy bank rightKey)
    (move : In₂ × In₁) :
    Out₂ × (Σ next : ChildCode,
      ProfiledRawJointIndexedPolicyRightReceiver A strategy ChildCode source
        policy next) := by
  classical
  by_cases h : receiverKey = rightKey
  · subst rightKey
    let next := continueProfiledRawJointUnitRightPolicyReceiver A strategy
      (source receiverKey) (policy receiverKey) (bank receiverKey) receiver
      owner move
    exact (next.1, ⟨receiverKey, next.2⟩)
  · let fallbackOwner :=
      initialProfiledRawJointUnitRightPolicyOwner A strategy
        (source receiverKey) (policy receiverKey) (bank receiverKey) receiver.1
    let next := continueProfiledRawJointUnitRightPolicyReceiver A strategy
      (source receiverKey) (policy receiverKey) (bank receiverKey) receiver
      fallbackOwner move
    exact (next.1, ⟨receiverKey, next.2⟩)

/-- Left-oriented mirror of the equality-sensitive continuing receive. -/
noncomputable def profiledRawJointIndexedPolicyContinueLeftReceiver
    [DecidableEq ChildCode]
    (receiverKey leftKey : ChildCode)
    (receiver : ProfiledRawJointIndexedPolicyLeftReceiver A strategy ChildCode
      source policy receiverKey)
    (owner : ProfiledRawJointIndexedPolicyLeftOwner A strategy ChildCode source
      policy bank leftKey)
    (move : In₁ × In₂) :
    Out₁ × (Σ next : ChildCode,
      ProfiledRawJointIndexedPolicyLeftReceiver A strategy ChildCode source
        policy next) := by
  classical
  by_cases h : receiverKey = leftKey
  · subst leftKey
    let next := continueProfiledRawJointUnitLeftPolicyReceiver A strategy
      (source receiverKey) (policy receiverKey) (bank receiverKey) receiver
      owner move
    exact (next.1, ⟨receiverKey, next.2⟩)
  · let fallbackOwner :=
      initialProfiledRawJointUnitLeftPolicyOwner A strategy
        (source receiverKey) (policy receiverKey) (bank receiverKey) receiver.1
    let next := continueProfiledRawJointUnitLeftPolicyReceiver A strategy
      (source receiverKey) (policy receiverKey) (bank receiverKey) receiver
      fallbackOwner move
    exact (next.1, ⟨receiverKey, next.2⟩)

/-! ## Complete indexed kernel -/

/-- Lift the fixed-policy recurrent table pointwise over a finite child key.
The only non-pointwise cases are the two explicitly totalized continuing
receives above. -/
noncomputable def profiledRawJointIndexedPolicyLeaderFreeKernel
    [DecidableEq ChildCode]
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    (adapter : ProfiledRawJointIndexedPolicyExceptionalAdapter A strategy
      ChildCode source policy bank InitialOne InitialTwo ExceptionalOne
      ExceptionalTwo) :
    ProfiledRawJointLeaderFreeKernel In₁ In₂ Out₁ Out₂ InitialOne
      InitialTwo ExceptionalOne ExceptionalTwo ChildCode
      (ProfiledRawJointIndexedPolicyRightOwner A strategy ChildCode source
        policy bank)
      (ProfiledRawJointIndexedPolicyLeftReceiver A strategy ChildCode source
        policy)
      (ProfiledRawJointIndexedPolicyRightReceiver A strategy ChildCode source
        policy)
      (ProfiledRawJointIndexedPolicyLeftOwner A strategy ChildCode source policy
        bank) where
  initialOne := adapter.initialOne
  initialTwo := adapter.initialTwo
  initialOutputOne := adapter.initialOutputOne
  initialOutputTwo := adapter.initialOutputTwo
  initialNoRecvOne := adapter.initialNoRecvOne
  exceptionalNoRecvOne := adapter.exceptionalNoRecvOne
  rightOwnerNoRecvOne := fun key owner input =>
    stepProfiledRawJointUnitRightPolicyOwner A strategy (source key)
      (policy key) (bank key) owner input
  leftReceiverNoRecvOne := fun key receiver input =>
    let next := profiledRawJointUnitPolicyStartRightOwner A strategy
      (source key) (policy key) (bank key) receiver input
    (next.1, ⟨key, next.2⟩)
  initialNoRecvTwo := adapter.initialNoRecvTwo
  exceptionalNoRecvTwo := adapter.exceptionalNoRecvTwo
  rightReceiverNoRecvTwo := fun key receiver input =>
    let next := profiledRawJointUnitPolicyStartLeftOwner A strategy
      (source key) (policy key) (bank key) receiver input
    (next.1, ⟨key, next.2⟩)
  leftOwnerNoRecvTwo := fun key owner input =>
    stepProfiledRawJointUnitLeftPolicyOwner A strategy (source key)
      (policy key) (bank key) owner input
  matchedRightRecvOne := fun _ receiverKey _ inputOne receiver inputTwo =>
    let next := profiledRawJointUnitPolicyStartLeftReceiver A strategy
      (source receiverKey) (policy receiverKey) (bank receiverKey) receiver
      (inputOne, inputTwo)
    (next.1, ⟨receiverKey, next.2⟩)
  matchedRightRecvTwo := fun receiverKey rightKey receiver inputTwo owner
      inputOne =>
    profiledRawJointIndexedPolicyContinueRightReceiver A strategy ChildCode
      source policy bank receiverKey rightKey receiver owner
      (inputTwo, inputOne)
  matchedLeftRecvOne := fun receiverKey leftKey receiver inputOne owner
      inputTwo =>
    profiledRawJointIndexedPolicyContinueLeftReceiver A strategy ChildCode
      source policy bank receiverKey leftKey receiver owner
      (inputOne, inputTwo)
  matchedLeftRecvTwo := fun _ receiverKey _ inputTwo receiver inputOne =>
    let next := profiledRawJointUnitPolicyStartRightReceiver A strategy
      (source receiverKey) (policy receiverKey) (bank receiverKey) receiver
      (inputTwo, inputOne)
    (next.1, ⟨receiverKey, next.2⟩)
  crossRecvOne := fun _ rightKey _ inputOne right inputTwo =>
    let next := profiledRawJointUnitPolicyStartLeftReceiver A strategy
      (source rightKey) (policy rightKey) (bank rightKey) right
      (inputOne, inputTwo)
    (next.1, ⟨rightKey, next.2⟩)
  crossRecvTwo := fun _ leftKey _ inputTwo left inputOne =>
    let next := profiledRawJointUnitPolicyStartRightReceiver A strategy
      (source leftKey) (policy leftKey) (bank leftKey) left
      (inputTwo, inputOne)
    (next.1, ⟨leftKey, next.2⟩)
  otherRecvOne := adapter.otherRecvOne
  otherRecvTwo := adapter.otherRecvTwo

end

end DetParityAutomaton

end DistributedSynthesis
