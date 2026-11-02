/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointUnitPolicyLocalHandoff

/-!
# Matched recurrent phases for the singleton raw-joint policy

These constructors are proof-level synchronization witnesses between the two
independent finite local controls.  They are not a shared runtime mode and do
not tell either process which side is currently informed.  Interior closure
uses only the two local step functions and preserves the common policy macro.
-/

namespace DistributedSynthesis

universe u v x y s

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

/-- Proof-level synchronized recurrent configurations.  The equality is the
only coupling: both local controls carry one literally common finite macro. -/
inductive ProfiledRawJointUnitPolicyMatchedPhase
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    where
  | right
      (owner : ProfiledRawJointUnitRightPolicyOwnerControl A strategy initial
        policy bank)
      (receiver : ProfiledRawJointUnitRightPolicyReceiverControl A strategy
        initial policy)
      (sameSource : owner.1 = receiver.1)
  | left
      (receiver : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy
        initial policy)
      (owner : ProfiledRawJointUnitLeftPolicyOwnerControl A strategy initial
        policy bank)
      (sameSource : receiver.1 = owner.1)

/-- One interior physical round.  The proof-level orientation only selects
which already-local transition is used; it is not an argument to either local
transition function. -/
noncomputable def ProfiledRawJointUnitPolicyMatchedPhase.continue
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)}
    {policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A)}
    {bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy}
    (phase : ProfiledRawJointUnitPolicyMatchedPhase A strategy initial policy
      bank) (move : In₁ × In₂) :
    (Out₁ × Out₂) ×
      ProfiledRawJointUnitPolicyMatchedPhase A strategy initial policy bank :=
  match phase with
  | .right owner receiver sameSource =>
      let one := stepProfiledRawJointUnitRightPolicyOwner A strategy initial
        policy bank owner move.1
      let two := continueProfiledRawJointUnitRightPolicyReceiver A strategy
        initial policy bank receiver owner (move.2, move.1)
      ((one.1, two.1), .right one.2 two.2 (by
        rw [stepProfiledRawJointUnitRightPolicyOwner_source,
          continueProfiledRawJointUnitRightPolicyReceiver_source]
        exact sameSource))
  | .left receiver owner sameSource =>
      let one := continueProfiledRawJointUnitLeftPolicyReceiver A strategy
        initial policy bank receiver owner move
      let two := stepProfiledRawJointUnitLeftPolicyOwner A strategy initial
        policy bank owner move.2
      ((one.1, two.1), .left one.2 two.2 (by
        rw [continueProfiledRawJointUnitLeftPolicyReceiver_source,
          stepProfiledRawJointUnitLeftPolicyOwner_source]
        exact sameSource))

/-- Initialize a synchronized right phase from one common macro. -/
noncomputable def profiledRawJointUnitInitialMatchedRight
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy (initial.code A)
      policy) (row : PairedEntryRow) :
    ProfiledRawJointUnitPolicyMatchedPhase A strategy initial policy bank :=
  .right
    (initialProfiledRawJointUnitRightPolicyOwner A strategy initial policy bank
      source)
    (initialProfiledRawJointUnitRightPolicyReceiver A strategy initial policy
      source row)
    rfl

/-- Initialize a synchronized left phase from one common macro. -/
noncomputable def profiledRawJointUnitInitialMatchedLeft
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy (initial.code A)
      policy) (row : PairedEntryRow) :
    ProfiledRawJointUnitPolicyMatchedPhase A strategy initial policy bank :=
  .left
    (initialProfiledRawJointUnitLeftPolicyReceiver A strategy initial policy
      source row)
    (initialProfiledRawJointUnitLeftPolicyOwner A strategy initial policy bank
      source)
    rfl

end

end DetParityAutomaton

end DistributedSynthesis
