/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenIndexedPolicyUniformityGate
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenIndexedCodeParity

/-!
# Local-uniformity gate for the code-observable indexed policy

This specializes the pair-output audit to the locality-safe parity
presentation.  Its objective DPA reads only the finite child belief code, so
there is no remaining raw-direction congruence premise.  The only gate left
is genuinely operational: policy states that can coexist in one reachable
local belief must admit output-compatible simultaneous tables.
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

variable [Fintype I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

abbrev ProfiledOpenIndexedCodeRationalPolicy
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)) :=
  SourceFreeBeliefCodeParityRationalPolicy
    (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode)
    initialCode
    (ProfiledOpenIndexedBiBeliefValid A)
    (profiledOpenIndexedBiBeliefNext A)

abbrev ProfiledOpenIndexedCodePolicyState
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)) :=
  (profiledOpenIndexedBiBeliefCodeRunAutomaton A initialCode).State

def ProfiledOpenIndexedCodePolicyMoveRealizesAt
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (policy : ProfiledOpenIndexedCodeRationalPolicy A initialCode)
    (state : ProfiledOpenIndexedCodePolicyState A initialCode)
    (move : ProfiledOpenIndexedBiBeliefMove A) : Prop :=
  SourceFreeBeliefCodeParityRationalPolicy.MoveRealizesAt
    (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode)
    initialCode
    (ProfiledOpenIndexedBiBeliefValid A)
    (profiledOpenIndexedBiBeliefNext A)
    policy state move

/-- Exact remaining pair-output gate after the monitor has been made
child-code observable. -/
def ProfiledOpenIndexedCodePolicyPairOutputCoherentOn
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (policy : ProfiledOpenIndexedCodeRationalPolicy A initialCode)
    (CanCooccur : ProfiledOpenIndexedCodePolicyState A initialCode →
      ProfiledOpenIndexedCodePolicyState A initialCode → Prop) : Prop :=
  ∀ leftState rightState,
    CanCooccur leftState rightState →
      ∃ leftMove rightMove,
        ProfiledOpenIndexedCodePolicyMoveRealizesAt A initialCode policy
            leftState leftMove ∧
          ProfiledOpenIndexedCodePolicyMoveRealizesAt A initialCode policy
            rightState rightMove ∧
          ProfiledOpenIndexedInitialOutputPairCoherent A leftState.1
            rightState.1 leftMove rightMove

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Every realizing move still has the unconditional within-table T1 law. -/
theorem profiledOpenIndexedCodePolicyMove_t1
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (policy : ProfiledOpenIndexedCodeRationalPolicy A initialCode)
    (state : ProfiledOpenIndexedCodePolicyState A initialCode)
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (hmove : ProfiledOpenIndexedCodePolicyMoveRealizesAt A initialCode policy
      state move) :
    ProfiledOpenIndexedBiBeliefT1 A state.1 move :=
  profiledOpenIndexedBiBeliefT1_of_valid A state.1 move hmove.1

/-- Fail-fast certificate for a reachable pair separated by every pair of
policy-realizing moves. -/
structure ProfiledOpenIndexedCodePolicyPairOutputCollision
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (policy : ProfiledOpenIndexedCodeRationalPolicy A initialCode)
    (CanCooccur : ProfiledOpenIndexedCodePolicyState A initialCode →
      ProfiledOpenIndexedCodePolicyState A initialCode → Prop) where
  leftState : ProfiledOpenIndexedCodePolicyState A initialCode
  rightState : ProfiledOpenIndexedCodePolicyState A initialCode
  cooccurs : CanCooccur leftState rightState
  separated :
    ∀ leftMove rightMove,
      ProfiledOpenIndexedCodePolicyMoveRealizesAt A initialCode policy
          leftState leftMove →
        ProfiledOpenIndexedCodePolicyMoveRealizesAt A initialCode policy
            rightState rightMove →
          ¬ ProfiledOpenIndexedInitialOutputPairCoherent A leftState.1
            rightState.1 leftMove rightMove

omit [Inhabited In₁] [Inhabited In₂] in
theorem not_profiledOpenIndexedCodePolicyPairOutputCoherentOn_of_collision
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (policy : ProfiledOpenIndexedCodeRationalPolicy A initialCode)
    (CanCooccur : ProfiledOpenIndexedCodePolicyState A initialCode →
      ProfiledOpenIndexedCodePolicyState A initialCode → Prop)
    (collision : ProfiledOpenIndexedCodePolicyPairOutputCollision A
      initialCode policy CanCooccur) :
    ¬ ProfiledOpenIndexedCodePolicyPairOutputCoherentOn A initialCode policy
      CanCooccur := by
  intro hcoherent
  rcases hcoherent collision.leftState collision.rightState
      collision.cooccurs with ⟨leftMove, rightMove, hleft, hright, hagree⟩
  exact collision.separated leftMove rightMove hleft hright hagree

end

end DetParityAutomaton

end DistributedSynthesis
