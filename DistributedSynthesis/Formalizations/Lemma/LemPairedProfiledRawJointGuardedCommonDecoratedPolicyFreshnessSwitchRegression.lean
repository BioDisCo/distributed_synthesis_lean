/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonDecoratedPolicyFreshnessCarrier

/-!
# Alternating-switch regression for the local freshness carrier

The shortest stale-copy counterexample to a key-only implementation is two
strict rounds in one direction followed by one strict round in the other.
After the first two rounds the blind endpoint still stores the old policy
copy; at the switch it must use the finite copy delivered by its partner.

These two symbolic regression lemmas calculate both orientations.  They are
uniform in the automaton, strategy, policy state, and inputs.  Thus they test
the actual finite local-event mechanism rather than a special finite model.
The executable transitions see only receive/no-receive and delivered finite
controls; neither graph orientation nor a leader bit is an argument.
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

private abbrev Package (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy hwin initial
    (CrossValid A strategy hwin)

private abbrev State :=
  ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin initial
    (CrossValid A strategy hwin)

/-- After `right,right,left`, process one advances the copy delivered by
process two, not its own stale initial copy.  The current state has advanced
exactly three policy letters. -/
theorem decoratedFreshness_right_right_left_switch
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (input₀ input₁ input₂ : In₁ × In₂) :
    let start := decoratedFreshnessBothInitial A strategy hwin state
    let after₀ := decoratedFreshnessLocalStep A strategy hwin package
      start.1 start.2 input₀ .right
    let after₁ := decoratedFreshnessLocalStep A strategy hwin package
      after₀.1 after₀.2 input₁ .right
    let after₂ := decoratedFreshnessLocalStep A strategy hwin package
      after₁.1 after₁.2 input₂ .left
    after₂.1.1 = package.policy.successor after₁.2.1 input₂ ∧
      decoratedFreshnessCurrent A strategy hwin after₂.1 after₂.2 =
        package.policy.successor
          (package.policy.successor
            (package.policy.successor state input₀) input₁) input₂ := by
  constructor <;> rfl

/-- Mirror regression: after `left,left,right`, process two advances the copy
delivered by process one and the current state again moves by exactly three
policy letters. -/
theorem decoratedFreshness_left_left_right_switch
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (input₀ input₁ input₂ : In₁ × In₂) :
    let start := decoratedFreshnessBothInitial A strategy hwin state
    let after₀ := decoratedFreshnessLocalStep A strategy hwin package
      start.1 start.2 input₀ .left
    let after₁ := decoratedFreshnessLocalStep A strategy hwin package
      after₀.1 after₀.2 input₁ .left
    let after₂ := decoratedFreshnessLocalStep A strategy hwin package
      after₁.1 after₁.2 input₂ .right
    after₂.2.1 = package.policy.successor after₁.1.1 input₂ ∧
      decoratedFreshnessCurrent A strategy hwin after₂.1 after₂.2 =
        package.policy.successor
          (package.policy.successor
            (package.policy.successor state input₀) input₁) input₂ := by
  constructor <;> rfl

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
