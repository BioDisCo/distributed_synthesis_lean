/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonDecoratedPolicyFreshnessCarrier

/-!
# Local source selected by a freshness receive

A receiving endpoint must retain both the source policy state and its
successor: the source indexes the fresh literal seam, while the successor is
the new local freshness state.  This file names the two endpoint-local source
selectors already implicit in `decoratedFreshnessRecvOne/Two` and proves that
they denote the unique proof-side current state whenever freshness is aligned.

The selectors use only the receiver's stored phase and the delivered finite
partner control.  They receive no graph, hierarchy side, or leader bit.
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

namespace ProfiledRawJointGuardedCommonDecoratedPolicyPackage

variable {initial : CommonPoint A strategy}

private abbrev FreshOne :=
  ProfiledRawJointGuardedCommonDecoratedFreshnessOneState A strategy hwin
    initial

private abbrev FreshTwo :=
  ProfiledRawJointGuardedCommonDecoratedFreshnessTwoState A strategy hwin
    initial

private abbrev State :=
  ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin initial
    (ProfiledRawJointGuardedCommonLiteralCrossExtraValid A strategy hwin)

/-- The source used by a process-one receive. -/
def decoratedFreshnessRecvOneSource
    (one : FreshOne A strategy hwin (initial := initial))
    (two : FreshTwo A strategy hwin (initial := initial)) :
    State A strategy hwin (initial := initial) :=
  if one.2 then one.1 else two.1

/-- The mirror source used by a process-two receive. -/
def decoratedFreshnessRecvTwoSource
    (two : FreshTwo A strategy hwin (initial := initial))
    (one : FreshOne A strategy hwin (initial := initial)) :
    State A strategy hwin (initial := initial) :=
  if two.2 then one.1 else two.1

/-- Process one's local source is definitionally the proof-side current
policy copy. -/
@[simp] theorem decoratedFreshnessRecvOneSource_eq_current
    (one : FreshOne A strategy hwin (initial := initial))
    (two : FreshTwo A strategy hwin (initial := initial)) :
    decoratedFreshnessRecvOneSource A strategy hwin one two =
      decoratedFreshnessCurrent A strategy hwin one two :=
  rfl

/-- Under the invariant, process two's differently oriented local test names
the same unique current copy. -/
theorem decoratedFreshnessRecvTwoSource_eq_current_of_aligned
    (one : FreshOne A strategy hwin (initial := initial))
    (two : FreshTwo A strategy hwin (initial := initial))
    (haligned : DecoratedFreshnessAligned A strategy hwin one two) :
    decoratedFreshnessRecvTwoSource A strategy hwin two one =
      decoratedFreshnessCurrent A strategy hwin one two := by
  rcases one with ⟨oneState, oneSide⟩
  rcases two with ⟨twoState, twoSide⟩
  cases oneSide <;> cases twoSide
  · rfl
  · exact False.elim haligned
  · change oneState = twoState at haligned
    simpa [decoratedFreshnessRecvTwoSource, decoratedFreshnessCurrent] using
      haligned.symm
  · rfl

/-- A process-one receive stores exactly one policy successor of its selected
local source. -/
@[simp] theorem decoratedFreshnessRecvOne_state
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial
        (ProfiledRawJointGuardedCommonLiteralCrossExtraValid A strategy hwin))
    (one : FreshOne A strategy hwin (initial := initial)) (own : In₁)
    (two : FreshTwo A strategy hwin (initial := initial)) (delivered : In₂) :
    (decoratedFreshnessRecvOne A strategy hwin package one own two
      delivered).1 =
      package.policy.successor
        (decoratedFreshnessRecvOneSource A strategy hwin one two)
        (own, delivered) :=
  rfl

/-- Process-two mirror. -/
@[simp] theorem decoratedFreshnessRecvTwo_state
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial
        (ProfiledRawJointGuardedCommonLiteralCrossExtraValid A strategy hwin))
    (two : FreshTwo A strategy hwin (initial := initial)) (own : In₂)
    (one : FreshOne A strategy hwin (initial := initial)) (delivered : In₁) :
    (decoratedFreshnessRecvTwo A strategy hwin package two own one
      delivered).1 =
      package.policy.successor
        (decoratedFreshnessRecvTwoSource A strategy hwin two one)
        (delivered, own) :=
  rfl

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
