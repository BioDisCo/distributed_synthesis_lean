/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingBankLiteralCrossTraceInvariant
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTwoRoundFront

/-!
# Honest two-round activation of a dependent acknowledged bank

The dependent bank has one finite fibre for every concrete seed/package.  Its
standalone paired controller accepts an arbitrary initial key only because a
`FinitePairedMealyController` must have initial controls.  That arbitrary key
must not be used by the model-facing construction.

This file closes the honest `both`/`both` entrance.  After the first receive,
each endpoint retains the same first input pair in its existing finite hybrid
shadow.  On the next receive, each endpoint reconstructs the same two-round
seed, emits the already verified literal common output, and installs a known
acknowledgement relay at the bank member selected by that seed.  The installed
relay pair satisfies the complete bank relation and arbitrary-depth blind-fork
invariant.

Only the initial values of `bankPairedMealyController` depend on its key.  Its
control types and four executable transition maps are definitionally
key-independent.  Consequently the activated controls enter one fixed finite
tail controller even though their honest bank key is learned only at the
second receive.

Every executable map below receives only a local first-round shadow, the
endpoint's current input, and the partner input delivered by the current
receive.  No map receives a graph, orientation, hierarchy side, leader bit,
strict-leader bit, history, or view.
-/

namespace DistributedSynthesis

universe u v x y s k c₁ c₂

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
  (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)

open FiniteAcknowledgedDelayedCarrier

namespace FiniteAcknowledgedDelayedCarrier.FiniteExactClosingBlindFamily

variable {Key : Type k} [Fintype Key]
variable
  (family : FiniteExactClosingBlindFamily.{u, v, x, y, k, c₁, c₂}
    (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
      Key)

private abbrev Seed := (In₁ × In₂) × (In₁ × In₂)

private abbrev Tail (fallback : Key) :=
  family.base.bankPairedMealyController fallback

/-! ## The tail really is independent of its arbitrary initial key -/

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂]

@[simp] theorem bankPairedMealyController_noRecvOne_key_independent
    (left right : Key) :
    (family.base.bankPairedMealyController left).noRecvOne =
      (family.base.bankPairedMealyController right).noRecvOne :=
  rfl

@[simp] theorem bankPairedMealyController_noRecvTwo_key_independent
    (left right : Key) :
    (family.base.bankPairedMealyController left).noRecvTwo =
      (family.base.bankPairedMealyController right).noRecvTwo :=
  rfl

@[simp] theorem bankPairedMealyController_recvOne_key_independent
    (left right : Key) :
    (family.base.bankPairedMealyController left).recvOne =
      (family.base.bankPairedMealyController right).recvOne :=
  rfl

@[simp] theorem bankPairedMealyController_recvTwo_key_independent
    (left right : Key) :
    (family.base.bankPairedMealyController left).recvTwo =
      (family.base.bankPairedMealyController right).recvTwo :=
  rfl

end

/-! ## Local activation maps -/

/-- Process one reconstructs the two-round seed from its retained first pair
and the input pair delivered by its current receive, emits the literal common
output, and enters the acknowledged bank at the corresponding key. -/
noncomputable def twoRoundBankActivateOne
    (fallback : Key) (keyOfSeed : Seed (In₁ := In₁) (In₂ := In₂) → Key)
    (state : ProfiledRawJointGuardedCommonTwoRoundSeedOne A strategy hwin
      controllers)
    (own : In₁) (delivered : In₂) :
    (Tail family fallback).OneControl × Out₁ :=
  let seed := (state.common.1, (own, delivered))
  ((family.base.bankPairedMealyController (keyOfSeed seed)).initialOne,
    profiledRawJointInitialCommonBothOutputOneOfReceive A strategy
      state.common.1 own delivered)

/-- Process-two mirror. -/
noncomputable def twoRoundBankActivateTwo
    (fallback : Key) (keyOfSeed : Seed (In₁ := In₁) (In₂ := In₂) → Key)
    (state : ProfiledRawJointGuardedCommonTwoRoundSeedTwo A strategy hwin
      controllers)
    (own : In₂) (delivered : In₁) :
    (Tail family fallback).TwoControl × Out₂ :=
  let seed := (state.common.1, (delivered, own))
  ((family.base.bankPairedMealyController (keyOfSeed seed)).initialTwo,
    profiledRawJointInitialCommonBothOutputTwoOfReceive A strategy
      state.common.1 own delivered)

/-! ## Honest simultaneous entrance -/

section
omit [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem twoRoundBankActivateOne_eq_honest
    (fallback : Key) (keyOfSeed : Seed (In₁ := In₁) (In₂ := In₂) → Key)
    (first current : In₁ × In₂) :
    twoRoundBankActivateOne A strategy hwin controllers family fallback
        keyOfSeed
        (profiledRawJointGuardedCommonTwoRoundFirstRecvOne A strategy hwin
          controllers () first.1 first.2).2 current.1 current.2 =
      ((family.base.bankPairedMealyController
          (keyOfSeed (first, current))).initialOne,
        profiledRawJointInitialCommonBothOutputOneOfReceive A strategy first
          current.1 current.2) :=
  rfl

@[simp] theorem twoRoundBankActivateTwo_eq_honest
    (fallback : Key) (keyOfSeed : Seed (In₁ := In₁) (In₂ := In₂) → Key)
    (first current : In₁ × In₂) :
    twoRoundBankActivateTwo A strategy hwin controllers family fallback
        keyOfSeed
        (profiledRawJointGuardedCommonTwoRoundFirstRecvTwo A strategy hwin
          controllers () first.2 first.1).2 current.2 current.1 =
      ((family.base.bankPairedMealyController
          (keyOfSeed (first, current))).initialTwo,
        profiledRawJointInitialCommonBothOutputTwoOfReceive A strategy first
          current.2 current.1) :=
  rfl

/-- The activation round emits exactly the already verified literal common
output pair. -/
@[simp] theorem twoRoundBankActivate_outputs_eq_literalBoth
    (fallback : Key) (keyOfSeed : Seed (In₁ := In₁) (In₂ := In₂) → Key)
    (first current : In₁ × In₂) :
    ((twoRoundBankActivateOne A strategy hwin controllers family fallback
        keyOfSeed
        (profiledRawJointGuardedCommonTwoRoundFirstRecvOne A strategy hwin
          controllers () first.1 first.2).2 current.1 current.2).2,
      (twoRoundBankActivateTwo A strategy hwin controllers family fallback
        keyOfSeed
        (profiledRawJointGuardedCommonTwoRoundFirstRecvTwo A strategy hwin
          controllers () first.2 first.1).2 current.2 current.1).2) =
      profiledRawJointInitialCommonBothOutput A strategy (first, current) :=
  rfl

/-- Both locally reconstructed controls are the known initial relays of the
same dependent bank fibre.  Hence the complete relation and arbitrary-depth
blind-fork invariant hold immediately after activation. -/
theorem twoRoundBankActivate_blindForkInvariant
    (fallback : Key) (keyOfSeed : Seed (In₁ := In₁) (In₂ := In₂) → Key)
    (first current : In₁ × In₂) :
    ExactClosingBlindForkInvariant family.base.BankRel family.BankBlindOne
      family.BankBlindTwo
      (twoRoundBankActivateOne A strategy hwin controllers family fallback
        keyOfSeed
        (profiledRawJointGuardedCommonTwoRoundFirstRecvOne A strategy hwin
          controllers () first.1 first.2).2 current.1 current.2).1
      (twoRoundBankActivateTwo A strategy hwin controllers family fallback
        keyOfSeed
        (profiledRawJointGuardedCommonTwoRoundFirstRecvTwo A strategy hwin
          controllers () first.2 first.1).2 current.2 current.1).1 := by
  change ExactClosingBlindForkInvariant family.base.BankRel
    family.BankBlindOne family.BankBlindTwo
      (⟨.known (family.base.bankInitialOne (keyOfSeed (first, current))),
        none⟩)
      (⟨.known (family.base.bankInitialTwo (keyOfSeed (first, current))),
        none⟩)
  exact (family.bankBlindForkLaws (keyOfSeed (first, current))).initial_invariant
    (family.base.bankInitialOne (keyOfSeed (first, current)))
    (family.base.bankInitialTwo (keyOfSeed (first, current)))
    family.base.bankNoRecvOne family.base.bankNoRecvTwo
    family.base.bankOpenRecvOne family.base.bankOpenRecvTwo
    family.base.bankClose family.base.BankRel family.BankBlindOne
    family.BankBlindTwo

/-- The selected underlying bank controls carry exactly the honest key. -/
theorem twoRoundBankActivate_selects_initials
    (fallback : Key) (keyOfSeed : Seed (In₁ := In₁) (In₂ := In₂) → Key)
    (first current : In₁ × In₂) :
    PairSelects
      (twoRoundBankActivateOne A strategy hwin controllers family fallback
        keyOfSeed
        (profiledRawJointGuardedCommonTwoRoundFirstRecvOne A strategy hwin
          controllers () first.1 first.2).2 current.1 current.2).1
      (twoRoundBankActivateTwo A strategy hwin controllers family fallback
        keyOfSeed
        (profiledRawJointGuardedCommonTwoRoundFirstRecvTwo A strategy hwin
          controllers () first.2 first.1).2 current.2 current.1).1
      (family.base.bankInitialOne (keyOfSeed (first, current)))
      (family.base.bankInitialTwo (keyOfSeed (first, current))) := by
  change PairSelects
    (⟨.known (family.base.bankInitialOne (keyOfSeed (first, current))), none⟩)
    (⟨.known (family.base.bankInitialTwo (keyOfSeed (first, current))), none⟩)
    (family.base.bankInitialOne (keyOfSeed (first, current)))
    (family.base.bankInitialTwo (keyOfSeed (first, current)))
  exact pairSelects_known_known _ _ none none

end

end FiniteAcknowledgedDelayedCarrier.FiniteExactClosingBlindFamily

end

end DetParityAutomaton

end DistributedSynthesis
