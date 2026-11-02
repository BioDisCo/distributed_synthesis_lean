/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorCarrier
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralPhaseLiveCompatibleReadback
import DistributedSynthesis.Formalizations.Lemma.LemFiniteGlobalMachinePhysicalAcceptanceOfAccepts

/-!
# Readback from compatible successor-carrier tails

The acknowledged successor carrier produces a direct accepting physical word
once its exact cut audit is available.  This file connects that result to the
existing phase-live readback endpoint.

Only the two genuinely recurrent graph regimes need an infinite successor
carrier: recurring simultaneous communication and persistent strict
reversal.  The eventually fixed right and left regimes continue to use the
already proved live-stage tail cuts.  Thus no alternating cut stream is
silently demanded from an eventually fixed graph word.

The compatible policy and finite physical controller are selected before the
environment is quantified.  Carrier members, targets, cuts, and graph regimes
below are proof-side data.  No executable endpoint receives a graph,
orientation, hierarchy side, leader bit, strict-leader bit, history, or view.
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

private abbrev DefaultInitial
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂) :=
  literalCombinedFreshPendingOnlyDefaultInitial A strategy

private abbrev HybridInitial
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂) :=
  (DefaultInitial A strategy).world A strategy

private abbrev CompatiblePolicy
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)) :=
  ProfiledRawJointHybridPhysicalCompatibleRationalPolicy A strategy hwin
    (HybridInitial A strategy)

private abbrev DefaultPackage
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)) :=
  literalCombinedFreshPendingOnlyDefaultPackage A strategy hwin

private abbrev PhaseLiveController
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)) :=
  (DefaultPackage A strategy hwin
    ).literalCombinedFreshPhaseLiveRootPhysicalController A strategy hwin

private abbrev CarrierTail
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (policy : CompatiblePolicy A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) :=
  ProfiledRawJointHybridPhysicalCompatibleSuccessorCarrierCutTail A strategy
    hwin policy Unit
      (PhaseLiveController A strategy hwin).globalMachine
      (PhaseLiveController A strategy hwin).globalOutputOne
      (PhaseLiveController A strategy hwin).globalOutputTwo env

/-! ## Exact remaining per-environment package -/

/-- The two infinite compatible-carrier traces plus the existing fixed-tail
bookkeeping for one environment.

`Unit` is sufficient as the proof-side carrier payload here: the successor
key equations are independent of the operational payload's concrete
presentation.  A concrete controller may retain richer finite data and erase
it when constructing this audit. -/
structure LiteralCombinedFreshPhaseLiveCompatibleSuccessorCarrierBookkeeping
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (env : EnvironmentSequence In₁ In₂)
    (policy : CompatiblePolicy A strategy hwin) : Prop where
  recurrent : GraphBothRecurrent (fun n ↦ (env n).graph) →
    Nonempty (CarrierTail A strategy hwin policy env)
  reversal : PersistentStrictReversalTail (fun n ↦ (env n).graph) →
    Nonempty (CarrierTail A strategy hwin policy env)
  fixed :
    ProfiledRawJointGuardedCommonDecoratedPolicyPackage.LiteralCombinedFreshPhaseLiveStageFixedTailBookkeeping
      A strategy hwin (DefaultPackage A strategy hwin)
        (PhaseLiveController A strategy hwin) env

namespace
    LiteralCombinedFreshPhaseLiveCompatibleSuccessorCarrierBookkeeping

variable {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
variable {hwin : ∀ env : EnvironmentSequence In₁ In₂,
  A.Accepts (execution strategy env)}
variable {env : EnvironmentSequence In₁ In₂}
variable {policy : CompatiblePolicy A strategy hwin}

/-- Direct carrier acceptance fills the hard fields, while the live-stage
bookkeeping supplies the two eventually fixed fields. -/
noncomputable def physicalAcceptance
    (bookkeeping :
      LiteralCombinedFreshPhaseLiveCompatibleSuccessorCarrierBookkeeping A
        strategy hwin env policy) :
    A.FiniteGlobalMachinePhysicalAcceptance
      (PhaseLiveController A strategy hwin).globalMachine
      (PhaseLiveController A strategy hwin).globalOutputOne
      (PhaseLiveController A strategy hwin).globalOutputTwo env where
  recurrent := by
    intro hboth
    let tail := Classical.choice (bookkeeping.recurrent hboth)
    let direct := A.finiteGlobalMachinePhysicalAcceptance_of_accepts
      (PhaseLiveController A strategy hwin).globalMachine
      (PhaseLiveController A strategy hwin).globalOutputOne
      (PhaseLiveController A strategy hwin).globalOutputTwo env
      (tail.accepts A strategy hwin)
    exact direct.recurrent hboth
  alternatingTail := by
    intro hreversal
    let tail := Classical.choice (bookkeeping.reversal hreversal)
    let direct := A.finiteGlobalMachinePhysicalAcceptance_of_accepts
      (PhaseLiveController A strategy hwin).globalMachine
      (PhaseLiveController A strategy hwin).globalOutputOne
      (PhaseLiveController A strategy hwin).globalOutputTwo env
      (tail.accepts A strategy hwin)
    exact direct.alternatingTail hreversal
  strictRightTail := bookkeeping.fixed.fixedRight A strategy hwin
  strictLeftTail := bookkeeping.fixed.fixedLeft A strategy hwin

end LiteralCombinedFreshPhaseLiveCompatibleSuccessorCarrierBookkeeping

/-! ## Strategy-indexed readback -/

/-- The compatible policy is chosen once for a winning strategy.  Only the
proof-side carrier audits may depend on the environment. -/
def PerStrategyWinningLiteralCombinedFreshPhaseLiveCompatibleSuccessorCarrierBookkeeping :
    Prop :=
  ∀ (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (env : EnvironmentSequence In₁ In₂),
    LiteralCombinedFreshPhaseLiveCompatibleSuccessorCarrierBookkeeping A
      strategy hwin env
        (literalCombinedFreshPhaseLiveCompatiblePolicy A strategy hwin)

/-- Carrier bookkeeping is exactly sufficient for the existing phase-live
physical-acceptance endpoint. -/
theorem
    perStrategyWinningLiteralCombinedFreshPhaseLivePhysicalAcceptance_of_compatibleSuccessorCarrier
    (hcarrier :
      PerStrategyWinningLiteralCombinedFreshPhaseLiveCompatibleSuccessorCarrierBookkeeping
        A) :
    PerStrategyWinningLiteralCombinedFreshPhaseLivePhysicalAcceptance A := by
  intro strategy hwin
  dsimp only
  intro env
  let policy := literalCombinedFreshPhaseLiveCompatiblePolicy A strategy hwin
  let bookkeeping := hcarrier strategy hwin env
  exact ⟨bookkeeping.physicalAcceptance A⟩

/-- One-arrow local-summary extraction from the finite delayed carrier. -/
theorem exists_readbackUpgrade_of_phaseLiveCompatibleSuccessorCarrier
    (fallback : LocalSummaryAutomaton.{u, v,
      max (max (max (max s u) v) x) y} In₁ In₂)
    (hcarrier :
      PerStrategyWinningLiteralCombinedFreshPhaseLiveCompatibleSuccessorCarrierBookkeeping
        A) :
    ∃ M : LocalSummaryAutomaton.{u, v,
        max (max (max (max s u) v) x) y} In₁ In₂,
      M.ReadbackUpgrade (Out₁ := Out₁) (Out₂ := Out₂) A := by
  exact exists_readbackUpgrade_of_phaseLivePhysicalAcceptance A fallback
    (perStrategyWinningLiteralCombinedFreshPhaseLivePhysicalAcceptance_of_compatibleSuccessorCarrier
      A hcarrier)

end

end DetParityAutomaton

end DistributedSynthesis
