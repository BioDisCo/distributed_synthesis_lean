/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorDeferredHandlers
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorResolvedControllerReadback

/-!
# Readback endpoint for the concrete compatible-successor controller

The deferred handlers construct one finite local *probe* controller from six
finite initial/totalization values.  This file packages those values as one
seed and connects any proof of that controller's own four-regime bookkeeping
directly to `ReadbackUpgrade`.  It does not assert that the bookkeeping holds:
repeated same-direction receives require the retained phase-live receiver
overlay, and the common root requires a checked root-compatible first stage.

The seed is fixed once per winning strategy, before the environment is
quantified.  Its fields are finite local data only.  In particular no graph,
orientation, hierarchy side, leader bit, strict-leader bit, history, or view
is supplied to an executable transition.
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

private abbrev CompatiblePolicy
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleRationalPolicy A strategy hwin
    initial

private abbrev OneShared
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  ProfiledRawJointHybridPhysicalCompatibleFrontierOneShared.{u, v, x, y, s,
    max u v x y s} A strategy hwin policy

private abbrev TwoShared
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  ProfiledRawJointHybridPhysicalCompatibleFrontierTwoShared.{u, v, x, y, s,
    max u v x y s} A strategy hwin policy

private abbrev OnePayload
    {initial : ProfiledRawJointCommonBaseWorld A strategy} :=
  ProfiledRawJointHybridPhysicalCompatibleFrontierOnePayload A strategy hwin
    (initial := initial)

private abbrev TwoPayload
    {initial : ProfiledRawJointCommonBaseWorld A strategy} :=
  ProfiledRawJointHybridPhysicalCompatibleFrontierTwoPayload A strategy hwin
    (initial := initial)

private abbrev OnePending
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (OneShared A strategy hwin policy)
    (OnePayload A strategy hwin (initial := initial))

private abbrev TwoPending
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (TwoShared A strategy hwin policy)
    (TwoPayload A strategy hwin (initial := initial))

private abbrev LeftOutput
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleSuccessorLeftReceiverOutput A
    strategy hwin initial

private abbrev RightOutput
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleSuccessorRightReceiverOutput A
    strategy hwin initial

/-- All finite choices needed to totalize and initialize the concrete
deferred controller.  The proof that the totalization branches are
unreachable is already supplied by `DeferredHandlers`. -/
structure ProfiledRawJointHybridPhysicalCompatibleOperationalSeed
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (policy : CompatiblePolicy A strategy hwin initial) where
  initialOne : OnePending A strategy hwin policy
  initialTwo : TwoPending A strategy hwin policy
  fallbackOneShared : OneShared A strategy hwin policy
  fallbackTwoShared : TwoShared A strategy hwin policy
  fallbackLeft : PairedEntryRow × LeftOutput A strategy hwin initial
  fallbackRight : PairedEntryRow × RightOutput A strategy hwin initial

namespace ProfiledRawJointHybridPhysicalCompatibleOperationalSeed

variable {initial : ProfiledRawJointCommonBaseWorld A strategy}
variable {policy : CompatiblePolicy A strategy hwin initial}

/-- The actual finite local Moore controller determined by a seed. -/
noncomputable def controller
    (seed : ProfiledRawJointHybridPhysicalCompatibleOperationalSeed A strategy
      hwin initial policy) :=
  profiledRawJointHybridPhysicalCompatibleOperationalPhysicalController A
    strategy hwin policy seed.initialOne seed.initialTwo
      seed.fallbackOneShared seed.fallbackTwoShared seed.fallbackLeft
        seed.fallbackRight

end ProfiledRawJointHybridPhysicalCompatibleOperationalSeed

/-- Exact remaining positive premise for the concrete controller: one seed is
chosen per winning strategy, and the four regimes are proved for that same
controller's own physical word in every environment. -/
def PerStrategyWinningCompatibleSuccessorOperationalBookkeeping : Prop :=
  ∀ (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)),
    ∃ initial : ProfiledRawJointCommonBaseWorld A strategy,
      ∃ policy : CompatiblePolicy A strategy hwin initial,
        ∃ seed :
            ProfiledRawJointHybridPhysicalCompatibleOperationalSeed A
              strategy hwin initial policy,
          ∀ env : EnvironmentSequence In₁ In₂,
            LiteralCompatibleSuccessorResolvedControllerBookkeeping A strategy
              hwin initial policy (seed.controller A strategy hwin) env

/-- Concrete operational bookkeeping instantiates the machine-parametric
resolved-controller premise without any further construction. -/
theorem
    perStrategyWinningResolvedController_of_operationalBookkeeping
    (hoperational :
      PerStrategyWinningCompatibleSuccessorOperationalBookkeeping A) :
    PerStrategyWinningLiteralCompatibleSuccessorResolvedControllerBookkeeping.{u,
      v, x, y, s, max u v x y s} A := by
  intro strategy hwin
  obtain ⟨initial, policy, seed, hseed⟩ := hoperational strategy hwin
  exact ⟨initial, policy, seed.controller A strategy hwin, hseed⟩

/-- The concrete controller's four regime proofs yield the unconditional
finite readback object in one arrow. -/
theorem exists_readbackUpgrade_of_compatibleSuccessorOperationalBookkeeping
    (fallback : LocalSummaryAutomaton.{u, v, max u v x y s} In₁ In₂)
    (hoperational :
      PerStrategyWinningCompatibleSuccessorOperationalBookkeeping A) :
    ∃ M : LocalSummaryAutomaton.{u, v, max u v x y s} In₁ In₂,
      M.ReadbackUpgrade (Out₁ := Out₁) (Out₂ := Out₂) A := by
  exact exists_readbackUpgrade_of_resolvedSuccessorController A fallback
    (perStrategyWinningResolvedController_of_operationalBookkeeping A
      hoperational)

end

end DetParityAutomaton

end DistributedSynthesis
