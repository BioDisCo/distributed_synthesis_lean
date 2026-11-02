/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorResolvedMemberStream
import DistributedSynthesis.Formalizations.Lemma.LemFiniteGlobalMachinePhysicalAcceptanceOfAccepts
import DistributedSynthesis.Formalizations.Lemma.LemFinitePairedPhysicalControllerReadback

/-!
# Readback for the finite controller carrying resolved successor packets

The compatible deferred family constructs a new finite local controller.  Its
acceptance proof must therefore refer to that controller's own physical word,
not to a different controller with a different control type.  This file is
the machine-parametric endpoint.

For the two productive hard regimes, a resolved-member stream supplies direct
acceptance.  The two eventually fixed regimes supply their usual DPA tail
parity for the same controller.  The resulting physical-acceptance package is
then consumed by the generic finite-paired-controller readback theorem.
-/

namespace DistributedSynthesis

universe u v x y s w

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

private abbrev CompatiblePolicy
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleRationalPolicy A strategy hwin
    initial

private abbrev ResolvedStream
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (policy : CompatiblePolicy A strategy hwin initial)
    (controller :
      FinitePairedPhysicalController.{u, v, x, y, w, w}
        In₁ In₂ Out₁ Out₂)
    (env : EnvironmentSequence In₁ In₂) :=
  ProfiledRawJointHybridPhysicalCompatibleResolvedMemberStream A strategy hwin
    policy controller.globalMachine controller.globalOutputOne
      controller.globalOutputTwo env

/-- Complete per-environment acceptance data for the newly constructed local
controller.  Every field refers to this one controller's physical word. -/
structure LiteralCompatibleSuccessorResolvedControllerBookkeeping
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (policy : CompatiblePolicy A strategy hwin initial)
    (controller :
      FinitePairedPhysicalController.{u, v, x, y, w, w}
        In₁ In₂ Out₁ Out₂)
    (env : EnvironmentSequence In₁ In₂) : Prop where
  recurrent : GraphBothRecurrent (fun n ↦ (env n).graph) →
    Nonempty (ResolvedStream A strategy hwin initial policy controller env)
  reversal : PersistentStrictReversalTail (fun n ↦ (env n).graph) →
    Nonempty (ResolvedStream A strategy hwin initial policy controller env)
  strictRight : EventuallyStrictRight (fun n ↦ (env n).graph) →
    ∃ start : Nat, NatSeqMinEvenParity
      (fun n ↦ A.priority
        (A.run
          (controller.globalMachine.globalMachineTraceWord
            controller.globalOutputOne controller.globalOutputTwo env)
          (start + n)))
  strictLeft : EventuallyStrictLeft (fun n ↦ (env n).graph) →
    ∃ start : Nat, NatSeqMinEvenParity
      (fun n ↦ A.priority
        (A.run
          (controller.globalMachine.globalMachineTraceWord
            controller.globalOutputOne controller.globalOutputTwo env)
          (start + n)))

namespace LiteralCompatibleSuccessorResolvedControllerBookkeeping

variable {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
variable {hwin : ∀ env : EnvironmentSequence In₁ In₂,
  A.Accepts (execution strategy env)}
variable {initial : ProfiledRawJointCommonBaseWorld A strategy}
variable {policy : CompatiblePolicy A strategy hwin initial}
variable {controller :
  FinitePairedPhysicalController.{u, v, x, y, w, w}
    In₁ In₂ Out₁ Out₂}
variable {env : EnvironmentSequence In₁ In₂}

/-- Resolved streams fill the two hard fields; fixed-tail parity is retained
verbatim. -/
noncomputable def physicalAcceptance
    (bookkeeping :
      LiteralCompatibleSuccessorResolvedControllerBookkeeping A strategy hwin
        initial policy controller env) :
    A.FiniteGlobalMachinePhysicalAcceptance controller.globalMachine
      controller.globalOutputOne controller.globalOutputTwo env where
  recurrent hboth := by
    let stream := Classical.choice (bookkeeping.recurrent hboth)
    let direct := A.finiteGlobalMachinePhysicalAcceptance_of_accepts
      controller.globalMachine controller.globalOutputOne
        controller.globalOutputTwo env (stream.accepts A strategy hwin)
    exact direct.recurrent hboth
  alternatingTail hreversal := by
    let stream := Classical.choice (bookkeeping.reversal hreversal)
    let direct := A.finiteGlobalMachinePhysicalAcceptance_of_accepts
      controller.globalMachine controller.globalOutputOne
        controller.globalOutputTwo env (stream.accepts A strategy hwin)
    exact direct.alternatingTail hreversal
  strictRightTail := bookkeeping.strictRight
  strictLeftTail := bookkeeping.strictLeft

end LiteralCompatibleSuccessorResolvedControllerBookkeeping

/-- Exact strategy-indexed target for the concrete deferred controller. -/
def PerStrategyWinningLiteralCompatibleSuccessorResolvedControllerBookkeeping :
    Prop :=
  ∀ (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)),
    ∃ initial : ProfiledRawJointCommonBaseWorld A strategy,
      ∃ policy : CompatiblePolicy A strategy hwin initial,
        ∃ controller :
            FinitePairedPhysicalController.{u, v, x, y, w, w}
              In₁ In₂ Out₁ Out₂,
          ∀ env : EnvironmentSequence In₁ In₂,
            LiteralCompatibleSuccessorResolvedControllerBookkeeping A strategy
              hwin initial policy controller env

/-- The packet-stream bookkeeping is already the generic local-controller
physical-acceptance premise. -/
theorem
    perStrategyWinningFinitePairedPhysicalControllerPhysicalAcceptance_of_resolvedController
    (hresolved :
      PerStrategyWinningLiteralCompatibleSuccessorResolvedControllerBookkeeping.{u,
        v, x, y, s, w} A) :
    PerStrategyWinningFinitePairedPhysicalControllerPhysicalAcceptance.{u, v,
      x, y, s, w} A := by
  intro strategy hwin
  obtain ⟨initial, policy, controller, hcontroller⟩ :=
    hresolved strategy hwin
  refine ⟨controller, fun env ↦ ?_⟩
  exact ⟨(hcontroller env).physicalAcceptance A⟩

/-- One-arrow finite-summary extraction for the new compatible successor
controller. -/
theorem exists_readbackUpgrade_of_resolvedSuccessorController
    (fallback : LocalSummaryAutomaton.{u, v, w} In₁ In₂)
    (hresolved :
      PerStrategyWinningLiteralCompatibleSuccessorResolvedControllerBookkeeping.{u,
        v, x, y, s, w} A) :
    ∃ M : LocalSummaryAutomaton.{u, v, w} In₁ In₂,
      M.ReadbackUpgrade (Out₁ := Out₁) (Out₂ := Out₂) A := by
  exact exists_readbackUpgrade_of_finitePairedPhysicalControllerPhysicalAcceptance
    A fallback
      (perStrategyWinningFinitePairedPhysicalControllerPhysicalAcceptance_of_resolvedController
        A hresolved)

end

end DetParityAutomaton

end DistributedSynthesis
