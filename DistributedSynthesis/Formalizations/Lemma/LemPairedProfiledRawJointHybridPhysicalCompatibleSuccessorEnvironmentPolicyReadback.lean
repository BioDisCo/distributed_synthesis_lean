/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorResolvedControllerReadback

/-!
# Readback for a finite bank of compatible policies

A root-pinned construction may compile a finite dependent bank of ordinary
compatible tails into one controller.  The controller must be selected before
the environment, but the proof-side tag naming the bank member followed by a
particular environment need not be selected that early.

This file records exactly that quantifier order.  For each environment we may
choose the initial common world and compatible policy used to certify the
controller's already fixed physical word.  The resulting physical-acceptance
package forgets those proof witnesses, so the standard finite-controller
readback applies unchanged.

No executable map below receives an environment, graph, orientation, leader,
or strict-leader bit.  This is only a logical adapter; it does not assert that
the required finite bank/controller has been constructed.
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

/-- Exact bank-friendly construction target.

The finite paired controller is outside the environment quantifier.  Only the
semantic witnesses used to prove acceptance of its fixed trace are inside. -/
def
    PerStrategyWinningLiteralCompatibleSuccessorEnvironmentPolicyResolvedControllerBookkeeping :
    Prop :=
  ∀ (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)),
    ∃ controller :
        FinitePairedPhysicalController.{u, v, x, y, w, w}
          In₁ In₂ Out₁ Out₂,
      ∀ env : EnvironmentSequence In₁ In₂,
        ∃ initial : ProfiledRawJointCommonBaseWorld A strategy,
          ∃ policy : CompatiblePolicy A strategy hwin initial,
            LiteralCompatibleSuccessorResolvedControllerBookkeeping A strategy
              hwin initial policy controller env

/-- Environment-selected proof policies still yield physical acceptance for
one controller selected before the environment. -/
theorem
    perStrategyWinningFinitePairedPhysicalControllerPhysicalAcceptance_of_environmentPolicyResolvedController
    (hresolved :
      PerStrategyWinningLiteralCompatibleSuccessorEnvironmentPolicyResolvedControllerBookkeeping.{u,
        v, x, y, s, w} A) :
    PerStrategyWinningFinitePairedPhysicalControllerPhysicalAcceptance.{u, v,
      x, y, s, w} A := by
  intro strategy hwin
  obtain ⟨controller, hcontroller⟩ := hresolved strategy hwin
  refine ⟨controller, fun env ↦ ?_⟩
  obtain ⟨initial, policy, bookkeeping⟩ := hcontroller env
  exact ⟨bookkeeping.physicalAcceptance A⟩

/-- Hence a finite policy bank reaches the ordinary readback endpoint without
moving the controller choice under the environment quantifier. -/
theorem exists_readbackUpgrade_of_environmentPolicyResolvedSuccessorController
    (fallback : LocalSummaryAutomaton.{u, v, w} In₁ In₂)
    (hresolved :
      PerStrategyWinningLiteralCompatibleSuccessorEnvironmentPolicyResolvedControllerBookkeeping.{u,
        v, x, y, s, w} A) :
    ∃ M : LocalSummaryAutomaton.{u, v, w} In₁ In₂,
      M.ReadbackUpgrade (Out₁ := Out₁) (Out₂ := Out₂) A := by
  exact
    exists_readbackUpgrade_of_finitePairedPhysicalControllerPhysicalAcceptance
      A fallback
        (perStrategyWinningFinitePairedPhysicalControllerPhysicalAcceptance_of_environmentPolicyResolvedController
          A hresolved)

end

end DetParityAutomaton

end DistributedSynthesis
