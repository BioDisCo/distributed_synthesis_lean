/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshPendingOnlyAcceptanceIntegration
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshPhaseLiveTraceInvariant
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossPriorityAcceptance
import DistributedSynthesis.Formalizations.Lemma.LemFinitePairedPhysicalControllerReadback

/-!
# Direct priority readback for the phase-live controller

The physically executed controller in the positive route is the acknowledged
phase-live controller.  It never has to cross a pending/recurrent fork: both
hidden meanings of every receive remain in the literally shared finite table,
whose arbitrary-depth output coherence is already proved.

The optional activated controller is therefore needed only proof-side, to
identify a live target thread at a reversal.  It is not used here as a
physical controller.  This distinction avoids the stronger and unnecessary
cross-rationalization output equation between a pending table and an
independently rationalized recurrent controller.

This file gives the last plumbing arrow.  Once the actual phase-live physical
controller has the four priority-facing acceptance fields, the existing
priority-only extraction supplies `ReadbackUpgrade` directly.  Executable
endpoints still receive no graph, orientation, hierarchy side, leader bit,
history, or semantic view.
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

open ProfiledRawJointGuardedCommonLiteralCrossCanonicalPriorityAlignment

/-- The single concrete remaining strategy-indexed target for the positive
phase-live route.  The controller is fixed before the environment is chosen;
only proof-side acceptance witnesses may depend on the environment. -/
def PerStrategyWinningLiteralCombinedFreshPhaseLivePriorityAcceptance : Prop :=
  ∀ (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)),
    let package := literalCombinedFreshPendingOnlyDefaultPackage A strategy
      hwin
    let controller :=
      package.literalCombinedFreshPhaseLiveRootPhysicalController A strategy
        hwin
    ∀ env : EnvironmentSequence In₁ In₂,
      Nonempty
        (ProfiledRawJointGuardedCommonLiteralCrossCanonicalPriorityAlignment.FinitePairedPhysicalControllerPriorityAcceptance
          A strategy controller env)

/-- Anchor-free acceptance target for the same fixed phase-live controller.

The carried whole-block route constructs the standard four-regime physical
acceptance object directly: its recurrent and reversal fields come from one
parent-linked hybrid run, while its eventually fixed fields come from the
retained live seam stage.  It therefore need not manufacture the older
one-sided canonical-policy anchor merely to reach readback. -/
def PerStrategyWinningLiteralCombinedFreshPhaseLivePhysicalAcceptance : Prop :=
  ∀ (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)),
    let package := literalCombinedFreshPendingOnlyDefaultPackage A strategy
      hwin
    let controller :=
      package.literalCombinedFreshPhaseLiveRootPhysicalController A strategy
        hwin
    ∀ env : EnvironmentSequence In₁ In₂,
      Nonempty
        (A.FiniteGlobalMachinePhysicalAcceptance controller.globalMachine
          controller.globalOutputOne controller.globalOutputTwo env)

/-- The concrete phase-live target is an instance of the generic
priority-only finite-controller extraction. -/
theorem
    perStrategyWinningFinitePairedPhysicalControllerPriorityAcceptance_of_phaseLive
    (hphase :
      PerStrategyWinningLiteralCombinedFreshPhaseLivePriorityAcceptance A) :
    ProfiledRawJointGuardedCommonLiteralCrossCanonicalPriorityAlignment.PerStrategyWinningFinitePairedPhysicalControllerPriorityAcceptance.{u, v,
      x, y, s, max (max (max (max s u) v) x) y} A := by
  intro suppliedStrategy suppliedWin
  let package := literalCombinedFreshPendingOnlyDefaultPackage A
    suppliedStrategy suppliedWin
  let controller :=
    package.literalCombinedFreshPhaseLiveRootPhysicalController A
      suppliedStrategy suppliedWin
  refine ⟨controller, ?_⟩
  intro env
  exact hphase suppliedStrategy suppliedWin env

/-- The anchor-free phase-live target is exactly the generic finite paired
physical-controller endpoint. -/
theorem
    perStrategyWinningFinitePairedPhysicalControllerPhysicalAcceptance_of_phaseLive
    (hphase :
      PerStrategyWinningLiteralCombinedFreshPhaseLivePhysicalAcceptance A) :
    PerStrategyWinningFinitePairedPhysicalControllerPhysicalAcceptance.{u, v,
      x, y, s, max (max (max (max s u) v) x) y} A := by
  intro suppliedStrategy suppliedWin
  let package := literalCombinedFreshPendingOnlyDefaultPackage A
    suppliedStrategy suppliedWin
  let controller :=
    package.literalCombinedFreshPhaseLiveRootPhysicalController A
      suppliedStrategy suppliedWin
  refine ⟨controller, ?_⟩
  intro env
  exact hphase suppliedStrategy suppliedWin env

/-- One-arrow local-summary extraction from the actual phase-live controller.
No record-list equality and no physically activated pending/recurrent relay is
present in the hypothesis. -/
theorem exists_readbackUpgrade_of_phaseLivePriorityAcceptance
    (fallback : LocalSummaryAutomaton.{u, v,
      max (max (max (max s u) v) x) y} In₁ In₂)
    (hphase :
      PerStrategyWinningLiteralCombinedFreshPhaseLivePriorityAcceptance A) :
    ∃ M : LocalSummaryAutomaton.{u, v,
        max (max (max (max s u) v) x) y} In₁ In₂,
      M.ReadbackUpgrade (Out₁ := Out₁) (Out₂ := Out₂) A := by
  exact
    ProfiledRawJointGuardedCommonLiteralCrossCanonicalPriorityAlignment.exists_readbackUpgrade_of_finitePairedPhysicalControllerPriority
      A fallback
      (perStrategyWinningFinitePairedPhysicalControllerPriorityAcceptance_of_phaseLive
        A hphase)

/-- Direct local-summary extraction from the carried route's standard
four-regime physical acceptance package.  No canonical one-sided policy,
root schedule, or independent proof anchor is present in this hypothesis. -/
theorem exists_readbackUpgrade_of_phaseLivePhysicalAcceptance
    (fallback : LocalSummaryAutomaton.{u, v,
      max (max (max (max s u) v) x) y} In₁ In₂)
    (hphase :
      PerStrategyWinningLiteralCombinedFreshPhaseLivePhysicalAcceptance A) :
    ∃ M : LocalSummaryAutomaton.{u, v,
        max (max (max (max s u) v) x) y} In₁ In₂,
      M.ReadbackUpgrade (Out₁ := Out₁) (Out₂ := Out₂) A := by
  exact
    exists_readbackUpgrade_of_finitePairedPhysicalControllerPhysicalAcceptance
      A fallback
      (perStrategyWinningFinitePairedPhysicalControllerPhysicalAcceptance_of_phaseLive
        A hphase)

end

end DetParityAutomaton

end DistributedSynthesis
