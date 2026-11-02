/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorWholeTraceBookkeeping
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorResolvedControllerMain

/-!
# Strategy-indexed whole-trace endpoint

This is pure quantifier assembly for the repaired compatible-successor route.
For each supplied winning strategy, the initial compatible world, policy, and
finite paired controller are selected once, before the environment.  Each
environment then owes only

* whole-trace cut witnesses in the recurrent and reversal regimes; and
* installed-table alignments in the two eventually homogeneous regimes.

The preceding adapters turn those data into the exact resolved-controller
bookkeeping premise.  All star, direct-DPA, and LTL endpoints then apply.
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

/-- The two controller-independent environment obligations after one repaired
finite controller has been fixed. -/
structure LiteralCompatibleSuccessorWholeTraceEnvironmentBookkeeping
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (policy : CompatiblePolicy A strategy hwin initial)
    (controller :
      FinitePairedPhysicalController.{u, v, x, y, w, w}
        In₁ In₂ Out₁ Out₂)
    (env : EnvironmentSequence In₁ In₂) : Prop where
  hard :
    ProfiledRawJointHybridPhysicalCompatibleHardRegimeWholeTraceBookkeeping
      A strategy hwin policy controller.globalMachine
        controller.globalOutputOne controller.globalOutputTwo env
  fixed : EventuallyInstalledFixedTailBookkeeping A
    (controller.globalMachine.globalMachineTraceWord
      controller.globalOutputOne controller.globalOutputTwo env)
    (fun n ↦ (env n).graph)

namespace LiteralCompatibleSuccessorWholeTraceEnvironmentBookkeeping

variable {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
variable {hwin : ∀ env : EnvironmentSequence In₁ In₂,
  A.Accepts (execution strategy env)}
variable {initial : ProfiledRawJointCommonBaseWorld A strategy}
variable {policy : CompatiblePolicy A strategy hwin initial}
variable {controller :
  FinitePairedPhysicalController.{u, v, x, y, w, w}
    In₁ In₂ Out₁ Out₂}
variable {env : EnvironmentSequence In₁ In₂}

/-- One environment package is already the exact four-regime bookkeeping. -/
noncomputable def toResolvedController
    (bookkeeping :
      LiteralCompatibleSuccessorWholeTraceEnvironmentBookkeeping A strategy
        hwin initial policy controller env) :
    LiteralCompatibleSuccessorResolvedControllerBookkeeping A strategy hwin
      initial policy controller env :=
  LiteralCompatibleSuccessorResolvedControllerBookkeeping.ofWholeTraceAndInstalledFixedTails
    A strategy hwin bookkeeping.hard bookkeeping.fixed

end LiteralCompatibleSuccessorWholeTraceEnvironmentBookkeeping

/-- Exact construction target for the concrete phase-live controller.

The three finite objects are chosen once per winning strategy; only their
trace witnesses depend on the environment. -/
def PerStrategyWinningLiteralCompatibleSuccessorWholeTraceBookkeeping : Prop :=
  ∀ (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)),
    ∃ initial : ProfiledRawJointCommonBaseWorld A strategy,
      ∃ policy : CompatiblePolicy A strategy hwin initial,
        ∃ controller :
            FinitePairedPhysicalController.{u, v, x, y, w, w}
              In₁ In₂ Out₁ Out₂,
          ∀ env : EnvironmentSequence In₁ In₂,
            LiteralCompatibleSuccessorWholeTraceEnvironmentBookkeeping A
              strategy hwin initial policy controller env

/-- The whole-trace construction target implies the existing exact resolved-
controller premise. -/
theorem
    perStrategyWinningResolvedController_of_wholeTraceBookkeeping
    (hwhole :
      PerStrategyWinningLiteralCompatibleSuccessorWholeTraceBookkeeping.{u, v,
        x, y, s, w} A) :
    PerStrategyWinningLiteralCompatibleSuccessorResolvedControllerBookkeeping.{u,
      v, x, y, s, w} A := by
  intro strategy hwin
  obtain ⟨initial, policy, controller, henv⟩ := hwhole strategy hwin
  refine ⟨initial, policy, controller, fun env ↦ ?_⟩
  exact (henv env).toResolvedController A

/-! ## Canonical direct endpoints -/

section EqualUniverse

variable {I₁ I₂ O₁ O₂ : Type u}
variable
  (B : DetParityAutomaton.{u, u}
    (RoundRecord I₁ I₂ Graph O₁ O₂))
variable [Inhabited I₁] [Inhabited I₂] [Inhabited O₁]
  [Inhabited O₂]
variable [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
variable [DecidableEq I₁] [DecidableEq I₂]

/-- Whole-trace packages supply the star fold with the canonical one-state
negative-case fallback. -/
noncomputable def starFoldPackageOfWholeTraceSuccessorController
    (hwhole :
      PerStrategyWinningLiteralCompatibleSuccessorWholeTraceBookkeeping.{u, u,
        u, u, u, u} B) :
    StarFoldPackage B :=
  starFoldPackageOfResolvedSuccessorController B
    (unitLocalSummaryAutomaton I₁ I₂)
    (perStrategyWinningResolvedController_of_wholeTraceBookkeeping B hwhole)

/-- Canonical direct DPA synthesis decidability. -/
noncomputable def synthesisDecidable_direct_of_wholeTraceSuccessorController
    (hwhole :
      PerStrategyWinningLiteralCompatibleSuccessorWholeTraceBookkeeping.{u, u,
        u, u, u, u} B) :
    Decidable
      (∃ strategy : StrategyPair I₁ I₂ O₁ O₂,
        ∀ env : EnvironmentSequence I₁ I₂,
          B.Accepts (execution strategy env)) :=
  synthesisDecidable_direct_of_resolvedSuccessorController_canonical B
    (perStrategyWinningResolvedController_of_wholeTraceBookkeeping B hwhole)

end EqualUniverse

end


end DetParityAutomaton

/-! ## Canonically compiled LTL endpoint -/

/-- Full finite-alphabet LTL synthesis from the concrete whole-trace package. -/
noncomputable def
    main_result_for_ltl_full_synthesis_finiteAlphabets_of_wholeTraceSuccessorController
    {AP : Type}
    (In₁ In₂ Out₁ Out₂ : Type)
    [DecidableEq AP]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    (interp : AP → RoundRecord In₁ In₂ Graph Out₁ Out₂ → Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (formula : LTL AP)
    [DecidableEq
      ((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile
        formula).State]
    (hwhole :
      DetParityAutomaton.PerStrategyWinningLiteralCompatibleSuccessorWholeTraceBookkeeping
        ((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile formula)) :
    Decidable
      (∃ strategy : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          LTL.Satisfies interp (execution strategy env) formula) :=
  main_result_for_ltl_full_synthesis_finiteAlphabets_of_resolvedSuccessorController_canonical
    In₁ In₂ Out₁ Out₂ interp dec formula
      (DetParityAutomaton.perStrategyWinningResolvedController_of_wholeTraceBookkeeping
        ((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile formula)
        hwhole)

end DistributedSynthesis
