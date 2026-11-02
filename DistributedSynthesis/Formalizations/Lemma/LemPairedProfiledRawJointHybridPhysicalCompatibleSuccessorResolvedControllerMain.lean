/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorResolvedControllerReadback
import DistributedSynthesis.Formalizations.Lemma.LemStarSummaryHosting
import DistributedSynthesis.Formalizations.Theorem.ThmMainSummaryWinner

/-!
# Star and main-theorem endpoints for a resolved compatible controller

This is final composition for the repaired controller route.  Once one finite
compatible-successor controller supplies recurrent/reversal resolved streams
and the two fixed-tail parity fields for its own physical word, the existing
readback, star, direct-DPA, and finite-alphabet LTL endpoints apply without an
additional controller identification.
-/

namespace DistributedSynthesis

universe u

/-! ## Canonical fallback summary -/

/-- The one-state local summary automaton.  Readback uses its fallback branch
only when no winning strategy exists, so callers of the final resolved-
controller endpoint should not have to manufacture an irrelevant summary
automaton by hand. -/
def unitLocalSummaryAutomaton (In₁ In₂ : Type u) :
    LocalSummaryAutomaton.{u, u, u} In₁ In₂ where
  Summary := fun _ ↦ PUnit
  finite := fun _ ↦ inferInstance
  initial := fun _ ↦ PUnit.unit
  stepNoRecv := fun _ _ _ ↦ PUnit.unit
  stepRecv := fun _ _ _ _ _ ↦ PUnit.unit

namespace DetParityAutomaton

variable {In₁ In₂ Out₁ Out₂ : Type u}
variable
  (A : DetParityAutomaton.{u, u}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-- Resolved bookkeeping for one repaired finite controller supplies the
complete star fold. -/
noncomputable def starFoldPackageOfResolvedSuccessorController
    (fallback : LocalSummaryAutomaton.{u, u, u} In₁ In₂)
    (hresolved :
      PerStrategyWinningLiteralCompatibleSuccessorResolvedControllerBookkeeping.{u,
        u, u, u, u, u} A) :
    StarFoldPackage A :=
  starFoldPackageOfExistsReadbackUpgrade A
    (exists_readbackUpgrade_of_resolvedSuccessorController A fallback hresolved)

/-- Direct DPA synthesis decidability for the same repaired controller. -/
noncomputable def synthesisDecidable_direct_of_resolvedSuccessorController
    (fallback : LocalSummaryAutomaton.{u, u, u} In₁ In₂)
    (hresolved :
      PerStrategyWinningLiteralCompatibleSuccessorResolvedControllerBookkeeping.{u,
        u, u, u, u, u} A) :
    Decidable
      (∃ strategy : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          A.Accepts (execution strategy env)) := by
  classical
  exact
    (starFoldPackageOfResolvedSuccessorController A fallback hresolved
      ).synthesisDecidable_direct

/-- The direct DPA endpoint with the irrelevant negative-case fallback fixed
canonically to the one-state summary automaton. -/
noncomputable def
    synthesisDecidable_direct_of_resolvedSuccessorController_canonical
    (hresolved :
      PerStrategyWinningLiteralCompatibleSuccessorResolvedControllerBookkeeping.{u,
        u, u, u, u, u} A) :
    Decidable
      (∃ strategy : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          A.Accepts (execution strategy env)) :=
  synthesisDecidable_direct_of_resolvedSuccessorController A
    (unitLocalSummaryAutomaton In₁ In₂) hresolved

end

end DetParityAutomaton

/-! ## Canonically compiled LTL objective -/

/-- Full finite-alphabet LTL synthesis from resolved bookkeeping for the
repaired compatible-successor controller. -/
noncomputable def
    main_result_for_ltl_full_synthesis_finiteAlphabets_of_resolvedSuccessorController
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
    (fallback : LocalSummaryAutomaton.{0, 0, 0} In₁ In₂)
    (hresolved :
      DetParityAutomaton.PerStrategyWinningLiteralCompatibleSuccessorResolvedControllerBookkeeping
        ((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile formula)) :
    Decidable
      (∃ strategy : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          LTL.Satisfies interp (execution strategy env) formula) :=
  main_result_for_ltl_full_synthesis_finiteAlphabets_of_existsReadbackUpgrade
    In₁ In₂ Out₁ Out₂ interp dec formula
      (DetParityAutomaton.exists_readbackUpgrade_of_resolvedSuccessorController
        ((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile formula)
        fallback hresolved)

/-- Full finite-alphabet LTL synthesis with the negative-case fallback fixed
to the canonical one-state local summary. -/
noncomputable def
    main_result_for_ltl_full_synthesis_finiteAlphabets_of_resolvedSuccessorController_canonical
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
    (hresolved :
      DetParityAutomaton.PerStrategyWinningLiteralCompatibleSuccessorResolvedControllerBookkeeping
        ((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile formula)) :
    Decidable
      (∃ strategy : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          LTL.Satisfies interp (execution strategy env) formula) :=
  main_result_for_ltl_full_synthesis_finiteAlphabets_of_resolvedSuccessorController
    In₁ In₂ Out₁ Out₂ interp dec formula
      (unitLocalSummaryAutomaton In₁ In₂) hresolved

end DistributedSynthesis
