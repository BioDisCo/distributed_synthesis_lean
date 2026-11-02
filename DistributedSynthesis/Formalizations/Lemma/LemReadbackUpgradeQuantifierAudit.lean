/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmSummaryEpochCertificate

/-!
# Quantifier boundary for existential readback upgrades

`LocalSummaryAutomaton.ReadbackUpgrade M A` fixes `M` before quantifying over
the supplied winning strategy.  Consequently a construction performed under
that strategy binder may not silently change the summary or move types.

The existential endpoint has one legitimate escape hatch, recorded below.
If the construction under a winning strategy already returns a *complete
winning readback* for some finite summary automaton, then classical choice may
select one winning strategy once, outside `ReadbackUpgrade`, and fix the
resulting automaton.  The readback selected there is then reused for every
later strategy argument.  Producing merely a strategy-indexed finite move,
candidate bank, or local one-step certificate does not meet this premise.
-/

namespace DistributedSynthesis

universe u v w a s o

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type w} {Out₂ : Type a}

namespace DetParityAutomaton

variable
  (A : DetParityAutomaton.{max u v w a, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

/-- A full readback may choose its finite summary automaton after seeing one
winning strategy.  This is deliberately stronger than producing a finite
move or a one-step controller under that strategy. -/
def PerStrategyWinningReadback
    (_fallback : LocalSummaryAutomaton.{u, v, o} In₁ In₂) : Prop :=
  ∀ strategy : StrategyPair In₁ In₂ Out₁ Out₂,
    (∀ environment : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy environment)) →
      ∃ (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂)
        (outputOne : M.Summary Proc.one → Out₁)
        (outputTwo : M.Summary Proc.two → Out₂),
        ∀ environment : EnvironmentSequence In₁ In₂,
          A.Accepts
            (execution (M.readbackStrategy outputOne outputTwo) environment)

/-- Correct outer-existential bridge.  In the realizable branch one winning
strategy and its already winning readback are selected once.  The resulting
summary automaton is fixed before the `ReadbackUpgrade` strategy binder.  In
the unrealizable branch any supplied finite fallback summary works vacuously.
-/
theorem exists_readbackUpgrade_of_perStrategyWinningReadback
    (fallback : LocalSummaryAutomaton.{u, v, o} In₁ In₂)
    (hextract : PerStrategyWinningReadback A fallback) :
    ∃ M : LocalSummaryAutomaton.{u, v, o} In₁ In₂,
      M.ReadbackUpgrade (Out₁ := Out₁) (Out₂ := Out₂) A := by
  classical
  let P : Prop :=
      ∃ strategy : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ environment : EnvironmentSequence In₁ In₂,
          A.Accepts (execution strategy environment)
  letI : Decidable P := Classical.propDecidable P
  by_cases hrealizable : P
  · obtain ⟨strategy, hstrategy⟩ := hrealizable
    obtain ⟨M, outputOne, outputTwo, hreadback⟩ :=
      hextract strategy hstrategy
    refine ⟨M, ?_⟩
    intro _strategy _hstrategy
    exact ⟨outputOne, outputTwo, hreadback⟩
  · refine ⟨fallback, ?_⟩
    intro strategy hstrategy
    exact False.elim (hrealizable ⟨strategy, hstrategy⟩)

/-- Exact quantifier characterization at a fixed summary universe.  The
strategy-indexed formulation is equivalent to the outer existential only
because its witness is already an all-environment winning readback. -/
theorem exists_readbackUpgrade_iff_perStrategyWinningReadback
    (fallback : LocalSummaryAutomaton.{u, v, o} In₁ In₂) :
    (∃ M : LocalSummaryAutomaton.{u, v, o} In₁ In₂,
        M.ReadbackUpgrade (Out₁ := Out₁) (Out₂ := Out₂) A) ↔
      PerStrategyWinningReadback A fallback := by
  constructor
  · rintro ⟨M, hM⟩ strategy hstrategy
    obtain ⟨outputOne, outputTwo, hreadback⟩ := hM strategy hstrategy
    exact ⟨M, outputOne, outputTwo, hreadback⟩
  · exact exists_readbackUpgrade_of_perStrategyWinningReadback A fallback

end DetParityAutomaton

end DistributedSynthesis
