/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteGlobalBeliefReadback
import DistributedSynthesis.Formalizations.Theorem.ThmFiniteGlobalLocalPresentation

/-!
# Closing finite-global belief readback from an honest local presentation

This file packages the preferred concrete endpoint for the full-model proof.
For each winning distributed strategy, the model construction supplies a
finite proof-side round machine.  Its two Moore outputs are presented by
graph-blind local `noRecv`/`recv` tables, and its actual physical trace follows
the original strategy's outputs.

The local-presentation theorem proves output uniformity on every reachable
finite belief.  Pointwise strategy agreement identifies the global trace with
the original winning execution.  Consequently these two transparent laws
discharge the complete finite-global-machine premise used by the unconditional
readback route.

No process receives the proof-side global state, active side, graph,
orientation, strict leader, or a hidden bit.  Permanently indistinguishable
global states remain together in a belief and must have the same locally
presented output.
-/

namespace DistributedSynthesis

universe u v w x y s a b

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable [Fintype In₁] [Fintype In₂]
variable [Inhabited Out₁] [Inhabited Out₂]
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

/-- The transparent strategy-indexed construction sufficient for the generic
belief readback.  `LocalPresentation` exposes the actual graph-blind local
transition laws; `StrategyOutputAgreement` exposes the physical-word
coupling.  Neither reachable-belief uniformity nor DPA acceptance is assumed
as an opaque field. -/
def PerStrategyWinningFiniteGlobalLocalPresentation : Prop :=
  ∀ strategy : StrategyPair In₁ In₂ Out₁ Out₂,
    (∀ environment : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy environment)) →
      ∃ (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
        (outputOne : G.State → Out₁)
        (outputTwo : G.State → Out₂),
        Nonempty
            (FiniteGlobalRoundMachine.LocalPresentation.{u, v, w, x, y, a, b}
              G outputOne outputTwo) ∧
          G.StrategyOutputAgreement outputOne outputTwo strategy

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- An honest graph-blind local presentation plus physical output agreement
supplies the exact finite-global belief-machine package. -/
theorem perStrategyWinningFiniteGlobalBeliefMachine_of_localPresentation
    (fallback : LocalSummaryAutomaton.{u, v, w} In₁ In₂)
    (hextract :
      PerStrategyWinningFiniteGlobalLocalPresentation.{u, v, w, x, y, s, a, b}
        A) :
    PerStrategyWinningFiniteGlobalBeliefMachine A fallback := by
  intro strategy hwin
  obtain ⟨G, outputOne, outputTwo, ⟨presentation⟩, hagrees⟩ :=
    hextract strategy hwin
  refine ⟨G, outputOne, outputTwo, ?_, ?_⟩
  · exact FiniteGlobalRoundMachine.LocalPresentation.reachableBeliefsUniform
      G outputOne outputTwo presentation
  · exact G.globalMachine_allEnvironment_of_strategyOutputAgreement
      outputOne outputTwo strategy hagrees A.Accepts hwin

/-- Direct existential readback endpoint from the transparent local
presentation package. -/
theorem exists_readbackUpgrade_of_finiteGlobalLocalPresentation
    (fallback : LocalSummaryAutomaton.{u, v, w} In₁ In₂)
    (hextract :
      PerStrategyWinningFiniteGlobalLocalPresentation.{u, v, w, x, y, s, a, b}
        A) :
    ∃ M : LocalSummaryAutomaton.{u, v, w} In₁ In₂,
      M.ReadbackUpgrade (Out₁ := Out₁) (Out₂ := Out₂) A := by
  exact exists_readbackUpgrade_of_finiteGlobalBeliefMachine A fallback
    (perStrategyWinningFiniteGlobalBeliefMachine_of_localPresentation A
      fallback hextract)

end DetParityAutomaton

end DistributedSynthesis
