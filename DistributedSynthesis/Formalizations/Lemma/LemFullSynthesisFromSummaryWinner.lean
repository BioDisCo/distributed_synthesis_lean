/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmReversalForgiving
import DistributedSynthesis.Formalizations.Lemma.LemReadbackUpgradeReduction
import DistributedSynthesis.Formalizations.Theorem.ThmFiniteStateSummaryCompilation

/-!
# Full-model decidability gated on the summary-observable winner certificate

`dpa_full_synthesis_decidable` (`ThmReversalForgiving`) decides full `{←,→,↔}` synthesis conditional
on `EntryIndexedCertificate` (an ad-hoc boundary-game certificate), routing through
`fullSummaries`/`full_readbackUpgrade` to the summary epoch certificate and then the
epoch → finite game → `thm:dynhiersynth` pipeline.

This file gives the *principled* endpoint: it decides the same problem conditional on a **fixed**
summary automaton `M` together with `SummaryObservableWinnerCertificate A M` -- the finite-summary
winner obligation stated at the game-abstraction level (`LemReadbackUpgradeReduction`).  A derivation
of that obligation from the external hierarchical-synthesis theorem still needs the model-specific
finite retraction and hierarchy adapter. The pipeline is
shared verbatim; only the readback upgrade is supplied by
`readbackUpgrade_of_summaryObservableWinner` instead of `full_readbackUpgrade`. So the full-model
decidability rests on exactly the finite-game-level summary-observable winner, no ad-hoc
boundary-game certificate.
-/

namespace DistributedSynthesis

universe u v x y s

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

namespace DetParityAutomaton

variable
  [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
  [DecidableEq In₁] [DecidableEq In₂]
  [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
  [Countable In₁] [Countable In₂] [Countable Out₁] [Countable Out₂]

/-- Full synthesis decidability from the semantic readback upgrade itself.
This is the common downstream consumer for both a fixed summary-observable
winner certificate and an existential summary enriched with extracted Moore
controller memory. -/
noncomputable def dpa_full_synthesis_decidable_of_readbackUpgrade
    (A :
      DetParityAutomaton.{max u v x y, max u v x y}
        (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    [DecidableEq A.State]
    (Branch : Proc -> Type (max u v x y))
    (Label : Proc -> Type (max u v x y))
    (target :
      (d : Proc) ->
        InputFreeParityTreeAutomaton.{max u v x y, max u v x y,
          max u v x y} (Branch d) (Label d))
    (targetNonempty :
      ∀ d : Proc,
        ∃ tree : LabeledTree (Branch d) (Label d),
          (target d).acceptsTree tree)
    (M : LocalSummaryAutomaton.{u, v, max u v x y} In₁ In₂)
    (hupgrade : M.ReadbackUpgrade (Out₁ := Out₁) (Out₂ := Out₂) A) :
    Decidable
      (∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂, A.Accepts (execution σ env)) :=
  let compilation :=
    (RoundAwareLambdaRotatingRationalRunEpochBackendCertificate.ofEpochCertificate
        A Branch Label target targetNonempty
        (summaryEpochCertificate A M hupgrade)).toDPAToFiniteGameCompilation
  letI : Decidable compilation.finiteGame.realizable :=
    Classical.choice
      (dynamic_hierarchy_synthesis_bridge compilation.finiteGame).2.2
  decidable_of_iff compilation.finiteGame.realizable
    compilation.realizabilityEquivalent

/-- Full synthesis decidability when the finite-state extraction chooses the
local summary automaton by enriching it with private controller memories. -/
noncomputable def dpa_full_synthesis_decidable_of_existsReadbackUpgrade
    (A :
      DetParityAutomaton.{max u v x y, max u v x y}
        (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    [DecidableEq A.State]
    (Branch : Proc -> Type (max u v x y))
    (Label : Proc -> Type (max u v x y))
    (target :
      (d : Proc) ->
        InputFreeParityTreeAutomaton.{max u v x y, max u v x y,
          max u v x y} (Branch d) (Label d))
    (targetNonempty :
      ∀ d : Proc,
        ∃ tree : LabeledTree (Branch d) (Label d),
          (target d).acceptsTree tree)
    (hexists :
      ∃ M : LocalSummaryAutomaton.{u, v, max u v x y} In₁ In₂,
        M.ReadbackUpgrade (Out₁ := Out₁) (Out₂ := Out₂) A) :
    Decidable
      (∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂, A.Accepts (execution σ env)) :=
  dpa_full_synthesis_decidable_of_readbackUpgrade A Branch Label target
    targetNonempty (Classical.choose hexists) (Classical.choose_spec hexists)

/-- **Full `{←,→,↔}` synthesis decidability, gated on the summary-observable winner certificate.**
Identical pipeline to `dpa_full_synthesis_decidable`, but the summary epoch certificate's readback
upgrade is supplied by `readbackUpgrade_of_summaryObservableWinner A M hcert` for a fixed `M` and
`hcert : SummaryObservableWinnerCertificate A M`, in place of `full_readbackUpgrade` (which needed
`EntryIndexedCertificate`). The epoch → finite game → `thm:dynhiersynth` chain is shared. -/
noncomputable def dpa_full_synthesis_decidable_of_summaryObservableWinner
    (A :
      DetParityAutomaton.{max u v x y, max u v x y}
        (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    [DecidableEq A.State]
    (Branch : Proc -> Type (max u v x y))
    (Label : Proc -> Type (max u v x y))
    (target :
      (d : Proc) ->
        InputFreeParityTreeAutomaton.{max u v x y, max u v x y,
          max u v x y} (Branch d) (Label d))
    (targetNonempty :
      ∀ d : Proc,
        ∃ tree : LabeledTree (Branch d) (Label d),
          (target d).acceptsTree tree)
    (M : LocalSummaryAutomaton.{u, v, max u v x y} In₁ In₂)
    (hcert : SummaryObservableWinnerCertificate A M) :
    Decidable
      (∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂, A.Accepts (execution σ env)) :=
  dpa_full_synthesis_decidable_of_readbackUpgrade A Branch Label target
    targetNonempty M (readbackUpgrade_of_summaryObservableWinner A M hcert)

end DetParityAutomaton

end DistributedSynthesis
