/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmSummaryMeasurableTransfer

/-!
# The epoch-game certificate from the readback upgrade

This file assembles the full
`RoundAwareLambdaEpochGameAbstractionCertificate` for the journal-shape
transformer of `def:epochtransformer` from a single named proposition.

`LocalSummaryAutomaton.ReadbackUpgrade M A` states the measurability
upgrade of `prop:journalgivesuniform`: every distributed strategy all
of whose real executions are accepted by `A` is dominated by a winning
summary readback strategy over `M`.  Everything else in the certificate
is discharged unconditionally:

* `sound`: an arbitrary lambda-observable controller factors through
  the summary observations, its output tables are extracted by choice
  on attained observation values
  (`SummaryTracking.extractedTableOne/Two`), and the readback of the
  extracted tables is sound by
  `SummaryTracking.strategySound`.
* `complete`: the upgrade produces winning tables, and the transfer
  theorem `exists_lambdaController_wins_of_readback_accepts` turns them
  into a winning lambda controller.
* `winsDecidable` comes from the state-loop decision procedure inside
  `ofTransformer`.

The endpoint is `DetParityAutomaton.summaryEpochCertificate`.  The
hypothesis is `ReadbackUpgrade`, to be
proved for a concrete summary automaton per objective automaton by the
journal construction: block decomposition, per-block narrowing, the
boundary parity-game fixpoint, and fringe elimination.
-/

namespace DistributedSynthesis

universe u v w a s z o b x

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type w} {Out₂ : Type a}

namespace LocalSummaryAutomaton

/--
The measurability upgrade of `prop:journalgivesuniform` for a summary
automaton and an objective automaton: every winning distributed
strategy is dominated by a winning summary readback strategy.
-/
def ReadbackUpgrade
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂)
    (A :
      DetParityAutomaton.{max u v w a, s}
        (RoundRecord In₁ In₂ Graph Out₁ Out₂)) : Prop :=
  ∀ σ : StrategyPair In₁ In₂ Out₁ Out₂,
    (∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution σ env)) ->
      ∃ (outputOne : M.Summary Proc.one -> Out₁)
        (outputTwo : M.Summary Proc.two -> Out₂),
        ∀ env : EnvironmentSequence In₁ In₂,
          A.Accepts
            (execution (M.readbackStrategy outputOne outputTwo) env)

end LocalSummaryAutomaton

namespace FiniteEpochTransformer

namespace SummaryTracking

variable
  {T :
    FiniteEpochTransformer.{max u v w a, u, v, w, a, z}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂) In₁ In₂ Out₁ Out₂}
  {M : LocalSummaryAutomaton.{u, v, o} In₁ In₂}
  (tracking : SummaryTracking T M)

/--
The output table of process one extracted from a finite controller by
choice on attained observation values.
-/
noncomputable def extractedTableOne
    [Inhabited Out₁]
    (controller : RoundAwareControllerCode T) :
    M.Summary Proc.one -> Out₁ := fun s =>
  letI :
      Decidable
        (∃ p : GameState T × EnvironmentRound In₁ In₂,
          tracking.fringeDecoder Proc.one p.1 p.2 = s) :=
    Classical.propDecidable _
  if h :
      ∃ p : GameState T × EnvironmentRound In₁ In₂,
        tracking.fringeDecoder Proc.one p.1 p.2 = s then
    (controller h.choose.1 h.choose.2).1
  else default

/--
The output table of process two extracted from a finite controller by
choice on attained observation values.
-/
noncomputable def extractedTableTwo
    [Inhabited Out₂]
    (controller : RoundAwareControllerCode T) :
    M.Summary Proc.two -> Out₂ := fun s =>
  letI :
      Decidable
        (∃ p : GameState T × EnvironmentRound In₁ In₂,
          tracking.fringeDecoder Proc.two p.1 p.2 = s) :=
    Classical.propDecidable _
  if h :
      ∃ p : GameState T × EnvironmentRound In₁ In₂,
        tracking.fringeDecoder Proc.two p.1 p.2 = s then
    (controller h.choose.1 h.choose.2).2
  else default

/--
A controller that is lambda observable through constant history
decoders and the summary fringe decoders factors through its extracted
tables.
-/
theorem controller_eq_extractedTables
    [Inhabited Out₁] [Inhabited Out₂]
    {H₁ : Type b} {H₂ : Type x}
    {historyOne : GameState T -> EnvironmentRound In₁ In₂ -> List H₁}
    {historyTwo : GameState T -> EnvironmentRound In₁ In₂ -> List H₂}
    (hhistoryOne :
      ∀ stateA envA stateB envB,
        historyOne stateA envA = historyOne stateB envB)
    (hhistoryTwo :
      ∀ stateA envA stateB envB,
        historyTwo stateA envA = historyTwo stateB envB)
    {controller : RoundAwareControllerCode T}
    (hobs :
      RoundAwareControllerLocallyObservableByFiniteLambda
        T historyOne historyTwo
        (tracking.fringeDecoder Proc.one) (tracking.fringeDecoder Proc.two)
        controller) :
    ∀ (state : GameState T) (envRound : EnvironmentRound In₁ In₂),
      controller state envRound =
        (tracking.extractedTableOne controller
            (tracking.fringeDecoder Proc.one state envRound),
          tracking.extractedTableTwo controller
            (tracking.fringeDecoder Proc.two state envRound)) := by
  intro state envRound
  have hexistsOne :
      ∃ p : GameState T × EnvironmentRound In₁ In₂,
        tracking.fringeDecoder Proc.one p.1 p.2 =
          tracking.fringeDecoder Proc.one state envRound :=
    ⟨(state, envRound), rfl⟩
  have hexistsTwo :
      ∃ p : GameState T × EnvironmentRound In₁ In₂,
        tracking.fringeDecoder Proc.two p.1 p.2 =
          tracking.fringeDecoder Proc.two state envRound :=
    ⟨(state, envRound), rfl⟩
  have hfst :
      tracking.extractedTableOne controller
          (tracking.fringeDecoder Proc.one state envRound) =
        (controller state envRound).1 := by
    simp only [extractedTableOne]
    rw [dif_pos hexistsOne]
    exact
      (hobs.1 state envRound hexistsOne.choose.1 hexistsOne.choose.2
        (hhistoryOne state envRound hexistsOne.choose.1 hexistsOne.choose.2)
        hexistsOne.choose_spec.symm).symm
  have hsnd :
      tracking.extractedTableTwo controller
          (tracking.fringeDecoder Proc.two state envRound) =
        (controller state envRound).2 := by
    simp only [extractedTableTwo]
    rw [dif_pos hexistsTwo]
    exact
      (hobs.2 state envRound hexistsTwo.choose.1 hexistsTwo.choose.2
        (hhistoryTwo state envRound hexistsTwo.choose.1 hexistsTwo.choose.2)
        hexistsTwo.choose_spec.symm).symm
  calc
    controller state envRound =
        ((controller state envRound).1, (controller state envRound).2) :=
      rfl
    _ =
        (tracking.extractedTableOne controller
            (tracking.fringeDecoder Proc.one state envRound),
          tracking.extractedTableTwo controller
            (tracking.fringeDecoder Proc.two state envRound)) := by
      rw [hfst, hsnd]

end SummaryTracking

end FiniteEpochTransformer

namespace DetParityAutomaton

open FiniteEpochTransformer

variable
  [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
  [Inhabited Out₁] [Inhabited Out₂]
  (A :
    DetParityAutomaton.{max u v w a, max u v w a}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))
  (M : LocalSummaryAutomaton.{u, v, max u v w a} In₁ In₂)

/--
The epoch-game certificate for the journal-shape transformer,
conditional on exactly one proposition: the readback upgrade.  The
lambda decoders are the trivial history and the summary observations;
soundness extracts output tables by choice and applies the tracked
readback soundness; completeness composes the upgrade with the
transfer theorem.
-/
noncomputable def summaryEpochCertificate
    (hupgrade :
      M.ReadbackUpgrade (Out₁ := Out₁) (Out₂ := Out₂) A) :
    RoundAwareLambdaEpochGameAbstractionCertificate A :=
  RoundAwareLambdaEpochGameAbstractionCertificate.ofTransformer A
    (A.summaryEpochTransformer (Out₁ := Out₁) (Out₂ := Out₂) M)
    (A.summaryInitialBoundary M)
    (fun _ _ => ([] : List PUnit))
    (fun _ _ => ([] : List PUnit))
    ((A.summaryEpochTransformerTracking
        (Out₁ := Out₁) (Out₂ := Out₂) M).fringeDecoder Proc.one)
    ((A.summaryEpochTransformerTracking M).fringeDecoder Proc.two)
    (fun controller =>
      M.readbackStrategy
        ((A.summaryEpochTransformerTracking M).extractedTableOne
          controller.1)
        ((A.summaryEpochTransformerTracking M).extractedTableTwo
          controller.1))
    True True trivial trivial
    (fun controller hwins =>
      (A.summaryEpochTransformerTracking M).strategySound
        (A.epochTransformerTracking.prodFst (M.carrier A))
        (A.summaryInitialBoundary M) rfl rfl (fun _ => Iff.rfl)
        ((A.summaryEpochTransformerTracking M).extractedTableOne
          controller.1)
        ((A.summaryEpochTransformerTracking M).extractedTableTwo
          controller.1)
        controller.1
        ((A.summaryEpochTransformerTracking M).controller_eq_extractedTables
          (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) controller.2)
        hwins)
    (fun σ hσ => by
      rcases hupgrade σ hσ with ⟨outputOne, outputTwo, haccepts⟩
      exact
        (A.summaryEpochTransformerTracking
            M).exists_lambdaController_wins_of_readback_accepts
          (A.summaryInitialBoundary M) rfl (fun _ => Iff.rfl)
          (fun _ _ => ([] : List PUnit))
          (fun _ _ => ([] : List PUnit))
          outputOne outputTwo haccepts)

end DetParityAutomaton

end DistributedSynthesis
