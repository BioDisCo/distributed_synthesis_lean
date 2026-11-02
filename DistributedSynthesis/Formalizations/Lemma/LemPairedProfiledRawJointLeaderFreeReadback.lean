/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointLeaderFreeControllerCarrier
import DistributedSynthesis.Formalizations.Lemma.LemFiniteGlobalBeliefReadback

/-!
# Direct readback of the leader-free physical controller

The leader-free carrier is already a pair of finite local automata.  It does
not need a powerset belief construction to become a distributed strategy.
This file packages its joint execution as a finite global proof machine and
proves that the carrier's own local-summary readback emits exactly the same
physical word.

The global machine is used only to state epoch/tail acceptance.  Its joint
state is not exposed to either process: the executable readback folds each
view through `ProfiledRawJointLeaderFreeKernel.summaryAutomaton` and reads the
last locally produced output.
-/

namespace DistributedSynthesis

universe u v x y s i₁ i₂ e₁ e₂ k ro lr rr lo

namespace ProfiledRawJointLeaderFreeKernel

variable
  {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
  {InitialOne : Type i₁} {InitialTwo : Type i₂}
  {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
  {ChildCode : Type k}
  {RightOwner : ChildCode → Type ro}
  {LeftReceiver : ChildCode → Type lr}
  {RightReceiver : ChildCode → Type rr}
  {LeftOwner : ChildCode → Type lo}

variable (kernel : ProfiledRawJointLeaderFreeKernel In₁ In₂ Out₁ Out₂
  InitialOne InitialTwo ExceptionalOne ExceptionalTwo ChildCode RightOwner
  LeftReceiver RightReceiver LeftOwner)

variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [Fintype InitialOne] [Fintype InitialTwo]
variable [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
variable [Fintype ChildCode]
variable [∀ key, Fintype (RightOwner key)]
variable [∀ key, Fintype (LeftReceiver key)]
variable [∀ key, Fintype (RightReceiver key)]
variable [∀ key, Fintype (LeftOwner key)]

/-! ## Joint proof machine and local output tables -/

/-- The proof-side joint execution of the two genuinely local controls. -/
noncomputable def globalMachine : FiniteGlobalRoundMachine In₁ In₂ where
  State := (kernel.physicalController).OneControl ×
    (kernel.physicalController).TwoControl
  stateFinite := inferInstance
  initial := ((kernel.physicalController).initialOne,
    (kernel.physicalController).initialTwo)
  step := (kernel.physicalController).advanceControls

/-- Moore output of process one on the joint proof state. -/
noncomputable def globalOutputOne (state : (kernel.globalMachine).State) : Out₁ :=
  (kernel.physicalController).outputOne state.1

/-- Process-two mirror. -/
noncomputable def globalOutputTwo (state : (kernel.globalMachine).State) : Out₂ :=
  (kernel.physicalController).outputTwo state.2

/-- Local output table on the process-one summary. -/
noncomputable def summaryOutputOne
    (summary : (kernel.summaryAutomaton).Summary Proc.one) : Out₁ :=
  (kernel.physicalController).outputOne summary.down

/-- Local output table on the process-two summary. -/
noncomputable def summaryOutputTwo
    (summary : (kernel.summaryAutomaton).Summary Proc.two) : Out₂ :=
  (kernel.physicalController).outputTwo summary.down

/-- The distributed strategy read directly from the two local controls. -/
noncomputable def readbackStrategy : StrategyPair In₁ In₂ Out₁ Out₂ :=
  (kernel.summaryAutomaton).readbackStrategy
    kernel.summaryOutputOne kernel.summaryOutputTwo

/-! ## Exact trace correspondence -/

section
omit [Fintype In₁] [Fintype In₂]

/-- Folding the two execution views through the carrier summaries gives the
two local controls of the joint proof machine after the same prefix. -/
theorem readPair_executionPrefix
    (env : EnvironmentSequence In₁ In₂) : ∀ n : Nat,
    (kernel.summaryAutomaton).readPair
        (viewPair (executionPrefix kernel.readbackStrategy env n)) =
      (.up ((kernel.globalMachine).globalStateTrace env n).1,
        .up ((kernel.globalMachine).globalStateTrace env n).2) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [executionPrefix_succ, viewPair_append,
        (kernel.summaryAutomaton).readPair_advanceViews]
      rw [ih]
      simp only [nextRound, FiniteGlobalRoundMachine.globalStateTrace_succ]
      cases hgraph : (env n).graph <;>
        simp [LocalSummaryAutomaton.advance, summaryAutomaton, globalMachine,
          physicalController, FinitePairedPhysicalController.advanceControls,
          hgraph]

/-- The outputs emitted in physical round `n` are the Moore outputs of the
joint proof machine after consuming that round. -/
theorem readback_execution_outputs
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    ((execution kernel.readbackStrategy env n).outputOne,
      (execution kernel.readbackStrategy env n).outputTwo) =
    (kernel.globalOutputOne
        ((kernel.globalMachine).globalStateTrace env (n + 1)),
      kernel.globalOutputTwo
        ((kernel.globalMachine).globalStateTrace env (n + 1))) := by
  have hread := kernel.readPair_executionPrefix env (n + 1)
  rw [executionPrefix_succ, viewPair_append] at hread
  rw [execution_apply]
  change
    (kernel.summaryOutputOne
        ((kernel.summaryAutomaton).read
          (nextView Proc.one
            (executionPrefix kernel.readbackStrategy env n) (env n))),
      kernel.summaryOutputTwo
        ((kernel.summaryAutomaton).read
          (nextView Proc.two
            (executionPrefix kernel.readbackStrategy env n) (env n)))) = _
  have hout := congrArg
    (fun pair ↦
      (kernel.summaryOutputOne pair.1,
        kernel.summaryOutputTwo pair.2)) hread
  simpa [summaryOutputOne, summaryOutputTwo, globalOutputOne, globalOutputTwo,
    advanceViews, advanceViewsWithEnvironment] using hout

/-- The distributed readback word is exactly the explicit physical word of
the joint controller. -/
theorem execution_eq_globalMachineTraceWord
    (env : EnvironmentSequence In₁ In₂) :
    execution kernel.readbackStrategy env =
      (kernel.globalMachine).globalMachineTraceWord kernel.globalOutputOne
        kernel.globalOutputTwo env := by
  funext n
  have houtputs := kernel.readback_execution_outputs env n
  have hone := congrArg Prod.fst houtputs
  have htwo := congrArg Prod.snd houtputs
  rw [execution_apply] at hone htwo ⊢
  simp only [nextRound_outputOne] at hone
  simp only [nextRound_outputTwo] at htwo
  simp only [FiniteGlobalRoundMachine.globalMachineTraceWord, nextRound]
  rw [hone, htwo]

/-- Any all-environment property of the physical global-machine word transfers
directly to the executable distributed readback. -/
theorem readback_allEnvironment_of_globalMachine
    (predicate : (Nat → RoundRecord In₁ In₂ Graph Out₁ Out₂) → Prop)
    (hglobal : ∀ env : EnvironmentSequence In₁ In₂,
      predicate
        ((kernel.globalMachine).globalMachineTraceWord kernel.globalOutputOne
          kernel.globalOutputTwo env)) :
    ∀ env : EnvironmentSequence In₁ In₂,
      predicate (execution kernel.readbackStrategy env) := by
  intro env
  rw [kernel.execution_eq_globalMachineTraceWord env]
  exact hglobal env

end

/-! ## Direct local-summary upgrade -/

omit [Fintype In₁] [Fintype In₂] in
/-- Original-DPA acceptance of the joint physical trace transfers without a
belief-uniformity hypothesis to the genuinely local summary readback. -/
theorem readback_accepts_of_globalMachine
    (A : DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (hglobal : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts
        ((kernel.globalMachine).globalMachineTraceWord kernel.globalOutputOne
          kernel.globalOutputTwo env)) :
    ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution kernel.readbackStrategy env) :=
  kernel.readback_allEnvironment_of_globalMachine A.Accepts hglobal

omit [Fintype In₁] [Fintype In₂] in
/-- Once the physical carrier wins, its own finite local summaries satisfy
`ReadbackUpgrade`.  The arbitrary winning strategy supplied to the upgrade
premise is irrelevant because this carrier has already selected a fixed
winning readback. -/
theorem summaryAutomaton_readbackUpgrade_of_globalMachine
    (A : DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (hglobal : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts
        ((kernel.globalMachine).globalMachineTraceWord kernel.globalOutputOne
          kernel.globalOutputTwo env)) :
    (kernel.summaryAutomaton).ReadbackUpgrade A := by
  intro _strategy _hstrategy
  refine ⟨kernel.summaryOutputOne, kernel.summaryOutputTwo, ?_⟩
  exact kernel.readback_accepts_of_globalMachine A hglobal

end ProfiledRawJointLeaderFreeKernel

end DistributedSynthesis
