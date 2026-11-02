/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossCanonicalAcceptance

/-!
# Per-round controller equations imply canonical literal-cross extraction

This file is the final generic trace-induction adapter for the literal-cross
route.  A concrete finite paired controller supplies one proof-side invariant
on its pair of local controls, an initial proof, three preservation equations
for the three environment graphs, and one Moore-output equation.  The generic
induction proves equality of the complete physical word with a proof-side
reference word.

For each hard environment regime the caller then gives the canonical schedule
data for that reference word.  Rewriting by the generic word equality produces
`ProfiledRawJointGuardedCommonLiteralCrossCanonicalTraceAlignment`, and the
existing acceptance adapter produces the strategy-indexed extraction target.

The graph cases below are proof-side cases selecting the executable local
handlers.  The controller's `recv` and `noRecv` maps still receive no graph,
orientation, leader bit, strict-leader bit, or history.
-/

namespace DistributedSynthesis

universe u v x y s w w₁ w₂

namespace FinitePairedPhysicalController

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (controller : FinitePairedPhysicalController.{u, v, x, y, w₁, w₂}
    In₁ In₂ Out₁ Out₂)

noncomputable section

/-! ## A finite list of concrete per-round proof obligations -/

/-- Graph-split reachable-state equations for one actual environment trace.

`StateInvariant` is proof-only and may mention a semantic schedule, a row, or
the prefix index.  It is not stored by either endpoint.  The three step fields
are deliberately stated with the controller's literal endpoint maps, so a
concrete product carrier can discharge them from its local transition lemmas
without unfolding a global proof machine.

In particular no rule for two unresolved fork IDs is assumed here.  A
concrete delayed carrier must include the partner acknowledgement `(old ID,
bit)` in its finite local state and use it in these step equations.  Thus the
stale-ID/fresh-ID case is resolved before the exact `outputs` field is proved;
it cannot be silently treated as open/open. -/
structure LiteralCrossGraphTraceInvariant
    (env : EnvironmentSequence In₁ In₂) where
  expectedOutputOne : Nat → Out₁
  expectedOutputTwo : Nat → Out₂
  StateInvariant :
    controller.OneControl × controller.TwoControl → Nat → Prop
  initial : StateInvariant (controller.initialOne, controller.initialTwo) 0
  leftStep : ∀ (n : Nat)
      (controls : controller.OneControl × controller.TwoControl),
    StateInvariant controls n → (env n).graph = .left →
      StateInvariant
        (controller.recvOne controls.1 (env n).inputOne controls.2
            (env n).inputTwo,
          controller.noRecvTwo controls.2 (env n).inputTwo)
        (n + 1)
  rightStep : ∀ (n : Nat)
      (controls : controller.OneControl × controller.TwoControl),
    StateInvariant controls n → (env n).graph = .right →
      StateInvariant
        (controller.noRecvOne controls.1 (env n).inputOne,
          controller.recvTwo controls.2 (env n).inputTwo controls.1
            (env n).inputOne)
        (n + 1)
  bothStep : ∀ (n : Nat)
      (controls : controller.OneControl × controller.TwoControl),
    StateInvariant controls n → (env n).graph = .both →
      StateInvariant
        (controller.recvOne controls.1 (env n).inputOne controls.2
            (env n).inputTwo,
          controller.recvTwo controls.2 (env n).inputTwo controls.1
            (env n).inputOne)
        (n + 1)
  outputs : ∀ (n : Nat)
      (controls : controller.OneControl × controller.TwoControl),
    StateInvariant controls (n + 1) →
      controller.outputOne controls.1 = expectedOutputOne n ∧
        controller.outputTwo controls.2 = expectedOutputTwo n

namespace LiteralCrossGraphTraceInvariant

/-- The proof-side recorded word named by the expected Moore outputs.  Its
environment coordinates are the actual environment coordinates by
definition. -/
def referenceWord
    {env : EnvironmentSequence In₁ In₂}
    (invariant : controller.LiteralCrossGraphTraceInvariant env) :
    OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  fun n ↦
    { inputOne := (env n).inputOne
      inputTwo := (env n).inputTwo
      graph := (env n).graph
      outputOne := invariant.expectedOutputOne n
      outputTwo := invariant.expectedOutputTwo n }

/-- The actual product control satisfies the supplied proof-side invariant at
every time.  This is the only induction in the adapter. -/
theorem stateInvariant_globalStateTrace
    [Fintype In₁] [Fintype In₂]
    {env : EnvironmentSequence In₁ In₂}
    (invariant : controller.LiteralCrossGraphTraceInvariant env) :
    ∀ n : Nat,
      invariant.StateInvariant
        (controller.globalMachine.globalStateTrace env n) n := by
  intro n
  induction n with
  | zero =>
      exact invariant.initial
  | succ n ih =>
      rw [FiniteGlobalRoundMachine.globalStateTrace_succ]
      change invariant.StateInvariant
        (controller.advanceControls
          (controller.globalMachine.globalStateTrace env n) (env n)) (n + 1)
      cases hgraph : (env n).graph with
      | left =>
          simpa [FinitePairedPhysicalController.advanceControls, hgraph] using
            invariant.leftStep n
              (controller.globalMachine.globalStateTrace env n) ih hgraph
      | right =>
          simpa [FinitePairedPhysicalController.advanceControls, hgraph] using
            invariant.rightStep n
              (controller.globalMachine.globalStateTrace env n) ih hgraph
      | both =>
          simpa [FinitePairedPhysicalController.advanceControls, hgraph] using
            invariant.bothStep n
              (controller.globalMachine.globalStateTrace env n) ih hgraph

/-- The per-round local equations identify the complete controller word with
the reference word.  All later cut and DPA arguments can therefore be carried
out solely on the reference word. -/
theorem globalMachineTraceWord_eq_referenceWord
    [Fintype In₁] [Fintype In₂]
    {env : EnvironmentSequence In₁ In₂}
    (invariant : controller.LiteralCrossGraphTraceInvariant env) :
    controller.globalMachine.globalMachineTraceWord controller.globalOutputOne
        controller.globalOutputTwo env =
      invariant.referenceWord controller := by
  funext n
  have hstate := invariant.stateInvariant_globalStateTrace controller (n + 1)
  obtain ⟨hone, htwo⟩ := invariant.outputs n
    (controller.globalMachine.globalStateTrace env (n + 1)) hstate
  unfold FiniteGlobalRoundMachine.globalMachineTraceWord referenceWord
    FinitePairedPhysicalController.globalOutputOne
    FinitePairedPhysicalController.globalOutputTwo
  rw [hone, htwo]

end LiteralCrossGraphTraceInvariant

end

end FinitePairedPhysicalController

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

/-! ## Canonical schedule data for one simulated hard-regime trace -/

/-- One graph-split trace invariant together with the canonical scheduled
interpretation of its reference word.

The two final fields concern only the proof-side reference word.  The generic
word-equality theorem transports them to the actual controller trace. -/
structure FinitePairedPhysicalControllerCanonicalLiteralCrossTraceWitness
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (controller :
      FinitePairedPhysicalController.{u, v, x, y, w, w}
        In₁ In₂ Out₁ Out₂)
    (physicalEnv : EnvironmentSequence In₁ In₂) where
  trace : controller.LiteralCrossGraphTraceInvariant physicalEnv
  base : Nat
  anchor : ProfiledRawJointGuardedCommonTailPolicyAnchor A strategy
  hterm : OperationalStrictRunsTerminate
    (profiledRawJointPhysicalGraphTail physicalEnv base)
  rowAt : Nat → PairedEntryRow
  referenceEntryStateAt : ∀ k : Nat,
    let schedule :=
      profiledRawJointUnitPolicyPhysicalCloseSchedule A strategy
        anchor.initial anchor.policy anchor.bank physicalEnv base hterm
          anchor.seed rowAt
    let cuts :=
      profiledRawJointUnitPolicyRootOrientedCuts A strategy anchor.initial
        anchor.policy anchor.bank physicalEnv base hterm anchor.seed schedule
    let root :=
      profiledRawJointUnitPolicyScheduledRoot A strategy anchor.initial
        anchor.policy anchor.bank anchor.seed schedule k
    let query := schedule k root
    A.run (trace.referenceWord controller) (base + cuts k) =
      query.entryState A strategy anchor.initial anchor.policy
  referenceEmittedRoundAt : ∀ k : Nat,
    let schedule :=
      profiledRawJointUnitPolicyPhysicalCloseSchedule A strategy
        anchor.initial anchor.policy anchor.bank physicalEnv base hterm
          anchor.seed rowAt
    let cuts :=
      profiledRawJointUnitPolicyRootOrientedCuts A strategy anchor.initial
        anchor.policy anchor.bank physicalEnv base hterm anchor.seed schedule
    let root :=
      profiledRawJointUnitPolicyScheduledRoot A strategy anchor.initial
        anchor.policy anchor.bank anchor.seed schedule k
    let query := schedule k root
    ∀ (j : Nat)
      (hj : j <
        (query.records A strategy anchor.initial anchor.policy
          anchor.bank).length),
      trace.referenceWord controller (base + cuts k + j) =
        (query.records A strategy anchor.initial anchor.policy
          anchor.bank)[j]'hj

/-- Transport the canonical schedule interpretation across the one generic
trace-word equality. -/
noncomputable def
    FinitePairedPhysicalControllerCanonicalLiteralCrossTraceWitness.toCanonicalAcceptanceWitness
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {controller :
      FinitePairedPhysicalController.{u, v, x, y, w, w}
        In₁ In₂ Out₁ Out₂}
    {physicalEnv : EnvironmentSequence In₁ In₂}
    (witness :
      FinitePairedPhysicalControllerCanonicalLiteralCrossTraceWitness A
        strategy controller physicalEnv) :
    ProfiledRawJointGuardedCommonLiteralCrossCanonicalAcceptanceWitness A
      strategy controller.globalMachine controller.globalOutputOne
        controller.globalOutputTwo physicalEnv where
  base := witness.base
  anchor := witness.anchor
  hterm := witness.hterm
  rowAt := witness.rowAt
  alignment :=
    { entryStateAt := by
        intro k
        rw [witness.trace.globalMachineTraceWord_eq_referenceWord controller]
        exact witness.referenceEntryStateAt k
      emittedRoundAt := by
        intro k
        dsimp only
        intro j hj
        rw [witness.trace.globalMachineTraceWord_eq_referenceWord controller]
        exact witness.referenceEmittedRoundAt k j hj }

/-! ## Environment and strategy-indexed assembly -/

/-- All operational data owed by one fixed controller in one environment.
The hard regimes use graph-split trace witnesses; the two fixed strict tails
retain their already-established parity proofs. -/
structure FinitePairedPhysicalControllerLiteralCrossTraceExtraction
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (controller :
      FinitePairedPhysicalController.{u, v, x, y, w, w}
        In₁ In₂ Out₁ Out₂)
    (physicalEnv : EnvironmentSequence In₁ In₂) where
  fixedRight :
    EventuallyStrictRight (fun n ↦ (physicalEnv n).graph) →
      ∃ start : Nat, NatSeqMinEvenParity
        (fun n ↦ A.priority
          (A.run
            (controller.globalMachine.globalMachineTraceWord
              controller.globalOutputOne controller.globalOutputTwo
                physicalEnv)
            (start + n)))
  fixedLeft :
    EventuallyStrictLeft (fun n ↦ (physicalEnv n).graph) →
      ∃ start : Nat, NatSeqMinEvenParity
        (fun n ↦ A.priority
          (A.run
            (controller.globalMachine.globalMachineTraceWord
              controller.globalOutputOne controller.globalOutputTwo
                physicalEnv)
            (start + n)))
  recurrentTrace :
    ∀ _hboth : GraphBothRecurrent (fun n ↦ (physicalEnv n).graph),
      FinitePairedPhysicalControllerCanonicalLiteralCrossTraceWitness A
        strategy controller physicalEnv
  reversalTrace :
    ∀ _hreversal :
        PersistentStrictReversalTail (fun n ↦ (physicalEnv n).graph),
      FinitePairedPhysicalControllerCanonicalLiteralCrossTraceWitness A
        strategy controller physicalEnv

/-- The finite graph-split obligations assemble the existing canonical
acceptance package. -/
noncomputable def
    FinitePairedPhysicalControllerLiteralCrossTraceExtraction.toCanonicalAcceptance
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {controller :
      FinitePairedPhysicalController.{u, v, x, y, w, w}
        In₁ In₂ Out₁ Out₂}
    {physicalEnv : EnvironmentSequence In₁ In₂}
    (extraction :
      FinitePairedPhysicalControllerLiteralCrossTraceExtraction A strategy
        controller physicalEnv) :
    FinitePairedPhysicalControllerCanonicalLiteralCrossAcceptance A strategy
      controller physicalEnv where
  fixedRight := extraction.fixedRight
  fixedLeft := extraction.fixedLeft
  recurrentAlignment hboth :=
    (extraction.recurrentTrace hboth).toCanonicalAcceptanceWitness A
  reversalAlignment hreversal :=
    (extraction.reversalTrace hreversal).toCanonicalAcceptanceWitness A

/-- Strategy-indexed version of the finite per-round trace obligations. -/
def PerStrategyWinningFinitePairedPhysicalControllerLiteralCrossTraceExtraction :
    Prop :=
  ∀ strategy : StrategyPair In₁ In₂ Out₁ Out₂,
    (∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)) →
      ∃ controller :
          FinitePairedPhysicalController.{u, v, x, y, w, w}
            In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          Nonempty
            (FinitePairedPhysicalControllerLiteralCrossTraceExtraction A
              strategy controller env)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- One-arrow conversion from per-round graph-split equations to the exact
canonical literal-cross extraction consumed by physical acceptance. -/
theorem
    perStrategyWinningFinitePairedPhysicalControllerCanonicalLiteralCrossAcceptance_of_traceExtraction
    (hextract :
      PerStrategyWinningFinitePairedPhysicalControllerLiteralCrossTraceExtraction.{u,
        v, x, y, s, w} A) :
    PerStrategyWinningFinitePairedPhysicalControllerCanonicalLiteralCrossAcceptance.{u,
      v, x, y, s, w} A := by
  intro strategy hwin
  obtain ⟨controller, htrace⟩ := hextract strategy hwin
  refine ⟨controller, fun env ↦ ?_⟩
  obtain ⟨extraction⟩ := htrace env
  exact ⟨extraction.toCanonicalAcceptance A⟩

/-- Final direct readback consumer for a concrete product carrier proved by
the finite graph-split trace obligations above. -/
theorem exists_readbackUpgrade_of_finitePairedPhysicalControllerTraceExtraction
    (fallback : LocalSummaryAutomaton.{u, v, w} In₁ In₂)
    (hextract :
      PerStrategyWinningFinitePairedPhysicalControllerLiteralCrossTraceExtraction.{u,
        v, x, y, s, w} A) :
    ∃ M : LocalSummaryAutomaton.{u, v, w} In₁ In₂,
      M.ReadbackUpgrade (Out₁ := Out₁) (Out₂ := Out₂) A := by
  exact
    exists_readbackUpgrade_of_finitePairedPhysicalControllerCanonicalLiteralCross
      A fallback
        (perStrategyWinningFinitePairedPhysicalControllerCanonicalLiteralCrossAcceptance_of_traceExtraction
          A hextract)

end


end DetParityAutomaton

end DistributedSynthesis
