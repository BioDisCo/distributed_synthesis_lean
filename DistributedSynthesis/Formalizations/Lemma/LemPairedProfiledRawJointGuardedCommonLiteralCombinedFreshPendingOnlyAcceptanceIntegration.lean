/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonCodePhysicalAcceptance
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshPendingOnlyPhysicalAcceptance
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedInitialCommonPolicyBank

/-!
# Final extraction socket for the pending-only literal-table controller

The controller, its acknowledged-relay simulation, and the accepting stream
of exact installed child codes are already unconditional.  This file records
the exact four-regime acceptance socket for that controller: recurrent
communication, persistent strict reversal, and the two eventually fixed
strict directions.  It is a conditional diagnostic endpoint, not the final
unconditional route.

The operational-close audit showed why the present pending-only controller
does not fill this socket.  During a repeated strict run the receiver refreshes
its table every round while the nonreceiver retains its old key.  Consequently
the close-key theorem alone supplies neither the DPA entry-state equation nor
the emitted-record equation after the first round of the block.  The positive
route must repair the local phase/live-stage carrier before using the separate
readback socket in
`LemPairedProfiledRawJointGuardedCommonPhaseLiveStageReadbackSocket`.

Two stronger code/physical bridges are retained as optional sufficient
routes.  Neither is the claimed mixed-graph obligation.  The fixed-offset
`GuardedCommonCodePhysicalCoupling` misaligns a freshly installed child code
with the old table emitting the current strict-round output.  The single-code
time cut coupling is likewise clock-sensitive on a strict block: the code
controller advances on every physical round whereas one raw block closes only
at its reversal.

This file performs the complete integration around that equation:

* inputs and graphs are projected from the actual environment;
* accepted codes are the exact literal children installed by the controller;
* the physical word is the controller's canonical table-only reference word;
* optional accepted-code pointwise or cut transfer can prove that reference
  word when their stronger hypotheses happen to hold;
* the diagnostic endpoint assembles the four actual graph regimes directly;
* the acknowledged trace equality transports acceptance to the real finite
  controller; and
* a default finite common seed yields the strategy-indexed extraction shape.

Both couplings are proof-only.  No executable map below receives a graph,
orientation, hierarchy side, leader bit, strict-leader bit, history, or
semantic view.
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

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

private abbrev CommonPoint :=
  ProfiledRawJointGuardedCommonSemanticPoint A strategy

private abbrev CrossValid :=
  ProfiledRawJointGuardedCommonLiteralCrossExtraValid A strategy hwin

namespace ProfiledRawJointGuardedCommonDecoratedPolicyPackage

variable {initial : CommonPoint A strategy}

private abbrev Package :=
  ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy hwin initial
    (CrossValid A strategy hwin)

/-! ## The exact two words supplied to the generic coupling -/

/-- Physical input pair read from one actual environment round. -/
def literalCombinedFreshPendingOnlyRootEnvironmentInputs
    (env : EnvironmentSequence In₁ In₂) : Nat → In₁ × In₂ :=
  fun n ↦ ((env n).inputOne, (env n).inputTwo)

/-- Proof-side graph stream used only to select the corresponding local
freshness product transition. -/
def literalCombinedFreshPendingOnlyRootEnvironmentGraphs
    (env : EnvironmentSequence In₁ In₂) : Nat → Graph :=
  fun n ↦ (env n).graph

/-- The accepted exact installed-child code stream for an environment. -/
def literalCombinedFreshPendingOnlyRootCodeWord
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) :=
  package.literalCombinedFreshPendingInstalledChildCodeWord A strategy hwin
    (literalCombinedFreshPendingOnlyRootEnvironmentInputs env)
    (literalCombinedFreshPendingOnlyRootEnvironmentGraphs env)

/-- The installed-child code word in the coupling is accepted
unconditionally by the one decorated rational policy. -/
theorem literalCombinedFreshPendingOnlyRootCodeWord_accepts
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) :
    (profiledRawJointGuardedCommonCodeParityDPA A
      (initial.code A strategy)).Accepts
        (package.literalCombinedFreshPendingOnlyRootCodeWord A strategy hwin
          env) := by
  exact package.literalCombinedFreshPendingInstalledChildCodeWord_accepts A
    strategy hwin
      (literalCombinedFreshPendingOnlyRootEnvironmentInputs env)
      (literalCombinedFreshPendingOnlyRootEnvironmentGraphs env)

/-! ## One-arrow consumption of the exact physical coupling -/

/-- The single exact code/physical coupling proves the canonical reference
word. -/
theorem literalCombinedFreshPendingOnlyRootReferenceWord_accepts_of_coupling
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂)
    (coupling : GuardedCommonCodePhysicalCoupling A
      (initial.code A strategy)
      (package.literalCombinedFreshPendingOnlyRootCodeWord A strategy hwin env)
      (package.literalCombinedFreshPendingOnlyRootReferenceWord A strategy
        hwin env)) :
    A.Accepts
      (package.literalCombinedFreshPendingOnlyRootReferenceWord A strategy
        hwin env) := by
  exact coupling.physicalWord_accepts A
    (package.literalCombinedFreshPendingOnlyRootCodeWord_accepts A strategy
      hwin env)

/-- Acceptance transfers to the actual finite controller word.  Relay IDs,
acknowledgements, and Mooreization have already disappeared behind the proved
trace equality. -/
theorem literalCombinedFreshPendingOnlyRootTraceWord_accepts_of_coupling
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂)
    (coupling : GuardedCommonCodePhysicalCoupling A
      (initial.code A strategy)
      (package.literalCombinedFreshPendingOnlyRootCodeWord A strategy hwin env)
      (package.literalCombinedFreshPendingOnlyRootReferenceWord A strategy
        hwin env)) :
    let controller :=
      package.literalCombinedFreshPendingOnlyRootPhysicalController A strategy
        hwin
    A.Accepts
      (controller.globalMachine.globalMachineTraceWord
        controller.globalOutputOne controller.globalOutputTwo env) := by
  dsimp only
  rw [package.literalCombinedFreshPendingOnlyRootTraceWord_eq_referenceWord A
    strategy hwin env]
  exact package.literalCombinedFreshPendingOnlyRootReferenceWord_accepts_of_coupling
    A strategy hwin env coupling

/-- Fixed-strategy extraction endpoint.  Supplying the one proof-side
coupling in every environment produces the genuinely local finite physical
controller expected by direct readback. -/
theorem exists_literalCombinedFreshPendingOnlyRootController_of_coupling
    (package : Package A strategy hwin (initial := initial))
    (hcoupling : ∀ env : EnvironmentSequence In₁ In₂,
      Nonempty (GuardedCommonCodePhysicalCoupling A
        (initial.code A strategy)
        (package.literalCombinedFreshPendingOnlyRootCodeWord A strategy hwin
          env)
        (package.literalCombinedFreshPendingOnlyRootReferenceWord A strategy
          hwin env))) :
    ∃ controller :
        FinitePairedPhysicalController.{u, v, x, y,
          max (max (max (max s u) v) x) y,
          max (max (max (max s u) v) x) y}
          In₁ In₂ Out₁ Out₂,
      ∀ env : EnvironmentSequence In₁ In₂,
        A.Accepts
          (controller.globalMachine.globalMachineTraceWord
            controller.globalOutputOne controller.globalOutputTwo env) := by
  let controller :=
    package.literalCombinedFreshPendingOnlyRootPhysicalController A strategy
      hwin
  refine ⟨controller, fun env ↦ ?_⟩
  obtain ⟨coupling⟩ := hcoupling env
  exact package.literalCombinedFreshPendingOnlyRootTraceWord_accepts_of_coupling
    A strategy hwin env coupling

/-- Conditional fixed-strategy extraction endpoint through the stronger
single-code-time cut coupling.  It is useful when separately available, but
is not the mixed-graph obligation of the unconditional route. -/
theorem exists_literalCombinedFreshPendingOnlyRootController_of_cutCoupling
    (package : Package A strategy hwin (initial := initial))
    (hcoupling : ∀ env : EnvironmentSequence In₁ In₂,
      Nonempty
        (LiteralCombinedFreshPendingOnlyRootPhysicalPriorityCoupling A
          strategy hwin package env)) :
    ∃ controller :
        FinitePairedPhysicalController.{u, v, x, y,
          max (max (max (max s u) v) x) y,
          max (max (max (max s u) v) x) y}
          In₁ In₂ Out₁ Out₂,
      ∀ env : EnvironmentSequence In₁ In₂,
        A.Accepts
          (controller.globalMachine.globalMachineTraceWord
            controller.globalOutputOne controller.globalOutputTwo env) := by
  let controller :=
    package.literalCombinedFreshPendingOnlyRootPhysicalController A strategy
      hwin
  refine ⟨controller, fun env ↦ ?_⟩
  obtain ⟨coupling⟩ := hcoupling env
  exact coupling.rootTraceWord_accepts A strategy hwin

/-! ## Exact four-regime physical-acceptance socket -/

/-- The two genuinely hard physical regimes for the fixed pending-only
controller.  Recurrent synchronization supplies an epoch coupling; a
persistent strict-reversal tail supplies parity of one actual physical tail.

The eventually fixed right/left tails are deliberately absent.  They are the
standard one-sided member-monitor arguments and are passed separately to the
assembly below.  This separation prevents the false consecutive-code clock
from being smuggled into a fixed-direction tail. -/
structure LiteralCombinedFreshPendingOnlyHardRegimeAcceptance
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) where
  recurrent :
    GraphBothRecurrent (fun n ↦ (env n).graph) →
      A.FiniteGlobalMachineEpochCoupling
        (package.literalCombinedFreshPendingOnlyRootPhysicalController A
          strategy hwin).globalMachine
        (package.literalCombinedFreshPendingOnlyRootPhysicalController A
          strategy hwin).globalOutputOne
        (package.literalCombinedFreshPendingOnlyRootPhysicalController A
          strategy hwin).globalOutputTwo env
  alternatingTail :
    PersistentStrictReversalTail (fun n ↦ (env n).graph) →
      ∃ start : Nat, NatSeqMinEvenParity
        (fun n ↦ A.priority
          (A.run
            ((package.literalCombinedFreshPendingOnlyRootPhysicalController A
              strategy hwin).globalMachine.globalMachineTraceWord
              (package.literalCombinedFreshPendingOnlyRootPhysicalController A
                strategy hwin).globalOutputOne
              (package.literalCombinedFreshPendingOnlyRootPhysicalController A
                strategy hwin).globalOutputTwo env)
            (start + n)))

/-- The two standard fixed-direction tail fields, kept separate from the
hard clock-sensitive regimes above. -/
structure LiteralCombinedFreshPendingOnlyFixedTailAcceptance
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) : Prop where
  strictRight :
    EventuallyStrictRight (fun n ↦ (env n).graph) →
      ∃ start : Nat, NatSeqMinEvenParity
        (fun n ↦ A.priority
          (A.run
            ((package.literalCombinedFreshPendingOnlyRootPhysicalController A
              strategy hwin).globalMachine.globalMachineTraceWord
              (package.literalCombinedFreshPendingOnlyRootPhysicalController A
                strategy hwin).globalOutputOne
              (package.literalCombinedFreshPendingOnlyRootPhysicalController A
                strategy hwin).globalOutputTwo env)
            (start + n)))
  strictLeft :
    EventuallyStrictLeft (fun n ↦ (env n).graph) →
      ∃ start : Nat, NatSeqMinEvenParity
        (fun n ↦ A.priority
          (A.run
            ((package.literalCombinedFreshPendingOnlyRootPhysicalController A
              strategy hwin).globalMachine.globalMachineTraceWord
              (package.literalCombinedFreshPendingOnlyRootPhysicalController A
                strategy hwin).globalOutputOne
              (package.literalCombinedFreshPendingOnlyRootPhysicalController A
                strategy hwin).globalOutputTwo env)
            (start + n)))

/-- The hard and fixed-tail packages assemble the repository's exhaustive
four-regime physical-acceptance interface without any code-clock assumption. -/
noncomputable def literalCombinedFreshPendingOnlyPhysicalAcceptance
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂)
    (hard : LiteralCombinedFreshPendingOnlyHardRegimeAcceptance A strategy
      hwin package env)
    (fixed : LiteralCombinedFreshPendingOnlyFixedTailAcceptance A strategy
      hwin package env) :
    A.FiniteGlobalMachinePhysicalAcceptance
      (package.literalCombinedFreshPendingOnlyRootPhysicalController A
        strategy hwin).globalMachine
      (package.literalCombinedFreshPendingOnlyRootPhysicalController A
        strategy hwin).globalOutputOne
      (package.literalCombinedFreshPendingOnlyRootPhysicalController A
        strategy hwin).globalOutputTwo env where
  recurrent := hard.recurrent
  alternatingTail := hard.alternatingTail
  strictRightTail := fixed.strictRight
  strictLeftTail := fixed.strictLeft

/-- Four-regime data proves the actual finite-controller word directly. -/
theorem literalCombinedFreshPendingOnlyRootTraceWord_accepts_of_fourRegimes
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂)
    (hard : LiteralCombinedFreshPendingOnlyHardRegimeAcceptance A strategy
      hwin package env)
    (fixed : LiteralCombinedFreshPendingOnlyFixedTailAcceptance A strategy
      hwin package env) :
    let controller :=
      package.literalCombinedFreshPendingOnlyRootPhysicalController A strategy
        hwin
    A.Accepts
      (controller.globalMachine.globalMachineTraceWord
        controller.globalOutputOne controller.globalOutputTwo env) := by
  dsimp only
  exact A.finiteGlobalMachineTraceWord_accepts_of_physicalAcceptance _ _ _ env
    (package.literalCombinedFreshPendingOnlyPhysicalAcceptance A strategy hwin
      env hard fixed)

/-- Fixed-strategy extraction through the honest four-regime interface. -/
theorem exists_literalCombinedFreshPendingOnlyRootController_of_fourRegimes
    (package : Package A strategy hwin (initial := initial))
    (hhard : ∀ env : EnvironmentSequence In₁ In₂,
      Nonempty
        (LiteralCombinedFreshPendingOnlyHardRegimeAcceptance A strategy hwin
          package env))
    (hfixed : ∀ env : EnvironmentSequence In₁ In₂,
      Nonempty
        (LiteralCombinedFreshPendingOnlyFixedTailAcceptance A strategy hwin
          package env)) :
    ∃ controller :
        FinitePairedPhysicalController.{u, v, x, y,
          max (max (max (max s u) v) x) y,
          max (max (max (max s u) v) x) y}
          In₁ In₂ Out₁ Out₂,
      ∀ env : EnvironmentSequence In₁ In₂,
        A.Accepts
          (controller.globalMachine.globalMachineTraceWord
            controller.globalOutputOne controller.globalOutputTwo env) := by
  let controller :=
    package.literalCombinedFreshPendingOnlyRootPhysicalController A strategy
      hwin
  refine ⟨controller, fun env ↦ ?_⟩
  obtain ⟨hard⟩ := hhard env
  obtain ⟨fixed⟩ := hfixed env
  exact package.literalCombinedFreshPendingOnlyRootTraceWord_accepts_of_fourRegimes
    A strategy hwin env hard fixed

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

/-! ## A canonical default common root -/

/-- One fixed finite common seed.  It is construction data only; parity is
prefix independent, and the concrete coupling may discard the harmless
initial table prefix independently on its two sides. -/
def literalCombinedFreshPendingOnlyDefaultInitial :
    ProfiledRawJointGuardedCommonSemanticPoint A strategy :=
  profiledRawJointGuardedInitialCommonPoint A strategy
    (((default, default), (default, default)))

/-- The unconditionally selected decorated package at the default root. -/
noncomputable def literalCombinedFreshPendingOnlyDefaultPackage :=
  profiledRawJointGuardedCommonLiteralCrossDecoratedPolicyPackage A strategy
    hwin (literalCombinedFreshPendingOnlyDefaultInitial A strategy)

/-- Strategy-indexed form of the two genuinely hard graph regimes.  This is
the exact positive target left after the finite controller and its trace have
been constructed: recurrent communication must yield the existing epoch
coupling, and a persistent reversal tail must yield parity of the actual
physical tail. -/
def PerStrategyWinningLiteralCombinedFreshPendingOnlyHardRegimeAcceptance :
    Prop :=
  ∀ (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (env : EnvironmentSequence In₁ In₂),
    let package := literalCombinedFreshPendingOnlyDefaultPackage A strategy
      hwin
    Nonempty
      (ProfiledRawJointGuardedCommonDecoratedPolicyPackage.LiteralCombinedFreshPendingOnlyHardRegimeAcceptance
        A strategy hwin package env)

/-- Strategy-indexed form of the two standard eventually fixed-direction
tail arguments.  It is kept distinct from the hard regimes so that no false
code clock can enter those one-sided proofs. -/
def PerStrategyWinningLiteralCombinedFreshPendingOnlyFixedTailAcceptance :
    Prop :=
  ∀ (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (env : EnvironmentSequence In₁ In₂),
    let package := literalCombinedFreshPendingOnlyDefaultPackage A strategy
      hwin
    Nonempty
      (ProfiledRawJointGuardedCommonDecoratedPolicyPackage.LiteralCombinedFreshPendingOnlyFixedTailAcceptance
        A strategy hwin package env)

/-- The two named four-regime obligations yield the strategy-indexed finite
physical controller.  No code/physical clock equation is assumed. -/
theorem
    perStrategyWinningFinitePairedPhysicalController_of_pendingOnlyFourRegimes
    (hhard :
      PerStrategyWinningLiteralCombinedFreshPendingOnlyHardRegimeAcceptance A)
    (hfixed :
      PerStrategyWinningLiteralCombinedFreshPendingOnlyFixedTailAcceptance A) :
    PerStrategyWinningFinitePairedPhysicalController.{u, v, x, y, s,
      max (max (max (max s u) v) x) y} A := by
  intro suppliedStrategy suppliedWin
  let package := literalCombinedFreshPendingOnlyDefaultPackage A
    suppliedStrategy suppliedWin
  exact
    package.exists_literalCombinedFreshPendingOnlyRootController_of_fourRegimes
      A suppliedStrategy suppliedWin
        (fun env ↦ hhard suppliedStrategy suppliedWin env)
        (fun env ↦ hfixed suppliedStrategy suppliedWin env)

/-- Four-regime physical acceptance feeds the direct finite-controller
readback theorem and supplies the existential local-summary upgrade consumed
by the star fold. -/
theorem exists_readbackUpgrade_of_pendingOnlyFourRegimes
    (fallback :
      LocalSummaryAutomaton.{u, v,
        max (max (max (max s u) v) x) y} In₁ In₂)
    (hhard :
      PerStrategyWinningLiteralCombinedFreshPendingOnlyHardRegimeAcceptance A)
    (hfixed :
      PerStrategyWinningLiteralCombinedFreshPendingOnlyFixedTailAcceptance A) :
    ∃ M :
        LocalSummaryAutomaton.{u, v,
          max (max (max (max s u) v) x) y} In₁ In₂,
      M.ReadbackUpgrade (Out₁ := Out₁) (Out₂ := Out₂) A := by
  exact exists_readbackUpgrade_of_finitePairedPhysicalController A fallback
    (perStrategyWinningFinitePairedPhysicalController_of_pendingOnlyFourRegimes
      A hhard hfixed)

/-- Strategy-indexed form of the optional single-code-time cut invariant. -/
def PerStrategyWinningLiteralCombinedFreshPendingOnlyCutCoupling : Prop :=
  ∀ (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (env : EnvironmentSequence In₁ In₂),
    let package := literalCombinedFreshPendingOnlyDefaultPackage A strategy
      hwin
    Nonempty
      (ProfiledRawJointGuardedCommonDecoratedPolicyPackage.LiteralCombinedFreshPendingOnlyRootPhysicalPriorityCoupling
        A strategy hwin package env)

/-- The optional productive-cut coupling family yields the strategy-indexed
finite physical controller in one arrow. -/
theorem
    perStrategyWinningFinitePairedPhysicalController_of_pendingOnlyCutCoupling
    (hcoupling :
      PerStrategyWinningLiteralCombinedFreshPendingOnlyCutCoupling A) :
    PerStrategyWinningFinitePairedPhysicalController.{u, v, x, y, s,
      max (max (max (max s u) v) x) y} A := by
  intro suppliedStrategy suppliedWin
  let package := literalCombinedFreshPendingOnlyDefaultPackage A
    suppliedStrategy suppliedWin
  exact
    package.exists_literalCombinedFreshPendingOnlyRootController_of_cutCoupling
      A suppliedStrategy suppliedWin (fun env ↦ hcoupling suppliedStrategy
        suppliedWin env)

/-- Once the stronger cut invariant is supplied, the pending-only controller
feeds the direct finite-controller readback theorem.  This is a sufficient
conditional route, not the residual obligation of the four-regime route. -/
theorem exists_readbackUpgrade_of_pendingOnlyCutCoupling
    (fallback :
      LocalSummaryAutomaton.{u, v,
        max (max (max (max s u) v) x) y} In₁ In₂)
    (hcoupling :
      PerStrategyWinningLiteralCombinedFreshPendingOnlyCutCoupling A) :
    ∃ M :
        LocalSummaryAutomaton.{u, v,
          max (max (max (max s u) v) x) y} In₁ In₂,
      M.ReadbackUpgrade (Out₁ := Out₁) (Out₂ := Out₂) A := by
  exact exists_readbackUpgrade_of_finitePairedPhysicalController A fallback
    (perStrategyWinningFinitePairedPhysicalController_of_pendingOnlyCutCoupling
      A hcoupling)

/-- Optional stronger fixed-offset bridge.  The mixed-graph construction does
not owe this pointwise statement; use the four-regime interface for the main
route. -/
def PerStrategyWinningLiteralCombinedFreshPendingOnlyCoupling : Prop :=
  ∀ (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (env : EnvironmentSequence In₁ In₂),
    let initial := literalCombinedFreshPendingOnlyDefaultInitial A strategy
    let package := literalCombinedFreshPendingOnlyDefaultPackage A strategy
      hwin
    Nonempty (GuardedCommonCodePhysicalCoupling A
      (initial.code A strategy)
      (package.literalCombinedFreshPendingOnlyRootCodeWord A strategy hwin env)
      (package.literalCombinedFreshPendingOnlyRootReferenceWord A strategy
        hwin env))

/-- A pointwise coupling family also yields the controller, when available. -/
theorem perStrategyWinningFinitePairedPhysicalController_of_pendingOnlyCoupling
    (hcoupling :
      PerStrategyWinningLiteralCombinedFreshPendingOnlyCoupling A) :
    PerStrategyWinningFinitePairedPhysicalController.{u, v, x, y, s,
      max (max (max (max s u) v) x) y} A := by
  intro suppliedStrategy suppliedWin
  let initial := literalCombinedFreshPendingOnlyDefaultInitial A
    suppliedStrategy
  let package := literalCombinedFreshPendingOnlyDefaultPackage A
    suppliedStrategy suppliedWin
  exact package.exists_literalCombinedFreshPendingOnlyRootController_of_coupling
    A suppliedStrategy suppliedWin (fun env ↦ hcoupling suppliedStrategy
      suppliedWin env)

/-- Optional fixed-offset readback theorem. -/
theorem exists_readbackUpgrade_of_pendingOnlyCoupling
    (fallback :
      LocalSummaryAutomaton.{u, v,
        max (max (max (max s u) v) x) y} In₁ In₂)
    (hcoupling :
      PerStrategyWinningLiteralCombinedFreshPendingOnlyCoupling A) :
    ∃ M :
        LocalSummaryAutomaton.{u, v,
          max (max (max (max s u) v) x) y} In₁ In₂,
      M.ReadbackUpgrade (Out₁ := Out₁) (Out₂ := Out₂) A := by
  exact exists_readbackUpgrade_of_finitePairedPhysicalController A fallback
    (perStrategyWinningFinitePairedPhysicalController_of_pendingOnlyCoupling A
      hcoupling)

end

end DetParityAutomaton

end DistributedSynthesis
