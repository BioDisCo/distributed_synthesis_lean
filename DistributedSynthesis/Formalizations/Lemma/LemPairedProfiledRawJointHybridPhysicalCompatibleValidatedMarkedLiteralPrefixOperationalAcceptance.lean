/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixPolicyBank
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleExtraOperationalAcceptance

/-!
# Canonical operational endpoint for the marked literal-policy bank

This is the bank-safe specialization of the generic current-valid operational
consumer.  Unlike the earlier unmarked specialization, a hard witness does
not choose a fresh rational policy under the environment quantifier.  It
chooses only a finite `CommonControl` index and follows the policy already
stored in the globally selected marked bank at that index.

Thus the quantifier order is explicit:

1. fix `A`, a winning strategy, and its all-environment proof;
2. select the finite marked policy bank and physical controller;
3. for each environment, identify a finite bank index, a path in that fixed
   entry, and the proof-only parity cuts.

The remaining construction obligation is consequently operational: make the
finite physical controller's actual cut blocks equal the selected bank path's
literal record blocks.  No semantic source, graph, hierarchy side, leader
bit, or strict-leader bit is available to a runtime transition.
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

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

private abbrev MarkedExtra :=
  ProfiledRawJointHybridMarkedLiteralPrefixExtra A

private abbrev CommonControl :=
  ProfiledRawJointHybridCommonControl A strategy hwin

private abbrev Package
    (control : CommonControl A strategy hwin) :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixRootPackage A strategy
    hwin control

private abbrev BankPath
    (control : CommonControl A strategy hwin) :=
  ProfiledRawJointHybridPhysicalCompatibleValidatedExtraAllowedPath A strategy
    hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixRootPackageBank A
        strategy hwin control).policy

private abbrev PhysicalController :=
  FinitePairedPhysicalController.{u, v, x, y, w, w}
    In₁ In₂ Out₁ Out₂

/-! ## Hard witnesses drawn only from the preselected bank -/

/-- Smallest hard-regime certificate at the canonical bank endpoint.  The
policy is determined by the finite `control`; only the path and cut proof are
execution-specific. -/
abbrev
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankHardCertificateBundle
    (controller : PhysicalController (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂))
    (env : EnvironmentSequence In₁ In₂) :=
  Σ control : CommonControl A strategy hwin,
    Σ path : BankPath A strategy hwin control,
      Σ start : Nat, Σ cuts : Nat → Nat,
        ProfiledRawJointHybridPhysicalCompatibleValidatedExtraPhysicalCutAlignment
          A strategy hwin path controller.globalMachine
            controller.globalOutputOne controller.globalOutputTwo env start
              cuts

/-- Insert the marked seed, validity predicate, and replace-only advance map
into the generic accepted-path consumer.  The policy is literally the bank
entry; no second rationalization is performed. -/
noncomputable def
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankHardCertificateBundle.toExtraBundle
    {controller : PhysicalController (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {env : EnvironmentSequence In₁ In₂}
    (bundle :
      ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankHardCertificateBundle
        A strategy hwin controller env) :
    ProfiledRawJointHybridPhysicalCompatibleExtraHardCertificateBundle A
      strategy hwin (Extra := MarkedExtra A) controller env := by
  rcases bundle with ⟨control, path, start, cuts, alignment⟩
  let installed :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A strategy
      hwin control
  let package :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixRootPackageBank A
      strategy hwin control
  exact ⟨installed.world,
    profiledRawJointHybridMarkedLiteralPrefixInitial A strategy hwin
      installed.world,
    ProfiledRawJointHybridMarkedLiteralPrefixCurrentCompatible A strategy hwin
      installed.world,
    profiledRawJointHybridMarkedLiteralPrefixAdvance A strategy hwin,
    package.policy, path, start, cuts, alignment⟩

/-- Four-regime bookkeeping whose hard paths range only over the fixed marked
bank. -/
structure
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankControllerBookkeeping
    (controller : PhysicalController (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂))
    (env : EnvironmentSequence In₁ In₂) : Prop where
  recurrent : GraphBothRecurrent (fun n ↦ (env n).graph) →
    Nonempty
      (ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankHardCertificateBundle
        A strategy hwin controller env)
  reversal : PersistentStrictReversalTail (fun n ↦ (env n).graph) →
    Nonempty
      (ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankHardCertificateBundle
        A strategy hwin controller env)
  fixed : EventuallyInstalledOutputTailBookkeeping A controller env

namespace
  ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankControllerBookkeeping

/-- Forget only the concrete marked bank names.  The selected policy and path
remain literally unchanged. -/
noncomputable def toExtraBookkeeping
    {controller : PhysicalController (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {env : EnvironmentSequence In₁ In₂}
    (bookkeeping :
      ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankControllerBookkeeping
        A strategy hwin controller env) :
    ProfiledRawJointHybridPhysicalCompatibleExtraControllerBookkeeping A
      strategy hwin (Extra := MarkedExtra A) controller env where
  recurrent := fun hboth ↦
    ⟨(Classical.choice (bookkeeping.recurrent hboth)).toExtraBundle A
      strategy hwin⟩
  reversal := fun hreversal ↦
    ⟨(Classical.choice (bookkeeping.reversal hreversal)).toExtraBundle A
      strategy hwin⟩
  fixed := bookkeeping.fixed

end
  ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankControllerBookkeeping

/-! ## Canonical one-arrow consumer -/

/-- The exact remaining controller theorem after bank selection.  Only the
physical controller is existential before `env`; the finite marked policy
bank is already a definition from `A`, `strategy`, and `hwin`. -/
def
    PerStrategyWinningValidatedMarkedLiteralPrefixBankControllerBookkeeping :
    Prop :=
  ∀ (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)),
    ∃ controller :
        FinitePairedPhysicalController.{u, v, x, y, w, w}
          In₁ In₂ Out₁ Out₂,
      ∀ env : EnvironmentSequence In₁ In₂,
        ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankControllerBookkeeping
          A strategy hwin controller env

theorem
    perStrategyWinningPhysicalCompatibleExtraControllerBookkeeping_of_validatedMarkedLiteralPrefixBank
    (hbookkeeping :
      PerStrategyWinningValidatedMarkedLiteralPrefixBankControllerBookkeeping.{u,
        v, x, y, s, w} A) :
    PerStrategyWinningPhysicalCompatibleExtraControllerBookkeeping.{u, v, x,
      y, s, max u v x y s, w} A
      (Extra := MarkedExtra A) := by
  intro strategy hwin
  obtain ⟨controller, hcontroller⟩ := hbookkeeping strategy hwin
  refine ⟨controller, fun env ↦ ?_⟩
  exact (hcontroller env).toExtraBookkeeping A strategy hwin

/-- The canonical marked-bank route reaches `ReadbackUpgrade` in one arrow. -/
theorem exists_readbackUpgrade_of_validatedMarkedLiteralPrefixBankBookkeeping
    (fallback : LocalSummaryAutomaton.{u, v, w} In₁ In₂)
    (hbookkeeping :
      PerStrategyWinningValidatedMarkedLiteralPrefixBankControllerBookkeeping.{u,
        v, x, y, s, w} A) :
    ∃ M : LocalSummaryAutomaton.{u, v, w} In₁ In₂,
      M.ReadbackUpgrade (Out₁ := Out₁) (Out₂ := Out₂) A := by
  exact exists_readbackUpgrade_of_physicalCompatibleExtraBookkeeping A
    fallback
      (perStrategyWinningPhysicalCompatibleExtraControllerBookkeeping_of_validatedMarkedLiteralPrefixBank
        A hbookkeeping)

end

end DetParityAutomaton

end DistributedSynthesis
