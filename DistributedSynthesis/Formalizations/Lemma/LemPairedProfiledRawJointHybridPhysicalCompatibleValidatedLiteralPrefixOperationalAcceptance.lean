/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedLiteralPrefixPolicy
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleExtraOperationalAcceptance

/-!
# Reusable unmarked operational endpoint for validated literal-prefix policies

This file specializes the generic current-valid acceptance adapter to the
actual replace-only literal-prefix annotation.  It fills the generic seed,
validity predicate, and update map definitionally.  Therefore the one
remaining hard-regime construction has a compact signature: choose one
validated literal-prefix policy, walk one root-started path of that policy,
and align the actual physical cut minima with one accepted coded lineage.

Only the finite physical controller is selected before the environment.  The
semantic root, policy, path, and alignment remain proof-side witnesses.

This module is intentionally retained as the generic unmarked specialization:
its `CurrentCompatible` disjunction is sufficient for positive-depth
provenance, but it does not make the root disjunct unique.  It must therefore
not be used as the finite bank endpoint.  The canonical bank-safe consumer is
`LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixOperationalAcceptance`,
whose fresh-root bit pins the root and whose hard paths use policies already
selected in the finite `CommonControl` bank.
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

private abbrev LiteralExtra :=
  ProfiledRawJointHybridLiteralPrefixEdgeAnnotation A

private abbrev LiteralPolicy
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleValidatedLiteralPrefixPolicy A
    strategy hwin initial

private abbrev LiteralPath
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : LiteralPolicy A strategy hwin initial) :=
  ProfiledRawJointHybridPhysicalCompatibleValidatedExtraAllowedPath A
    strategy hwin policy

private abbrev PhysicalController :=
  FinitePairedPhysicalController.{u, v, x, y, w, w}
    In₁ In₂ Out₁ Out₂

/-- The exact concrete hard-regime witness still owed by the shared-fibre
Tail.  All current-valid annotation fields have already been instantiated. -/
abbrev
    ProfiledRawJointHybridPhysicalCompatibleValidatedLiteralPrefixHardCertificateBundle
    (controller : PhysicalController (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂))
    (env : EnvironmentSequence In₁ In₂) :=
  Σ initial : ProfiledRawJointCommonBaseWorld A strategy,
    Σ policy : LiteralPolicy A strategy hwin initial,
      Σ path : LiteralPath A strategy hwin policy,
        Σ start : Nat, Σ cuts : Nat → Nat,
          ProfiledRawJointHybridPhysicalCompatibleValidatedExtraPhysicalCutAlignment
            A strategy hwin path controller.globalMachine
              controller.globalOutputOne controller.globalOutputTwo env start
                cuts

/-- Insert the concrete seed, current-validity relation, and replace-only
advance map into the generic hard certificate. -/
noncomputable def
    ProfiledRawJointHybridPhysicalCompatibleValidatedLiteralPrefixHardCertificateBundle.toExtraBundle
    {controller : PhysicalController (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {env : EnvironmentSequence In₁ In₂}
    (bundle :
      ProfiledRawJointHybridPhysicalCompatibleValidatedLiteralPrefixHardCertificateBundle
        A strategy hwin controller env) :
    ProfiledRawJointHybridPhysicalCompatibleExtraHardCertificateBundle A
      strategy hwin (Extra := LiteralExtra A) controller env := by
  rcases bundle with ⟨initial, policy, path, start, cuts, alignment⟩
  exact ⟨initial,
    profiledRawJointHybridLiteralPrefixSeedAnnotation A strategy hwin initial,
    ProfiledRawJointHybridLiteralPrefixCurrentCompatible A strategy hwin
      initial,
    profiledRawJointHybridLiteralPrefixAnnotationAdvance A strategy hwin,
    policy, path, start, cuts, alignment⟩

/-- Four-regime bookkeeping at the fully concrete validated annotation. -/
structure
    ProfiledRawJointHybridPhysicalCompatibleValidatedLiteralPrefixControllerBookkeeping
    (controller : PhysicalController (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂))
    (env : EnvironmentSequence In₁ In₂) : Prop where
  recurrent : GraphBothRecurrent (fun n ↦ (env n).graph) →
    Nonempty
      (ProfiledRawJointHybridPhysicalCompatibleValidatedLiteralPrefixHardCertificateBundle
        A strategy hwin controller env)
  reversal : PersistentStrictReversalTail (fun n ↦ (env n).graph) →
    Nonempty
      (ProfiledRawJointHybridPhysicalCompatibleValidatedLiteralPrefixHardCertificateBundle
        A strategy hwin controller env)
  fixed : EventuallyInstalledOutputTailBookkeeping A controller env

namespace
  ProfiledRawJointHybridPhysicalCompatibleValidatedLiteralPrefixControllerBookkeeping

/-- Forget only the concrete names; the current-valid policy and its path are
preserved exactly. -/
noncomputable def toExtraBookkeeping
    {controller : PhysicalController (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {env : EnvironmentSequence In₁ In₂}
    (bookkeeping :
      ProfiledRawJointHybridPhysicalCompatibleValidatedLiteralPrefixControllerBookkeeping
        A strategy hwin controller env) :
    ProfiledRawJointHybridPhysicalCompatibleExtraControllerBookkeeping A
      strategy hwin (Extra := LiteralExtra A) controller env where
  recurrent := fun hboth ↦
    ⟨(Classical.choice (bookkeeping.recurrent hboth)).toExtraBundle A
      strategy hwin⟩
  reversal := fun hreversal ↦
    ⟨(Classical.choice (bookkeeping.reversal hreversal)).toExtraBundle A
      strategy hwin⟩
  fixed := bookkeeping.fixed

end
  ProfiledRawJointHybridPhysicalCompatibleValidatedLiteralPrefixControllerBookkeeping

/-- Smallest strategy-indexed controller theorem that now reaches the generic
physical-acceptance and readback backends. -/
def
    PerStrategyWinningValidatedLiteralPrefixControllerBookkeeping : Prop :=
  ∀ (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)),
    ∃ controller :
        FinitePairedPhysicalController.{u, v, x, y, w, w}
          In₁ In₂ Out₁ Out₂,
      ∀ env : EnvironmentSequence In₁ In₂,
        ProfiledRawJointHybridPhysicalCompatibleValidatedLiteralPrefixControllerBookkeeping
          A strategy hwin controller env

/-- The concrete validated literal-prefix premise fills the generic
current-valid operational endpoint. -/
theorem
    perStrategyWinningPhysicalCompatibleExtraControllerBookkeeping_of_validatedLiteralPrefix
    (hbookkeeping :
      PerStrategyWinningValidatedLiteralPrefixControllerBookkeeping.{u, v,
        x, y, s, w} A) :
    PerStrategyWinningPhysicalCompatibleExtraControllerBookkeeping.{u, v, x,
      y, s, max u v x y s, w} A
      (Extra := LiteralExtra A) := by
  intro strategy hwin
  obtain ⟨controller, hcontroller⟩ := hbookkeeping strategy hwin
  refine ⟨controller, fun env ↦ ?_⟩
  exact (hcontroller env).toExtraBookkeeping A strategy hwin

/-- One-arrow readback extraction from the exact remaining concrete
controller theorem. -/
theorem exists_readbackUpgrade_of_validatedLiteralPrefixBookkeeping
    (fallback : LocalSummaryAutomaton.{u, v, w} In₁ In₂)
    (hbookkeeping :
      PerStrategyWinningValidatedLiteralPrefixControllerBookkeeping.{u, v,
        x, y, s, w} A) :
    ∃ M : LocalSummaryAutomaton.{u, v, w} In₁ In₂,
      M.ReadbackUpgrade (Out₁ := Out₁) (Out₂ := Out₂) A := by
  exact exists_readbackUpgrade_of_physicalCompatibleExtraBookkeeping A
    fallback
      (perStrategyWinningPhysicalCompatibleExtraControllerBookkeeping_of_validatedLiteralPrefix
        A hbookkeeping)

end

end DetParityAutomaton

end DistributedSynthesis
