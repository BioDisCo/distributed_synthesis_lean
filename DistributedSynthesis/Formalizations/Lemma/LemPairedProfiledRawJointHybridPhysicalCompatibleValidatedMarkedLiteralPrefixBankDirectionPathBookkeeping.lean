/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixPolicyBankDirectionPath
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixOperationalAcceptance

/-!
# Direction-path bookkeeping for the marked literal-prefix bank

This file is the quantifier-only adapter between the canonical direction path
through a fixed marked bank entry and the operational acceptance endpoint.
For each hard-regime environment, the proof may choose a finite bank index, a
stream of semantic directions, and parity cuts.  The executable controller was
already fixed before the environment and receives none of those witnesses.

The canonical direction path is an allowed path in the selected bank by
construction.  Consequently an alignment for that path is already the exact
hard certificate consumed by
`PerStrategyWinningValidatedMarkedLiteralPrefixBankControllerBookkeeping`.
No controller transition, semantic transition, or parity equation is proved
in this adapter; those remain precisely the fields of the supplied physical
cut alignment.
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

private abbrev CommonControl :=
  ProfiledRawJointHybridCommonControl A strategy hwin

private abbrev HybridDirection :=
  ProfiledRawJointHybridDirection (In₁ := In₁) (In₂ := In₂)

private abbrev PhysicalController :=
  FinitePairedPhysicalController.{u, v, x, y, w, w}
    In₁ In₂ Out₁ Out₂

/-! ## One hard-regime direction-path witness -/

/-- A physical cut alignment for the canonical path obtained by driving one
already selected marked bank entry with a proof-side direction stream. -/
abbrev
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankDirectionHardCertificateBundle
    (controller : PhysicalController (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂))
    (env : EnvironmentSequence In₁ In₂) :=
  Σ control : CommonControl A strategy hwin,
    Σ direction : Nat → HybridDirection (In₁ := In₁) (In₂ := In₂),
      Σ start : Nat, Σ cuts : Nat → Nat,
        ProfiledRawJointHybridPhysicalCompatibleValidatedExtraPhysicalCutAlignment
          A strategy hwin
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankDirectionPath
              A strategy hwin control direction)
            controller.globalMachine controller.globalOutputOne
              controller.globalOutputTwo env start cuts

namespace
  ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankDirectionHardCertificateBundle

/-- Forget that the allowed bank path was constructed canonically from a
direction stream.  This is only dependent-pair reassociation; the alignment
itself is unchanged. -/
noncomputable def toBankHardCertificate
    {controller : PhysicalController (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {env : EnvironmentSequence In₁ In₂}
    (bundle :
      ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankDirectionHardCertificateBundle
        A strategy hwin controller env) :
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankHardCertificateBundle
      A strategy hwin controller env := by
  rcases bundle with ⟨control, direction, start, cuts, alignment⟩
  exact ⟨control,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankDirectionPath A
      strategy hwin control direction,
    start, cuts, alignment⟩

end
  ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankDirectionHardCertificateBundle

/-! ## Environment and strategy quantifier assembly -/

/-- The exact environment-local obligations when hard executions are aligned
with canonical direction paths through the fixed marked bank. -/
structure
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankDirectionControllerBookkeeping
    (controller : PhysicalController (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂))
    (env : EnvironmentSequence In₁ In₂) : Prop where
  recurrent : GraphBothRecurrent (fun n ↦ (env n).graph) →
    Nonempty
      (ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankDirectionHardCertificateBundle
        A strategy hwin controller env)
  reversal : PersistentStrictReversalTail (fun n ↦ (env n).graph) →
    Nonempty
      (ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankDirectionHardCertificateBundle
        A strategy hwin controller env)
  fixed : EventuallyInstalledOutputTailBookkeeping A controller env

namespace
  ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankDirectionControllerBookkeeping

/-- Canonical direction-path witnesses fill the two hard fields of the
marked-bank operational bookkeeping without changing the controller or its
physical trace. -/
noncomputable def toBankControllerBookkeeping
    {controller : PhysicalController (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {env : EnvironmentSequence In₁ In₂}
    (bookkeeping :
      ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankDirectionControllerBookkeeping
        A strategy hwin controller env) :
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankControllerBookkeeping
      A strategy hwin controller env where
  recurrent := fun hboth ↦ by
    rcases bookkeeping.recurrent hboth with ⟨bundle⟩
    exact ⟨bundle.toBankHardCertificate A strategy hwin⟩
  reversal := fun hreversal ↦ by
    rcases bookkeeping.reversal hreversal with ⟨bundle⟩
    exact ⟨bundle.toBankHardCertificate A strategy hwin⟩
  fixed := bookkeeping.fixed

end
  ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankDirectionControllerBookkeeping

/-- Strategy-indexed construction premise in the direction-path presentation.
The controller is selected before the environment; the bank index, direction
stream, path, and cuts remain proof-side environment witnesses. -/
def
    PerStrategyWinningValidatedMarkedLiteralPrefixBankDirectionControllerBookkeeping :
    Prop :=
  ∀ (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)),
    ∃ controller :
        FinitePairedPhysicalController.{u, v, x, y, w, w}
          In₁ In₂ Out₁ Out₂,
      ∀ env : EnvironmentSequence In₁ In₂,
        ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankDirectionControllerBookkeeping
          A strategy hwin controller env

/-- Pure quantifier/certificate conversion to the canonical marked-bank
operational premise. -/
theorem
    perStrategyWinningValidatedMarkedLiteralPrefixBankControllerBookkeeping_of_directionPaths
    (hdirection :
      PerStrategyWinningValidatedMarkedLiteralPrefixBankDirectionControllerBookkeeping.{u,
        v, x, y, s, w} A) :
    PerStrategyWinningValidatedMarkedLiteralPrefixBankControllerBookkeeping.{u,
      v, x, y, s, w} A := by
  intro strategy hwin
  obtain ⟨controller, hcontroller⟩ := hdirection strategy hwin
  refine ⟨controller, fun env ↦ ?_⟩
  exact (hcontroller env).toBankControllerBookkeeping A strategy hwin

/-- One-arrow `ReadbackUpgrade` endpoint for the direction-path presentation. -/
theorem exists_readbackUpgrade_of_validatedMarkedLiteralPrefixBankDirectionBookkeeping
    (fallback : LocalSummaryAutomaton.{u, v, w} In₁ In₂)
    (hdirection :
      PerStrategyWinningValidatedMarkedLiteralPrefixBankDirectionControllerBookkeeping.{u,
        v, x, y, s, w} A) :
    ∃ M : LocalSummaryAutomaton.{u, v, w} In₁ In₂,
      M.ReadbackUpgrade (Out₁ := Out₁) (Out₂ := Out₂) A := by
  exact exists_readbackUpgrade_of_validatedMarkedLiteralPrefixBankBookkeeping
    A fallback
      (perStrategyWinningValidatedMarkedLiteralPrefixBankControllerBookkeeping_of_directionPaths
        A hdirection)

end

end DetParityAutomaton

end DistributedSynthesis
