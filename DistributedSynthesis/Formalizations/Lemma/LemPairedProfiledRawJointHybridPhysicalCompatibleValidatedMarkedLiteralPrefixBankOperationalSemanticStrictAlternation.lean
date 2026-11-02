/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankOperationalSemanticCutPath
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankOperationalStrictAlternation

/-!
# Strict alternation for the semantic-payload operational schedule

This is the direct junction between the corrected cut schedule and the hidden
lineage bookkeeping.  Rational narrowing may change the semantic prefix stored
in a strict bank direction, but it cannot change that direction's physical
graph side.  Hence the eventual no-`BOTH` tail alternates exactly as before.
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

private abbrev BankControl :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl A strategy hwin

/-- The exact semantic-payload schedule has an eventually alternating strict
suffix in every persistent-reversal environment.  In particular, replacing
the false raw-prefix direction equality loses no side/parity information. -/
theorem
    OperationalCloseCutPackage.exists_eventualStrictAlternation_of_semanticCloseWitness
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (trace : Nat → BankControl A strategy hwin)
    (hclose :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalSemanticCloseWitness
        A strategy hwin env cuts trace)
    (hreversal : PersistentStrictReversalTail (fun n ↦ (env n).graph)) :
    ∃ startIndex : Nat,
      Nonempty
        (ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalStrictAlternationFrom
          (In₁ := In₁) (In₂ := In₂)
          (DistributedSynthesis.DetParityAutomaton.OperationalCloseCutPackage.toSemanticBankOperationalCutSchedule
            A strategy hwin env cuts trace hclose)
          startIndex) := by
  exact
    (DistributedSynthesis.DetParityAutomaton.OperationalCloseCutPackage.toSemanticBankOperationalCutSchedule
      A strategy hwin env cuts trace hclose).exists_eventualStrictAlternation
        hreversal

end

end DetParityAutomaton

end DistributedSynthesis
