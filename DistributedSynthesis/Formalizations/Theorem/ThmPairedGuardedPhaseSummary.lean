/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedGuardedMatchedReadback

/-!
# Moore summaries for the guarded finite phase machine

`LocalSummaryAutomaton.readbackStrategy` reads the output after folding the
current view constructor.  Consequently a phase summary stores the finite
post-observation control together with the physical output produced by that
observation.  The root output is arbitrary and is never used by a nonempty
execution.

The control component remains the asymmetric local carrier from
`ThmPairedGuardedPhaseCarrier`; no common phase or leader field is added.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))
  (rightBasis : ∀ target profile,
    (rightProfileGuardedAutomaton A target profile).RationalRunBasis)
  (leftBasis : ∀ target profile,
    (leftProfileGuardedAutomaton A target profile).RationalRunBasis)
  (controllers : LocallyConsistentGuardedInitialControllers
    A strategy hwin rightBasis leftBasis)
  (bank : FiniteGuardedFirstControllerBank A)

abbrev GuardedPhaseOneSummary :=
  GuardedPhaseOneControl A strategy hwin rightBasis leftBasis controllers bank × Out₁

abbrev GuardedPhaseTwoSummary :=
  GuardedPhaseTwoControl A strategy hwin rightBasis leftBasis controllers bank × Out₂

noncomputable instance : Fintype
    (GuardedPhaseOneSummary A strategy hwin rightBasis leftBasis controllers bank) := by
  classical
  infer_instance

noncomputable instance : Fintype
    (GuardedPhaseTwoSummary A strategy hwin rightBasis leftBasis controllers bank) := by
  classical
  infer_instance

noncomputable def initialGuardedPhaseOneSummary :
    GuardedPhaseOneSummary A strategy hwin rightBasis leftBasis controllers bank :=
  (initialGuardedPhaseOneControl A strategy hwin rightBasis leftBasis controllers bank,
    default)

noncomputable def initialGuardedPhaseTwoSummary :
    GuardedPhaseTwoSummary A strategy hwin rightBasis leftBasis controllers bank :=
  (initialGuardedPhaseTwoControl A strategy hwin rightBasis leftBasis controllers bank,
    default)

/-- The eventual process-one readback table is just this projection. -/
def guardedPhaseOutputOne
    (summary : GuardedPhaseOneSummary A strategy hwin rightBasis leftBasis
      controllers bank) : Out₁ :=
  summary.2

/-- Process-two mirror. -/
def guardedPhaseOutputTwo
    (summary : GuardedPhaseTwoSummary A strategy hwin rightBasis leftBasis
      controllers bank) : Out₂ :=
  summary.2

@[simp] theorem guardedPhaseOutputOne_mk
    (control : GuardedPhaseOneControl A strategy hwin rightBasis leftBasis
      controllers bank) (output : Out₁) :
    guardedPhaseOutputOne A strategy hwin rightBasis leftBasis controllers bank
      (control, output) = output := rfl

@[simp] theorem guardedPhaseOutputTwo_mk
    (control : GuardedPhaseTwoControl A strategy hwin rightBasis leftBasis
      controllers bank) (output : Out₂) :
    guardedPhaseOutputTwo A strategy hwin rightBasis leftBasis controllers bank
      (control, output) = output := rfl

end


end DetParityAutomaton

end DistributedSynthesis
