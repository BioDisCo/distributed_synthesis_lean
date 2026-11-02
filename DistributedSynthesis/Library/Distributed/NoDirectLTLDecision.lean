/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.NoDirectDecision
import DistributedSynthesis.Library.Automata.LTLComputable

/-! # Executable no-direct-reversal synthesis for LTL

The input is a formula and a decidable interpretation of its atoms over round
records. No automaton compiler, journal checker, or tree solver is a parameter.
The specification quantifies over the original perfect-recall strategies.
An encoded mathlib `ComputablePred` theorem is a separate obligation.
-/

namespace DistributedSynthesis.NoDirectLTLDecision

variable {AP In₁ In₂ Out₁ Out₂ : Type}
variable [DecidableEq AP]
variable (interp : AP → RoundRecord In₁ In₂ Graph Out₁ Out₂ → Prop)
variable (dec : ∀ ap letter, Decidable (interp ap letter))

def Realizable (φ : LTL AP) : Prop :=
  ∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
    ∀ env : EnvironmentSequence In₁ In₂,
      NoDirectReversalSequence env → LTL.Satisfies interp (execution σ env) φ

theorem realizable_iff (φ : LTL AP) :
    Realizable interp φ ↔ NoDirectJournal.Realizable (LTLComputable.compile interp dec φ) := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨σ, fun env henv => (LTLComputable.correct interp dec φ _).mpr (hσ env henv)⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨σ, fun env henv => (LTLComputable.correct interp dec φ _).mp (hσ env henv)⟩

variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

def decideRealizable (φ : LTL AP) : Decidable (Realizable interp φ) := by
  letI : DecidableEq (LTLComputable.compile interp dec φ).State :=
    LTLComputable.stateDecidableEq interp dec φ
  letI := NoDirectDecision.decideRealizable (LTLComputable.compile interp dec φ)
  exact decidable_of_iff _ (realizable_iff interp dec φ).symm

def solve (φ : LTL AP) : Bool := @decide (Realizable interp φ) (decideRealizable interp dec φ)

theorem solve_correct (φ : LTL AP) : solve interp dec φ = true ↔ Realizable interp φ := by
  unfold solve
  exact @decide_eq_true_iff _ (decideRealizable interp dec φ)

end DistributedSynthesis.NoDirectLTLDecision
