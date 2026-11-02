/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.PhysicalContinuation
import DistributedSynthesis.Library.Distributed.GraphAdversaries.Inputs
import DistributedSynthesis.Library.Distributed.EncodedNoDirectParity

/-! Connect the actual finite-input LTL target to the guarded physical
automaton used by the new phase and global parity constructions. The original
verified LTL frontend is reused on the entire round-record alphabet. -/
namespace Characterisation
open DistributedSynthesis

def continuationRecord {I₁ I₂ O₁ O₂ : Type}
    (letter : ContinuationLetter I₁ I₂ O₁ O₂) : RoundRecord I₁ I₂ Graph O₁ O₂ :=
  ⟨letter.1.1, letter.1.2.1, letter.1.2.2, letter.2.1, letter.2.2⟩

@[simp] theorem continuationRecord_record {I₁ I₂ O₁ O₂ : Type}
    (record : RoundRecord I₁ I₂ Graph O₁ O₂) :
    continuationRecord (recordContinuationLetter record) = record := by
  cases record
  rfl

namespace WithInputs

abbrev TupleLetter (d : Instance) :=
  ContinuationLetter (Fin (d.inputOneSizeMinusOne+1)) (Fin (d.inputTwoSizeMinusOne+1))
    (Fin (d.outputOneSizeMinusOne+1)) (Fin (d.outputTwoSizeMinusOne+1))

abbrev Strategies (d : Instance) :=
  StrategyPair (Fin (d.inputOneSizeMinusOne+1)) (Fin (d.inputTwoSizeMinusOne+1))
    (Fin (d.outputOneSizeMinusOne+1)) (Fin (d.outputTwoSizeMinusOne+1))

noncomputable def guardedInstanceObjective (adversary : DetParityAutomaton Graph)
    (d : Instance) : DetParityAutomaton (TupleLetter d) :=
  guardedPhysicalObjective adversary ((EncodedNoDirectParity.automaton d).comap continuationRecord)

/-- The compiled guarded objective expresses exactly the original LTL
requirement on admitted executions. Finite-input alphabets, X, and the
adversary's infinite acceptance all retain their original semantics. -/
theorem guardedInstanceObjective_execution_iff (adversary : DetParityAutomaton Graph)
    (d : Instance) (σ : Strategies d) (env : EnvironmentSequence
      (Fin (d.inputOneSizeMinusOne+1)) (Fin (d.inputTwoSizeMinusOne+1))) :
    (guardedInstanceObjective adversary d).Accepts
      (fun n => recordContinuationLetter (execution σ env n)) ↔
      (adversary.Accepts (fun n => (env n).graph) →
        LTL.Satisfies (EncodedNoDirect.interp d) (execution σ env)
          (EncodedFiniteLTL.decode d.formula)) := by
  rw [guardedInstanceObjective, guardedPhysicalObjective_accepts_iff,
    DetParityAutomaton.comap_accepts_iff]
  have letters : OmegaWord.map continuationRecord
      (fun n => recordContinuationLetter (execution σ env n)) = execution σ env := by
    funext n
    exact continuationRecord_record _
  have graphs : (fun n => (recordContinuationLetter (execution σ env n)).1.2.2) =
      fun n => (env n).graph := by
    funext n
    rw [execution_apply]
    rfl
  rw [letters, graphs, EncodedNoDirectParity.accepts_iff]

/-- Exact frontend equivalence for the requested target. This is the LTL
to guarded-parity step, not yet a finite-game decision theorem. -/
theorem realizable_iff_guarded_objective (A : Set (Nat → Graph))
    (adversary : DetParityAutomaton Graph) (recognizes : ∀ word, word ∈ A ↔ adversary.Accepts word)
    (d : Instance) :
    Realizable A d ↔ ∃ σ : Strategies d, ∀ env,
      (guardedInstanceObjective adversary d).Accepts
        (fun n => recordContinuationLetter (execution σ env n)) := by
  constructor
  · rintro ⟨σ, winning⟩
    refine ⟨σ, fun env => ?_⟩
    apply (guardedInstanceObjective_execution_iff adversary d σ env).mpr
    intro admitted
    exact winning env ((recognizes _).mpr admitted)
  · rintro ⟨σ, winning⟩
    refine ⟨σ, fun env admitted => ?_⟩
    exact (guardedInstanceObjective_execution_iff adversary d σ env).mp (winning env)
      ((recognizes _).mp admitted)

end WithInputs
end Characterisation
