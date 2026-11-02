/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.InputParityObjective
import DistributedSynthesis.Library.Distributed.EncodedRoundObjectives
import DistributedSynthesis.Library.Distributed.EncodedJournalPriorities

/-! Reuse the library's numeric round objectives in the leader construction.
The data, state numbering, round-letter order, and min-even priorities are
unchanged. Only the semantic alphabet is converted from records to tuples.
This module does not encode the guarded objective or the leader game. -/
namespace Characterisation.EncodedLeaderObjective
open DistributedSynthesis

abbrev Data := EncodedRoundObjectives.Data

/-- Use the existing record alphabet through its exact tuple adapter. -/
def automaton (data : Data) : DetParityAutomaton (WithInputs.TupleLetter data.1) :=
  (EncodedRoundObjectives.automaton data).comap continuationRecord

/-- The existing journal maximum supplies an explicit numeric rank bound. -/
def priorityBound (data : Data) : Nat :=
  EncodedJournalTransitions.maximum
    ((List.range (EncodedRoundObjectives.stateCount data)).map (EncodedRoundObjectives.objectivePriority data))

theorem priorityBound_primrec : Primrec priorityBound :=
  EncodedJournalTransitions.maximum_primrec.comp
    (Primrec.list_map (Primrec.list_range.comp EncodedRoundObjectives.stateCount_primrec)
      EncodedRoundObjectives.objectivePriority_primrec.to₂)

theorem priority_le_bound (data : Data) (q : (automaton data).State) :
    (automaton data).priority q ≤ priorityBound data := by
  unfold priorityBound
  rw [EncodedJournalPriorities.maximum_eq_sup]
  apply Finset.le_sup (f:=id)
  apply List.mem_toFinset.mpr
  exact List.mem_map.mpr ⟨q.val,List.mem_range.mpr q.isLt,rfl⟩

/-- Exact finite ranks for the numbered game; no priority is reduced modulo
an unrelated bound. -/
def rank (data : Data) (q : (automaton data).State) : Fin (priorityBound data+1) :=
  ⟨(automaton data).priority q,Nat.lt_succ_of_le (priority_le_bound data q)⟩

theorem rank_exact (data : Data) (q : (automaton data).State) :
    (rank data q).val = (automaton data).priority q := rfl

/-- The primitive-recursive frontend is the existing library compiler. -/
theorem frontend_primrec : Primrec EncodedRoundObjectives.fromInstance :=
  EncodedRoundObjectives.fromInstance_primrec

theorem frontend_priorityBound_primrec :
    Primrec (fun instanceData => priorityBound (EncodedRoundObjectives.fromInstance instanceData)) :=
  priorityBound_primrec.comp EncodedRoundObjectives.fromInstance_primrec

theorem automaton_fromInstance (instanceData : WithInputs.Instance) :
    automaton (EncodedRoundObjectives.fromInstance instanceData) =
      (EncodedNoDirectParity.automaton instanceData).comap continuationRecord := by
  rw [automaton,EncodedRoundObjectives.automaton_fromInstance]
  rfl

/-- The frontend recognizes the original LTL formula on every physical
execution. No no-direct-reversal graph assumption is required. -/
theorem frontend_execution_iff (instanceData : WithInputs.Instance)
    (σ : WithInputs.Strategies instanceData)
    (env : EnvironmentSequence (Fin (instanceData.inputOneSizeMinusOne+1))
      (Fin (instanceData.inputTwoSizeMinusOne+1))) :
    (automaton (EncodedRoundObjectives.fromInstance instanceData)).Accepts
      (fun n => recordContinuationLetter (execution σ env n)) ↔
      LTL.Satisfies (EncodedNoDirect.interp instanceData) (execution σ env)
        (EncodedFiniteLTL.decode instanceData.formula) := by
  rw [automaton_fromInstance]
  erw [DetParityAutomaton.comap_accepts_iff]
  have letters : OmegaWord.map continuationRecord
      (fun n => recordContinuationLetter (execution σ env n)) = execution σ env := by
    funext n
    exact continuationRecord_record _
  erw [letters,EncodedNoDirectParity.accepts_iff]

/-- This is exactly the objective used in the checked holes reduction, once
the existing semantic guard is applied. Numeric guard compilation remains
separate from this compatibility theorem. -/
theorem guarded_frontend_eq (adversary : DetParityAutomaton Graph)
    (instanceData : WithInputs.Instance) :
    guardedPhysicalObjective adversary (automaton (EncodedRoundObjectives.fromInstance instanceData)) =
      WithInputs.guardedInstanceObjective adversary instanceData := by
  rw [automaton_fromInstance]
  rfl

end Characterisation.EncodedLeaderObjective
