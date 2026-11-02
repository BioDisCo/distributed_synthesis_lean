/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedGuardedObjectiveCorrect
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedParityPresentation

/-! A uniform guarded frontend for every fixed finite graph adversary,
expressed in the original library's numeric round-objective interface. -/
namespace Characterisation.EncodedGuardedObjective
open DistributedSynthesis

set_option maxHeartbeats 1600000 in
/-- The semantic adapter reads precisely the compiled numeric table. -/
theorem automaton_eq_round (d : Data) :
    automaton d = EncodedLeaderObjective.automaton (roundData d) := by
  unfold automaton EncodedParityFamilies.automaton EncodedMuller.automaton
    EncodedLeaderObjective.automaton EncodedRoundObjectives.automaton
    EncodedParityTables.automaton DetParityAutomaton.comap
  rfl

/-- Fixing the adversary fixes its finite table. The resulting frontend is
primitive recursive uniformly in the LTL instance and its finite alphabets.
There is no graph-prefix or closed-adversary restriction on this language
correspondence. -/
theorem uniform_frontend (adversary : DetParityAutomaton Graph) :
    ∃ tables : EncodedNoDirect.Instance → EncodedParityTables.Data,
      Primrec tables ∧ ∀ instanceData (word : OmegaWord (WithInputs.TupleLetter instanceData)),
        (EncodedLeaderObjective.automaton (instanceData,tables instanceData)).Accepts word ↔
          (WithInputs.guardedInstanceObjective adversary instanceData).Accepts word := by
  obtain ⟨adversaryData,alphabet,recognizes⟩ := EncodedParityPresentation.graph_presentation adversary
  refine ⟨fun i => compile (adversaryData,i),compile_primrec.comp ((Primrec.const adversaryData).pair Primrec.id),?_⟩
  intro i word
  change (EncodedLeaderObjective.automaton (roundData (adversaryData,i))).Accepts word ↔ _
  rw [← automaton_eq_round]
  apply (accepts_iff (adversaryData,i) alphabet word).trans
  rw [WithInputs.guardedInstanceObjective,guardedPhysicalObjective_accepts_iff,
    EncodedLeaderObjective.automaton_fromInstance]
  change ((graphAutomaton adversaryData alphabet).Accepts (fun n => (word n).1.2.2) → _) ↔ _
  rw [show (graphAutomaton adversaryData alphabet).Accepts (fun n => (word n).1.2.2) ↔
    adversary.Accepts (fun n => (word n).1.2.2) from recognizes _]
  rfl

/-- The same uniform construction has a uniform exact finite priority bound,
ready for the leader game's per-round minimum annotations. -/
theorem uniform_frontend_with_ranks (adversary : DetParityAutomaton Graph) :
    ∃ tables : EncodedNoDirect.Instance → EncodedParityTables.Data,
    ∃ bound : EncodedNoDirect.Instance → Nat,
      Primrec tables ∧ Primrec bound ∧
      (∀ i (q : (EncodedLeaderObjective.automaton (i,tables i)).State),
        (EncodedLeaderObjective.automaton (i,tables i)).priority q ≤ bound i) ∧
      ∀ i (word : OmegaWord (WithInputs.TupleLetter i)),
        (EncodedLeaderObjective.automaton (i,tables i)).Accepts word ↔
          (WithInputs.guardedInstanceObjective adversary i).Accepts word := by
  obtain ⟨tables,computable,correct⟩ := uniform_frontend adversary
  refine ⟨tables,fun i => EncodedLeaderObjective.priorityBound (i,tables i),computable,
    EncodedLeaderObjective.priorityBound_primrec.comp (Primrec.id.pair computable),?_,correct⟩
  intro i q
  exact EncodedLeaderObjective.priority_le_bound _ q

end Characterisation.EncodedGuardedObjective
