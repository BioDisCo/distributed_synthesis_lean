/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedRoleExchange
import DistributedSynthesis.Library.Distributed.LeaderGame.RoleExchange

/-! Numeric role exchange is exactly the existing semantic exchangeLetter
operation. It preserves the carried objective state and every physical round. -/
namespace Characterisation.EncodedRoleExchange
open DistributedSynthesis
open EncodedNoDirect

theorem swapGraph_code (g : Graph) : swapGraph (EncodedNoDirect.graphCode g) = EncodedNoDirect.graphCode (exchangeGraph g) := by
  cases g <;> rfl

theorem swapCode_encode (d : EncodedRoundObjectives.Data) (a : EncodedNoDirect.Letter (swapInstance d.1)) :
    swapCode (letterCode a) = letterCode (data:=d.1) (exchangeRound a) := by
  unfold swapCode letterCode
  rw [swapGraph_code]
  rfl

theorem objectiveStep_swap (d : EncodedRoundObjectives.Data)
    (q : Fin (EncodedRoundObjectives.stateCount d)) (a : EncodedNoDirect.Letter (swapInstance d.1)) :
    EncodedRoundObjectives.objectiveStep (swap d) q.val (letterCode a) =
      EncodedRoundObjectives.objectiveStep d q.val (letterCode (data:=d.1) (exchangeRound a)) := by
  have member := (mem_letters_iff (swapInstance d.1) (letterCode a)).mpr ⟨a,rfl⟩
  have bound := List.idxOf_lt_length_of_mem member
  have row : (transitions d).getD ((letters (swapInstance d.1)).idxOf (letterCode a)) [] =
      (List.range (EncodedRoundObjectives.stateCount d)).map
        (fun q => EncodedRoundObjectives.objectiveStep d q (swapCode (letterCode a))) := by
    unfold transitions
    rw [List.getD_eq_getElem _ _ (by simpa using bound)]
    simp only [List.getElem_map,List.getElem_idxOf]
  unfold EncodedRoundObjectives.objectiveStep EncodedParityTables.next
  change ((transitions d).getD ((letters (swapInstance d.1)).idxOf (letterCode a)) []).getD q.val 0 %
    EncodedRoundObjectives.stateCount d = _
  rw [row,List.getD_eq_getElem _ _ (by simpa using q.isLt)]
  simp only [List.getElem_map,List.getElem_range]
  rw [swapCode_encode]
  exact Nat.mod_eq_of_lt (Nat.mod_lt _ (Nat.succ_pos _))

/-- This is equality in the existing round-objective interface, including
state identity and priorities, not only equivalence from the initial state. -/
theorem automaton_swap (d : EncodedRoundObjectives.Data) :
    EncodedLeaderObjective.automaton (swap d) =
      (EncodedLeaderObjective.automaton d).comap exchangeLetter := by
  unfold EncodedLeaderObjective.automaton EncodedRoundObjectives.automaton DetParityAutomaton.comap
  congr 1
  funext q a
  apply Fin.ext
  exact objectiveStep_swap d q (continuationRecord a)

theorem runFrom_swap (d : EncodedRoundObjectives.Data)
    (q : (EncodedLeaderObjective.automaton d).State)
    (word : OmegaWord (WithInputs.TupleLetter (swapInstance d.1))) (t : Nat) :
    (EncodedLeaderObjective.automaton (swap d)).runFrom q word t =
      ((EncodedLeaderObjective.automaton d).comap exchangeLetter).runFrom q word t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change (EncodedLeaderObjective.automaton (swap d)).step
      ((EncodedLeaderObjective.automaton (swap d)).runFrom q word t) (word t) = _
    rw [ih]
    apply Fin.ext
    exact objectiveStep_swap d _ (continuationRecord (word t))

/-- Residual acceptance is preserved with the very same carried state. -/
theorem acceptsFrom_swap (d : EncodedRoundObjectives.Data)
    (q : (EncodedLeaderObjective.automaton d).State)
    (word : OmegaWord (WithInputs.TupleLetter (swapInstance d.1))) :
    (EncodedLeaderObjective.automaton (swap d)).AcceptsFrom q word ↔
      ((EncodedLeaderObjective.automaton d).comap exchangeLetter).AcceptsFrom q word := by
  rw [← DetParityAutomaton.withInitial_accepts_iff,← DetParityAutomaton.withInitial_accepts_iff]
  rw [DetParityAutomaton.accepts_iff_natSeqMinEvenParity,DetParityAutomaton.accepts_iff_natSeqMinEvenParity]
  simp only [DetParityAutomaton.withInitial_run,runFrom_swap]
  rfl

end Characterisation.EncodedRoleExchange
