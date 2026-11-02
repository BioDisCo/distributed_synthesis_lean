/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.NumberedOriginalSuccessors

/-! Original-strategy successor annotations retain the actual global
objective state and the minimum over every physical round of the phase. -/
namespace Characterisation
open DistributedSynthesis

section
variable {GQ I₁ I₂ O₁ O₂ : Type} {d K B C : Nat}
variable [Fintype GQ] [DecidableEq GQ]
variable (M : Recognizer Graph GQ) [DecidablePred (· ∈ M.accept)]
variable (objective : DetParityAutomaton (ContinuationLetter I₁ I₂ O₁ O₂))
variable (rank : objective.State → Fin (C+1)) (P : List Graph → Prop)
variable (σ : StrategyPair I₁ I₂ O₁ O₂)

theorem numberedOriginal_successor_rep
    (header : NumberedLeaderHeader (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)
    (past : Fin header.1.val → EnvHistory I₁ I₂) (old target : LeaderPhaseOrigin I₁ I₂)
    (source : NumberedBoundaryRep M objective P
      (strategyHistoryLabel σ (fun s input output => objective.step s (input,output)) objective.initial) header past old)
    (outcome : NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)
    (nextPast : Fin outcome.1.1.val → EnvHistory I₁ I₂)
    (successor : NumberedSuccessorRep M objective rank P header past σ target outcome nextPast) :
    NumberedBoundaryRep M objective P
      (strategyHistoryLabel σ (fun s input output => objective.step s (input,output)) objective.initial)
      outcome.1 nextPast target ∧
    ∀ i, (outcome.2.2 i).val = historyPhaseMinimum
      (fun h => (rank (strategyHistoryLabel σ (fun s input output => objective.step s (input,output)) objective.initial h)).val)
      old.1 target.1 (nextPast i) := by
  refine ⟨⟨successor.1,successor.2.1,successor.2.2.1,successor.2.2.2.1,successor.2.2.2.2.1,?_⟩,?_⟩
  · intro i
    obtain ⟨j,word,_,extension,_,replay⟩ := successor.2.2.2.2.2.2 i
    rw [replay,leaderAnnotation_objective,source.2.2.2.2.2 j,← strategyHistoryLabel_continuation,← extension]
  · intro i
    obtain ⟨j,word,_,extension,nonempty,replay⟩ := successor.2.2.2.2.2.2 i
    have length : target.1 = old.1 + List.length word := by
      rw [← successor.2.2.1 i,extension,List.length_append,source.2.2.1 j]
    rw [successor.2.2.2.2.2.1 i,replay,leaderAnnotation_minimum M objective rank σ _ _ _ nonempty,
      source.2.2.2.2.2 j]
    simp only [historyPhaseMinimum,length,Nat.add_sub_cancel_left]
    apply rangeMin_congr
    intro k _
    rw [← strategyHistoryLabel_continuation,extension]
    have prefixEq : (past j ++ word).take (old.1+k+1) = past j ++ word.take (k+1) := by
      rw [← source.2.2.1 j,show List.length (past j)+k+1 = List.length (past j)+(k+1) by omega,
        List.take_add,List.take_left,List.drop_left]
    rw [Nat.zero_add,prefixEq]

end
end Characterisation
