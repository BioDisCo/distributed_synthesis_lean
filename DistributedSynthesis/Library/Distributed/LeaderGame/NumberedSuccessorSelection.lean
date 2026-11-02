/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.CarriedNumberedHandover

/-! Select one whole numbered successor on the common target component.
The selected histories retain the certificate's numbering and every label
is replayed from its literal predecessor under the same phase strategy. -/
namespace Characterisation
open DistributedSynthesis

section
variable {GQ I₁ I₂ O₁ O₂ : Type} {d K B C : Nat}
variable [Fintype GQ] [DecidableEq GQ]
variable (M : Recognizer Graph GQ) [DecidablePred (· ∈ M.accept)]
variable (objective : DetParityAutomaton (ContinuationLetter I₁ I₂ O₁ O₂))
variable (rank : objective.State → Fin (C+1))
variable (P : List Graph → Prop)
variable (header : NumberedLeaderHeader (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)
variable (past : Fin header.1.val → EnvHistory I₁ I₂) (σ : StrategyPair I₁ I₂ O₁ O₂)

def NumberedSuccessorRep (target : LeaderPhaseOrigin I₁ I₂)
    (outcome : NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)
    (nextPast : Fin outcome.1.1.val → EnvHistory I₁ I₂) : Prop :=
  Function.Injective nextPast ∧
  (∀ k, k ∈ target.2 ↔ ∃ i, nextPast i = k) ∧
  (∀ i, List.length (nextPast i) = target.1) ∧
  RepresentsInputShape nextPast outcome.1.2.1 ∧
  (∀ i, GraphRootRep P M (History.graphSequence (nextPast i)) (outcome.1.2.2 i).1.1) ∧
  (∀ i, outcome.2.2 i = (outcome.1.2.2 i).2 ()) ∧
  ∀ i, ∃ (j : Fin header.1.val) (word : EnvHistory I₁ I₂),
    outcome.2.1 i = numberedLeaderSlot objective header j ∧
    nextPast i = past j ++ word ∧ word ≠ [] ∧
    outcome.1.2.2 i = strategyContinuationLabel σ (leaderAnnotationStep M objective rank)
      (resetLeaderMinimum objective (header.2.2 j)) (past j) word

theorem numberedCertificate_successor
    (closed : PrefixClosed P) (recognizes : ∀ g, P g ↔ M.eval g ∈ M.accept)
    (bounded : ∀ g, P g → Finite (HistoryComponent P g) ∧ Nat.card (HistoryComponent P g) ≤ K)
    (graphs : ∀ i, GraphRootRep P M (History.graphSequence (past i)) (header.2.2 i).1.1)
    {H : Type} (f : H → Fin header.1.val) (word : EnvHistory I₁ I₂)
    (initial : H → LeaderAnnotation (GQ:=GQ) (d:=d) (K:=K) (C:=C) objective)
    (out : ClosingPolicy H I₁ I₂ O₁ O₂ (d+1))
    (n : Nat) (positive : 0 < n) (bound : n ≤ d+1) (root : ClosingLayer H I₁ I₂ n)
    (move : ClosingBoundaryCertificate H I₁ I₂ O₁ O₂
      (LeaderAnnotation (GQ:=GQ) (d:=d) (K:=K) (C:=C) objective) B (d+1) n)
    (realizes : ClosingOfferRealizes P (fun h => past (f h) ++ word)
      (leaderAnnotationStep M objective rank) initial out bound root move)
    (labels : ∀ i,
      move.2.2.2.2 i = strategyContinuationLabel σ (leaderAnnotationStep M objective rank)
        (resetLeaderMinimum objective (header.2.2 (f (closingLayerRoot n (move.2.2.1 i)))) )
        (past (f (closingLayerRoot n (move.2.2.1 i)))) (word ++ closingSuffix n (move.2.2.1 i))) :
    NumberedSuccessorRep M objective rank P header past σ
      (boundaryOrigin P (closingLayerHistory (fun h => past (f h) ++ word) n root))
      (certificateHandover (numberedLeaderSlot objective header ∘ f) (fun q => q.2 ()) move)
      (closingLayerHistory (fun h => past (f h) ++ word) n ∘ move.2.2.1) := by
  refine ⟨realizes.1,realizes.2.1,?_,realizes.2.2.1,?_,(fun _ => rfl),?_⟩
  · intro i
    exact (inputConnected_length P ((realizes.2.1 _).mpr ⟨i,rfl⟩)).symm
  · intro i
    change GraphRootRep P M _ (move.2.2.2.2 i).1.1
    simp only [Function.comp_apply]
    rw [labels i,closingLayerHistory_suffix]
    simpa only [List.append_assoc] using leaderAnnotation_graph M objective rank σ P closed recognizes bounded
      (header.2.2 (f (closingLayerRoot n (move.2.2.1 i))))
      (past (f (closingLayerRoot n (move.2.2.1 i)))) (word ++ closingSuffix n (move.2.2.1 i)) (graphs _)
  · intro i
    refine ⟨f (closingLayerRoot n (move.2.2.1 i)),word ++ closingSuffix n (move.2.2.1 i),rfl,?_,?_,labels i⟩
    · simpa only [Function.comp_apply,List.append_assoc] using
        closingLayerHistory_suffix (fun h => past (f h) ++ word) n (move.2.2.1 i)
    · intro empty
      have len := congrArg List.length empty
      have suffixLength : List.length (closingSuffix n (move.2.2.1 i)) = n := by
        simpa only [closingSuffix,Nat.zero_add] using
          closingLayerHistory_length (fun _ : H => ([] : EnvHistory I₁ I₂)) 0 (fun _ => rfl) n (move.2.2.1 i)
      simp only [List.length_append,List.length_nil,suffixLength] at len
      omega

abbrev NumberedSuccessorChoice :=
  Σ outcome : NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective,
    Fin outcome.1.1.val → EnvHistory I₁ I₂

noncomputable def chooseNumberedSuccessor
    (permitted : Finset (NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective))
    (target : LeaderPhaseOrigin I₁ I₂) : Option (NumberedSuccessorChoice (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective) := by
  classical
  exact if possible : ∃ choice : NumberedSuccessorChoice (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective,
      choice.1 ∈ permitted ∧ NumberedSuccessorRep M objective rank P header past σ target choice.1 choice.2
  then some possible.choose else none

theorem chooseNumberedSuccessor_spec
    (permitted : Finset (NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective))
    (target : LeaderPhaseOrigin I₁ I₂)
    (possible : ∃ outcome nextPast, outcome ∈ permitted ∧
      NumberedSuccessorRep M objective rank P header past σ target outcome nextPast) :
    ∃ choice, chooseNumberedSuccessor M objective rank P header past σ permitted target = some choice ∧
      choice.1 ∈ permitted ∧ NumberedSuccessorRep M objective rank P header past σ target choice.1 choice.2 := by
  classical
  have witness : ∃ choice : NumberedSuccessorChoice (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective,
      choice.1 ∈ permitted ∧ NumberedSuccessorRep M objective rank P header past σ target choice.1 choice.2 := by
    obtain ⟨outcome,nextPast,member,rep⟩ := possible
    exact ⟨⟨outcome,nextPast⟩,member,rep⟩
  rw [chooseNumberedSuccessor,dif_pos witness]
  exact ⟨witness.choose,rfl,witness.choose_spec⟩

theorem chooseNumberedSuccessor_component
    (permitted : Finset (NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective))
    {h k : EnvHistory I₁ I₂} (conn : InputConnected P h k) :
    chooseNumberedSuccessor M objective rank P header past σ permitted (boundaryOrigin P h) =
      chooseNumberedSuccessor M objective rank P header past σ permitted (boundaryOrigin P k) := by
  rw [boundaryOrigin_component P conn]

end
end Characterisation
