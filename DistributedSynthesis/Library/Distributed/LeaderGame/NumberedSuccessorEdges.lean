/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.NumberedActualSuccessors

/-! A selected whole successor preserves the carried representation and
provides the actual predecessor edge for every history in its component. -/
namespace Characterisation
open DistributedSynthesis

section
variable {GQ I₁ I₂ O₁ O₂ : Type} {d K B C : Nat}
variable [Fintype GQ] [DecidableEq GQ]
variable (M : Recognizer Graph GQ) [DecidablePred (· ∈ M.accept)]
variable (objective : DetParityAutomaton (ContinuationLetter I₁ I₂ O₁ O₂))
variable (rank : objective.State → Fin (C+1))
variable (P : List Graph → Prop)

def NumberedBoundaryRep
    (labels : EnvHistory I₁ I₂ → objective.State)
    (header : NumberedLeaderHeader (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)
    (past : Fin header.1.val → EnvHistory I₁ I₂) (origin : LeaderPhaseOrigin I₁ I₂) : Prop :=
  Function.Injective past ∧
  (∀ k, k ∈ origin.2 ↔ ∃ i, past i = k) ∧
  (∀ i, List.length (past i) = origin.1) ∧
  RepresentsInputShape past header.2.1 ∧
  (∀ i, GraphRootRep P M (History.graphSequence (past i)) (header.2.2 i).1.1) ∧
  ∀ i, (header.2.2 i).1.2 = labels (past i)

noncomputable def numberedHistorySlot
    (header : NumberedLeaderHeader (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)
    (past : Fin header.1.val → EnvHistory I₁ I₂) (h : EnvHistory I₁ I₂) : Fin (B+1) := by
  classical
  exact if found : ∃ i, past i = h then numberedLeaderSlot objective header found.choose else 0

omit [Fintype GQ] [DecidableEq GQ] in
theorem numberedHistorySlot_at
    (header : NumberedLeaderHeader (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)
    (past : Fin header.1.val → EnvHistory I₁ I₂) (injective : Function.Injective past) (i : Fin header.1.val) :
    numberedHistorySlot objective header past (past i) = numberedLeaderSlot objective header i := by
  classical
  have found : ∃ j, past j = past i := ⟨i,rfl⟩
  rw [numberedHistorySlot,dif_pos found]
  exact congrArg (numberedLeaderSlot objective header) (injective found.choose_spec)

variable {Data : Type}
variable (decode : LeaderPhaseOrigin I₁ I₂ → CarriedLeaderState Data objective.State I₁ I₂ →
  StrategyPair I₁ I₂ O₁ O₂)
variable (update : CarriedLeaderState Data objective.State I₁ I₂ → LeaderPhaseOrigin I₁ I₂ →
  LeaderPhaseOrigin I₁ I₂ → (EnvHistory I₁ I₂ → objective.State) → (EnvHistory I₁ I₂ → Nat) → Data)

theorem numberedSuccessor_preserves_representation
    (state : CarriedLeaderState Data objective.State I₁ I₂)
    (old target : LeaderPhaseOrigin I₁ I₂)
    (header : NumberedLeaderHeader (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)
    (past : Fin header.1.val → EnvHistory I₁ I₂)
    (source : NumberedBoundaryRep M objective P state.label header past old)
    (outcome : NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)
    (nextPast : Fin outcome.1.1.val → EnvHistory I₁ I₂)
    (successor : NumberedSuccessorRep M objective rank P header past (decode old state) target outcome nextPast) :
    let next := carriedLeaderAdvance (fun s input output => objective.step s (input,output))
      (fun q => (rank q).val) decode update state old target
    NumberedBoundaryRep M objective P next.label outcome.1 nextPast target ∧
      ∀ i, (outcome.2.2 i).val = next.minimum (nextPast i) := by
  obtain ⟨injective,covers,depth,shape,graphs,minima,parents⟩ := successor
  have truth : ∀ i,
      (outcome.1.2.2 i).1.2 = (carriedLeaderAdvance (fun s input output => objective.step s (input,output))
        (fun q => (rank q).val) decode update state old target).label (nextPast i) ∧
      ((outcome.1.2.2 i).2 ()).val = (carriedLeaderAdvance (fun s input output => objective.step s (input,output))
        (fun q => (rank q).val) decode update state old target).minimum (nextPast i) := by
    intro i
    obtain ⟨j,word,_,extension,nonempty,replay⟩ := parents i
    have result := leaderAnnotation_matches_carried_advance M objective rank decode update state old target
      (header.2.2 j) (past j) word (source.2.2.1 j) (source.2.2.2.2.2 j) nonempty
    dsimp only at result
    rw [← replay,← extension] at result
    exact result
  refine ⟨⟨injective,covers,depth,shape,graphs,fun i => (truth i).1⟩,?_⟩
  intro i
  rw [minima i]
  exact (truth i).2

theorem numberedSuccessor_actual_edge
    (state : CarriedLeaderState Data objective.State I₁ I₂)
    (old target : LeaderPhaseOrigin I₁ I₂)
    (header : NumberedLeaderHeader (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)
    (past : Fin header.1.val → EnvHistory I₁ I₂)
    (source : NumberedBoundaryRep M objective P state.label header past old)
    (outcome : NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)
    (nextPast : Fin outcome.1.1.val → EnvHistory I₁ I₂)
    (successor : NumberedSuccessorRep M objective rank P header past (decode old state) target outcome nextPast)
    (h : EnvHistory I₁ I₂) (member : h ∈ target.2) (oldMinimum : Fin (C+1)) :
    let next := carriedLeaderAdvance (fun s input output => objective.step s (input,output))
      (fun q => (rank q).val) decode update state old target
    HandoverEdge (numberedHistorySlot objective header past (h.take old.1),oldMinimum) outcome ()
      (numberedHistorySlot objective outcome.1 nextPast h,
        ⟨next.minimum h % (C+1),Nat.mod_lt _ (by omega)⟩) := by
  obtain ⟨i,actual⟩ := (successor.2.1 h).mp member
  obtain ⟨j,word,parent,extension,_,_⟩ := successor.2.2.2.2.2.2 i
  have oldHistory : h.take old.1 = past j := by
    rw [← actual,extension,← source.2.2.1 j,List.take_left]
  have minimum := (numberedSuccessor_preserves_representation M objective rank P decode update
    state old target header past source outcome nextPast successor).2 i
  rw [actual] at minimum
  refine ⟨i,?_,?_⟩
  · rw [oldHistory,numberedHistorySlot_at objective header past source.1 j]
    exact parent
  · apply Prod.ext
    · rw [← actual,numberedHistorySlot_at objective outcome.1 nextPast successor.1 i]
      rfl
    · apply Fin.ext
      change _ % (C+1) = (outcome.2.2 i).val
      rw [← minimum]
      exact Nat.mod_eq_of_lt (outcome.2.2 i).isLt

end
end Characterisation
