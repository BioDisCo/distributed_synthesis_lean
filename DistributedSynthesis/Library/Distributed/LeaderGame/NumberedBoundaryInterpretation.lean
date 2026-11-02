/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.NumberedControllerChoice

/-! Interpret a represented boundary without renumbering its histories.
Every legal move supplies the concrete common-component successor choice. -/
namespace Characterisation
open DistributedSynthesis

section
variable {GQ I₁ I₂ O₁ O₂ : Type} {d K B C : Nat}
variable [Fintype GQ] [DecidableEq GQ]
variable (M : Recognizer Graph GQ) [DecidablePred (· ∈ M.accept)]
variable (objective : DetParityAutomaton (ContinuationLetter I₁ I₂ O₁ O₂))
variable (P : List Graph → Prop)
variable (labels : EnvHistory I₁ I₂ → objective.State)
variable (header : NumberedLeaderHeader (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)
variable (past : Fin header.1.val → EnvHistory I₁ I₂)

omit [Fintype GQ] [DecidableEq GQ] [DecidablePred (· ∈ M.accept)] in
theorem numberedBoundaryRep_enumeration (h : EnvHistory I₁ I₂)
    (rep : NumberedBoundaryRep M objective P labels header past (boundaryOrigin P h)) :
    ∃ e : Fin header.1.val ≃ InputHistoryComponent P h, ∀ i, (e i).val = past i := by
  let f : Fin header.1.val → InputHistoryComponent P h :=
    fun i => ⟨past i,(rep.2.1 _).mpr ⟨i,rfl⟩⟩
  have injective : Function.Injective f := fun i j same => rep.1 (congrArg Subtype.val same)
  have surjective : Function.Surjective f := by
    intro k
    obtain ⟨i,same⟩ := (rep.2.1 k.val).mp k.property
    exact ⟨i,Subtype.ext same⟩
  exact ⟨Equiv.ofBijective f ⟨injective,surjective⟩,fun _ => rfl⟩

variable [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
variable [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂]
variable [Inhabited I₁] [Inhabited I₂] [Inhabited O₁] [Inhabited O₂]
variable [DecidableEq objective.State] (rank : objective.State → Fin (C+1))
variable (move : NumberedLeaderMove (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)

omit [Inhabited I₁] [Inhabited I₂] [Inhabited O₁] [Inhabited O₂] in
theorem numberedBoundaryRep_leader (h : EnvHistory I₁ I₂) (live : P (History.graphSequence h))
    (rep : NumberedBoundaryRep M objective P labels header past (boundaryOrigin P h))
    (legal : numberedLeaderLegal M objective rank header move = true) :
    move.1 = componentLeader P d (History.graphSequence h) := by
  obtain ⟨i,actual⟩ := (rep.2.1 h).mp (show InputConnected P h h from Relation.ReflTransGen.refl)
  have checked : ∀ i, graphRootLeader (header.2.2 i).1.1 = move.1 := by
    simp only [numberedLeaderLegal,Bool.and_eq_true,decide_eq_true_eq] at legal
    exact legal.1
  have graphs := rep.2.2.2.2.1 i
  rw [actual] at graphs
  exact (checked i).symm.trans (graphRootLeader_exact P M _ live _ graphs)

variable (closed : PrefixClosed P) (recognizes : ∀ g, P g ↔ M.eval g ∈ M.accept)
variable (recent : ∀ g, P g → ∃ p, RecentOther P d g p)
variable (bounded : ∀ g, P g → Finite (HistoryComponent P g) ∧ Nat.card (HistoryComponent P g) ≤ K)
variable (small : ∀ k : EnvHistory I₁ I₂, P (History.graphSequence k) → leaderBoundary P d k = true →
  Nat.card (InputHistoryComponent P k) ≤ B)

include closed recognizes recent bounded small in
theorem numberedLegal_actual_choice
    (h : EnvHistory I₁ I₂) (live : P (History.graphSequence h)) (a : Nat)
    (phase : ConsecutiveLeaderBoundaries P d h a)
    (source : NumberedBoundaryRep M objective P labels header past (boundaryOrigin P (h.take a)))
    (legal : numberedLeaderLegal M objective rank header move = true) :
    let σ := chooseNumberedController M objective rank header past move.2 move.1
    ∃ choice, chooseNumberedSuccessor M objective rank P header past σ move.2 (boundaryOrigin P h) = some choice ∧
      choice.1 ∈ move.2 ∧
      NumberedSuccessorRep M objective rank P header past σ (boundaryOrigin P h) choice.1 choice.2 := by
  obtain ⟨e,numbering⟩ := numberedBoundaryRep_enumeration M objective P labels header past (h.take a) source
  have leader := numberedBoundaryRep_leader M objective P labels header past rank move (h.take a)
    (live_history_take P closed h live a) source legal
  have controller := chooseNumberedController_spec M objective rank header past move.2 move.1
    (by simpa only [Prod.eta] using legal) source.2.2.2.1 (List.length (h.take a)) source.2.2.1
  have controller' : NumberedController M objective rank header past move.2
      (componentLeader P d (History.graphSequence (h.take a)))
      (chooseNumberedController M objective rank header past move.2 move.1) := by
    rw [← leader]
    exact controller
  have possible := numberedController_actual_successor M objective rank header past move.2 P closed recognizes recent
    bounded small h live a phase e numbering source.2.2.2.1 source.2.2.2.2.1
    (chooseNumberedController M objective rank header past move.2 move.1) controller'
  exact chooseNumberedSuccessor_spec M objective rank P header past _ move.2 (boundaryOrigin P h) possible

end
end Characterisation
