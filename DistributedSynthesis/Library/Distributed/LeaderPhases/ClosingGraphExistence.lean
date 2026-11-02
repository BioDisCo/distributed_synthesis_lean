/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.ClosingGraphCoupling

/-! Complete bounded graph representations initialize each private-input
root. Total checked graph transitions fill every finite closing scan. -/
namespace Characterisation
open DistributedSynthesis FullViewPath

theorem graphRootRep_exists {Q : Type} (M : Recognizer Graph Q) (P : List Graph → Prop) (d K : Nat)
    (bounded : ∀ k, P k → Finite (HistoryComponent P k) ∧ Nat.card (HistoryComponent P k) ≤ K)
    (g : List Graph) : ∃ state : GraphRootState Q d K, GraphRootRep P M g state := by
  classical
  by_cases live : P g
  · obtain ⟨summary,e,shape,labels⟩ := bounded_graph_reception_interfaces M d K P bounded g live
    let root : HistoryComponent P g := ⟨g,Relation.ReflTransGen.refl⟩
    refine ⟨some ⟨summary,e.symm root⟩,live,(fun i => (e i).val),?_,?_⟩
    · refine ⟨Subtype.val_injective.comp e.injective,?_,shape,labels⟩
      intro k
      constructor
      · intro conn
        obtain ⟨i,eq⟩ := e.surjective (⟨k,conn⟩ : HistoryComponent P g)
        exact ⟨i,congrArg Subtype.val eq⟩
      · rintro ⟨i,rfl⟩
        exact (e i).property
    · simp only [Equiv.apply_symm_apply,root]
  · exact ⟨none,live⟩

section Choice
variable {Q : Type} [Fintype Q] [DecidableEq Q] {d K : Nat}
variable (M : Recognizer Graph Q) [DecidablePred (· ∈ M.accept)]

/-- Choice is used to prove existence of finite certificates. The legality
check is executable and its whole candidate alphabet is finite. -/
noncomputable def chooseGraphRootNext (state : GraphRootState Q d K) (g : Graph) : GraphRootState Q d K := by
  classical
  exact if possible : ∃ next, checkGraphRootStep M state g next = true then possible.choose else none

theorem chooseGraphRootNext_checked (state : GraphRootState Q d K) (g : Graph)
    (possible : ∃ next, checkGraphRootStep M state g next = true) :
    checkGraphRootStep M state g (chooseGraphRootNext M state g) = true := by
  classical
  unfold chooseGraphRootNext
  rw [dif_pos possible]
  exact possible.choose_spec

noncomputable def closingGraphRun {H I₁ I₂ : Type} (source : H → GraphRootState Q d K) :
    (n : Nat) → ClosingLayer H I₁ I₂ n → GraphRootState Q d K
  | 0, h => source h
  | n+1, s => chooseGraphRootNext M (closingGraphRun source n s.1) s.2.2.2

variable {H I₁ I₂ : Type}
variable (P : List Graph → Prop) (closed : PrefixClosed P) (recognizes : ∀ g, P g ↔ M.eval g ∈ M.accept)
variable (bounded : ∀ k, P k → Finite (HistoryComponent P k) ∧ Nat.card (HistoryComponent P k) ≤ K)
variable (past : H → EnvHistory I₁ I₂) (source : H → GraphRootState Q d K)
variable (sourceExact : ∀ h, GraphRootRep P M (History.graphSequence (past h)) (source h))

include closed recognizes bounded sourceExact in
theorem closingGraphRun_rep (n : Nat) (s : ClosingLayer H I₁ I₂ n) :
    GraphRootRep P M (History.graphSequence (closingLayerHistory past n s)) (closingGraphRun M source n s) := by
  induction n with
  | zero => exact sourceExact s
  | succ n ih =>
    have old := ih s.1
    have possible := graphRootStep_exists M P closed recognizes _ _ old s.2.2.2 bounded
    have valid := chooseGraphRootNext_checked M _ s.2.2.2 possible
    have next := graphRootStep_correct M P closed recognizes _ _ old s.2.2.2 _ valid
    simpa only [closingLayerHistory,scenarioHistory,History.graphSequence,List.map_append,List.map_cons,List.map_nil,
      closingGraphRun] using next

include closed recognizes bounded sourceExact in
/-- Every exact source graph bank admits an accepted finite scan covering
all graph and private-input continuations through the prescribed horizon. -/
theorem exists_checked_closing_graph_table [Fintype H] [Fintype I₁] [Fintype I₂] (D : Nat) :
    ∃ table : ClosingGraphTable H I₁ I₂ Q d K D, checkClosingGraphTable M source table = true := by
  classical
  let table : ClosingGraphTable H I₁ I₂ Q d K D := fun n s => closingGraphRun M source n.val s
  refine ⟨table,?_⟩
  simp only [checkClosingGraphTable,Bool.and_eq_true,decide_eq_true_eq]
  refine ⟨fun _ => rfl,?_⟩
  intro n s
  have old := closingGraphRun_rep M P closed recognizes bounded past source sourceExact n.val s.1
  exact chooseGraphRootNext_checked M _ s.2.2.2
    (graphRootStep_exists M P closed recognizes _ _ old s.2.2.2 bounded)

end Choice
end Characterisation
