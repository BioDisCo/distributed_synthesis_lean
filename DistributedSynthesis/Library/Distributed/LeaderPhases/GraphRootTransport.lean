/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.PointedGraphRoots

/-! The checked per-root graph transition is total on represented histories
and preserves their exact physical graph words, including dead prefixes. -/
namespace Characterisation
open DistributedSynthesis FullViewPath

section Transport
variable {Q : Type} [Fintype Q] [DecidableEq Q] {d K : Nat}
variable (M : Recognizer Graph Q) [DecidablePred (· ∈ M.accept)]
variable (P : List Graph → Prop) (closed : PrefixClosed P)
variable (recognizes : ∀ g, P g ↔ M.eval g ∈ M.accept)
variable (g : List Graph) (state : GraphRootState Q d K) (rep : GraphRootRep P M g state) (r : Graph)

include closed recognizes rep in
theorem graphRootStep_correct (next : GraphRootState Q d K)
    (valid : checkGraphRootStep M state r next = true) : GraphRootRep P M (g++[r]) next := by
  cases state with
  | none =>
    have eq : next = none := by simpa only [checkGraphRootStep,decide_eq_true_eq] using valid
    subst next
    exact fun live => rep (closed g [r] live)
  | some st =>
    by_cases alive : graphChildLive M st.1.2.2 (st.2,r) = true
    · have live := (graphRootLive_exact M P closed recognizes g (some st) rep r).mp alive
      obtain ⟨_,past,data,point⟩ := rep
      have selected : ∃ keep : GraphComponentReindex (Fin st.1.1.val) K,
          checkGraphReindex M st.1.2.1 st.1.2.2 (st.2,r) keep = true ∧
          ∃ index : Fin keep.1.val, keep.2 index = (st.2,r) ∧
            next = some ⟨graphReindexTarget M st.1.2.1 st.1.2.2 keep,index⟩ := by
        simpa only [checkGraphRootStep,if_pos alive,decide_eq_true_eq] using valid
      obtain ⟨keep,validKeep,index,indexEq,rfl⟩ := selected
      refine ⟨live,graphChildHistory past ∘ keep.2,?_,?_⟩
      · have target := graphReindexTarget_using M P closed recognizes d past data.1 st.1.2.1 data.2.2.1
          (graphComponentUsing_covers P M g st.1 past data) st.1.2.2 data.2.2.2 (st.2,r)
          (by simpa only [graphChildHistory,point] using live) keep validKeep
        simpa only [graphChildHistory,point] using target
      · simp only [Function.comp_apply,indexEq,graphChildHistory,point]
    · have dead : ¬ P (g++[r]) := fun live => alive
        ((graphRootLive_exact M P closed recognizes g (some st) rep r).mpr live)
      have eq : next = none := by
        simpa only [checkGraphRootStep,if_neg alive,decide_eq_true_eq] using valid
      subst next
      exact dead

include closed recognizes rep in
/-- For fixed finite graph-component bound K, some finite next state always
passes the transition check. Forbidden continuations have the unique dead state. -/
theorem graphRootStep_exists
    (bounded : ∀ k, P k → Finite (HistoryComponent P k) ∧ Nat.card (HistoryComponent P k) ≤ K) :
    ∃ next : GraphRootState Q d K, checkGraphRootStep M state r next = true := by
  cases state with
  | none => exact ⟨none,by simp only [checkGraphRootStep,decide_true]⟩
  | some st =>
    by_cases alive : graphChildLive M st.1.2.2 (st.2,r) = true
    · have live := (graphRootLive_exact M P closed recognizes g (some st) rep r).mp alive
      obtain ⟨_,past,data,point⟩ := rep
      have liveChild : P (graphChildHistory past (st.2,r)) := by simpa only [graphChildHistory,point] using live
      letI : Finite (HistoryComponent P (graphChildHistory past (st.2,r))) := (bounded _ liveChild).1
      obtain ⟨keep,index,checked,indexEq⟩ := exists_checked_pointed_graph_reindex M P closed recognizes d past
        data.1 st.1.2.1 data.2.2.1 (graphComponentUsing_covers P M g st.1 past data)
        st.1.2.2 data.2.2.2 (st.2,r) liveChild K (bounded _ liveChild).2
      refine ⟨some ⟨graphReindexTarget M st.1.2.1 st.1.2.2 keep,index⟩,?_⟩
      simp only [checkGraphRootStep,if_pos alive,decide_eq_true_eq]
      exact ⟨keep,checked,index,indexEq,rfl⟩
    · exact ⟨none,by simp only [checkGraphRootStep,if_neg alive,decide_true]⟩

end Transport

/-- The product of one optional pointed graph interface per original input
root is finite. Splitting into different graph components does not enlarge it. -/
instance graphRootBank_fintype {H Q : Type} [Fintype H] [DecidableEq H] [Fintype Q] (d K : Nat) :
    Fintype (H → GraphRootState Q d K) := by
  unfold GraphRootState
  infer_instance

/-- A checked bank follows every private-input root's own physical graph
history. No equality of graph components between different roots is required. -/
theorem graphRootBank_run_exact {H Q I₁ I₂ : Type} [Fintype Q] [DecidableEq Q] {d K : Nat}
    (M : Recognizer Graph Q) [DecidablePred (· ∈ M.accept)]
    (P : List Graph → Prop) (closed : PrefixClosed P) (recognizes : ∀ g, P g ↔ M.eval g ∈ M.accept)
    (history : Nat → H → EnvHistory I₁ I₂)
    (round : Nat → H → RoundRecord I₁ I₂ Graph Unit Unit)
    (extension : ∀ n h, history (n+1) h = history n h ++ [round n h])
    (bank : Nat → H → GraphRootState Q d K)
    (start : ∀ h, GraphRootRep P M (History.graphSequence (history 0 h)) (bank 0 h))
    (checked : ∀ n h, checkGraphRootStep M (bank n h) (round n h).graph (bank (n+1) h) = true) :
    ∀ n h, GraphRootRep P M (History.graphSequence (history n h)) (bank n h) := by
  intro n
  induction n with
  | zero => exact start
  | succ n ih =>
    intro h
    have correct := graphRootStep_correct M P closed recognizes _ (bank n h) (ih h) (round n h).graph
      (bank (n+1) h) (checked n h)
    simpa only [extension,History.graphSequence,List.map_append,List.map_cons,List.map_nil] using correct

end Characterisation
