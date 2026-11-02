/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.NumberedHandoverReplay
import DistributedSynthesis.Library.Distributed.LeaderPhases.PhaseParityComposition

/-! The finite annotation has the actual residual objective state and the
minimum over all physical outputs since the preceding leader boundary. -/
namespace Characterisation
open DistributedSynthesis

theorem strategyContinuationLabel_map {I₁ I₂ O₁ O₂ Q R : Type}
    (σ : StrategyPair I₁ I₂ O₁ O₂)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
    (next : R → (I₁ × I₂ × Graph) → (O₁ × O₂) → R)
    (f : Q → R) (commutes : ∀ q input output, f (step q input output) = next (f q) input output)
    (q : Q) (root word : EnvHistory I₁ I₂) :
    f (strategyContinuationLabel σ step q root word) =
      strategyContinuationLabel σ next (f q) root word := by
  have fold : ∀ (word : EnvHistory I₁ I₂) (root : EnvHistory I₁ I₂) (q : Q),
      f ((word.foldl (strategyLabelStep σ step) (root,q)).2) =
        (word.foldl (strategyLabelStep σ next) (root,f q)).2 := by
    intro word
    induction word with
    | nil => intros; rfl
    | cons r word ih =>
      intro root q
      simp only [List.foldl_cons,strategyLabelStep]
      rw [ih,commutes]
  exact fold word root q

section Minimum
variable {I₁ I₂ O₁ O₂ Q : Type} {C : Nat}
variable (σ : StrategyPair I₁ I₂ O₁ O₂)
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
variable (rank : Q → Fin (C+1))

abbrev strategyMinimumStep := closingMinimumStep step (fun q input output (_ : Unit) => rank (step q input output))

theorem strategyMinimum_state (q : Q) (old : Unit → Fin (C+1)) (root word : EnvHistory I₁ I₂) :
    (strategyContinuationLabel σ (strategyMinimumStep step rank) (q,old) root word).1 =
      strategyContinuationLabel σ step q root word :=
  strategyContinuationLabel_map σ _ step Prod.fst (fun _ _ _ => rfl) (q,old) root word

theorem strategyMinimum_nonempty (q : Q) (root word : EnvHistory I₁ I₂) (nonempty : word ≠ []) :
    ((strategyContinuationLabel σ (strategyMinimumStep step rank)
      (q,fun _ => Fin.last C) root word).2 ()).val =
      rangeMin (fun i => (rank (strategyContinuationLabel σ step q root (word.take (i+1)))).val)
        0 (List.length word-1) := by
  induction word using List.reverseRecOn with
  | nil => exact False.elim (nonempty rfl)
  | append_singleton word r ih =>
    rw [strategyContinuationLabel_append]
    change (min
      ((strategyContinuationLabel σ (strategyMinimumStep step rank) (q,fun _ => Fin.last C) root word).2 ())
      (rank (step (strategyContinuationLabel σ (strategyMinimumStep step rank)
        (q,fun _ => Fin.last C) root word).1 (r.inputOne,r.inputTwo,r.graph)
        (σ.one (currentView .one (root++word++[r])),σ.two (currentView .two (root++word++[r])))))).val = _
    rw [strategyMinimum_state,← strategyContinuationLabel_append σ step q root word r]
    by_cases empty : word = []
    · subst word
      simp only [strategyContinuationLabel,List.foldl_nil,
        List.nil_append,List.length_singleton,Nat.sub_self,rangeMin,Nat.zero_add]
      exact min_eq_right (Nat.le_of_lt_succ (rank _).isLt)
    · have positive : 0 < List.length word := List.length_pos_iff.mpr empty
      rw [Fin.coe_min,ih empty]
      have length : List.length (word++[r])-1 = (List.length word-1)+1 := by
        simp only [List.length_append,List.length_singleton]
        omega
      rw [length,rangeMin]
      congr 1
      · apply rangeMin_congr
        intro i le
        rw [List.take_append_of_le_length (by omega)]
      · have length' : 0+(List.length word-1+1)+1 = List.length (word++[r]) := by
          simp only [List.length_append,List.length_singleton]
          omega
        rw [length',List.take_length]

end Minimum

section Annotation
variable {GQ I₁ I₂ O₁ O₂ : Type} {d K C : Nat}
variable [Fintype GQ] [DecidableEq GQ]
variable (M : Recognizer Graph GQ) [DecidablePred (· ∈ M.accept)]
variable (objective : DetParityAutomaton (ContinuationLetter I₁ I₂ O₁ O₂))
variable (rank : objective.State → Fin (C+1))
variable (σ : StrategyPair I₁ I₂ O₁ O₂)

theorem leaderAnnotation_graph
    (P : List Graph → Prop) (closed : PrefixClosed P)
    (recognizes : ∀ g, P g ↔ M.eval g ∈ M.accept)
    (bounded : ∀ g, P g → Finite (HistoryComponent P g) ∧ Nat.card (HistoryComponent P g) ≤ K)
    (q : LeaderAnnotation (GQ:=GQ) (d:=d) (K:=K) (C:=C) objective)
    (root word : EnvHistory I₁ I₂)
    (source : GraphRootRep P M (History.graphSequence root) q.1.1) :
    GraphRootRep P M (History.graphSequence (root++word))
      (strategyContinuationLabel σ (leaderAnnotationStep M objective rank)
        (resetLeaderMinimum objective q) root word).1.1 := by
  induction word using List.reverseRecOn with
  | nil => simpa only [List.append_nil,strategyContinuationLabel,List.foldl_nil,resetLeaderMinimum] using source
  | append_singleton word r ih =>
    rw [strategyContinuationLabel_append]
    change GraphRootRep P M (History.graphSequence (root++(word++[r])))
      (chooseGraphRootNext M
        (strategyContinuationLabel σ (leaderAnnotationStep M objective rank)
          (resetLeaderMinimum objective q) root word).1.1 r.graph)
    have possible := graphRootStep_exists M P closed recognizes _ _ ih r.graph bounded
    have checked := chooseGraphRootNext_checked M _ r.graph possible
    have next := graphRootStep_correct M P closed recognizes _ _ ih r.graph _ checked
    simpa only [History.graphSequence,List.map_append,List.map_singleton,List.append_assoc] using next

theorem leaderAnnotation_objective
    (q : LeaderAnnotation (GQ:=GQ) (d:=d) (K:=K) (C:=C) objective)
    (root word : EnvHistory I₁ I₂) :
    (strategyContinuationLabel σ (leaderAnnotationStep M objective rank)
      (resetLeaderMinimum objective q) root word).1.2 =
      strategyContinuationLabel σ (fun s input output => objective.step s (input,output)) q.1.2 root word :=
  strategyContinuationLabel_map σ (leaderAnnotationStep M objective rank) _
    (fun s => s.1.2) (fun _ _ _ => rfl) (resetLeaderMinimum objective q) root word

theorem leaderAnnotation_minimum
    (q : LeaderAnnotation (GQ:=GQ) (d:=d) (K:=K) (C:=C) objective)
    (root word : EnvHistory I₁ I₂) (nonempty : word ≠ []) :
    ((strategyContinuationLabel σ (leaderAnnotationStep M objective rank)
      (resetLeaderMinimum objective q) root word).2 ()).val =
      rangeMin (fun i => (rank (strategyContinuationLabel σ
        (fun s input output => objective.step s (input,output)) q.1.2 root (word.take (i+1)))).val)
        0 (List.length word-1) := by
  have result := strategyMinimum_nonempty σ (leaderStateStep M objective)
    (fun s => rank s.2) q.1 root word nonempty
  refine result.trans ?_
  apply rangeMin_congr
  intro i _
  have projected := strategyContinuationLabel_map σ (leaderStateStep M objective)
    (fun s input output => objective.step s (input,output)) Prod.snd
    (fun _ _ _ => rfl) q.1 root (word.take (i+1))
  simpa only [Nat.zero_add] using congrArg (fun s => (rank s).val) projected

end Annotation
end Characterisation
