/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.StrategyBoundaryTransition

/-! Couple leader-view groups at a common phase boundary. Their strategies
may differ, but their initial closing plans come from one common strategy.
This suffices for a joint local readback throughout the rightward phase. -/
namespace Characterisation
open DistributedSynthesis

theorem rollingSourceHistory_receiver_zero {H I₁ I₂ : Type}
    (past : H → EnvHistory I₁ I₂) (node : List (I₂ × I₁)) (h : H) (nonempty : node ≠ []) :
    silentAge (currentView .two (rollingSourceHistory past node h)) = 0 := by
  obtain ⟨old,r,rfl⟩ := (List.eq_nil_or_concat' node).resolve_left nonempty
  rw [rollingSourceHistory_snoc]
  change silentAge (currentView .two (History.append _ ⟨r.2,r.1,.right,(),()⟩)) = 0
  rw [currentView_two_append]
  rfl

theorem rollingWindow_initial_take {H I₁ I₂ : Type} {D : Nat}
    (past : H → EnvHistory I₁ I₂) (L : Nat) (depth : ∀ h, List.length (past h) = L)
    (node : List (I₂ × I₁)) (s : WindowScenario H I₁ I₂ (D+1)) :
    (windowHistory (rollingSourceHistory past node) (D+1) s).take L = past s.1 := by
  simp only [windowHistory,rollingSourceHistory,List.append_assoc]
  rw [← depth s.1,List.take_left]

section Groups
variable {H G I₁ I₂ O₁ O₂ : Type} {D : Nat}
variable (past : H → EnvHistory I₁ I₂) (L : Nat) (depth : ∀ h, List.length (past h) = L)
variable (group : H → G)
variable (observable : ∀ h k, currentView .one (past h) = currentView .one (past k) → group h = group k)

include depth observable in
/-- The leader retains its initial view, and therefore its group, through
every later closing window. Equal views need not reveal a root index. -/
theorem leader_group_from_window_view
    (node word : List (I₂ × I₁)) (s t : WindowScenario H I₁ I₂ (D+1))
    (same : currentView .one (windowHistory (rollingSourceHistory past node) (D+1) s) =
      currentView .one (windowHistory (rollingSourceHistory past word) (D+1) t)) :
    group s.1 = group t.1 := by
  have earlier := equal_currentView_take .one _ _ same L (by
    simp only [windowHistory,List.length_append,rollingSourceHistory_length,depth,List.length_ofFn]
    omega)
  rw [rollingWindow_initial_take past L depth,rollingWindow_initial_take past L depth] at earlier
  exact observable _ _ earlier

include depth observable in
/-- Once a window source contains a rightward round, the receiver's final
view identifies the initial history, hence the leader-view group. It still
does not distinguish a current rightward reception from a both reception. -/
theorem receiver_group_from_nonempty_source
    (node word : List (I₂ × I₁)) (nonempty : node ≠ [])
    (s t : WindowScenario H I₁ I₂ (D+1))
    (same : currentView .two (windowHistory (rollingSourceHistory past node) (D+1) s) =
      currentView .two (windowHistory (rollingSourceHistory past word) (D+1) t)) :
    group s.1 = group t.1 := by
  have zero := rollingSourceHistory_receiver_zero past node s.1 nonempty
  have age := silentAge_suffix_le .two (rollingSourceHistory past node s.1)
    (List.ofFn (fun i => let r := s.2.2 i
      (⟨r.1,r.2.1,r.2.2,(),()⟩ : RoundRecord I₁ I₂ Graph Unit Unit)))
  rw [zero,Nat.zero_add,List.length_ofFn] at age
  have positive : 0 < node.length := List.length_pos_iff.mpr nonempty
  have earlier := equal_view_recent_prefix .two _ _ same L (by
    change silentAge (currentView .two (windowHistory (rollingSourceHistory past node) (D+1) s)) ≤ _ at age
    have len : List.length (windowHistory (rollingSourceHistory past node) (D+1) s) =
        L + node.length + (s.2.1.val + 1) := by
      simp only [windowHistory,List.length_append,rollingSourceHistory_length,depth,List.length_ofFn]
    rw [len]
    omega)
  rw [rollingWindow_initial_take past L depth,rollingWindow_initial_take past L depth] at earlier
  exact observable _ _ (congrArg (currentView .one) earlier)

variable [Nonempty O₁] [Nonempty O₂]
variable (initialStrategy : StrategyPair I₁ I₂ O₁ O₂) (strategies : G → StrategyPair I₁ I₂ O₁ O₂)
variable (initialPlans : ∀ h, closingPlanOfStrategy (strategies (group h)) (past h) (D+1) =
  closingPlanOfStrategy initialStrategy (past h) (D+1))

include depth observable initialPlans in
/-- Group strategies with a common initial bank have one joint local
implementation on the entire unbounded family of closing windows. This
couples all initial leader-view groups of a boundary component. -/
theorem leader_groups_phase_readback :
    ∃ σ : StrategyPair I₁ I₂ O₁ O₂, ∀ node h,
      closingPlanOfStrategy σ (rollingSourceHistory past node h) (D+1) =
        closingPlanOfStrategy (strategies (group h)) (rollingSourceHistory past node h) (D+1) := by
  let hist (node : List (I₂ × I₁)) (s : WindowScenario H I₁ I₂ (D+1)) :=
    windowHistory (rollingSourceHistory past node) (D+1) s
  let out (node : List (I₂ × I₁)) (s : WindowScenario H I₁ I₂ (D+1)) :=
    ((strategies (group s.1)).one (currentView .one (hist node s)),
     (strategies (group s.1)).two (currentView .two (hist node s)))
  have initial : ∀ s : WindowScenario H I₁ I₂ (D+1), out [] s =
      (initialStrategy.one (currentView .one (hist [] s)),initialStrategy.two (currentView .two (hist [] s))) := by
    intro s
    have eq := congrFun (initialPlans s.1) ((),s.2)
    simpa only [closingPlanOfStrategy,windowHistory,hist,out,rollingSourceHistory,rightInputHistory,
      List.map_nil,List.append_nil] using eq
  have compatible : TablesCompatible hist out := by
    constructor
    · intro node word s t same
      have groups := leader_group_from_window_view past L depth group observable node word s t same
      change (strategies (group s.1)).one (currentView .one (hist node s)) =
        (strategies (group t.1)).one (currentView .one (hist word t))
      rw [groups,same]
    · intro node word s t same
      by_cases nodeNonempty : node ≠ []
      · have groups := receiver_group_from_nonempty_source past L depth group observable node word nodeNonempty s t same
        change (strategies (group s.1)).two (currentView .two (hist node s)) =
          (strategies (group t.1)).two (currentView .two (hist word t))
        rw [groups,same]
      · have nodeEmpty : node = [] := Classical.not_not.mp nodeNonempty
        subst node
        by_cases wordNonempty : word ≠ []
        · have groups := receiver_group_from_nonempty_source past L depth group observable word [] wordNonempty t s same.symm
          change (strategies (group s.1)).two (currentView .two (hist [] s)) =
            (strategies (group t.1)).two (currentView .two (hist word t))
          rw [groups,same]
        · have wordEmpty : word = [] := Classical.not_not.mp wordNonempty
          subst word
          rw [initial,initial]
          exact congrArg initialStrategy.two same
  obtain ⟨σ,correct⟩ := (tables_compatible_iff_local hist out).mp compatible
  refine ⟨σ,fun node h => ?_⟩
  funext s
  have result := correct node (h,s.2)
  exact Prod.ext result.1 result.2

end Groups
end Characterisation
