/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.ClosingGraphCoupling

/-! Closing masks inspect boundary flags only on live prefixes of a live
scenario. Neither dead-history flags nor the zero-depth marker matter. -/
namespace Characterisation
open DistributedSynthesis

theorem closingActive_congr_on_live {H I₁ I₂ : Type}
    (P : List Graph → Prop) (closed : PrefixClosed P) (past : H → EnvHistory I₁ I₂)
    (boundary other : (n : Nat) → ClosingLayer H I₁ I₂ n → Bool) (D : Nat)
    (agree : ∀ n, 0 < n → n ≤ D → ∀ s, P (History.graphSequence (closingLayerHistory past n s)) → boundary n s = other n s)
    (n : Nat) (bound : n ≤ D) (s : ClosingLayer H I₁ I₂ n)
    (live : P (History.graphSequence (closingLayerHistory past n s))) :
    closingActive boundary n s = closingActive other n s := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n _ ih =>
    have parent := closingLayerHistory_live_parent P closed past (n+1) s live
    simp only [closingActive,ih (by omega) s.1 parent,agree (n+1) (by omega) (by omega) s.1 parent]

theorem closingFirstExit_congr_on_live {H I₁ I₂ : Type}
    (P : List Graph → Prop) (closed : PrefixClosed P) (past : H → EnvHistory I₁ I₂)
    (boundary other : (n : Nat) → ClosingLayer H I₁ I₂ n → Bool) (D : Nat)
    (agree : ∀ n, 0 < n → n ≤ D → ∀ s, P (History.graphSequence (closingLayerHistory past n s)) → boundary n s = other n s)
    (n : Nat) (bound : n ≤ D) (s : ClosingLayer H I₁ I₂ n)
    (live : P (History.graphSequence (closingLayerHistory past n s))) :
    closingFirstExit boundary n s = closingFirstExit other n s := by
  cases n with
  | zero => rfl
  | succ n =>
    simp only [closingFirstExit,closingActive_congr_on_live P closed past boundary other D agree (n+1) bound s live,
      agree (n+1) (by omega) bound s live]

theorem closingFirstExit_exact_on_live {H I₁ I₂ : Type}
    (P : List Graph → Prop) (closed : PrefixClosed P) (d : Nat) (past : H → EnvHistory I₁ I₂)
    (L : Nat) (depth : ∀ h, List.length (past h) = L)
    (boundary : (n : Nat) → ClosingLayer H I₁ I₂ n → Bool) (D : Nat)
    (exactFlags : ∀ n, 0 < n → n ≤ D → ∀ s, P (History.graphSequence (closingLayerHistory past n s)) →
      boundary n s = leaderBoundary P d (closingLayerHistory past n s))
    (n : Nat) (bound : n+1 ≤ D) (s : ClosingLayer H I₁ I₂ (n+1))
    (live : P (History.graphSequence (closingLayerHistory past (n+1) s))) :
    closingFirstExit boundary (n+1) s = true ↔
      (∀ m, L < m → m < L+(n+1) → leaderBoundary P d ((closingLayerHistory past (n+1) s).take m) = false) ∧
      leaderBoundary P d (closingLayerHistory past (n+1) s) = true := by
  rw [closingFirstExit_congr_on_live P closed past boundary
    (fun m s => leaderBoundary P d (closingLayerHistory past m s)) D exactFlags (n+1) bound s live]
  exact closingFirstExit_exact P d past L depth _ D (fun _ _ _ => rfl) n bound s

/-- A checked bounded graph scan supplies exactly the live positive-depth
flags consumed by the old first-exit masks. -/
theorem closingGraphFlags_exact_on_live {H I₁ I₂ Q : Type}
    [Fintype H] [Fintype I₁] [Fintype I₂] [Fintype Q] [DecidableEq Q] {d K D : Nat}
    (M : Recognizer Graph Q) [DecidablePred (· ∈ M.accept)]
    (P : List Graph → Prop) (closed : PrefixClosed P) (recognizes : ∀ g, P g ↔ M.eval g ∈ M.accept)
    (past : H → EnvHistory I₁ I₂) (source : H → GraphRootState Q d K)
    (sourceExact : ∀ h, GraphRootRep P M (History.graphSequence (past h)) (source h))
    (table : ClosingGraphTable H I₁ I₂ Q d K D) (checked : checkClosingGraphTable M source table = true) :
    ∀ n, 0 < n → n ≤ D → ∀ s, P (History.graphSequence (closingLayerHistory past n s)) →
      closingFlagAt (closingGraphBoundaryTable M table) n s = leaderBoundary P d (closingLayerHistory past n s) := by
  intro n positive bound s live
  cases n with
  | zero => omega
  | succ n =>
    simp only [closingFlagAt,dif_pos (show n+1 < D+1 by omega),closingGraphBoundaryTable]
    exact closingGraphBoundary_exact_on_live M P closed recognizes past source sourceExact table checked n bound s live


/-- The complete scheduled bundle checker is unchanged by replacing flags
outside live positive-depth scenarios. This permits reuse of the earlier
certificate soundness theorem with its semantic boundary table. -/
theorem checkScheduledExitBundle_boundary_congr_on_live {H I₁ I₂ O₁ O₂ Q : Type} {B D : Nat}
    [Fintype H] [Fintype I₁] [Fintype I₂]
    [DecidableEq H] [DecidableEq I₁] [DecidableEq I₂]
    [DecidableEq O₁] [DecidableEq O₂] [DecidableEq Q]
    (P : List Graph → Prop) (closed : PrefixClosed P) (past : H → EnvHistory I₁ I₂)
    (shape : InputShape H) (initialWindow : Bool)
    (boundary other live : ClosingFlagTable H I₁ I₂ D)
    (liveExact : ∀ m s, live m s = true ↔ P (History.graphSequence (closingLayerHistory past m.val s)))
    (agree : ∀ n, 0 < n → n ≤ D → ∀ s, P (History.graphSequence (closingLayerHistory past n s)) →
      closingFlagAt boundary n s = closingFlagAt other n s)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (initial : H → Q)
    (Allowed : SwitchInterface Q B → Prop) [DecidablePred Allowed]
    (expected : ClosingPolicy H I₁ I₂ O₁ O₂ D) (bundle : FirstExitBundle H I₁ I₂ O₁ O₂ Q B D) :
    checkScheduledExitBundle shape initialWindow boundary live step initial Allowed expected bundle =
      checkScheduledExitBundle shape initialWindow other live step initial Allowed expected bundle := by
  have exits : ∀ (n : Fin D) s, closingFlagAt live (n.val+1) s = true →
      closingFirstExit (closingFlagAt boundary) (n.val+1) s = closingFirstExit (closingFlagAt other) (n.val+1) s := by
    intro n s alive
    exact closingFirstExit_congr_on_live P closed past _ _ D agree (n.val+1) (by omega) s
      ((closingLiveTable_exact P past live liveExact (n.val+1) (by omega) s).mp alive)
  apply Bool.eq_iff_iff.mpr
  rw [checkScheduledExitBundle_correct,checkScheduledExitBundle_correct]
  constructor
  · rintro ⟨tied,coherent,valid⟩
    refine ⟨tied,coherent,fun n s scheduled alive exit => valid n s scheduled alive ?_⟩
    rwa [exits n s alive]
  · rintro ⟨tied,coherent,valid⟩
    refine ⟨tied,coherent,fun n s scheduled alive exit => valid n s scheduled alive ?_⟩
    rwa [← exits n s alive]

end Characterisation
