/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.CoherentLeaderTables

/-! Closing windows retain absolute round numbers. Replenishing a plan
transports its remaining promises, including arbitrary closing branches;
it does not delete or identify physical rounds. -/
namespace Characterisation
open DistributedSynthesis

/-- The history at which offset `t` of a closing plan produces its output.
The output occurs after exactly `t+1` new rounds. -/
def closingEntryHistory {I₁ I₂ : Type*} (past : EnvHistory I₁ I₂)
    (rounds : Nat → I₁ × I₂ × Graph) (t : Nat) : EnvHistory I₁ I₂ :=
  past ++ List.ofFn (fun i : Fin (t+1) =>
    let r := rounds i.val
    (⟨r.1,r.2.1,r.2.2,(),()⟩ : RoundRecord I₁ I₂ Graph Unit Unit))

@[simp] theorem closingEntryHistory_length {I₁ I₂ : Type*}
    (past : EnvHistory I₁ I₂) (rounds : Nat → I₁ × I₂ × Graph) (t : Nat) :
    List.length (closingEntryHistory past rounds t) = List.length past + t + 1 := by
  simp [closingEntryHistory,Nat.add_assoc]

/-- Equal views imply equal absolute output rounds, even if the closing
windows began at different times. -/
theorem closingEntryHistory_same_round {I₁ I₂ : Type*} (p : Proc)
    (past other : EnvHistory I₁ I₂)
    (rounds future : Nat → I₁ × I₂ × Graph) (t u : Nat)
    (same : currentView p (closingEntryHistory past rounds t) =
      currentView p (closingEntryHistory other future u)) :
    List.length past + t + 1 = List.length other + u + 1 := by
  have len := congrArg (fun v => (ownInputs v).length) same
  simpa only [ownInputs_current,inputWord,List.length_map,
    closingEntryHistory_length] using len

/-- Only entries in the finite inspected prefix matter. -/
theorem closingPlanEntry_congr {I₁ I₂ O₁ O₂ : Type*} {D : Nat}
    (plan : LeaderClosingPlan I₁ I₂ O₁ O₂ D)
    (rounds future : Nat → I₁ × I₂ × Graph) (t : Fin D)
    (same : ∀ n, n ≤ t.val → rounds n = future n) :
    closingPlanEntry plan rounds t = closingPlanEntry plan future t := by
  unfold closingPlanEntry
  apply congrArg plan
  apply Prod.ext
  · rfl
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  funext i
  exact same i.val (Nat.le_of_lt_succ i.isLt)

/-- Advance the start by `k` actual rounds and decrease the output offset
by `k`. Every arbitrary closing continuation is preserved. The two sides
refer to the same absolute round; the future after the cut is unrestricted. -/
theorem rollingClosingPlans_transport {I₁ I₂ O₁ O₂ : Type*} {D : Nat}
    (plans : Nat → LeaderClosingPlan I₁ I₂ O₁ O₂ (D+1))
    (rounds : Nat → I₁ × I₂ × Graph)
    (overlap : ∀ a, RollingClosingOverlap (plans a) (plans (a+1)) (rounds a))
    (future : Nat → I₁ × I₂ × Graph) (k t : Nat) (within : k+t < D+1)
    (follows : ∀ n, n < k → future n = rounds n) :
    closingPlanEntry (plans 0) future ⟨k+t,within⟩ =
      closingPlanEntry (plans k) (fun n => future (k+n)) ⟨t,by omega⟩ := by
  induction k generalizing plans rounds future with
  | zero => simp
  | succ k ih =>
    have first : future 0 = rounds 0 := follows 0 (by omega)
    have offset : k+1+t = (k+t)+1 := by omega
    have step := closingPlanEntry_succ (plans 0) future ⟨k+t,by omega⟩
    have shifted := ih (fun n => plans (n+1)) (fun n => rounds (n+1))
      (fun n => overlap (n+1)) (fun n => future (n+1)) (by omega)
      (fun n hn => follows (n+1) (by omega))
    rw [first,overlap 0,closingPlanEntry_restrict] at step
    exact (show closingPlanEntry (plans 0) future ⟨k+1+t,within⟩ =
      closingPlanEntry (plans 1) (fun n => future (n+1)) ⟨k+t,by omega⟩ by
        simpa only [offset] using step).trans (by
          simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using shifted)

/-- Splitting a history at a later cut changes its representation only.
The complete input/graph history and its absolute depth are identical. -/
theorem closingEntryHistory_split {I₁ I₂ : Type*}
    (past : EnvHistory I₁ I₂) (future : Nat → I₁ × I₂ × Graph) (k t : Nat) :
    closingEntryHistory past future (k+t) =
      closingEntryHistory
        (past ++ List.ofFn (fun i : Fin k =>
          let r := future i.val
          (⟨r.1,r.2.1,r.2.2,(),()⟩ : RoundRecord I₁ I₂ Graph Unit Unit)))
        (fun n => future (k+n)) t := by
  unfold closingEntryHistory
  simp only [Nat.add_assoc]
  rw [List.ofFn_add,List.append_assoc]
  rfl

end Characterisation
