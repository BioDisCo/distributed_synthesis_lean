/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.RollingWindowTransport

/-! Readback across renewed closing windows contained in one earlier
window. All receiver-input branches are quantified together; the common
local implementation preserves the round of every output. -/
namespace Characterisation
open DistributedSynthesis

theorem rightInputHistory_branchNode {I₁ I₂ : Type}
    (env : Nat → I₂ × I₁) (k : Nat) :
    rightInputHistory (branchNode env k) =
      List.ofFn (fun i : Fin k =>
        (⟨(env i.val).2,(env i.val).1,.right,(),()⟩ : RoundRecord I₁ I₂ Graph Unit Unit)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.ofFn_succ']
    simpa [branchNode,rightInputHistory,List.concat_eq_append] using
      congrArg (fun h => h ++ [⟨(env k).2,(env k).1,.right,(),()⟩]) ih

/-- The suffix is evaluated at its actual history, not a history with the
one-way rounds removed. -/
theorem rollingSourceHistory_closing_split {H I₁ I₂ : Type}
    (past : H → EnvHistory I₁ I₂) (node : List (I₂ × I₁)) (h : H)
    (env : Nat → I₂ × I₁) (future : Nat → I₁ × I₂ × Graph) (k t : Nat)
    (follows : ∀ n, n < k → future n = ((env n).2,(env n).1,.right)) :
    closingEntryHistory (rollingSourceHistory past node h) future (k+t) =
      closingEntryHistory (rollingSourceHistory past (node ++ branchNode env k) h)
        (fun n => future (k+n)) t := by
  rw [closingEntryHistory_split]
  have wordEq : List.ofFn (fun i : Fin k =>
      let r := future i.val
      (⟨r.1,r.2.1,r.2.2,(),()⟩ : RoundRecord I₁ I₂ Graph Unit Unit)) =
      rightInputHistory (branchNode env k) := by
    rw [rightInputHistory_branchNode]
    congr 1
    funext i
    rw [follows i.val i.isLt]
  rw [wordEq]
  simp only [rollingSourceHistory,rightInputHistory,List.map_append,List.append_assoc]

/-- Rolling overlap preserves arbitrary closing suffixes on every input
branch, not just the physical all-right branch used by the phase monitor. -/
theorem rollingBanks_transport {H I₁ I₂ O₁ O₂ : Type} {D : Nat}
    (banks : List (I₂ × I₁) → ClosingPlanBank H I₁ I₂ O₁ O₂ D)
    (overlap : ∀ node r h, RollingClosingOverlap (banks node h)
      (banks (node ++ [r]) h) (r.2,r.1,.right))
    (node : List (I₂ × I₁)) (h : H) (env : Nat → I₂ × I₁)
    (future : Nat → I₁ × I₂ × Graph) (k t : Nat) (within : k+t < D+1)
    (follows : ∀ n, n < k → future n = ((env n).2,(env n).1,.right)) :
    closingPlanEntry (banks node h) future ⟨k+t,within⟩ =
      closingPlanEntry (banks (node ++ branchNode env k) h)
        (fun n => future (k+n)) ⟨t,by omega⟩ := by
  have checks : ∀ n, RollingClosingOverlap (banks (node ++ branchNode env n) h)
      (banks (node ++ branchNode env (n+1)) h) ((env n).2,(env n).1,.right) := by
    intro n
    simpa only [branchNode,List.append_assoc] using overlap (node ++ branchNode env n) (env n) h
  simpa only [branchNode,List.append_nil] using rollingClosingPlans_transport
    (fun n => banks (node ++ branchNode env n) h)
    (fun n => ((env n).2,(env n).1,.right)) checks future k t within follows

/-- One local strategy simultaneously implements all renewed windows whose
outputs lie in the initial window. The quantifiers include different roots,
different input threads, different cut times, and arbitrary closing graphs.
No agreement is imposed between different absolute output rounds. -/
theorem rollingBanks_common_window_local {H I₁ I₂ O₁ O₂ : Type} {D : Nat}
    [DecidableEq I₁] [DecidableEq I₂] [Nonempty O₁] [Nonempty O₂]
    (past : H → EnvHistory I₁ I₂) (shape : InputShape H)
    (rep : RepresentsInputShape past shape) (L : Nat) (depth : ∀ h, List.length (past h) = L)
    (banks : List (I₂ × I₁) → ClosingPlanBank H I₁ I₂ O₁ O₂ D)
    (overlap : ∀ node r h, RollingClosingOverlap (banks node h)
      (banks (node ++ [r]) h) (r.2,r.1,.right))
    (coherent : ClosingBankCoherent shape (banks [])) :
    ∃ σ : StrategyPair I₁ I₂ O₁ O₂,
      ∀ h (env : Nat → I₂ × I₁) (future : Nat → I₁ × I₂ × Graph)
        (k t : Nat) (within : k+t < D+1),
        (∀ n, n < k → future n = ((env n).2,(env n).1,.right)) →
        let hist := closingEntryHistory (rollingSourceHistory past (branchNode env k) h)
          (fun n => future (k+n)) t
        let out := closingPlanEntry (banks (branchNode env k) h)
          (fun n => future (k+n)) ⟨t,by omega⟩
        σ.one (currentView .one hist) = out.1 ∧
          σ.two (currentView .two hist) = out.2 := by
  obtain ⟨σ,correct⟩ := closingBankCoherent_local past shape rep L depth (banks []) coherent
  refine ⟨σ,fun h env future k t within follows => ?_⟩
  have output := rollingBanks_transport banks overlap [] h env future k t within follows
  have history := rollingSourceHistory_closing_split past [] h env future k t follows
  simp only [List.nil_append] at output history
  have result := correct h ((),⟨⟨k+t,within⟩,fun j => future j.val⟩)
  change σ.one (currentView .one (closingEntryHistory (past h) future (k+t))) =
      (closingPlanEntry (banks [] h) future ⟨k+t,within⟩).1 ∧
    σ.two (currentView .two (closingEntryHistory (past h) future (k+t))) =
      (closingPlanEntry (banks [] h) future ⟨k+t,within⟩).2 at result
  have initial : rollingSourceHistory past [] h = past h := by
    simp [rollingSourceHistory,rightInputHistory]
  rw [initial] at history
  rw [history,output] at result
  exact result

end Characterisation
