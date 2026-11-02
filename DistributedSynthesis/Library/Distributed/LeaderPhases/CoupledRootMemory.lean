/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.RootGraphActivity

/-! One finite phase-memory update carries the graph bank, persistent
activity bits, and physical objective labels. Proposed graph updates are
checked by the existing per-root transition relation. -/
namespace Characterisation
open DistributedSynthesis

abbrev CoupledRootMemory (H Q R : Type) (d K : Nat) :=
  (H → GraphRootState Q d K) × (H → Bool) × (H → R)

abbrev CoupledRootLetter (H Q I₁ I₂ O₁ O₂ : Type) (d K : Nat) :=
  (H → RoundRecord I₁ I₂ Graph Unit Unit) × (H → O₁ × O₂) × (H → GraphRootState Q d K)

instance coupledRootMemory_fintype {H Q R : Type} [Fintype H] [DecidableEq H] [Fintype Q] [Fintype R]
    (d K : Nat) : Fintype (CoupledRootMemory H Q R d K) := by
  unfold CoupledRootMemory
  infer_instance

def coupledRootNext {H Q R I₁ I₂ O₁ O₂ : Type} {d K : Nat}
    (M : Recognizer Graph Q) [DecidablePred (· ∈ M.accept)]
    (step : R → (I₁ × I₂ × Graph) → (O₁ × O₂) → R)
    (state : CoupledRootMemory H Q R d K) (letter : CoupledRootLetter H Q I₁ I₂ O₁ O₂ d K) :
    CoupledRootMemory H Q R d K :=
  (letter.2.2,rootActivityNext state.2.1 (fun h => graphRootStop M (state.1 h) (letter.1 h).graph),
    fun h => step (state.2.2 h) ((letter.1 h).inputOne,(letter.1 h).inputTwo,(letter.1 h).graph) (letter.2.1 h))

def checkCoupledRootStep {H Q R I₁ I₂ O₁ O₂ : Type} [Fintype H] [Fintype Q] [DecidableEq Q] {d K : Nat}
    (M : Recognizer Graph Q) [DecidablePred (· ∈ M.accept)]
    (state : CoupledRootMemory H Q R d K) (letter : CoupledRootLetter H Q I₁ I₂ O₁ O₂ d K) : Bool :=
  decide (∀ h, checkGraphRootStep M (state.1 h) (letter.1 h).graph (letter.2.2 h) = true)

/-- The combined update uses exactly the old activity and objective replay
recurrences. Graph certificates cannot change a round's inputs or outputs. -/
theorem coupledRootMemory_run_fields {H Q R I₁ I₂ O₁ O₂ : Type} {d K : Nat}
    (M : Recognizer Graph Q) [DecidablePred (· ∈ M.accept)]
    (step : R → (I₁ × I₂ × Graph) → (O₁ × O₂) → R) (initial : H → R)
    (bank : Nat → H → GraphRootState Q d K)
    (round : Nat → H → RoundRecord I₁ I₂ Graph Unit Unit) (output : Nat → H → O₁ × O₂) (n : Nat) :
    phaseMemoryRun (bank 0,(fun _ : H => true),initial) (coupledRootNext M step)
      (fun i => (round i,output i,bank (i+1))) n =
      (bank n,rootActivityRun (fun i h => graphRootStop M (bank i h) (round i h).graph) n,
        rootMonitorRun step initial round output n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [phaseMemoryRun,ih,coupledRootNext,rootActivityRun,rootMonitorRun]

/-- Passing the finite combined guard is precisely passing every root's
physical graph transition check. It fits the existing sticky parity guard. -/
theorem checkCoupledRootStep_run_iff {H Q R I₁ I₂ O₁ O₂ : Type}
    [Fintype H] [Fintype Q] [DecidableEq Q] {d K : Nat}
    (M : Recognizer Graph Q) [DecidablePred (· ∈ M.accept)]
    (step : R → (I₁ × I₂ × Graph) → (O₁ × O₂) → R) (initial : H → R)
    (bank : Nat → H → GraphRootState Q d K)
    (round : Nat → H → RoundRecord I₁ I₂ Graph Unit Unit) (output : Nat → H → O₁ × O₂) :
    (∀ n, checkCoupledRootStep M
      (phaseMemoryRun (bank 0,(fun _ : H => true),initial) (coupledRootNext M step)
        (fun i => (round i,output i,bank (i+1))) n) (round n,output n,bank (n+1)) = true) ↔
      ∀ n h, checkGraphRootStep M (bank n h) (round n h).graph (bank (n+1) h) = true := by
  simp only [coupledRootMemory_run_fields,checkCoupledRootStep,decide_eq_true_eq]

/-- In addition to graph/bit alignment, the same state carries the actual
objective label on each surviving live input root, under the earlier active
policy-implementation hypothesis. The boundary output is included. -/
theorem coupledRootMemory_active_label {H Q R I₁ I₂ O₁ O₂ : Type} {d K : Nat}
    (M : Recognizer Graph Q) [DecidablePred (· ∈ M.accept)]
    (P : List Graph → Prop) (closed : PrefixClosed P) (σ : StrategyPair I₁ I₂ O₁ O₂)
    (step : R → (I₁ × I₂ × Graph) → (O₁ × O₂) → R) (q₀ : R) (initial : H → R)
    (bank : Nat → H → GraphRootState Q d K)
    (history : Nat → H → EnvHistory I₁ I₂)
    (round : Nat → H → RoundRecord I₁ I₂ Graph Unit Unit)
    (extension : ∀ n h, history (n+1) h = history n h ++ [round n h])
    (output : Nat → H → O₁ × O₂)
    (start : ∀ h, P (History.graphSequence (history 0 h)) → initial h = strategyHistoryLabel σ step q₀ (history 0 h))
    (implements : ∀ n h, rootActivityRun (fun i h => graphRootStop M (bank i h) (round i h).graph) n h = true →
      P (History.graphSequence (history (n+1) h)) → output n h =
        (σ.one (currentView .one (history (n+1) h)),σ.two (currentView .two (history (n+1) h))))
    (n : Nat) (h : H)
    (active : rootActivityRun (fun i h => graphRootStop M (bank i h) (round i h).graph) n h = true)
    (live : P (History.graphSequence (history (n+1) h))) :
    (phaseMemoryRun (bank 0,(fun _ : H => true),initial) (coupledRootNext M step)
      (fun i => (round i,output i,bank (i+1))) (n+1)).2.2 h =
      strategyHistoryLabel σ step q₀ (history (n+1) h) := by
  rw [coupledRootMemory_run_fields]
  exact rootMonitorRun_exit_exact P closed σ step q₀ initial history round extension
    (fun i h => graphRootStop M (bank i h) (round i h).graph) output start implements n h active live

end Characterisation
