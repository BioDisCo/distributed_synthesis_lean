/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.BoundaryTargetCertificates

/-! Bind closing certificates to the actual strategy's monitor labels.
The source-label invariant is transported through every closing round;
retained labels are not freely chosen annotations or independently reset states. -/
namespace Characterisation
open DistributedSynthesis

def strategyLabelStep {I₁ I₂ O₁ O₂ Q : Type}
    (σ : StrategyPair I₁ I₂ O₁ O₂)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
    (state : EnvHistory I₁ I₂ × Q) (r : RoundRecord I₁ I₂ Graph Unit Unit) : EnvHistory I₁ I₂ × Q :=
  let next := state.1 ++ [r]
  (next,step state.2 (r.inputOne,r.inputTwo,r.graph)
    (σ.one (currentView .one next),σ.two (currentView .two next)))

def strategyHistoryLabel {I₁ I₂ O₁ O₂ Q : Type}
    (σ : StrategyPair I₁ I₂ O₁ O₂)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (initial : Q)
    (h : EnvHistory I₁ I₂) : Q :=
  (h.foldl (strategyLabelStep σ step) ([],initial)).2

theorem strategyLabelStep_history {I₁ I₂ O₁ O₂ Q : Type}
    (σ : StrategyPair I₁ I₂ O₁ O₂)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
    (h : EnvHistory I₁ I₂) (q : Q) (u : EnvHistory I₁ I₂) :
    (u.foldl (strategyLabelStep σ step) (h,q)).1 = h++u := by
  induction u generalizing h q with
  | nil => simp
  | cons r u ih =>
    simp only [List.foldl_cons,strategyLabelStep]
    rw [ih]
    simp only [List.append_assoc,List.singleton_append]

theorem strategyHistoryLabel_append {I₁ I₂ O₁ O₂ Q : Type}
    (σ : StrategyPair I₁ I₂ O₁ O₂)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (initial : Q)
    (h : EnvHistory I₁ I₂) (r : RoundRecord I₁ I₂ Graph Unit Unit) :
    strategyHistoryLabel σ step initial (h++[r]) =
      step (strategyHistoryLabel σ step initial h) (r.inputOne,r.inputTwo,r.graph)
        (σ.one (currentView .one (h++[r])),σ.two (currentView .two (h++[r]))) := by
  unfold strategyHistoryLabel
  rw [List.foldl_append]
  simp only [List.foldl_cons,List.foldl_nil,strategyLabelStep,strategyLabelStep_history,List.nil_append]

/-- Monitor replay along a closing layer is exactly the full-history label
of the same strategy when the carried source labels are truthful. -/
theorem closingLayerLabels_strategyHistory {H I₁ I₂ O₁ O₂ Q : Type} {D : Nat}
    (σ : StrategyPair I₁ I₂ O₁ O₂) (past : H → EnvHistory I₁ I₂)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (q₀ : Q) (initial : H → Q)
    (source : ∀ h, initial h = strategyHistoryLabel σ step q₀ (past h))
    (out : ClosingPolicy H I₁ I₂ O₁ O₂ D)
    (implements : ∀ t s, out t s =
      (σ.one (currentView .one (closingLayerHistory past (t.val+1) s)),
       σ.two (currentView .two (closingLayerHistory past (t.val+1) s))))
    (n : Nat) (bound : n ≤ D) (s : ClosingLayer H I₁ I₂ n) :
    closingLayerLabels step initial out n bound s =
      strategyHistoryLabel σ step q₀ (closingLayerHistory past n s) := by
  induction n with
  | zero => exact source s
  | succ n ih =>
    simp only [closingLayerLabels]
    rw [ih,implements]
    change step (strategyHistoryLabel σ step q₀ (closingLayerHistory past n s.1)) s.2
      (σ.one (currentView .one (closingLayerHistory past (n+1) s)),
       σ.two (currentView .two (closingLayerHistory past (n+1) s))) = _
    simpa only [closingLayerHistory,scenarioHistory] using
      (strategyHistoryLabel_append σ step q₀ (closingLayerHistory past n s.1)
        ⟨s.2.1,s.2.2.1,s.2.2.2,(),()⟩).symm

/-- The exact-plan equality supplied by whole-phase readback also gives
exact outputs in the existing closing-policy representation. -/
theorem closingPolicyOfBank_implements {H I₁ I₂ O₁ O₂ : Type} {D : Nat}
    (σ : StrategyPair I₁ I₂ O₁ O₂) (past : H → EnvHistory I₁ I₂)
    (bank : ClosingPlanBank H I₁ I₂ O₁ O₂ D)
    (plans : ∀ h, closingPlanOfStrategy σ (past h) (D+1) = bank h) :
    ∀ t s, closingPolicyOfBank bank t s =
      (σ.one (currentView .one (closingLayerHistory past (t.val+1) s)),
       σ.two (currentView .two (closingLayerHistory past (t.val+1) s))) := by
  intro t s
  simp only [closingPolicyOfBank,← plans,closingPlanOfStrategy,windowHistory,closingLayerHistory_word]

/-- A passing certificate cannot reset or invent retained monitor labels.
This statement is independent of target coverage, which is checked by the
separate complete-component enumeration theorem. -/
theorem checkedClosingCertificate_strategy_labels {H I₁ I₂ O₁ O₂ Q : Type}
    [Fintype H] [Fintype I₁] [Fintype I₂]
    [DecidableEq H] [DecidableEq I₁] [DecidableEq I₂]
    [DecidableEq O₁] [DecidableEq O₂] [DecidableEq Q]
    (σ : StrategyPair I₁ I₂ O₁ O₂) (past : H → EnvHistory I₁ I₂)
    (shape : InputShape H)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (q₀ : Q) (initial : H → Q)
    (source : ∀ h, initial h = strategyHistoryLabel σ step q₀ (past h))
    {B D n : Nat} (bound : n ≤ D)
    (live : ClosingLayer H I₁ I₂ n → Bool) (root : ClosingLayer H I₁ I₂ n)
    (Allowed : SwitchInterface Q B → Prop) [DecidablePred Allowed]
    (move : ClosingBoundaryCertificate H I₁ I₂ O₁ O₂ Q B D n)
    (valid : checkClosingBoundaryCertificate shape step initial bound live root Allowed move = true)
    (implements : ∀ t s, move.2.1 t s =
      (σ.one (currentView .one (closingLayerHistory past (t.val+1) s)),
       σ.two (currentView .two (closingLayerHistory past (t.val+1) s)))) :
    ∀ s, move.2.2.2.2 s = strategyHistoryLabel σ step q₀
      (closingLayerHistory past n (move.2.2.1 s)) := by
  simp only [checkClosingBoundaryCertificate,Bool.and_eq_true] at valid
  have check := valid.1
  simp only [checkClosingMove,decide_eq_true_eq] at check
  intro s
  rw [check.2.1]
  exact closingLayerLabels_strategyHistory σ past step q₀ initial source move.2.1 implements n bound _

end Characterisation
