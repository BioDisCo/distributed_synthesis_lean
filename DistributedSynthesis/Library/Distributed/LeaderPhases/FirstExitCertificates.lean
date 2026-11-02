/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.StoppedClosingReplay

/-! Bind the unchanged full-policy certificate checker to first exits of
an actual phase. Completeness of the target component forces every retained
history to be a first exit, where only active outputs determine its label. -/
namespace Characterisation
open DistributedSynthesis

/-- A complete first-exit certificate has the actual composed strategy's
monitor labels although its auxiliary policy may differ after handover.
The source labels, flag interpretation, and target coverage are explicit. -/
theorem first_exit_certificate_correct {H I₁ I₂ O₁ O₂ Q : Type}
    [Fintype H] [Fintype I₁] [Fintype I₂]
    [DecidableEq H] [DecidableEq I₁] [DecidableEq I₂]
    [DecidableEq O₁] [DecidableEq O₂] [DecidableEq Q]
    [Nonempty O₁] [Nonempty O₂]
    (P : List Graph → Prop) (closed : PrefixClosed P) (d : Nat)
    (recent : ∀ g, P g → ∃ p, RecentOther P d g p)
    (past : H → EnvHistory I₁ I₂) (injective : Function.Injective past)
    (shape : InputShape H) (rep : RepresentsInputShape past shape)
    (L : Nat) (depth : ∀ h, List.length (past h) = L)
    (boundary : (n : Nat) → ClosingLayer H I₁ I₂ n → Bool)
    (σ : StrategyPair I₁ I₂ O₁ O₂)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (q₀ : Q) (initial : H → Q)
    (source : ∀ h, initial h = strategyHistoryLabel σ step q₀ (past h))
    {B D n : Nat} (bound : n+1 ≤ D)
    (boundaryExact : ∀ m, m ≤ D → ∀ s, boundary m s = leaderBoundary P d (closingLayerHistory past m s))
    (live : ClosingLayer H I₁ I₂ (n+1) → Bool)
    (liveExact : ∀ s, live s = true ↔ P (History.graphSequence (closingLayerHistory past (n+1) s)))
    (root : ClosingLayer H I₁ I₂ (n+1))
    (rootLive : P (History.graphSequence (closingLayerHistory past (n+1) root)))
    (exit : closingFirstExit boundary (n+1) root = true)
    (covers : ∀ k, InputConnected P (closingLayerHistory past (n+1) root) k →
      ∃ s, closingLayerHistory past (n+1) s = k)
    (Allowed : SwitchInterface Q B → Prop) [DecidablePred Allowed]
    (move : ClosingBoundaryCertificate H I₁ I₂ O₁ O₂ Q B D (n+1))
    (valid : checkClosingBoundaryCertificate shape step initial bound live root Allowed move = true)
    (implements : ∀ t s, LiveClosingActive P past boundary (t.val+1) s → move.2.1 t s =
      (σ.one (currentView .one (closingLayerHistory past (t.val+1) s)),
       σ.two (currentView .two (closingLayerHistory past (t.val+1) s)))) :
    Function.Injective (closingLayerHistory past (n+1) ∘ move.2.2.1) ∧
    (∀ k, InputConnected P (closingLayerHistory past (n+1) root) k ↔
      ∃ s, closingLayerHistory past (n+1) (move.2.2.1 s) = k) ∧
    (∀ s, closingFirstExit boundary (n+1) (move.2.2.1 s) = true ∧
      move.2.2.2.2 s = strategyHistoryLabel σ step q₀ (closingLayerHistory past (n+1) (move.2.2.1 s))) ∧
    Allowed ⟨move.1,move.2.2.2⟩ := by
  have correct := (checkClosingBoundaryCertificate_correct_of_target_coverage P past injective shape rep
    L depth step initial bound live liveExact root rootLive covers Allowed move).mp valid
  have connected : ∀ s, InputConnected P (closingLayerHistory past (n+1) root)
      (closingLayerHistory past (n+1) (move.2.2.1 s)) :=
    fun s => (correct.2.2 _).mpr ⟨s,rfl⟩
  have exits : ∀ s, closingFirstExit boundary (n+1) (move.2.2.1 s) = true := by
    intro s
    rw [← closingFirstExit_component P closed d recent past L depth boundary D boundaryExact
      (n+1) bound root (move.2.2.1 s) rootLive (connected s)]
    exact exit
  have retained : ∀ s, LiveClosingActive P past boundary (n+1) (move.2.2.1 s) := by
    intro s
    have isExit := exits s
    simp only [closingFirstExit,Bool.and_eq_true] at isExit
    exact ⟨isExit.1,inputConnected_live P rootLive (connected s)⟩
  have labels := checkedClosingCertificate_active_labels P closed σ past shape boundary step q₀ initial
    source bound live root Allowed move valid implements retained
  exact ⟨correct.2.1,correct.2.2,fun s => ⟨exits s,labels s⟩,correct.1.2.2⟩

end Characterisation
