/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.FirstBoundaryMask

/-! Full closing policies may contain auxiliary entries after handover.
Only live active entries determine the monitor labels at first exits. -/
namespace Characterisation
open DistributedSynthesis

/-- Replay is insensitive to outputs outside any prefix-closed collection
of closing scenarios. The same source labels are used on both sides. -/
theorem closingLayerLabels_congr_on_prefixes {H I₁ I₂ O₁ O₂ Q : Type} {D : Nat}
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (initial : H → Q)
    (out other : ClosingPolicy H I₁ I₂ O₁ O₂ D)
    (valid : (n : Nat) → ClosingLayer H I₁ I₂ n → Prop)
    (parents : ∀ n s, valid (n+1) s → valid n s.1)
    (agree : ∀ t s, valid (t.val+1) s → out t s = other t s)
    (n : Nat) (bound : n ≤ D) (s : ClosingLayer H I₁ I₂ n) (member : valid n s) :
    closingLayerLabels step initial out n bound s = closingLayerLabels step initial other n bound s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [closingLayerLabels]
    rw [ih (by omega) s.1 (parents n s member),agree ⟨n,by omega⟩ s member]

theorem closingLayerHistory_live_parent {H I₁ I₂ : Type}
    (P : List Graph → Prop) (closed : PrefixClosed P) (past : H → EnvHistory I₁ I₂)
    (n : Nat) (s : ClosingLayer H I₁ I₂ (n+1))
    (live : P (History.graphSequence (closingLayerHistory past (n+1) s))) :
    P (History.graphSequence (closingLayerHistory past n s.1)) := by
  apply closed _ [s.2.2.2]
  simpa only [closingLayerHistory,scenarioHistory,History.graphSequence,List.map_append,
    List.map_cons,List.map_nil] using live

def LiveClosingActive {H I₁ I₂ : Type}
    (P : List Graph → Prop) (past : H → EnvHistory I₁ I₂)
    (boundary : (n : Nat) → ClosingLayer H I₁ I₂ n → Bool)
    (n : Nat) (s : ClosingLayer H I₁ I₂ n) : Prop :=
  closingActive boundary n s = true ∧ P (History.graphSequence (closingLayerHistory past n s))

theorem liveClosingActive_parent {H I₁ I₂ : Type}
    (P : List Graph → Prop) (closed : PrefixClosed P) (past : H → EnvHistory I₁ I₂)
    (boundary : (n : Nat) → ClosingLayer H I₁ I₂ n → Bool)
    (n : Nat) (s : ClosingLayer H I₁ I₂ (n+1))
    (valid : LiveClosingActive P past boundary (n+1) s) : LiveClosingActive P past boundary n s.1 :=
  ⟨closingActive_parent boundary n s valid.1,closingLayerHistory_live_parent P closed past n s valid.2⟩

/-- Only the live active outputs of the policy must be implemented by the
actual strategy. Arbitrary auxiliary entries beyond the boundary are ignored. -/
theorem closingActiveLabels_strategy {H I₁ I₂ O₁ O₂ Q : Type} {D : Nat}
    (P : List Graph → Prop) (closed : PrefixClosed P)
    (σ : StrategyPair I₁ I₂ O₁ O₂) (past : H → EnvHistory I₁ I₂)
    (boundary : (n : Nat) → ClosingLayer H I₁ I₂ n → Bool)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (q₀ : Q) (initial : H → Q)
    (source : ∀ h, initial h = strategyHistoryLabel σ step q₀ (past h))
    (out : ClosingPolicy H I₁ I₂ O₁ O₂ D)
    (implements : ∀ t s, LiveClosingActive P past boundary (t.val+1) s → out t s =
      (σ.one (currentView .one (closingLayerHistory past (t.val+1) s)),
       σ.two (currentView .two (closingLayerHistory past (t.val+1) s))))
    (n : Nat) (bound : n ≤ D) (s : ClosingLayer H I₁ I₂ n)
    (active : LiveClosingActive P past boundary n s) :
    closingLayerLabels step initial out n bound s = strategyHistoryLabel σ step q₀ (closingLayerHistory past n s) := by
  let actual : ClosingPolicy H I₁ I₂ O₁ O₂ D := fun t s =>
    (σ.one (currentView .one (closingLayerHistory past (t.val+1) s)),
     σ.two (currentView .two (closingLayerHistory past (t.val+1) s)))
  rw [closingLayerLabels_congr_on_prefixes step initial out actual
    (LiveClosingActive P past boundary) (liveClosingActive_parent P closed past boundary) implements n bound s active]
  exact closingLayerLabels_strategyHistory σ past step q₀ initial source actual (fun _ _ => rfl) n bound s

/-- A passing certificate has the actual strategy's labels at every retained
live active slot, even when its complete policy differs after handover. -/
theorem checkedClosingCertificate_active_labels {H I₁ I₂ O₁ O₂ Q : Type}
    [Fintype H] [Fintype I₁] [Fintype I₂]
    [DecidableEq H] [DecidableEq I₁] [DecidableEq I₂]
    [DecidableEq O₁] [DecidableEq O₂] [DecidableEq Q]
    (P : List Graph → Prop) (closed : PrefixClosed P)
    (σ : StrategyPair I₁ I₂ O₁ O₂) (past : H → EnvHistory I₁ I₂)
    (shape : InputShape H)
    (boundary : (n : Nat) → ClosingLayer H I₁ I₂ n → Bool)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (q₀ : Q) (initial : H → Q)
    (source : ∀ h, initial h = strategyHistoryLabel σ step q₀ (past h))
    {B D n : Nat} (bound : n ≤ D)
    (live : ClosingLayer H I₁ I₂ n → Bool) (root : ClosingLayer H I₁ I₂ n)
    (Allowed : SwitchInterface Q B → Prop) [DecidablePred Allowed]
    (move : ClosingBoundaryCertificate H I₁ I₂ O₁ O₂ Q B D n)
    (valid : checkClosingBoundaryCertificate shape step initial bound live root Allowed move = true)
    (implements : ∀ t s, LiveClosingActive P past boundary (t.val+1) s → move.2.1 t s =
      (σ.one (currentView .one (closingLayerHistory past (t.val+1) s)),
       σ.two (currentView .two (closingLayerHistory past (t.val+1) s))))
    (retained : ∀ s, LiveClosingActive P past boundary n (move.2.2.1 s)) :
    ∀ s, move.2.2.2.2 s = strategyHistoryLabel σ step q₀
      (closingLayerHistory past n (move.2.2.1 s)) := by
  simp only [checkClosingBoundaryCertificate,Bool.and_eq_true] at valid
  have check := valid.1
  simp only [checkClosingMove,decide_eq_true_eq] at check
  intro s
  rw [check.2.1]
  exact closingActiveLabels_strategy P closed σ past boundary step q₀ initial source
    move.2.1 implements n bound _ (retained s)

end Characterisation
