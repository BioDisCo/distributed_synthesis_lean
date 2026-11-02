/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.ActiveClosingRoots

/-! Correct carried activity is constant on the ancestors of a live target
component. Removing inactive roots therefore preserves complete target
coverage for every retained closing scenario. -/
namespace Characterisation
open DistributedSynthesis

theorem closingLayerHistory_take_source {H I₁ I₂ : Type}
    (past : H → EnvHistory I₁ I₂) (L : Nat) (depth : ∀ h, List.length (past h) = L)
    (n : Nat) (s : ClosingLayer H I₁ I₂ n) :
    (closingLayerHistory past n s).take L = past (closingLayerRoot n s) := by
  rw [closingLayerHistory_word,← depth (closingLayerRoot n s),List.take_left]

theorem closingLayerHistory_take_before_source {H I₁ I₂ : Type}
    (past : H → EnvHistory I₁ I₂) (L : Nat) (depth : ∀ h, List.length (past h) = L)
    (n : Nat) (s : ClosingLayer H I₁ I₂ n) (m : Nat) (bound : m ≤ L) :
    (closingLayerHistory past n s).take m = (past (closingLayerRoot n s)).take m := by
  rw [← closingLayerHistory_take_source past L depth n s,List.take_take,min_eq_left bound]

/-- The bit records absence of a boundary after the original phase start
and through the current source cut, including the cut itself. -/
def SourceActivityExact {H I₁ I₂ : Type}
    (P : List Graph → Prop) (d a L : Nat) (past : H → EnvHistory I₁ I₂) (active : H → Bool) : Prop :=
  ∀ h, active h = true ↔ ∀ m, a < m → m ≤ L → leaderBoundary P d ((past h).take m) = false

theorem sourceActivity_component {H I₁ I₂ : Type}
    (P : List Graph → Prop) (closed : PrefixClosed P) (d : Nat)
    (recent : ∀ g, P g → ∃ p, RecentOther P d g p)
    (past : H → EnvHistory I₁ I₂) (a L : Nat) (depth : ∀ h, List.length (past h) = L)
    (active : H → Bool) (exactActivity : SourceActivityExact P d a L past active)
    (n : Nat) (s t : ClosingLayer H I₁ I₂ n)
    (live : P (History.graphSequence (closingLayerHistory past n s)))
    (conn : InputConnected P (closingLayerHistory past n s) (closingLayerHistory past n t)) :
    active (closingLayerRoot n s) = active (closingLayerRoot n t) := by
  have flags : ∀ m, m ≤ L →
      leaderBoundary P d ((past (closingLayerRoot n s)).take m) =
        leaderBoundary P d ((past (closingLayerRoot n t)).take m) := by
    intro m hm
    have eq := leaderBoundary_history_component P closed d recent live conn m
    simpa only [closingLayerHistory_take_before_source past L depth n s m hm,
      closingLayerHistory_take_before_source past L depth n t m hm] using eq
  apply Bool.eq_iff_iff.mpr
  rw [exactActivity,exactActivity]
  constructor
  · intro all m lower upper
    rw [← flags m upper]
    exact all m lower upper
  · intro all m lower upper
    rw [flags m upper]
    exact all m lower upper

/-- A target covered by the original source family remains fully covered
when only the carried active roots are passed to the closing checker. -/
theorem activeClosingLayer_component_coverage {H I₁ I₂ : Type}
    (P : List Graph → Prop) (closed : PrefixClosed P) (d : Nat)
    (recent : ∀ g, P g → ∃ p, RecentOther P d g p)
    (past : H → EnvHistory I₁ I₂) (a L : Nat) (depth : ∀ h, List.length (past h) = L)
    (active : H → Bool) (exactActivity : SourceActivityExact P d a L past active)
    (n : Nat) (root : ClosingLayer (ActiveClosingRoots active) I₁ I₂ n)
    (live : P (History.graphSequence (closingLayerHistory (past ∘ Subtype.val) n root)))
    (covers : ∀ k, InputConnected P (closingLayerHistory (past ∘ Subtype.val) n root) k →
      ∃ s : ClosingLayer H I₁ I₂ n, closingLayerHistory past n s = k) :
    ∀ k, InputConnected P (closingLayerHistory (past ∘ Subtype.val) n root) k →
      ∃ s : ClosingLayer (ActiveClosingRoots active) I₁ I₂ n,
        closingLayerHistory (past ∘ Subtype.val) n s = k := by
  intro k conn
  obtain ⟨s,eq⟩ := covers k conn
  have oldLive : P (History.graphSequence (closingLayerHistory past n (mapClosingLayer Subtype.val n root))) := by
    rwa [← closingLayerHistory_map]
  have oldConn : InputConnected P (closingLayerHistory past n (mapClosingLayer Subtype.val n root))
      (closingLayerHistory past n s) := by
    simpa only [← closingLayerHistory_map,eq] using conn
  have alive : active (closingLayerRoot n s) = true := by
    rw [← sourceActivity_component P closed d recent past a L depth active exactActivity n
      (mapClosingLayer Subtype.val n root) s oldLive oldConn]
    exact activeClosingLayer_root_alive active n root
  obtain ⟨t,teq⟩ := activeClosingLayer_preimage active n s alive
  exact ⟨t,by rw [closingLayerHistory_map,teq,eq]⟩

/-- The persistent one-bit update provides the activity invariant required
by source restriction at every later physical cut. -/
theorem rootActivityRun_source_exact {H I₁ I₂ : Type}
    (P : List Graph → Prop) (d a : Nat)
    (history : Nat → H → EnvHistory I₁ I₂)
    (prefixes : ∀ i j, i ≤ j → ∀ h, (history j h).take (a+i) = history i h)
    (boundary : Nat → H → Bool)
    (exactFlags : ∀ i h, boundary i h = leaderBoundary P d (history (i+1) h)) (n : Nat) :
    SourceActivityExact P d a (a+n) (history n) (rootActivityRun boundary n) :=
  fun h => rootActivityRun_history P d a history prefixes boundary exactFlags n h

end Characterisation
