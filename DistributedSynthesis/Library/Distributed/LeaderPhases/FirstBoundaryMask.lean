/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.PhaseParityComposition

/-! A bounded closing scan stops after its first positive-depth boundary.
The boundary output is included. The mask is finite data; computing truthful
boundary flags from the eventual game interface is a separate obligation. -/
namespace Characterisation
open DistributedSynthesis

abbrev ClosingFlagTable (H I₁ I₂ : Type) (D : Nat) :=
  (n : Fin (D+1)) → ClosingLayer H I₁ I₂ n.val → Bool

instance closingFlagTable_fintype {H I₁ I₂ : Type}
    [Fintype H] [Fintype I₁] [Fintype I₂]
    [DecidableEq H] [DecidableEq I₁] [DecidableEq I₂] (D : Nat) :
    Fintype (ClosingFlagTable H I₁ I₂ D) := by
  unfold ClosingFlagTable
  infer_instance

def closingFlagAt {H I₁ I₂ : Type} {D : Nat}
    (table : ClosingFlagTable H I₁ I₂ D) (n : Nat) (s : ClosingLayer H I₁ I₂ n) : Bool :=
  if within : n < D+1 then table ⟨n,within⟩ s else false

/-- Initial sources do not terminate their own new scan. A boundary at
positive depth n terminates it after the output at depth n. -/
def closingActive {H I₁ I₂ : Type}
    (boundary : (n : Nat) → ClosingLayer H I₁ I₂ n → Bool) :
    (n : Nat) → ClosingLayer H I₁ I₂ n → Bool
  | 0, _ => true
  | 1, _ => true
  | n+2, s => closingActive boundary (n+1) s.1 && !boundary (n+1) s.1

def closingFirstExit {H I₁ I₂ : Type}
    (boundary : (n : Nat) → ClosingLayer H I₁ I₂ n → Bool) :
    (n : Nat) → ClosingLayer H I₁ I₂ n → Bool
  | 0, _ => false
  | n+1, s => closingActive boundary (n+1) s && boundary (n+1) s

theorem closingActive_parent {H I₁ I₂ : Type}
    (boundary : (n : Nat) → ClosingLayer H I₁ I₂ n → Bool)
    (n : Nat) (s : ClosingLayer H I₁ I₂ (n+1))
    (active : closingActive boundary (n+1) s = true) :
    closingActive boundary n s.1 = true := by
  cases n with
  | zero => rfl
  | succ n =>
    simp only [closingActive,Bool.and_eq_true] at active
    exact active.1

/-- The next position after a first exit is inactive, irrespective of its
inputs and graph. Prefix closure then prevents any later reactivation. -/
theorem closingFirstExit_stops {H I₁ I₂ : Type}
    (boundary : (n : Nat) → ClosingLayer H I₁ I₂ n → Bool)
    (n : Nat) (s : ClosingLayer H I₁ I₂ (n+1))
    (exit : closingFirstExit boundary (n+1) s = true)
    (r : I₁ × I₂ × Graph) : closingActive boundary (n+2) (s,r) = false := by
  simp only [closingFirstExit,Bool.and_eq_true] at exit
  have yes := exit.2
  simp only [closingActive,yes,Bool.not_true,Bool.and_false]

theorem closingLayerHistory_take_parent {H I₁ I₂ : Type}
    (past : H → EnvHistory I₁ I₂) (L : Nat) (depth : ∀ h, List.length (past h) = L)
    (n : Nat) (s : ClosingLayer H I₁ I₂ (n+1)) (m : Nat) (bound : m ≤ L+n) :
    (closingLayerHistory past (n+1) s).take m = (closingLayerHistory past n s.1).take m := by
  change (closingLayerHistory past n s.1 ++ [_]).take m = _
  exact List.take_append_of_le_length (by rw [closingLayerHistory_length past L depth]; exact bound)

/-- Exact meaning of the executable active mask: no boundary lies strictly
between the source depth and this output depth. -/
theorem closingActive_exact {H I₁ I₂ : Type}
    (P : List Graph → Prop) (d : Nat) (past : H → EnvHistory I₁ I₂)
    (L : Nat) (depth : ∀ h, List.length (past h) = L)
    (boundary : (n : Nat) → ClosingLayer H I₁ I₂ n → Bool)
    (D : Nat) (boundaryExact : ∀ n, n ≤ D → ∀ s,
      boundary n s = leaderBoundary P d (closingLayerHistory past n s))
    (n : Nat) (bound : n ≤ D) (s : ClosingLayer H I₁ I₂ n) :
    closingActive boundary n s = true ↔
      ∀ m, L < m → m < L+n →
        leaderBoundary P d ((closingLayerHistory past n s).take m) = false := by
  induction n using Nat.twoStepInduction with
  | zero =>
    constructor
    · intro _ m lo hi; omega
    · intro _; rfl
  | one =>
    constructor
    · intro _ m lo hi; omega
    · intro _; rfl
  | more n _ ih =>
    simp only [closingActive,Bool.and_eq_true,Bool.not_eq_true']
    rw [ih (by omega),boundaryExact (n+1) (by omega)]
    constructor
    · rintro ⟨before,last⟩ m lower upper
      by_cases early : m < L+(n+1)
      · rw [closingLayerHistory_take_parent past L depth (n+1) s m (by omega)]
        exact before m lower early
      · have eq : m = L+(n+1) := by omega
        subst m
        rw [closingLayerHistory_take_parent past L depth (n+1) s _ (by omega),
          ← closingLayerHistory_length past L depth (n+1) s.1,List.take_length]
        exact last
    · intro all
      constructor
      · intro m lower upper
        have no := all m lower (by omega)
        rwa [closingLayerHistory_take_parent past L depth (n+1) s m (by omega)] at no
      · have no := all (L+(n+1)) (by omega) (by omega)
        rwa [closingLayerHistory_take_parent past L depth (n+1) s _ (by omega),
          ← closingLayerHistory_length past L depth (n+1) s.1,List.take_length] at no

/-- No process learns an extra stopping signal: the active status is
constant throughout an actual live component at a fixed closing depth. -/
theorem closingActive_component {H I₁ I₂ : Type}
    (P : List Graph → Prop) (closed : PrefixClosed P) (d : Nat)
    (recent : ∀ g, P g → ∃ p, RecentOther P d g p)
    (past : H → EnvHistory I₁ I₂) (L : Nat) (depth : ∀ h, List.length (past h) = L)
    (boundary : (n : Nat) → ClosingLayer H I₁ I₂ n → Bool)
    (D : Nat) (boundaryExact : ∀ n, n ≤ D → ∀ s,
      boundary n s = leaderBoundary P d (closingLayerHistory past n s))
    (n : Nat) (bound : n ≤ D) (s t : ClosingLayer H I₁ I₂ n)
    (live : P (History.graphSequence (closingLayerHistory past n s)))
    (conn : InputConnected P (closingLayerHistory past n s) (closingLayerHistory past n t)) :
    closingActive boundary n s = closingActive boundary n t := by
  apply Bool.eq_iff_iff.mpr
  rw [closingActive_exact P d past L depth boundary D boundaryExact n bound,
    closingActive_exact P d past L depth boundary D boundaryExact n bound]
  have flags := leaderBoundary_history_component P closed d recent live conn
  simp only [flags]

/-- Exact first-exit semantics, including the current boundary output. -/
theorem closingFirstExit_exact {H I₁ I₂ : Type}
    (P : List Graph → Prop) (d : Nat) (past : H → EnvHistory I₁ I₂)
    (L : Nat) (depth : ∀ h, List.length (past h) = L)
    (boundary : (n : Nat) → ClosingLayer H I₁ I₂ n → Bool)
    (D : Nat) (boundaryExact : ∀ n, n ≤ D → ∀ s,
      boundary n s = leaderBoundary P d (closingLayerHistory past n s))
    (n : Nat) (bound : n+1 ≤ D) (s : ClosingLayer H I₁ I₂ (n+1)) :
    closingFirstExit boundary (n+1) s = true ↔
      (∀ m, L < m → m < L+(n+1) →
        leaderBoundary P d ((closingLayerHistory past (n+1) s).take m) = false) ∧
      leaderBoundary P d (closingLayerHistory past (n+1) s) = true := by
  simp only [closingFirstExit,Bool.and_eq_true,
    closingActive_exact P d past L depth boundary D boundaryExact (n+1) bound,
    boundaryExact (n+1) bound]

/-- Component invariance includes the current boundary flag, so a first-exit
component cannot mix histories that have already handed over with active ones. -/
theorem closingFirstExit_component {H I₁ I₂ : Type}
    (P : List Graph → Prop) (closed : PrefixClosed P) (d : Nat)
    (recent : ∀ g, P g → ∃ p, RecentOther P d g p)
    (past : H → EnvHistory I₁ I₂) (L : Nat) (depth : ∀ h, List.length (past h) = L)
    (boundary : (n : Nat) → ClosingLayer H I₁ I₂ n → Bool)
    (D : Nat) (boundaryExact : ∀ n, n ≤ D → ∀ s,
      boundary n s = leaderBoundary P d (closingLayerHistory past n s))
    (n : Nat) (bound : n ≤ D) (s t : ClosingLayer H I₁ I₂ n)
    (live : P (History.graphSequence (closingLayerHistory past n s)))
    (conn : InputConnected P (closingLayerHistory past n s) (closingLayerHistory past n t)) :
    closingFirstExit boundary n s = closingFirstExit boundary n t := by
  cases n with
  | zero => rfl
  | succ n =>
    simp only [closingFirstExit,
      closingActive_component P closed d recent past L depth boundary D boundaryExact (n+1) bound s t live conn,
      boundaryExact (n+1) bound]
    rw [leaderBoundary_component P closed d _ _
      (componentLeader_correct P d _ (recent _ live)) conn]

/-- A truthful finite flag table supplies exactly the bounded flags needed
by the scan. Truthfulness is a hypothesis, not inferred from the table type. -/
theorem closingFlagAt_exact {H I₁ I₂ : Type} {D : Nat}
    (table : ClosingFlagTable H I₁ I₂ D)
    (meaning : (n : Nat) → ClosingLayer H I₁ I₂ n → Bool)
    (correct : ∀ n s, table n s = meaning n.val s)
    (n : Nat) (bound : n ≤ D) (s : ClosingLayer H I₁ I₂ n) :
    closingFlagAt table n s = meaning n s := by
  simp only [closingFlagAt,dif_pos (show n < D+1 by omega)]
  exact correct ⟨n,by omega⟩ s

end Characterisation
