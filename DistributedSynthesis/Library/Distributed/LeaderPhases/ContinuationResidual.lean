/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.ContinuationWinning

/-! Restrict one winning continuation to every retained descendant at once.
Its residual labels are obtained by replay, and its future outputs remain
those of the same policy. -/
namespace Characterisation
open DistributedSynthesis

def graftClosingLayer {H S I₁ I₂ : Type} (n : Nat)
    (keep : S → ClosingLayer H I₁ I₂ n) :
    (k : Nat) → ClosingLayer S I₁ I₂ k → ClosingLayer H I₁ I₂ (n+k)
  | 0 => keep
  | k+1 => fun s => (graftClosingLayer n keep k s.1,s.2)

theorem graftClosingLayer_history {H S I₁ I₂ : Type}
    (past : H → EnvHistory I₁ I₂) (n : Nat)
    (keep : S → ClosingLayer H I₁ I₂ n) (k : Nat) (s : ClosingLayer S I₁ I₂ k) :
    closingLayerHistory past (n+k) (graftClosingLayer n keep k s) =
      closingLayerHistory (closingLayerHistory past n ∘ keep) k s := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change closingLayerHistory past (n+k) (graftClosingLayer n keep k s.1) ++ [_] = _
    rw [ih]
    rfl

def residualContinuationPolicy {H S I₁ I₂ O₁ O₂ : Type}
    (out : ContinuationPolicy H I₁ I₂ O₁ O₂) (n : Nat)
    (keep : S → ClosingLayer H I₁ I₂ n) : ContinuationPolicy S I₁ I₂ O₁ O₂ :=
  fun k s => out (n+k) (graftClosingLayer n keep (k+1) s)

/-- Exact local implementation survives simultaneous restriction to an
arbitrary family of descendants, including mutually indistinguishable ones. -/
theorem residualContinuationPolicy_coherent {H S I₁ I₂ O₁ O₂ : Type}
    [DecidableEq I₁] [DecidableEq I₂] [Nonempty O₁] [Nonempty O₂]
    (past : H → EnvHistory I₁ I₂) (shape : InputShape H)
    (rep : RepresentsInputShape past shape)
    (L : Nat) (depth : ∀ h, List.length (past h) = L)
    (out : ContinuationPolicy H I₁ I₂ O₁ O₂) (coherent : ContinuationCoherent shape out)
    (n : Nat) (keep : S → ClosingLayer H I₁ I₂ n) :
    ContinuationCoherent (restrictInputShape (closingLayerShape shape n) keep)
      (residualContinuationPolicy out n keep) := by
  obtain ⟨σ,correct⟩ := (continuation_coherent_iff_local past shape rep L depth out).mp coherent
  have eq : strategyContinuationPolicy σ (closingLayerHistory past n ∘ keep) =
      residualContinuationPolicy out n keep := by
    funext k s
    have result := correct (n+k) (graftClosingLayer n keep (k+1) s)
    erw [graftClosingLayer_history past n keep (k+1) s] at result
    exact Prod.ext result.1 result.2
  rw [← eq]
  exact strategyContinuationPolicy_coherent σ _ _
    (restrictInputShape_exact _ _ (closingLayerShape_exact past shape rep n) keep)

/-- Every finite scenario can be followed by any infinite input/graph word. -/
theorem exists_continuation_branch {H I₁ I₂ : Type}
    (n : Nat) (s : ClosingLayer H I₁ I₂ n) (env : Nat → I₁ × I₂ × Graph) :
    ∃ h full, continuationScenario h full n = s ∧ ∀ k, full (n+k) = env k := by
  induction n generalizing env with
  | zero => exact ⟨s,env,rfl,fun _ => by simp⟩
  | succ n ih =>
    let next : Nat → I₁ × I₂ × Graph := fun k => match k with
      | 0 => s.2
      | k+1 => env k
    obtain ⟨h,full,stem,tail⟩ := ih s.1 next
    refine ⟨h,full,?_,?_⟩
    · change (continuationScenario h full n,full n) = s
      rw [stem,show full n = s.2 from tail 0]
      rfl
    · intro k
      simpa only [Nat.succ_add,Nat.add_succ,next] using tail (k+1)

theorem continuationScenario_graft {H S I₁ I₂ : Type}
    (n : Nat) (keep : S → ClosingLayer H I₁ I₂ n)
    (h : H) (s : S) (full env : Nat → I₁ × I₂ × Graph)
    (stem : continuationScenario h full n = keep s)
    (tail : ∀ k, full (n+k) = env k) (k : Nat) :
    continuationScenario h full (n+k) =
      graftClosingLayer n keep k (continuationScenario s env k) := by
  induction k with
  | zero => exact stem
  | succ k ih =>
    exact Prod.ext ih (tail k)

def continuationLabels {H I₁ I₂ O₁ O₂ Q : Type}
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
    (label : H → Q) (out : ContinuationPolicy H I₁ I₂ O₁ O₂) :
    (n : Nat) → ClosingLayer H I₁ I₂ n → Q
  | 0 => label
  | n+1 => fun s => step (continuationLabels step label out n s.1) s.2 (out n s)

theorem continuationLabels_branch {H I₁ I₂ O₁ O₂ Q : Type}
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
    (label : H → Q) (out : ContinuationPolicy H I₁ I₂ O₁ O₂)
    (h : H) (env : Nat → I₁ × I₂ × Graph) (n : Nat) :
    continuationLabels step label out n (continuationScenario h env n) =
      (branchNode (continuationTrace out h env) n).foldl
        (fun q r => step q r.1 r.2) (label h) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [continuationLabels,continuationScenario,branchNode,List.foldl_append,
      List.foldl_cons,List.foldl_nil,← ih,continuationTrace]

/-- Removing a finite physical prefix updates the residual objective by
its exact state fold. Parity acceptance satisfies this property. -/
def ResidualAcceptance {I₁ I₂ O₁ O₂ Q : Type}
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
    (accept : Q → (Nat → ContinuationLetter I₁ I₂ O₁ O₂) → Prop) : Prop :=
  ∀ q trace n, accept q trace →
    accept ((branchNode trace n).foldl (fun q r => step q r.1 r.2) q)
      (fun k => trace (n+k))

/-- All retained successors inherit winning from the same infinite policy.
This uses actual replayed labels, not independently chosen successor states. -/
theorem residualContinuationPolicy_wins {H S I₁ I₂ O₁ O₂ Q : Type}
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
    (accept : Q → (Nat → ContinuationLetter I₁ I₂ O₁ O₂) → Prop)
    (residual : ResidualAcceptance step accept)
    (label : H → Q) (out : ContinuationPolicy H I₁ I₂ O₁ O₂)
    (wins : ContinuationWins accept label out)
    (n : Nat) (keep : S → ClosingLayer H I₁ I₂ n) :
    ContinuationWins accept (continuationLabels step label out n ∘ keep)
      (residualContinuationPolicy out n keep) := by
  intro s env
  obtain ⟨h,full,stem,tail⟩ := exists_continuation_branch n (keep s) env
  have winning := residual (label h) (continuationTrace out h full) n (wins h full)
  rw [← continuationLabels_branch, stem] at winning
  have traceEq : (fun k => continuationTrace out h full (n+k)) =
      continuationTrace (residualContinuationPolicy out n keep) s env := by
    funext k
    unfold continuationTrace residualContinuationPolicy
    exact Prod.ext (tail k) (congrArg (out (n+k))
      (continuationScenario_graft n keep h s full env stem tail (k+1)))
  rw [traceEq] at winning
  exact winning

end Characterisation
