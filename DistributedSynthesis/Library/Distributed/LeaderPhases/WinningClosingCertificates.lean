/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.ContinuationParity
import DistributedSynthesis.Library.Distributed.LeaderPhases.ScheduledExitBundles

/-! Upgrade truthful closing certificates to genuinely winning successors.
The witnesses are restrictions of one winning infinite policy; successor
winning is not an independent hypothesis for every certificate. -/
namespace Characterisation
open DistributedSynthesis

def continuationWindow {H I₁ I₂ O₁ O₂ : Type}
    (out : ContinuationPolicy H I₁ I₂ O₁ O₂) (D : Nat) :
    ClosingPolicy H I₁ I₂ O₁ O₂ D := fun n => out n.val

theorem continuationWindow_labels {H I₁ I₂ O₁ O₂ Q : Type}
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
    (label : H → Q) (out : ContinuationPolicy H I₁ I₂ O₁ O₂)
    {D n : Nat} (bound : n ≤ D) (s : ClosingLayer H I₁ I₂ n) :
    closingLayerLabels step label (continuationWindow out D) n bound s =
      continuationLabels step label out n s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [closingLayerLabels,continuationLabels,continuationWindow,ih]

/-- Every retained family, not only the actual root, has a jointly winning
continuation with the computed observation matrix and exact replayed labels. -/
theorem computedClosingTarget_winning {H S I₁ I₂ O₁ O₂ Q : Type}
    [DecidableEq I₁] [DecidableEq I₂] [Nonempty O₁] [Nonempty O₂]
    (past : H → EnvHistory I₁ I₂) (shape : InputShape H)
    (rep : RepresentsInputShape past shape)
    (L : Nat) (depth : ∀ h, List.length (past h) = L)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
    (accept : Q → (Nat → ContinuationLetter I₁ I₂ O₁ O₂) → Prop)
    (residual : ResidualAcceptance step accept)
    (label : H → Q) (out : ContinuationPolicy H I₁ I₂ O₁ O₂)
    (coherent : ContinuationCoherent shape out) (wins : ContinuationWins accept label out)
    {D n : Nat} (bound : n ≤ D) (keep : S → ClosingLayer H I₁ I₂ n) :
    let target := computedClosingTarget shape step label (continuationWindow out D) bound keep
    ContinuationWinning accept target.1 target.2 := by
  refine ⟨residualContinuationPolicy out n keep,
    residualContinuationPolicy_coherent past shape rep L depth out coherent n keep,?_⟩
  have labels : (computedClosingTarget shape step label (continuationWindow out D) bound keep).2 =
      continuationLabels step label out n ∘ keep := by
    funext s
    exact continuationWindow_labels step label out bound (keep s)
  rw [labels]
  exact residualContinuationPolicy_wins step accept residual label out wins n keep

section Certificates
variable {H I₁ I₂ O₁ O₂ Q : Type} {B D n : Nat}
variable [Fintype H] [Fintype I₁] [Fintype I₂]
variable [DecidableEq H] [DecidableEq I₁] [DecidableEq I₂]
variable [DecidableEq O₁] [DecidableEq O₂] [DecidableEq Q]
variable [Nonempty O₁] [Nonempty O₂]
variable (past : H → EnvHistory I₁ I₂) (shape : InputShape H)
variable (rep : RepresentsInputShape past shape)
variable (L : Nat) (depth : ∀ h, List.length (past h) = L)
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
variable (accept : Q → (Nat → ContinuationLetter I₁ I₂ O₁ O₂) → Prop)
variable (residual : ResidualAcceptance step accept)
variable (label : H → Q) (out : ContinuationPolicy H I₁ I₂ O₁ O₂)
variable (coherent : ContinuationCoherent shape out) (wins : ContinuationWins accept label out)
variable [DecidablePred (SwitchContinuationWinning (B:=B) accept)]

include rep depth in
/-- On an otherwise valid certificate, the stronger guard means exactly
that one local strategy wins simultaneously from all retained histories.
Thus the finite target predicate cannot be satisfied by incompatible
root-by-root witnesses. Labels here are the checker-verified target labels. -/
theorem closingCertificate_winning_iff_strategy (bound : n ≤ D)
    (live : ClosingLayer H I₁ I₂ n → Bool) (root : ClosingLayer H I₁ I₂ n)
    (move : ClosingBoundaryCertificate H I₁ I₂ O₁ O₂ Q B D n)
    (checked : checkClosingBoundaryCertificate shape step label bound live root (fun _ => True) move = true) :
    checkClosingBoundaryCertificate shape step label bound live root
        (SwitchContinuationWinning accept) move = true ↔
      ∃ σ : StrategyPair I₁ I₂ O₁ O₂,
        ContinuationWins accept move.2.2.2.2
          (strategyContinuationPolicy σ (closingLayerHistory past n ∘ move.2.2.1)) := by
  have checks := checked
  simp only [checkClosingBoundaryCertificate,Bool.and_eq_true,checkClosingMove,
    decide_eq_true_eq] at checks
  have targetRep : RepresentsInputShape (closingLayerHistory past n ∘ move.2.2.1)
      move.2.2.2.1 := by
    rw [checks.1.2.1]
    exact (computedClosingTarget_exact past shape rep step label move.2.1 bound move.2.2.1).1
  have semantic := switchContinuationWinning_iff_strategy accept
    (show SwitchInterface Q B from ⟨move.1,move.2.2.2⟩)
    (closingLayerHistory past n ∘ move.2.2.1) targetRep (L+n)
    (fun s => closingLayerHistory_length past L depth n (move.2.2.1 s))
  rw [← semantic]
  simp only [checkClosingBoundaryCertificate,Bool.and_eq_true,checkClosingMove,
    decide_eq_true_eq]
  constructor
  · intro result
    exact result.1.2.2
  · intro winning
    exact ⟨⟨checks.1.1,checks.1.2.1,winning⟩,checks.2⟩

include rep depth residual coherent wins in
/-- The very same finite certificate passes with winning successors in
place of True. Its policy, enumeration, and retained labels are unchanged. -/
theorem closingCertificate_upgrade_winning (bound : n ≤ D)
    (live : ClosingLayer H I₁ I₂ n → Bool) (root : ClosingLayer H I₁ I₂ n)
    (move : ClosingBoundaryCertificate H I₁ I₂ O₁ O₂ Q B D n)
    (policy : move.2.1 = continuationWindow out D)
    (checked : checkClosingBoundaryCertificate shape step label bound live root (fun _ => True) move = true) :
    checkClosingBoundaryCertificate shape step label bound live root
      (SwitchContinuationWinning accept) move = true := by
  simp only [checkClosingBoundaryCertificate,Bool.and_eq_true,checkClosingMove,
    decide_eq_true_eq] at checked ⊢
  refine ⟨⟨checked.1.1,checked.1.2.1,?_⟩,checked.2⟩
  change ContinuationWinning accept move.2.2.2.1 move.2.2.2.2
  have target := checked.1.2.1
  rw [policy] at target
  rw [target]
  exact computedClosingTarget_winning past shape rep L depth step accept residual label out
    coherent wins bound move.2.2.1

include rep depth residual coherent wins in
/-- A complete scheduled bundle inherits the stronger guard simultaneously
at every demanded exit. There is no separate winning-successor assumption. -/
theorem scheduledBundle_upgrade_winning (initialWindow : Bool)
    (boundary live : ClosingFlagTable H I₁ I₂ D)
    (bundle : FirstExitBundle H I₁ I₂ O₁ O₂ Q B D)
    (checked : checkScheduledExitBundle shape initialWindow boundary live step label (fun _ => True)
      (continuationWindow out D) bundle = true) :
    checkScheduledExitBundle shape initialWindow boundary live step label
      (SwitchContinuationWinning accept) (continuationWindow out D) bundle = true := by
  rw [checkScheduledExitBundle_correct] at checked ⊢
  refine ⟨checked.1,checked.2.1,?_⟩
  intro t root scheduled alive exit
  obtain ⟨policy,valid⟩ := checked.2.2 t root scheduled alive exit
  refine ⟨policy,?_⟩
  exact closingCertificate_upgrade_winning past shape rep L depth step accept residual label out
    coherent wins (show t.val+1 ≤ D by omega) _ root (bundle.2 t root)
      (policy.trans checked.1) valid

end Certificates
end Characterisation
