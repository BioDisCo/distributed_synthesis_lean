/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.ScheduledActiveCoverage

/-! Use the existing finite certificate format with the canonical demand
schedule. Unscheduled exits are handled by their earlier window, not checked
against an incomplete later source family. Policy coherence stays unchanged. -/
namespace Characterisation
open DistributedSynthesis

section Check
variable {H I₁ I₂ O₁ O₂ Q : Type} {B D : Nat}
variable [Fintype H] [Fintype I₁] [Fintype I₂]
variable [DecidableEq H] [DecidableEq I₁] [DecidableEq I₂]
variable [DecidableEq O₁] [DecidableEq O₂] [DecidableEq Q]
variable (shape : InputShape H) (initialWindow : Bool)
variable (boundary live : ClosingFlagTable H I₁ I₂ D)
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (initial : H → Q)
variable (Allowed : SwitchInterface Q B → Prop) [DecidablePred Allowed]

/-- The extra scheduling bit is source data. All certificates use the
expected carried policy; every scheduled live first exit is checked. -/
def checkScheduledExitBundle (expected : ClosingPolicy H I₁ I₂ O₁ O₂ D)
    (bundle : FirstExitBundle H I₁ I₂ O₁ O₂ Q B D) : Bool :=
  decide (bundle.1 = expected) && decide (ClosingPolicyCoherent shape bundle.1 ∧
    ∀ (n : Fin D) s, closingWindowScheduled initialWindow D (n.val+1) = true →
      closingFlagAt live (n.val+1) s = true →
      closingFirstExit (closingFlagAt boundary) (n.val+1) s = true →
        (bundle.2 n s).2.1 = bundle.1 ∧
        checkClosingBoundaryCertificate shape step initial (show n.val+1 ≤ D by omega)
          (closingFlagAt live (n.val+1)) s Allowed (bundle.2 n s) = true)

theorem checkScheduledExitBundle_correct (expected : ClosingPolicy H I₁ I₂ O₁ O₂ D)
    (bundle : FirstExitBundle H I₁ I₂ O₁ O₂ Q B D) :
    checkScheduledExitBundle shape initialWindow boundary live step initial Allowed expected bundle = true ↔
      bundle.1 = expected ∧ ClosingPolicyCoherent shape bundle.1 ∧
        ∀ (n : Fin D) s, closingWindowScheduled initialWindow D (n.val+1) = true →
          closingFlagAt live (n.val+1) s = true →
          closingFirstExit (closingFlagAt boundary) (n.val+1) s = true →
            (bundle.2 n s).2.1 = bundle.1 ∧
            checkClosingBoundaryCertificate shape step initial (show n.val+1 ≤ D by omega)
              (closingFlagAt live (n.val+1)) s Allowed (bundle.2 n s) = true := by
  simp only [checkScheduledExitBundle,Bool.and_eq_true,decide_eq_true_eq]

/-- Initial windows retain exactly the previous all-first-exit checker. -/
theorem checkScheduledExitBundle_initial (expected : ClosingPolicy H I₁ I₂ O₁ O₂ D)
    (bundle : FirstExitBundle H I₁ I₂ O₁ O₂ Q B D) :
    checkScheduledExitBundle shape true boundary live step initial Allowed expected bundle =
      checkFirstExitBundleFor shape boundary live step initial Allowed expected bundle := by
  apply Bool.eq_iff_iff.mpr
  simp only [checkScheduledExitBundle_correct,checkFirstExitBundleFor_correct,
    checkFirstExitBundle_correct,closingWindowScheduled,Bool.true_or,true_implies]

end Check

section Existence
variable {H I₁ I₂ O₁ O₂ Q : Type} {B D : Nat}
variable [Fintype H] [Fintype I₁] [Fintype I₂]
variable [DecidableEq H] [DecidableEq I₁] [DecidableEq I₂]
variable [DecidableEq O₁] [DecidableEq O₂] [DecidableEq Q] [Nonempty O₁] [Nonempty O₂]

/-- The old target-certificate construction is applied only at scheduled
exits. No coverage is required for the ignored shorter noninitial scans. -/
theorem scheduled_first_exit_bundle_exists
    (P : List Graph → Prop) (past : H → EnvHistory I₁ I₂) (injective : Function.Injective past)
    (shape : InputShape H) (rep : RepresentsInputShape past shape)
    (L : Nat) (depth : ∀ h, List.length (past h) = L) (initialWindow : Bool)
    (boundary live : ClosingFlagTable H I₁ I₂ D)
    (liveExact : ∀ m s, live m s = true ↔ P (History.graphSequence (closingLayerHistory past m.val s)))
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (initial : H → Q)
    (out : ClosingPolicy H I₁ I₂ O₁ O₂ D) (coherent : ClosingPolicyCoherent shape out)
    (covers : ∀ (n : Fin D) root, closingWindowScheduled initialWindow D (n.val+1) = true →
      closingFlagAt live (n.val+1) root = true →
      closingFirstExit (closingFlagAt boundary) (n.val+1) root = true →
      ∀ k, InputConnected P (closingLayerHistory past (n.val+1) root) k →
        ∃ s, closingLayerHistory past (n.val+1) s = k)
    (small : ∀ (n : Fin D) root, closingWindowScheduled initialWindow D (n.val+1) = true →
      closingFlagAt live (n.val+1) root = true →
      closingFirstExit (closingFlagAt boundary) (n.val+1) root = true →
        Nat.card (InputHistoryComponent P (closingLayerHistory past (n.val+1) root)) ≤ B) :
    ∃ bundle : FirstExitBundle H I₁ I₂ O₁ O₂ Q B D, bundle.1 = out ∧
      checkScheduledExitBundle shape initialWindow boundary live step initial (fun _ => True) out bundle = true := by
  classical
  have each : ∀ (n : Fin D) root, ∃ move : ClosingBoundaryCertificate H I₁ I₂ O₁ O₂ Q B D (n.val+1),
      closingWindowScheduled initialWindow D (n.val+1) = true →
      closingFlagAt live (n.val+1) root = true →
      closingFirstExit (closingFlagAt boundary) (n.val+1) root = true →
        move.2.1 = out ∧ checkClosingBoundaryCertificate shape step initial (show n.val+1 ≤ D by omega)
          (closingFlagAt live (n.val+1)) root (fun _ => True) move = true := by
    intro n root
    by_cases demanded : closingWindowScheduled initialWindow D (n.val+1) = true ∧
        closingFlagAt live (n.val+1) root = true ∧
        closingFirstExit (closingFlagAt boundary) (n.val+1) root = true
    · have exactLive := closingLiveTable_exact P past live liveExact (n.val+1) (by omega)
      obtain ⟨move,policy,checked⟩ := exists_checked_closing_boundary_of_target_coverage P past injective
        shape rep L depth step initial out coherent (show n.val+1 ≤ D by omega)
        (closingFlagAt live (n.val+1)) exactLive root ((exactLive root).mp demanded.2.1)
        (covers n root demanded.1 demanded.2.1 demanded.2.2) (small n root demanded.1 demanded.2.1 demanded.2.2)
      exact ⟨move,fun _ _ _ => ⟨policy,checked⟩⟩
    · let empty : ClosingBoundaryCertificate H I₁ I₂ O₁ O₂ Q B D (n.val+1) :=
        ⟨⟨0,by omega⟩,out,(fun i => Fin.elim0 i),(fun _ i => Fin.elim0 i),(fun i => Fin.elim0 i)⟩
      exact ⟨empty,fun scheduled alive exit => False.elim (demanded ⟨scheduled,alive,exit⟩)⟩
  choose moves correct using each
  exact ⟨(out,moves),rfl,
    (checkScheduledExitBundle_correct shape initialWindow boundary live step initial (fun _ => True) out _).mpr
      ⟨rfl,coherent,correct⟩⟩

end Existence
section Soundness
variable {H I₁ I₂ O₁ O₂ Q : Type} {B D : Nat}
variable [Fintype H] [Fintype I₁] [Fintype I₂]
variable [DecidableEq H] [DecidableEq I₁] [DecidableEq I₂]
variable [DecidableEq O₁] [DecidableEq O₂] [DecidableEq Q]
variable [Nonempty O₁] [Nonempty O₂]
variable (P : List Graph → Prop)
variable (past : H → EnvHistory I₁ I₂) (injective : Function.Injective past)
variable (shape : InputShape H) (rep : RepresentsInputShape past shape)
variable (L : Nat) (depth : ∀ h, List.length (past h) = L)
variable (boundary live : ClosingFlagTable H I₁ I₂ D)
variable (liveExact : ∀ m s, live m s = true ↔ P (History.graphSequence (closingLayerHistory past m.val s)))
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (initial : H → Q)


include injective rep depth liveExact in
/-- Every demanded certificate in an accepted finite bundle represents the
actual next component and actual monitor labels, assuming truthful incoming
source data and implementation only during the live active part of the scan. -/
theorem scheduled_first_exit_bundle_sound
    (closed : PrefixClosed P) (d : Nat) (recent : ∀ g, P g → ∃ p, RecentOther P d g p)
    (boundaryExact : ∀ m s, boundary m s = leaderBoundary P d (closingLayerHistory past m.val s))
    (σ : StrategyPair I₁ I₂ O₁ O₂) (q₀ : Q)
    (source : ∀ h, initial h = strategyHistoryLabel σ step q₀ (past h))
    (Allowed : SwitchInterface Q B → Prop) [DecidablePred Allowed]
    (initialWindow : Bool)
    (expected : ClosingPolicy H I₁ I₂ O₁ O₂ D)
    (bundle : FirstExitBundle H I₁ I₂ O₁ O₂ Q B D)
    (valid : checkScheduledExitBundle shape initialWindow boundary live step initial Allowed expected bundle = true)
    (implements : ∀ t s, LiveClosingActive P past (closingFlagAt boundary) (t.val+1) s → expected t s =
      (σ.one (currentView .one (closingLayerHistory past (t.val+1) s)),
       σ.two (currentView .two (closingLayerHistory past (t.val+1) s))))
    (n : Fin D)
    (scheduled : closingWindowScheduled initialWindow D (n.val+1) = true)
    (root : ClosingLayer H I₁ I₂ (n.val+1))
    (alive : closingFlagAt live (n.val+1) root = true)
    (exit : closingFirstExit (closingFlagAt boundary) (n.val+1) root = true)
    (covers : ∀ k, InputConnected P (closingLayerHistory past (n.val+1) root) k →
      ∃ s, closingLayerHistory past (n.val+1) s = k) :
    let move := bundle.2 n root
    Function.Injective (closingLayerHistory past (n.val+1) ∘ move.2.2.1) ∧
    (∀ k, InputConnected P (closingLayerHistory past (n.val+1) root) k ↔
      ∃ s, closingLayerHistory past (n.val+1) (move.2.2.1 s) = k) ∧
    (∀ s, closingFirstExit (closingFlagAt boundary) (n.val+1) (move.2.2.1 s) = true ∧
      move.2.2.2.2 s = strategyHistoryLabel σ step q₀ (closingLayerHistory past (n.val+1) (move.2.2.1 s))) ∧
    Allowed ⟨move.1,move.2.2.2⟩ := by
  have tied := (checkScheduledExitBundle_correct shape initialWindow boundary live step initial Allowed expected bundle).mp valid
  have checked := tied.2.2 n root scheduled alive exit
  have exactLive := closingLiveTable_exact P past live liveExact (n.val+1) (by omega)
  apply first_exit_certificate_correct P closed d recent past injective shape rep L depth
    (closingFlagAt boundary) σ step q₀ initial source (show n.val+1 ≤ D by omega)
    (closingFlagAt_exact boundary (fun m s => leaderBoundary P d (closingLayerHistory past m s)) boundaryExact)
    (closingFlagAt live (n.val+1)) exactLive root ((exactLive root).mp alive) exit covers Allowed
    (bundle.2 n root) checked.2
  intro t s active
  rw [checked.1,tied.1]
  exact implements t s active

end Soundness

end Characterisation
