/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.FirstExitGuard

/-! Soundness of the finite first-exit bundle checker. Boundary/live flags
are interpreted explicitly, and certificate outputs are tied to the shared
phase policy. No winning-successor existence is assumed by the checker. -/
namespace Characterisation
open DistributedSynthesis

theorem closingLiveTable_exact {H I₁ I₂ : Type} {D : Nat}
    (P : List Graph → Prop) (past : H → EnvHistory I₁ I₂)
    (live : ClosingFlagTable H I₁ I₂ D)
    (liveExact : ∀ m s, live m s = true ↔ P (History.graphSequence (closingLayerHistory past m.val s)))
    (n : Nat) (bound : n ≤ D) (s : ClosingLayer H I₁ I₂ n) :
    closingFlagAt live n s = true ↔ P (History.graphSequence (closingLayerHistory past n s)) := by
  simp only [closingFlagAt,dif_pos (show n < D+1 by omega)]
  exact liveExact ⟨n,by omega⟩ s

section Bundle
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
theorem first_exit_bundle_sound
    (closed : PrefixClosed P) (d : Nat) (recent : ∀ g, P g → ∃ p, RecentOther P d g p)
    (boundaryExact : ∀ m s, boundary m s = leaderBoundary P d (closingLayerHistory past m.val s))
    (σ : StrategyPair I₁ I₂ O₁ O₂) (q₀ : Q)
    (source : ∀ h, initial h = strategyHistoryLabel σ step q₀ (past h))
    (Allowed : SwitchInterface Q B → Prop) [DecidablePred Allowed]
    (expected : ClosingPolicy H I₁ I₂ O₁ O₂ D)
    (bundle : FirstExitBundle H I₁ I₂ O₁ O₂ Q B D)
    (valid : checkFirstExitBundleFor shape boundary live step initial Allowed expected bundle = true)
    (implements : ∀ t s, LiveClosingActive P past (closingFlagAt boundary) (t.val+1) s → expected t s =
      (σ.one (currentView .one (closingLayerHistory past (t.val+1) s)),
       σ.two (currentView .two (closingLayerHistory past (t.val+1) s))))
    (n : Fin D) (root : ClosingLayer H I₁ I₂ (n.val+1))
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
  have tied := (checkFirstExitBundleFor_correct shape boundary live step initial Allowed expected bundle).mp valid
  have checked := ((checkFirstExitBundle_correct shape boundary live step initial Allowed bundle).mp tied.2).2 n root alive exit
  have exactLive := closingLiveTable_exact P past live liveExact (n.val+1) (by omega)
  apply first_exit_certificate_correct P closed d recent past injective shape rep L depth
    (closingFlagAt boundary) σ step q₀ initial source (show n.val+1 ≤ D by omega)
    (closingFlagAt_exact boundary (fun m s => leaderBoundary P d (closingLayerHistory past m s)) boundaryExact)
    (closingFlagAt live (n.val+1)) exactLive root ((exactLive root).mp alive) exit covers Allowed
    (bundle.2 n root) checked.2
  intro t s active
  rw [checked.1,tied.1]
  exact implements t s active

include injective rep depth liveExact in
/-- With unrestricted allowed targets, coherent policies and complete
bounded target coverage suffice to populate every demanded certificate.
Non-exit slots use arbitrary empty targets and are never checked. -/
theorem first_exit_bundle_exists
    (out : ClosingPolicy H I₁ I₂ O₁ O₂ D) (coherent : ClosingPolicyCoherent shape out)
    (covers : ∀ (n : Fin D) root, closingFlagAt live (n.val+1) root = true →
      closingFirstExit (closingFlagAt boundary) (n.val+1) root = true →
      ∀ k, InputConnected P (closingLayerHistory past (n.val+1) root) k →
        ∃ s, closingLayerHistory past (n.val+1) s = k)
    (small : ∀ (n : Fin D) root, closingFlagAt live (n.val+1) root = true →
      closingFirstExit (closingFlagAt boundary) (n.val+1) root = true →
        Nat.card (InputHistoryComponent P (closingLayerHistory past (n.val+1) root)) ≤ B) :
    ∃ bundle : FirstExitBundle H I₁ I₂ O₁ O₂ Q B D, bundle.1 = out ∧
      checkFirstExitBundleFor shape boundary live step initial (fun _ => True) out bundle = true := by
  classical
  have each : ∀ (n : Fin D) root, ∃ move : ClosingBoundaryCertificate H I₁ I₂ O₁ O₂ Q B D (n.val+1),
      closingFlagAt live (n.val+1) root = true →
      closingFirstExit (closingFlagAt boundary) (n.val+1) root = true →
        move.2.1 = out ∧ checkClosingBoundaryCertificate shape step initial (show n.val+1 ≤ D by omega)
          (closingFlagAt live (n.val+1)) root (fun _ => True) move = true := by
    intro n root
    by_cases demanded : closingFlagAt live (n.val+1) root = true ∧
        closingFirstExit (closingFlagAt boundary) (n.val+1) root = true
    · have exactLive := closingLiveTable_exact P past live liveExact (n.val+1) (by omega)
      obtain ⟨move,policy,checked⟩ := exists_checked_closing_boundary_of_target_coverage P past injective
        shape rep L depth step initial out coherent (show n.val+1 ≤ D by omega)
        (closingFlagAt live (n.val+1)) exactLive root ((exactLive root).mp demanded.1)
        (covers n root demanded.1 demanded.2) (small n root demanded.1 demanded.2)
      exact ⟨move,fun _ _ => ⟨policy,checked⟩⟩
    · let empty : ClosingBoundaryCertificate H I₁ I₂ O₁ O₂ Q B D (n.val+1) :=
        ⟨⟨0,by omega⟩,out,(fun i => Fin.elim0 i),(fun _ i => Fin.elim0 i),(fun i => Fin.elim0 i)⟩
      exact ⟨empty,fun alive exit => False.elim (demanded ⟨alive,exit⟩)⟩
  choose moves correct using each
  refine ⟨(out,moves),rfl,?_⟩
  apply (checkFirstExitBundleFor_correct shape boundary live step initial (fun _ => True) out _).mpr
  exact ⟨rfl,(checkFirstExitBundle_correct shape boundary live step initial (fun _ => True) _).mpr
    ⟨coherent,correct⟩⟩

end Bundle
end Characterisation
