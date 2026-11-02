/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.ActivePhaseImplementation

/-! The existing finite first-exit checker can be invoked on exactly the
carried active roots. Restriction preserves target coverage, observations,
flags and replay; no new certificate format or coherence test is needed. -/
namespace Characterisation
open DistributedSynthesis

/-- Complete bounded target coverage for the original family suffices to
build an accepted bundle over its surviving roots. The carried activity
invariant proves that no demanded target history was removed. -/
theorem active_root_first_exit_bundle_exists {H I₁ I₂ O₁ O₂ Q : Type} {B D : Nat}
    [Fintype H] [Fintype I₁] [Fintype I₂]
    [DecidableEq H] [DecidableEq I₁] [DecidableEq I₂]
    [DecidableEq O₁] [DecidableEq O₂] [DecidableEq Q] [Nonempty O₁] [Nonempty O₂]
    (P : List Graph → Prop) (closed : PrefixClosed P) (d : Nat)
    (recent : ∀ g, P g → ∃ p, RecentOther P d g p)
    (past : H → EnvHistory I₁ I₂) (injective : Function.Injective past)
    (shape : InputShape H) (rep : RepresentsInputShape past shape)
    (a L : Nat) (depth : ∀ h, List.length (past h) = L)
    (active : H → Bool) (exactActivity : SourceActivityExact P d a L past active)
    (boundary live : ClosingFlagTable H I₁ I₂ D)
    (liveExact : ∀ m s, live m s = true ↔ P (History.graphSequence (closingLayerHistory past m.val s)))
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (initial : H → Q)
    (out : ClosingPolicy H I₁ I₂ O₁ O₂ D) (coherent : ClosingPolicyCoherent shape out)
    (covers : ∀ (n : Fin D) root, closingFlagAt live (n.val+1) root = true →
      active (closingLayerRoot (n.val+1) root) = true →
      closingFirstExit (closingFlagAt boundary) (n.val+1) root = true →
      ∀ k, InputConnected P (closingLayerHistory past (n.val+1) root) k →
        ∃ s, closingLayerHistory past (n.val+1) s = k)
    (small : ∀ (n : Fin D) root, closingFlagAt live (n.val+1) root = true →
      active (closingLayerRoot (n.val+1) root) = true →
      closingFirstExit (closingFlagAt boundary) (n.val+1) root = true →
        Nat.card (InputHistoryComponent P (closingLayerHistory past (n.val+1) root)) ≤ B) :
    ∃ bundle : FirstExitBundle (ActiveClosingRoots active) I₁ I₂ O₁ O₂ Q B D,
      bundle.1 = restrictClosingPolicy Subtype.val out ∧
      checkFirstExitBundleFor (restrictInputShape shape Subtype.val)
        (restrictClosingFlags Subtype.val boundary) (restrictClosingFlags Subtype.val live)
        step (initial ∘ Subtype.val) (fun _ => True) (restrictClosingPolicy Subtype.val out) bundle = true := by
  let f : ActiveClosingRoots active → H := Subtype.val
  have restrictedLive : ∀ m s, restrictClosingFlags f live m s = true ↔
      P (History.graphSequence (closingLayerHistory (past ∘ f) m.val s)) := by
    intro m s
    simpa only [restrictClosingFlags,closingLayerHistory_map] using liveExact m (mapClosingLayer f m.val s)
  apply first_exit_bundle_exists P (past ∘ f) (injective.comp Subtype.val_injective)
    (restrictInputShape shape f) (restrictInputShape_exact past shape rep f) L (fun h => depth (f h))
    (restrictClosingFlags f boundary) (restrictClosingFlags f live) restrictedLive step (initial ∘ f)
    (restrictClosingPolicy f out) (restrictClosingPolicy_coherent past shape rep L depth f out coherent)
  · intro n root alive exit
    have oldAlive : closingFlagAt live (n.val+1) (mapClosingLayer f (n.val+1) root) = true := by
      simpa only [closingFlagAt_restrict] using alive
    have oldExit : closingFirstExit (closingFlagAt boundary) (n.val+1) (mapClosingLayer f (n.val+1) root) = true := by
      simpa only [closingFirstExit_restrict] using exit
    have liveRoot := (closingLiveTable_exact P (past ∘ f) (restrictClosingFlags f live) restrictedLive
      (n.val+1) (by omega) root).mp alive
    apply activeClosingLayer_component_coverage P closed d recent past a L depth active exactActivity
      (n.val+1) root liveRoot
    intro k conn
    have oldConn : InputConnected P (closingLayerHistory past (n.val+1) (mapClosingLayer f (n.val+1) root)) k := by
      simpa only [closingLayerHistory_map] using conn
    exact covers n _ oldAlive (activeClosingLayer_root_alive active (n.val+1) root) oldExit k oldConn
  · intro n root alive exit
    have oldAlive : closingFlagAt live (n.val+1) (mapClosingLayer f (n.val+1) root) = true := by
      simpa only [closingFlagAt_restrict] using alive
    have oldExit : closingFirstExit (closingFlagAt boundary) (n.val+1) (mapClosingLayer f (n.val+1) root) = true := by
      simpa only [closingFirstExit_restrict] using exit
    simpa only [closingLayerHistory_map] using small n _ oldAlive
      (activeClosingLayer_root_alive active (n.val+1) root) oldExit

end Characterisation
