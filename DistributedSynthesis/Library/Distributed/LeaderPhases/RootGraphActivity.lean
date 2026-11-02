/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.GraphRootTransport

/-! Per-root graph states supply activity updates. Dead continuations stop
that root; boundary truth is needed only along live physical histories. -/
namespace Characterisation
open DistributedSynthesis

def graphRootStop {Q : Type} {d K : Nat} (M : Recognizer Graph Q) [DecidablePred (· ∈ M.accept)]
    (state : GraphRootState Q d K) (g : Graph) : Bool :=
  !graphRootLive M state g || graphRootBoundary M state g

theorem graphRootStop_exact_on_live {Q I₁ I₂ : Type} {d K : Nat}
    (M : Recognizer Graph Q) [DecidablePred (· ∈ M.accept)]
    (P : List Graph → Prop) (closed : PrefixClosed P) (recognizes : ∀ g, P g ↔ M.eval g ∈ M.accept)
    (h : EnvHistory I₁ I₂) (state : GraphRootState Q d K)
    (rep : GraphRootRep P M (History.graphSequence h) state)
    (r : RoundRecord I₁ I₂ Graph Unit Unit) (live : P (History.graphSequence (h++[r]))) :
    graphRootStop M state r.graph = leaderBoundary P d (h++[r]) := by
  have yes := (graphRootLive_exact M P closed recognizes _ state rep r.graph).mpr
    (by simpa only [History.graphSequence,List.map_append,List.map_cons,List.map_nil] using live)
  simp only [graphRootStop,yes,Bool.not_true,Bool.false_or]
  exact graphRootBoundary_exact M P closed recognizes h state rep r live

/-- This weaker truth invariant is sufficient at actual live source cuts.
Flags at forbidden histories can be assigned without a semantic boundary oracle. -/
def SourceActivityOnLive {H I₁ I₂ : Type} (P : List Graph → Prop) (d a L : Nat)
    (past : H → EnvHistory I₁ I₂) (active : H → Bool) : Prop :=
  ∀ h, P (History.graphSequence (past h)) →
    (active h = true ↔ ∀ m, a < m → m ≤ L → leaderBoundary P d ((past h).take m) = false)

/-- Prefix closure allows the earlier persistent-bit proof to be reused
when flags agree with boundaries only on live histories. -/
theorem rootActivityRun_history_on_live {H I₁ I₂ : Type}
    (P : List Graph → Prop) (closed : PrefixClosed P) (d a : Nat)
    (history : Nat → H → EnvHistory I₁ I₂)
    (prefixes : ∀ i j, i ≤ j → ∀ h, (history j h).take (a+i) = history i h)
    (boundary : Nat → H → Bool)
    (exactFlags : ∀ i h, P (History.graphSequence (history (i+1) h)) →
      boundary i h = leaderBoundary P d (history (i+1) h)) (n : Nat) :
    SourceActivityOnLive P d a (a+n) (history n) (rootActivityRun boundary n) := by
  intro h live
  let actual : Nat → H → Bool := fun i h => leaderBoundary P d (history (i+1) h)
  have same : ∀ i, i < n → boundary i h = actual i h := by
    intro i hi
    apply exactFlags
    rw [← prefixes (i+1) n (by omega) h]
    exact live_history_take P closed _ live _
  have bits : rootActivityRun boundary n h = rootActivityRun actual n h := by
    apply Bool.eq_iff_iff.mpr
    simp only [rootActivityRun_exact]
    constructor
    · intro all i hi
      rw [← same i hi]
      exact all i hi
    · intro all i hi
      rw [same i hi]
      exact all i hi
  rw [bits]
  exact rootActivityRun_history P d a history prefixes actual (fun _ _ => rfl) n h

/-- A checked graph bank supplies the live source-activity invariant at all
later cuts, independently for every original private-input root. -/
theorem graphRootBank_activity_exact {H Q I₁ I₂ : Type} [Fintype Q] [DecidableEq Q] {d K : Nat}
    (M : Recognizer Graph Q) [DecidablePred (· ∈ M.accept)]
    (P : List Graph → Prop) (closed : PrefixClosed P) (recognizes : ∀ g, P g ↔ M.eval g ∈ M.accept)
    (a : Nat) (history : Nat → H → EnvHistory I₁ I₂)
    (prefixes : ∀ i j, i ≤ j → ∀ h, (history j h).take (a+i) = history i h)
    (round : Nat → H → RoundRecord I₁ I₂ Graph Unit Unit)
    (extension : ∀ n h, history (n+1) h = history n h ++ [round n h])
    (bank : Nat → H → GraphRootState Q d K)
    (start : ∀ h, GraphRootRep P M (History.graphSequence (history 0 h)) (bank 0 h))
    (checked : ∀ n h, checkGraphRootStep M (bank n h) (round n h).graph (bank (n+1) h) = true)
    (n : Nat) :
    SourceActivityOnLive P d a (a+n) (history n)
      (rootActivityRun (fun i h => graphRootStop M (bank i h) (round i h).graph) n) := by
  have graphs := graphRootBank_run_exact M P closed recognizes history round extension bank start checked
  apply rootActivityRun_history_on_live P closed d a history prefixes
  intro i h live
  have exactFlag := graphRootStop_exact_on_live M P closed recognizes (history i h) (bank i h) (graphs i h)
    (round i h) (by rwa [← extension])
  simpa only [← extension] using exactFlag


/-- Starting from live boundary roots, every surviving root is still live.
This lets the existing objective-label theorem apply to every root retained
by a new closing scan, not only to an unspecified live subset. -/
theorem graphRootBank_active_live {H Q I₁ I₂ : Type} [Fintype Q] [DecidableEq Q] {d K : Nat}
    (M : Recognizer Graph Q) [DecidablePred (· ∈ M.accept)]
    (P : List Graph → Prop) (closed : PrefixClosed P) (recognizes : ∀ g, P g ↔ M.eval g ∈ M.accept)
    (history : Nat → H → EnvHistory I₁ I₂)
    (round : Nat → H → RoundRecord I₁ I₂ Graph Unit Unit)
    (extension : ∀ n h, history (n+1) h = history n h ++ [round n h])
    (bank : Nat → H → GraphRootState Q d K)
    (start : ∀ h, GraphRootRep P M (History.graphSequence (history 0 h)) (bank 0 h))
    (startLive : ∀ h, P (History.graphSequence (history 0 h)))
    (checked : ∀ n h, checkGraphRootStep M (bank n h) (round n h).graph (bank (n+1) h) = true)
    (n : Nat) (h : H)
    (active : rootActivityRun (fun i h => graphRootStop M (bank i h) (round i h).graph) n h = true) :
    P (History.graphSequence (history n h)) := by
  cases n with
  | zero => exact startLive h
  | succ n =>
    have no := (rootActivityRun_exact _ (n+1) h).mp active n (by omega)
    have yes : graphRootLive M (bank n h) (round n h).graph = true := by
      cases eq : graphRootLive M (bank n h) (round n h).graph
      · simp only [graphRootStop,eq,Bool.not_false,Bool.true_or] at no
        contradiction
      · rfl
    have rep := graphRootBank_run_exact M P closed recognizes history round extension bank start checked n h
    have live := (graphRootLive_exact M P closed recognizes _ _ rep (round n h).graph).mp yes
    simpa only [extension,History.graphSequence,List.map_append,List.map_cons,List.map_nil] using live

end Characterisation
