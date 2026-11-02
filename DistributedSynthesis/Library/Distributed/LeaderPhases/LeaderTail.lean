/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.LeaderCheckpoints

/-! A final phase with a fixed leader and no more delayed checkpoints is
eventually one-way from that leader. This identifies the communication form
of the final infinite phase, but does not prove its parity acceptance. -/
namespace Characterisation
open DistributedSynthesis

def leaderOutgoingGraph : Proc → Graph
  | .one => .right
  | .two => .left

theorem lagView_history_sequence {I₁ I₂ : Type*}
    (history : Nat → EnvHistory I₁ I₂)
    (round : Nat → RoundRecord I₁ I₂ Graph Unit Unit)
    (step : ∀ n, history (n+1) = history n ++ [round n])
    (p : Proc) (n d : Nat) :
    lagView d (currentView p (history (n+d))) = currentView p (history n) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [show n+(d+1) = (n+d)+1 by omega,step,lagView_append,ih]

theorem nonzero_age_outgoing {I₁ I₂ : Type*} (p : Proc)
    (h : EnvHistory I₁ I₂) (r : RoundRecord I₁ I₂ Graph Unit Unit)
    (nonzero : silentAge (currentView p (h++[r])) ≠ 0) : r.graph = leaderOutgoingGraph p := by
  change silentAge (currentView p (History.append h r)) ≠ 0 at nonzero
  cases p
  · rw [currentView_one_append] at nonzero
    cases rg : r.graph <;> simp_all [silentAge,leaderOutgoingGraph]
  · rw [currentView_two_append] at nonzero
    cases rg : r.graph <;> simp_all [silentAge,leaderOutgoingGraph]

/-- Absence of the delayed checkpoint rules out a leader reception d
rounds earlier. This also applies inside a finite interval between agreed
checkpoints; the closing d+1 rounds require separate bounded-window tables. -/
theorem no_delayed_checkpoint_outgoing {I₁ I₂ : Type*}
    (P : List Graph → Prop) (d : Nat)
    (history : Nat → EnvHistory I₁ I₂)
    (round : Nat → RoundRecord I₁ I₂ Graph Unit Unit)
    (step : ∀ n, history (n+1) = history n ++ [round n])
    (p : Proc) (n : Nat)
    (leader : componentLeader P d (History.graphSequence (history (n+1+d))) = p)
    (absent : leaderCheckpoint P d (history (n+1+d)) = false) :
    (round n).graph = leaderOutgoingGraph p := by
  unfold leaderCheckpoint at absent
  rw [leader,lagView_history_sequence history round step p (n+1) d] at absent
  have nonzero : silentAge (currentView p (history (n+1))) ≠ 0 := of_decide_eq_false absent
  rw [step] at nonzero
  exact nonzero_age_outgoing p (history n) (round n) nonzero

/-- If the agreed leader and the absence of checkpoints persist, every
sufficiently late round sends only from the leader to the other process. -/
theorem fixed_leader_without_checkpoints_oneway {I₁ I₂ : Type*}
    (P : List Graph → Prop) (d : Nat)
    (history : Nat → EnvHistory I₁ I₂)
    (round : Nat → RoundRecord I₁ I₂ Graph Unit Unit)
    (step : ∀ n, history (n+1) = history n ++ [round n])
    (p : Proc) (N M : Nat)
    (leader : ∀ n, N ≤ n → componentLeader P d (History.graphSequence (history n)) = p)
    (noCheckpoints : ∀ n, M ≤ n → leaderCheckpoint P d (history n) = false) :
    ∀ n, max N M ≤ n → (round n).graph = leaderOutgoingGraph p := by
  intro n late
  exact no_delayed_checkpoint_outgoing P d history round step p n
    (leader (n+1+d) (by omega)) (noCheckpoints (n+1+d) (by omega))

/-- The eventual form is independent of a particular choice of cutoffs. -/
theorem final_leader_phase_oneway {I₁ I₂ : Type*}
    (P : List Graph → Prop) (d : Nat)
    (history : Nat → EnvHistory I₁ I₂)
    (round : Nat → RoundRecord I₁ I₂ Graph Unit Unit)
    (step : ∀ n, history (n+1) = history n ++ [round n])
    (p : Proc)
    (leader : ∃ N, ∀ n, N ≤ n → componentLeader P d (History.graphSequence (history n)) = p)
    (noCheckpoints : ∃ M, ∀ n, M ≤ n → leaderCheckpoint P d (history n) = false) :
    ∃ K, ∀ n, K ≤ n → (round n).graph = leaderOutgoingGraph p := by
  obtain ⟨N,leader⟩ := leader
  obtain ⟨M,noCheckpoints⟩ := noCheckpoints
  exact ⟨max N M,fixed_leader_without_checkpoints_oneway P d history round step p N M leader noCheckpoints⟩

end Characterisation
