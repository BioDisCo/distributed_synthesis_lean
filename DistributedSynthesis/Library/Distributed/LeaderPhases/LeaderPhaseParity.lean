/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.LeaderClosingUpdates
import DistributedSynthesis.Formalizations.Theorem.ThmParityBlockPasting

/-! Parity accounting at agreed leader boundaries. We reuse the checked
block-minimum theorem from the no-direct-reversal construction. These are
statements about complete runs; choosing locally compatible winning plans
remains a separate obligation. -/
namespace Characterisation
open DistributedSynthesis

def InfinitelyManyLeaderBoundaries {I₁ I₂ : Type*}
    (P : List Graph → Prop) (d : Nat) (history : Nat → EnvHistory I₁ I₂) : Prop :=
  ∀ n, ∃ m, n < m ∧ leaderBoundary P d (history m) = true

/-- Depth zero followed by successive positive agreed boundaries. -/
def LeaderPhaseCuts {I₁ I₂ : Type*}
    (P : List Graph → Prop) (d : Nat) (history : Nat → EnvHistory I₁ I₂)
    (cuts : Nat → Nat) : Prop :=
  cuts 0 = 0 ∧ StrictMono cuts ∧
    ∀ k, leaderBoundary P d (history (cuts (k+1))) = true ∧
      ∀ t, cuts k < t → t < cuts (k+1) → leaderBoundary P d (history t) = false

theorem exists_leader_phase_cuts {I₁ I₂ : Type*}
    (P : List Graph → Prop) (d : Nat) (history : Nat → EnvHistory I₁ I₂)
    (infinitely : InfinitelyManyLeaderBoundaries P d history) :
    ∃ cuts, LeaderPhaseCuts P d history cuts := by
  classical
  let B := fun t => leaderBoundary P d (history t) = true
  have hinf : ∀ n, ∃ m, n < m ∧ B m := infinitely
  refine ⟨cutSeq hinf,cutSeq_zero hinf,cutSeq_strictMono hinf,?_⟩
  intro k
  refine ⟨marked_cutSeq_succ hinf k,?_⟩
  intro t lower upper
  have absent := not_marked_between hinf lower upper
  exact Bool.eq_false_iff.mpr absent

/-- After the last agreed boundary the selected leader is fixed, and every
subsequent round is one-way from that leader. No separate stabilization
assumption is needed. -/
theorem no_more_boundaries_fixed_leader {I₁ I₂ : Type*}
    (P : List Graph → Prop) (d : Nat)
    (history : Nat → EnvHistory I₁ I₂)
    (round : Nat → RoundRecord I₁ I₂ Graph Unit Unit)
    (step : ∀ n, history (n+1) = history n ++ [round n])
    (N : Nat) (absent : ∀ n, N < n → leaderBoundary P d (history n) = false) :
    ∃ p, (∀ n, N ≤ n → componentLeader P d (History.graphSequence (history n)) = p) ∧
      ∀ n, N ≤ n → (round n).graph = leaderOutgoingGraph p := by
  let p := componentLeader P d (History.graphSequence (history N))
  have fixed : ∀ n, N ≤ n → componentLeader P d (History.graphSequence (history n)) = p := by
    intro n lower
    exact leader_constant_between_boundaries P d history round step N (n+1)
      (fun t ht _ => absent t ht) n lower (by omega)
  refine ⟨p,fixed,?_⟩
  intro n lower
  exact no_delayed_checkpoint_outgoing P d history round step p n
    (fixed (n+1+d) (by omega))
    ((no_leaderBoundary P d _ (absent (n+1+d) (by omega))).1)

theorem finitely_many_boundaries_final_leader {I₁ I₂ : Type*}
    (P : List Graph → Prop) (d : Nat)
    (history : Nat → EnvHistory I₁ I₂)
    (round : Nat → RoundRecord I₁ I₂ Graph Unit Unit)
    (step : ∀ n, history (n+1) = history n ++ [round n])
    (finite : ¬ InfinitelyManyLeaderBoundaries P d history) :
    ∃ N p, (∀ n, N < n → leaderBoundary P d (history n) = false) ∧
      (∀ n, N ≤ n → componentLeader P d (History.graphSequence (history n)) = p) ∧
      ∀ n, N ≤ n → (round n).graph = leaderOutgoingGraph p := by
  classical
  unfold InfinitelyManyLeaderBoundaries at finite
  push Not at finite
  obtain ⟨N,hN⟩ := finite
  have absent : ∀ n, N < n → leaderBoundary P d (history n) = false :=
    fun n hn => Bool.eq_false_iff.mpr (hN n hn)
  obtain ⟨p,fixed,outgoing⟩ := no_more_boundaries_fixed_leader P d history round step N absent
  exact ⟨N,p,absent,fixed,outgoing⟩

/-- Each finite phase is one-way from its agreed leader except for at most
d+1 closing rounds, and its single minimum priority suffices for parity
across infinitely many phases. Priorities index rounds, not game stages. -/
theorem leader_phase_minima_correct {I₁ I₂ : Type*}
    (P : List Graph → Prop) (d : Nat)
    (history : Nat → EnvHistory I₁ I₂)
    (round : Nat → RoundRecord I₁ I₂ Graph Unit Unit)
    (step : ∀ n, history (n+1) = history n ++ [round n])
    (priority : Nat → Nat) (cuts : Nat → Nat)
    (phases : LeaderPhaseCuts P d history cuts) :
    (∀ k, ∃ c, cuts k ≤ c ∧ c ≤ cuts (k+1) ∧ cuts (k+1)-c ≤ d+1 ∧
      ∀ n, cuts k ≤ n → n < c → (round n).graph = leaderOutgoingGraph
        (componentLeader P d (History.graphSequence (history (cuts k))))) ∧
    (NatSeqMinEvenParity (cutBlockMin priority cuts) ↔ NatSeqMinEvenParity priority) := by
  constructor
  · intro k
    exact leader_phase_bounded_closing P d history round step (cuts k) (cuts (k+1))
      (Nat.le_of_lt (phases.2.1 (by omega))) (phases.2.2 k).2
  · exact natSeqMinEvenParity_cutBlockMin priority phases.2.1 phases.1

/-- Exhaustive acceptance split. Infinite boundary runs use phase minima;
runs with finitely many boundaries use the parity of their final one-way
leader phase. This does not assert either acceptance condition holds. -/
theorem leader_parity_dichotomy {I₁ I₂ : Type*}
    (P : List Graph → Prop) (d : Nat)
    (history : Nat → EnvHistory I₁ I₂)
    (round : Nat → RoundRecord I₁ I₂ Graph Unit Unit)
    (step : ∀ n, history (n+1) = history n ++ [round n])
    (priority : Nat → Nat) :
    (∃ cuts, LeaderPhaseCuts P d history cuts ∧
      (NatSeqMinEvenParity (cutBlockMin priority cuts) ↔ NatSeqMinEvenParity priority)) ∨
    (∃ N p, (∀ n, N < n → leaderBoundary P d (history n) = false) ∧
      (∀ n, N ≤ n → componentLeader P d (History.graphSequence (history n)) = p) ∧
      (∀ n, N ≤ n → (round n).graph = leaderOutgoingGraph p) ∧
      (NatSeqMinEvenParity (fun n => priority (N+n)) ↔ NatSeqMinEvenParity priority)) := by
  classical
  by_cases inf : InfinitelyManyLeaderBoundaries P d history
  · obtain ⟨cuts,phases⟩ := exists_leader_phase_cuts P d history inf
    exact Or.inl ⟨cuts,phases,(leader_phase_minima_correct P d history round step priority cuts phases).2⟩
  · obtain ⟨N,p,absent,fixed,outgoing⟩ := finitely_many_boundaries_final_leader P d history round step inf
    exact Or.inr ⟨N,p,absent,fixed,outgoing,natSeqMinEvenParity_shift priority N⟩

/-- The adversary's acceptance condition must be retained as well. Phase
minima preserve the implication from admitted graph runs to objective
acceptance, including adversaries that are not closed. -/
theorem leader_phase_guarded_parity {I₁ I₂ : Type*}
    (P : List Graph → Prop) (d : Nat) (history : Nat → EnvHistory I₁ I₂)
    (cuts : Nat → Nat) (phases : LeaderPhaseCuts P d history cuts)
    (adversaryPriority objectivePriority : Nat → Nat) :
    (NatSeqMinEvenParity adversaryPriority → NatSeqMinEvenParity objectivePriority) ↔
    (NatSeqMinEvenParity (cutBlockMin adversaryPriority cuts) →
      NatSeqMinEvenParity (cutBlockMin objectivePriority cuts)) := by
  rw [natSeqMinEvenParity_cutBlockMin adversaryPriority phases.2.1 phases.1,
    natSeqMinEvenParity_cutBlockMin objectivePriority phases.2.1 phases.1]

/-- Replacing whole finite phases preserves parity if their minima agree,
even when the corresponding phases have different lengths. This concerns
complete infinite runs, not independent choices of winning phase fragments. -/
theorem leader_phase_parity_transfer {I₁ I₂ J₁ J₂ : Type*}
    (P Q : List Graph → Prop) (d e : Nat)
    (history : Nat → EnvHistory I₁ I₂) (other : Nat → EnvHistory J₁ J₂)
    (cuts otherCuts : Nat → Nat)
    (phases : LeaderPhaseCuts P d history cuts)
    (otherPhases : LeaderPhaseCuts Q e other otherCuts)
    (priority otherPriority : Nat → Nat)
    (same : ∀ k, cutBlockMin priority cuts k = cutBlockMin otherPriority otherCuts k) :
    NatSeqMinEvenParity priority ↔ NatSeqMinEvenParity otherPriority := by
  have eq : cutBlockMin priority cuts = cutBlockMin otherPriority otherCuts := funext same
  rw [← natSeqMinEvenParity_cutBlockMin priority phases.2.1 phases.1,
    ← natSeqMinEvenParity_cutBlockMin otherPriority otherPhases.2.1 otherPhases.1,eq]

end Characterisation
