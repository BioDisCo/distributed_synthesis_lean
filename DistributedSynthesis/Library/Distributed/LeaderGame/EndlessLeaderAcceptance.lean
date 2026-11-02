/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.NumberedGameSoundness

/-! Acceptance of a final leader controller is acceptance of the composed
physical suffix from its actual incoming objective state. -/
namespace Characterisation
open DistributedSynthesis

theorem continuationRun_strategy {H I₁ I₂ O₁ O₂ : Type}
    (objective : DetParityAutomaton (ContinuationLetter I₁ I₂ O₁ O₂))
    (σ : StrategyPair I₁ I₂ O₁ O₂) (past : H → EnvHistory I₁ I₂)
    (q : objective.State) (h : H) (env : Nat → I₁ × I₂ × Graph) (n : Nat) :
    objective.runFrom q (continuationTrace (strategyContinuationPolicy σ past) h env) n =
      strategyContinuationLabel σ (fun s input output => objective.step s (input,output)) q (past h)
        ((branchNode env n).map (fun r => (⟨r.1,r.2.1,r.2.2,(),()⟩ : RoundRecord I₁ I₂ Graph Unit Unit))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [DetParityAutomaton.runFrom,ih]
    simp only [branchNode,List.map_append,List.map_singleton]
    rw [strategyContinuationLabel_append]
    simp only [continuationTrace,strategyContinuationPolicy,continuationScenario_history,branchNode,
      List.map_append,List.map_singleton,List.append_assoc]

theorem finalPhase_parity_of_accepts {I₁ I₂ O₁ O₂ : Type}
    (P : List Graph → Prop) (closed : PrefixClosed P) (d : Nat)
    (controllers : LeaderPhaseOrigin I₁ I₂ → StrategyPair I₁ I₂ O₁ O₂)
    (σ : StrategyPair I₁ I₂ O₁ O₂) (impl : ImplementsPhaseFamily P d controllers σ)
    (objective : DetParityAutomaton (ContinuationLetter I₁ I₂ O₁ O₂))
    (history : Nat → EnvHistory I₁ I₂)
    (depth : ∀ n, List.length (history n) = n)
    (prefixes : ∀ m n, m ≤ n → (history n).take m = history m)
    (live : ∀ n, P (History.graphSequence (history n)))
    (N : Nat) (start : N = 0 ∨ leaderBoundary P d (history N) = true)
    (absent : ∀ n, N < n → leaderBoundary P d (history n) = false)
    (env : Nat → I₁ × I₂ × Graph)
    (continuation : ∀ n, history N ++
      (branchNode env n).map (fun r => (⟨r.1,r.2.1,r.2.2,(),()⟩ : RoundRecord I₁ I₂ Graph Unit Unit)) = history (N+n))
    (accepted : objective.AcceptsFrom
      (strategyHistoryLabel σ (fun s input output => objective.step s (input,output)) objective.initial (history N))
      (continuationTrace (strategyContinuationPolicy
        (controllers (boundaryOrigin P (history N))) (fun _ : Unit => history N)) () env)) :
    NatSeqMinEvenParity (fun n => objective.priority (strategyHistoryLabel σ
      (fun s input output => objective.step s (input,output)) objective.initial (history (n+1)))) := by
  let step := fun s input output => objective.step s (input,output)
  let q := strategyHistoryLabel σ step objective.initial (history N)
  let τ := controllers (boundaryOrigin P (history N))
  let trace := continuationTrace (strategyContinuationPolicy τ (fun _ : Unit => history N)) () env
  have word : ∀ n,
      (branchNode env n).map (fun r => (⟨r.1,r.2.1,r.2.2,(),()⟩ : RoundRecord I₁ I₂ Graph Unit Unit)) =
        (history (N+n)).drop N := by
    intro n
    have dropped := congrArg (List.drop (List.length (history N))) (continuation n)
    rw [List.drop_left] at dropped
    simpa only [depth] using dropped
  have runs : ∀ n, objective.runFrom q trace n =
      strategyContinuationLabel τ step q (history N) ((history (N+n)).drop N) := by
    intro n
    have result := continuationRun_strategy objective τ (fun _ : Unit => history N) q () env n
    rwa [word] at result
  have parity : NatSeqMinEvenParity (fun n => objective.priority (objective.runFrom q trace n)) := accepted
  have shifted := (natSeqMinEvenParity_shift (fun n => objective.priority (objective.runFrom q trace n)) 1).mpr parity
  have priorities : (fun n => objective.priority (objective.runFrom q trace (1+n))) =
      finalPhasePriority P controllers σ step objective.initial history objective.priority N := by
    funext n
    rw [runs]
    simp only [finalPhasePriority,τ,q,boundaryOrigin,Nat.add_comm 1 n,Nat.add_assoc]
  rw [priorities] at shifted
  exact (final_phase_parity_iff P closed d controllers σ impl step objective.initial
    history depth prefixes live objective.priority N start absent).mp shifted

end Characterisation
