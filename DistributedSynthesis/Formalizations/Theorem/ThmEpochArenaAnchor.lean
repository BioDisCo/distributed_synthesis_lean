/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmLocalSummaryAutomaton
import DistributedSynthesis.Formalizations.Theorem.ThmZielonkaCountableParity

/-!
# The full-information anchor of the epoch game

This file formalizes step (i) of the finite-state-sufficiency argument for paper
`prop:starcomplete` -- the Berwanger--Mathew--van den Bogaard Theorem 10 instance
for the theta-bar dynamic hierarchy.

The epoch game of a tracked `FiniteEpochTransformer` is embedded as a
`CountableParityGame`, the **epoch arena**: at a coalition node the coalition
commits a *contingent move* (one joint output pair per possible current
environment round), and the environment resolves the round.  The arena priority
is read off the tracked objective-automaton state (`DPATracking.stateOf`), so
the arena objective is exactly acceptance of the emitted word.

The anchor theorem: from a realizing distributed strategy -- every real
execution accepted by the objective automaton -- the round-aware epoch game has
a (full-information, positional) controller winning against **every** finite
environment code.  The proof interleaves the distributed strategy against a
hypothetical positional environment winner (the sigma-versus-rho toolkit below,
reused by the belief-lifting bricks of route delta), contradicting determinacy,
and then extracts the controller from the proven positional determinacy of
countable parity games (`ThmZielonkaCountableParity`).

This is deliberately *not* the summary-observable factorization: the extracted
controller reads the full game state.  Factoring it through the two summary
observations is the remaining content of `SummaryObservableWinnerCertificate`.
-/

namespace DistributedSynthesis

universe u v w a s z

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type w} {Out₂ : Type a}

namespace FiniteEpochTransformer

/-- The coalition's committed **contingent move** for one arena round: one joint
output pair per possible current environment round.  Committing before the
round is revealed and evaluating at the revealed round is exactly the timing of
a round-aware controller. -/
abbrev ContingentRoundMove (In₁ : Type u) (In₂ : Type v)
    (Out₁ : Type w) (Out₂ : Type a) :=
  EnvironmentRound In₁ In₂ -> Out₁ × Out₂

variable
  (T :
    FiniteEpochTransformer.{max u v w a, u, v, w, a, z}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂) In₁ In₂ Out₁ Out₂)

/-- One epoch-arena transition: the committed contingent move, evaluated at the
environment's revealed round, drives the round-aware game transition. -/
def contingentTransition (state : GameState T)
    (move : ContingentRoundMove In₁ In₂ Out₁ Out₂)
    (envRound : EnvironmentRound In₁ In₂) : GameState T :=
  roundAwareGameTransition T (fun _ envRound' => move envRound') state envRound

/-- Every round-aware controller step is the contingent transition of the move
the controller commits at the current state. -/
theorem roundAwareGameTransition_eq_contingentTransition
    (controller : RoundAwareControllerCode T)
    (state : GameState T) (envRound : EnvironmentRound In₁ In₂) :
    roundAwareGameTransition T controller state envRound =
      contingentTransition T state (controller state) envRound := by
  cases envRound with
  | mk inputOne inputTwo graph =>
      cases state with
      | inl boundary => cases graph <;> rfl
      | inr side =>
          cases side with
          | inl withinOne => cases graph <;> rfl
          | inr withinTwo => cases graph <;> rfl

/-- The contingent move a distributed strategy commits at a real finite
history: each process's output at every possible current environment round,
read from its own next view. -/
def strategyContingentMove (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (h : History In₁ In₂ Graph Out₁ Out₂) :
    ContingentRoundMove In₁ In₂ Out₁ Out₂ :=
  fun envRound =>
    (σ.one (nextView Proc.one h envRound), σ.two (nextView Proc.two h envRound))

/-- The generated round of a strategy is the record of the environment round
with the contingent-move outputs. -/
theorem nextRound_eq_strategyContingentMove (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (h : History In₁ In₂ Graph Out₁ Out₂) (envRound : EnvironmentRound In₁ In₂) :
    nextRound σ h envRound =
      { inputOne := envRound.inputOne
        inputTwo := envRound.inputTwo
        graph := envRound.graph
        outputOne := (strategyContingentMove σ h envRound).1
        outputTwo := (strategyContingentMove σ h envRound).2 } := rfl

/-- The interleaved epoch-arena path of a state stream and a committed
contingent-move stream: the coalition node of the current state at even times,
the committed node at odd times. -/
def contingentPlayPath (states : Nat -> GameState T)
    (moves : Nat -> ContingentRoundMove In₁ In₂ Out₁ Out₂) (k : Nat) :
    GameState T ⊕ (GameState T × ContingentRoundMove In₁ In₂ Out₁ Out₂) :=
  if k % 2 = 0 then Sum.inl (states (k / 2))
  else Sum.inr (states (k / 2), moves (k / 2))

theorem contingentPlayPath_two_mul (states : Nat -> GameState T)
    (moves : Nat -> ContingentRoundMove In₁ In₂ Out₁ Out₂) (n : Nat) :
    contingentPlayPath T states moves (2 * n) = Sum.inl (states n) := by
  simp only [contingentPlayPath]
  rw [if_pos (by omega : 2 * n % 2 = 0), show 2 * n / 2 = n from by omega]

theorem contingentPlayPath_two_mul_add_one (states : Nat -> GameState T)
    (moves : Nat -> ContingentRoundMove In₁ In₂ Out₁ Out₂) (n : Nat) :
    contingentPlayPath T states moves (2 * n + 1) =
      Sum.inr (states n, moves n) := by
  simp only [contingentPlayPath]
  rw [if_neg (by omega : ¬ (2 * n + 1) % 2 = 0),
    show (2 * n + 1) / 2 = n from by omega]

variable
  {A :
    DetParityAutomaton.{max u v w a, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂)}
  (tracking : DPATracking T A)

/-- The controller-free record fold steps the tracked automaton state on the
absorbed record.  This is the record-level form of
`DPATracking.stateOf_roundAwareGameTransition`, used by the play
correspondences that carry real histories rather than game plays. -/
theorem DPATracking.stateOf_recordTransition
    (state : GameState T) (round : RoundRecord In₁ In₂ Graph Out₁ Out₂) :
    tracking.stateOf (recordTransition T state round) =
      A.step (tracking.stateOf state) round := by
  have h :=
    tracking.stateOf_roundAwareGameTransition
      (fun _ _ => (round.outputOne, round.outputTwo)) state
      { inputOne := round.inputOne
        inputTwo := round.inputTwo
        graph := round.graph }
  rw [← recordTransition_emitted] at h
  exact h

section Arena

variable [Fintype (GameState T)]
  [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
  [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

/-- **The epoch arena**: the round-aware epoch game of a tracked transformer as
a countable parity game.  The coalition (Even) owns the game states and commits
a contingent move; the environment (Odd) owns the committed nodes and resolves
the round.  Priority is the objective automaton's priority of the tracked
state, so the arena parity objective is acceptance of the emitted word. -/
def epochArena : CountableParityGame.{max u v w a z} where
  Position :=
    GameState T ⊕ (GameState T × ContingentRoundMove In₁ In₂ Out₁ Out₂)
  positionCountable := by
    haveI : Finite (EnvironmentRound In₁ In₂) := Finite.of_fintype _
    haveI : Countable (ContingentRoundMove In₁ In₂ Out₁ Out₂) :=
      Finite.to_countable
    haveI : Countable (GameState T) := Finite.to_countable
    exact inferInstance
  owner := Sum.elim (fun _ => ParityPlayer.even) fun _ => ParityPlayer.odd
  step p q :=
    match p, q with
    | Sum.inl s, Sum.inr sm => sm.1 = s
    | Sum.inr sm, Sum.inl s' =>
        ∃ e : EnvironmentRound In₁ In₂,
          s' = contingentTransition T sm.1 sm.2 e
    | _, _ => False
  step_total p := by
    cases p with
    | inl s => exact ⟨Sum.inr (s, fun _ => (default, default)), rfl⟩
    | inr sm =>
        exact
          ⟨Sum.inl
              (contingentTransition T sm.1 sm.2
                { inputOne := default, inputTwo := default, graph := Graph.both }),
            { inputOne := default, inputTwo := default, graph := Graph.both },
            rfl⟩
  priority :=
    Sum.elim (fun s => A.priority (tracking.stateOf s)) fun sm =>
      A.priority (tracking.stateOf sm.1)
  priority_finite := by
    apply (Set.finite_range A.priority).subset
    rintro _ ⟨p, rfl⟩
    cases p with
    | inl s => exact ⟨tracking.stateOf s, rfl⟩
    | inr sm => exact ⟨tracking.stateOf sm.1, rfl⟩

/-- Legality forces an Even (coalition) positional move at a coalition node to
commit a contingent move at the current state. -/
theorem exists_evenMove
    (τ : (epochArena T tracking).PositionalStrategy ParityPlayer.even)
    (s : GameState T) :
    ∃ m : ContingentRoundMove In₁ In₂ Out₁ Out₂,
      τ.move (Sum.inl s) = Sum.inr (s, m) := by
  have hleg := τ.legal (Sum.inl s) rfl
  cases hmv : τ.move (Sum.inl s) with
  | inl s' =>
      rw [hmv] at hleg
      exact absurd hleg (by simp [epochArena])
  | inr sm =>
      rw [hmv] at hleg
      obtain ⟨s₀, m⟩ := sm
      have hs : s₀ = s := by simpa [epochArena] using hleg
      subst hs
      exact ⟨m, rfl⟩

/-- Legality forces an Odd (environment) positional move at a committed node to
resolve some environment round of the contingent transition. -/
theorem exists_oddResponseEnv
    (ρ : (epochArena T tracking).PositionalStrategy ParityPlayer.odd)
    (s : GameState T) (m : ContingentRoundMove In₁ In₂ Out₁ Out₂) :
    ∃ e : EnvironmentRound In₁ In₂,
      ρ.move (Sum.inr (s, m)) = Sum.inl (contingentTransition T s m e) := by
  have hleg := ρ.legal (Sum.inr (s, m)) rfl
  cases hmv : ρ.move (Sum.inr (s, m)) with
  | inr sm' =>
      rw [hmv] at hleg
      exact absurd hleg (by simp [epochArena])
  | inl s' =>
      rw [hmv] at hleg
      obtain ⟨e, he⟩ : ∃ e : EnvironmentRound In₁ In₂,
          s' = contingentTransition T s m e := by
        simpa [epochArena] using hleg
      exact ⟨e, congrArg Sum.inl he⟩

/-- The environment round an Odd positional strategy resolves at a committed
node. -/
noncomputable def oddResponseEnv
    (ρ : (epochArena T tracking).PositionalStrategy ParityPlayer.odd)
    (s : GameState T) (m : ContingentRoundMove In₁ In₂ Out₁ Out₂) :
    EnvironmentRound In₁ In₂ :=
  (exists_oddResponseEnv T tracking ρ s m).choose

theorem oddResponseEnv_spec
    (ρ : (epochArena T tracking).PositionalStrategy ParityPlayer.odd)
    (s : GameState T) (m : ContingentRoundMove In₁ In₂ Out₁ Out₂) :
    ρ.move (Sum.inr (s, m)) =
      Sum.inl (contingentTransition T s m (oddResponseEnv T tracking ρ s m)) :=
  (exists_oddResponseEnv T tracking ρ s m).choose_spec

/-- The round-aware controller committed by an Even positional arena strategy:
its contingent move at each game state. -/
noncomputable def evenCommittedController
    (τ : (epochArena T tracking).PositionalStrategy ParityPlayer.even) :
    RoundAwareControllerCode T :=
  fun s => (exists_evenMove T tracking τ s).choose

theorem evenCommittedController_spec
    (τ : (epochArena T tracking).PositionalStrategy ParityPlayer.even)
    (s : GameState T) :
    τ.move (Sum.inl s) = Sum.inr (s, evenCommittedController T tracking τ s) :=
  (exists_evenMove T tracking τ s).choose_spec

/-!
## Play, consistency, and parity transfer along the interleaved path

The lemmas are stated against per-step hypotheses on the streams, so the same
toolkit serves the sigma-versus-rho interleaving here and the belief-game
bricks of route delta.
-/

variable (states : Nat -> GameState T)
  (moves : Nat -> ContingentRoundMove In₁ In₂ Out₁ Out₂)

theorem priority_contingentPlayPath (k : Nat) :
    (epochArena T tracking).priority
        (contingentPlayPath T states moves k) =
      A.priority (tracking.stateOf (states (k / 2))) := by
  rcases (by omega : k % 2 = 0 ∨ k % 2 = 1) with h | h
  · obtain ⟨n, rfl⟩ : ∃ n, k = 2 * n := ⟨k / 2, by omega⟩
    rw [contingentPlayPath_two_mul, show 2 * n / 2 = n from by omega]
    rfl
  · obtain ⟨n, rfl⟩ : ∃ n, k = 2 * n + 1 := ⟨k / 2, by omega⟩
    rw [contingentPlayPath_two_mul_add_one,
      show (2 * n + 1) / 2 = n from by omega]
    rfl

theorem contingentPlayPath_playFrom
    (hstep :
      ∀ n : Nat, ∃ e : EnvironmentRound In₁ In₂,
        states (n + 1) = contingentTransition T (states n) (moves n) e) :
    (epochArena T tracking).PlayFrom (Sum.inl (states 0))
      (contingentPlayPath T states moves) := by
  constructor
  · rw [show (0 : Nat) = 2 * 0 from rfl, contingentPlayPath_two_mul]
  · intro k
    rcases (by omega : k % 2 = 0 ∨ k % 2 = 1) with h | h
    · obtain ⟨n, rfl⟩ : ∃ n, k = 2 * n := ⟨k / 2, by omega⟩
      rw [contingentPlayPath_two_mul, contingentPlayPath_two_mul_add_one]
      exact rfl
    · obtain ⟨n, rfl⟩ : ∃ n, k = 2 * n + 1 := ⟨k / 2, by omega⟩
      rw [contingentPlayPath_two_mul_add_one,
        show 2 * n + 1 + 1 = 2 * (n + 1) from by omega, contingentPlayPath_two_mul]
      exact hstep n

theorem contingentPlayPath_consistent_even
    (τ : (epochArena T tracking).PositionalStrategy ParityPlayer.even)
    (hmove : ∀ n : Nat, τ.move (Sum.inl (states n)) = Sum.inr (states n, moves n)) :
    τ.Consistent (contingentPlayPath T states moves) := by
  intro k howner
  rcases (by omega : k % 2 = 0 ∨ k % 2 = 1) with h | h
  · obtain ⟨n, rfl⟩ : ∃ n, k = 2 * n := ⟨k / 2, by omega⟩
    rw [contingentPlayPath_two_mul, contingentPlayPath_two_mul_add_one]
    exact (hmove n).symm
  · obtain ⟨n, rfl⟩ : ∃ n, k = 2 * n + 1 := ⟨k / 2, by omega⟩
    rw [contingentPlayPath_two_mul_add_one] at howner
    exact absurd howner (by simp [epochArena])

theorem contingentPlayPath_consistent_odd
    (ρ : (epochArena T tracking).PositionalStrategy ParityPlayer.odd)
    (hmove :
      ∀ n : Nat,
        ρ.move (Sum.inr (states n, moves n)) = Sum.inl (states (n + 1))) :
    ρ.Consistent (contingentPlayPath T states moves) := by
  intro k howner
  rcases (by omega : k % 2 = 0 ∨ k % 2 = 1) with h | h
  · obtain ⟨n, rfl⟩ : ∃ n, k = 2 * n := ⟨k / 2, by omega⟩
    rw [contingentPlayPath_two_mul] at howner
    exact absurd howner (by simp [epochArena])
  · obtain ⟨n, rfl⟩ : ∃ n, k = 2 * n + 1 := ⟨k / 2, by omega⟩
    rw [contingentPlayPath_two_mul_add_one,
      show 2 * n + 1 + 1 = 2 * (n + 1) from by omega, contingentPlayPath_two_mul]
    exact (hmove n).symm

/-- Parity transfer along the interleaved path: a priority recurs on the path
iff it recurs on the automaton run of any word whose run the tracked states
carry. -/
theorem prioritySeen_contingentPlayPath_iff
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (hrun : ∀ n : Nat, tracking.stateOf (states n) = A.run word n) (q : Nat) :
    (epochArena T tracking).PrioritySeenInfinitelyOften
        (contingentPlayPath T states moves) q ↔
      A.PrioritySeenInfinitelyOften word q := by
  constructor
  · intro hseen n
    obtain ⟨k, hk, hkq⟩ := hseen (2 * n)
    refine ⟨k / 2, by omega, ?_⟩
    rw [priority_contingentPlayPath, hrun] at hkq
    exact hkq
  · intro hseen n
    obtain ⟨m, hm, hmq⟩ := hseen n
    refine ⟨2 * m, by omega, ?_⟩
    rw [priority_contingentPlayPath, show 2 * m / 2 = m from by omega, hrun m]
    exact hmq

/-- The interleaved path satisfies the arena min-even objective iff the
objective automaton accepts the carried word. -/
theorem minPriorityEven_contingentPlayPath_iff_accepts
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (hrun : ∀ n : Nat, tracking.stateOf (states n) = A.run word n) :
    (epochArena T tracking).MinPriorityEven
        (contingentPlayPath T states moves) ↔
      A.Accepts word := by
  have h := fun q =>
    prioritySeen_contingentPlayPath_iff T tracking states moves word hrun q
  constructor
  · rintro ⟨p, hpe, hps, hpm⟩
    exact ⟨p, hpe, (h p).mp hps, fun q hq => hpm q ((h q).mpr hq)⟩
  · rintro ⟨p, hpe, hps, hpm⟩
    exact ⟨p, hpe, (h p).mpr hps, fun q hq => hpm q ((h q).mp hq)⟩

/-!
## The sigma-versus-rho interleaving

Playing a distributed strategy against an Odd positional arena strategy
produces a single real play: the strategy commits its contingent move at the
current real history, and the Odd strategy resolves the round.  The lemmas
below are the reusable play correspondence: the carried history is the real
execution prefix against the read-off environment sequence, the carried game
state is the record fold of that prefix, and the tracked automaton state is the
acceptance run on the real execution.
-/

section StrategyReplay

variable (σ : StrategyPair In₁ In₂ Out₁ Out₂)
  (ρ : (epochArena T tracking).PositionalStrategy ParityPlayer.odd)
  (initialBoundary : T.boundary)

/-- The real play of a distributed strategy against an Odd positional arena
strategy: the carried real history and the carried game state. -/
noncomputable def strategyOddPlay :
    Nat -> History In₁ In₂ Graph Out₁ Out₂ × GameState T
  | 0 => ([], Sum.inl initialBoundary)
  | n + 1 =>
      let prev := strategyOddPlay n
      let e :=
        oddResponseEnv T tracking ρ prev.2 (strategyContingentMove σ prev.1)
      (History.append prev.1 (nextRound σ prev.1 e),
        contingentTransition T prev.2 (strategyContingentMove σ prev.1) e)

/-- The real environment sequence the Odd strategy induces against the
distributed strategy. -/
noncomputable def strategyOddEnv : EnvironmentSequence In₁ In₂ :=
  fun n =>
    oddResponseEnv T tracking ρ
      (strategyOddPlay T tracking σ ρ initialBoundary n).2
      (strategyContingentMove σ
        (strategyOddPlay T tracking σ ρ initialBoundary n).1)

@[simp]
theorem strategyOddPlay_zero :
    strategyOddPlay T tracking σ ρ initialBoundary 0 =
      ([], Sum.inl initialBoundary) := rfl

theorem strategyOddPlay_succ (n : Nat) :
    strategyOddPlay T tracking σ ρ initialBoundary (n + 1) =
      (History.append (strategyOddPlay T tracking σ ρ initialBoundary n).1
          (nextRound σ (strategyOddPlay T tracking σ ρ initialBoundary n).1
            (strategyOddEnv T tracking σ ρ initialBoundary n)),
        contingentTransition T
          (strategyOddPlay T tracking σ ρ initialBoundary n).2
          (strategyContingentMove σ
            (strategyOddPlay T tracking σ ρ initialBoundary n).1)
          (strategyOddEnv T tracking σ ρ initialBoundary n)) := rfl

/-- The carried history is the real execution prefix against the read-off
environment sequence. -/
theorem strategyOddPlay_fst (n : Nat) :
    (strategyOddPlay T tracking σ ρ initialBoundary n).1 =
      executionPrefix σ (strategyOddEnv T tracking σ ρ initialBoundary) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [executionPrefix_succ, ← ih, strategyOddPlay_succ]

/-- The Odd strategy's arena response at step `n` of the real play. -/
theorem strategyOddPlay_oddMove (n : Nat) :
    ρ.move
        (Sum.inr ((strategyOddPlay T tracking σ ρ initialBoundary n).2,
          strategyContingentMove σ
            (strategyOddPlay T tracking σ ρ initialBoundary n).1)) =
      Sum.inl (strategyOddPlay T tracking σ ρ initialBoundary (n + 1)).2 := by
  rw [strategyOddPlay_succ]
  exact oddResponseEnv_spec T tracking ρ _ _

/-- The carried game state is the controller-free record fold of the carried
history. -/
theorem strategyOddPlay_snd_eq_recordFold (n : Nat) :
    (strategyOddPlay T tracking σ ρ initialBoundary n).2 =
      recordFold T initialBoundary
        (strategyOddPlay T tracking σ ρ initialBoundary n).1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [strategyOddPlay_succ, recordFold_append, ← ih]
      exact
        (recordTransition_emitted T
          (fun _ envRound' =>
            strategyContingentMove σ
              (strategyOddPlay T tracking σ ρ initialBoundary n).1 envRound')
          (strategyOddPlay T tracking σ ρ initialBoundary n).2
          (strategyOddEnv T tracking σ ρ initialBoundary n)).symm

/-- Along the real play, the tracked automaton state is the acceptance run of
the objective automaton on the real execution. -/
theorem stateOf_strategyOddPlay_snd
    (hinitial : tracking.boundaryState initialBoundary = A.initial) (n : Nat) :
    tracking.stateOf (strategyOddPlay T tracking σ ρ initialBoundary n).2 =
      A.run (execution σ (strategyOddEnv T tracking σ ρ initialBoundary)) n := by
  induction n with
  | zero => exact hinitial
  | succ n ih =>
      rw [strategyOddPlay_succ]
      show tracking.stateOf
          (contingentTransition T
            (strategyOddPlay T tracking σ ρ initialBoundary n).2
            (strategyContingentMove σ
              (strategyOddPlay T tracking σ ρ initialBoundary n).1)
            (strategyOddEnv T tracking σ ρ initialBoundary n)) = _
      rw [contingentTransition, tracking.stateOf_roundAwareGameTransition, ih,
        DetParityAutomaton.run_succ]
      congr 1
      rw [execution_apply,
        ← strategyOddPlay_fst T tracking σ ρ initialBoundary n]
      rfl

end StrategyReplay

/-!
## The anchor: realizability yields a positional coalition winner
-/

/-- **Realizability implies an Even positional arena winner.**  If some
distributed strategy realizes the objective on every real environment
sequence, then Even wins the epoch arena positionally from the initial
boundary.  Otherwise, by the proven positional determinacy, Odd would win with
some positional `rho`; playing the distributed strategy against `rho` yields a
single real play whose execution is accepted (so the interleaved arena path is
min-even) yet `rho`-consistent (so min-odd) -- impossible. -/
theorem exists_evenPositionalWinner_of_realizable
    (initialBoundary : T.boundary)
    (hinitial : tracking.boundaryState initialBoundary = A.initial)
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (hσ : ∀ env : EnvironmentSequence In₁ In₂, A.Accepts (execution σ env)) :
    ∃ τ : (epochArena T tracking).PositionalStrategy ParityPlayer.even,
      CountableParityGame.PositionalStrategy.WinningFrom
        (G := epochArena T tracking) τ (Sum.inl (Sum.inl initialBoundary)) := by
  rcases
      (epochArena T tracking).positionalGameDetermined
        (Sum.inl (Sum.inl initialBoundary)) with
    heven | hodd
  · exact heven
  · exfalso
    obtain ⟨ρ, hρ⟩ := hodd
    have hstep :
        ∀ n : Nat, ∃ e : EnvironmentRound In₁ In₂,
          (strategyOddPlay T tracking σ ρ initialBoundary (n + 1)).2 =
            contingentTransition T
              (strategyOddPlay T tracking σ ρ initialBoundary n).2
              (strategyContingentMove σ
                (strategyOddPlay T tracking σ ρ initialBoundary n).1) e :=
      fun n =>
        ⟨strategyOddEnv T tracking σ ρ initialBoundary n, by
          rw [strategyOddPlay_succ]⟩
    have hplayFrom :
        (epochArena T tracking).PlayFrom (Sum.inl (Sum.inl initialBoundary))
          (contingentPlayPath T
            (fun n => (strategyOddPlay T tracking σ ρ initialBoundary n).2)
            (fun n =>
              strategyContingentMove σ
                (strategyOddPlay T tracking σ ρ initialBoundary n).1)) :=
      contingentPlayPath_playFrom T tracking _ _ hstep
    have hconsistent :=
      contingentPlayPath_consistent_odd T tracking
        (fun n => (strategyOddPlay T tracking σ ρ initialBoundary n).2)
        (fun n =>
          strategyContingentMove σ
            (strategyOddPlay T tracking σ ρ initialBoundary n).1)
        ρ (fun n => strategyOddPlay_oddMove T tracking σ ρ initialBoundary n)
    have hOdd :
        (epochArena T tracking).MinPriorityOdd
          (contingentPlayPath T
            (fun n => (strategyOddPlay T tracking σ ρ initialBoundary n).2)
            (fun n =>
              strategyContingentMove σ
                (strategyOddPlay T tracking σ ρ initialBoundary n).1)) := by
      have hwin := hρ _ hplayFrom hconsistent
      simpa [CountableParityGame.PlayerWinsPath] using hwin
    have hEven :
        (epochArena T tracking).MinPriorityEven
          (contingentPlayPath T
            (fun n => (strategyOddPlay T tracking σ ρ initialBoundary n).2)
            (fun n =>
              strategyContingentMove σ
                (strategyOddPlay T tracking σ ρ initialBoundary n).1)) :=
      (minPriorityEven_contingentPlayPath_iff_accepts T tracking _ _
          (execution σ (strategyOddEnv T tracking σ ρ initialBoundary))
          (fun n =>
            stateOf_strategyOddPlay_snd T tracking σ ρ initialBoundary
              hinitial n)).mpr
        (hσ (strategyOddEnv T tracking σ ρ initialBoundary))
    exact
      (epochArena T tracking).not_minPriorityEven_and_minPriorityOdd _
        ⟨hEven, hOdd⟩

/-- **The extracted controller wins against every environment code.**  The
round-aware play of the committed controller against any positional
environment code interleaves into an arena play consistent with the Even
positional winner, so its emitted word is accepted; the winning predicate
follows by the tracked-run correspondence. -/
theorem roundAwareGameWins_evenCommittedController_of_winningFrom
    (initialBoundary : T.boundary)
    (hinitial : tracking.boundaryState initialBoundary = A.initial)
    (hautomaton :
      ∀ word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂),
        T.automaton.Accepts word ↔ A.Accepts word)
    (τ : (epochArena T tracking).PositionalStrategy ParityPlayer.even)
    (hτ :
      CountableParityGame.PositionalStrategy.WinningFrom
        (G := epochArena T tracking) τ (Sum.inl (Sum.inl initialBoundary))) :
    ∀ environment : EnvironmentCode T,
      roundAwareGameWins T initialBoundary
        (evenCommittedController T tracking τ) environment := by
  intro environment
  have hstep :
      ∀ n : Nat, ∃ e : EnvironmentRound In₁ In₂,
        roundAwareGameStateStream T initialBoundary
            (evenCommittedController T tracking τ) environment (n + 1) =
          contingentTransition T
            (roundAwareGameStateStream T initialBoundary
              (evenCommittedController T tracking τ) environment n)
            (evenCommittedController T tracking τ
              (roundAwareGameStateStream T initialBoundary
                (evenCommittedController T tracking τ) environment n)) e :=
    fun n =>
      ⟨environment
          (roundAwareGameStateStream T initialBoundary
            (evenCommittedController T tracking τ) environment n), by
        rw [roundAwareGameStateStream_succ,
          roundAwareGameTransition_eq_contingentTransition]⟩
  have hplayFrom :
      (epochArena T tracking).PlayFrom (Sum.inl (Sum.inl initialBoundary))
        (contingentPlayPath T
          (roundAwareGameStateStream T initialBoundary
            (evenCommittedController T tracking τ) environment)
          (fun n =>
            evenCommittedController T tracking τ
              (roundAwareGameStateStream T initialBoundary
                (evenCommittedController T tracking τ) environment n))) :=
    contingentPlayPath_playFrom T tracking _ _ hstep
  have hconsistent :=
    contingentPlayPath_consistent_even T tracking
      (roundAwareGameStateStream T initialBoundary
        (evenCommittedController T tracking τ) environment)
      (fun n =>
        evenCommittedController T tracking τ
          (roundAwareGameStateStream T initialBoundary
            (evenCommittedController T tracking τ) environment n))
      τ
      (fun n => evenCommittedController_spec T tracking τ _)
  have hEven :
      (epochArena T tracking).MinPriorityEven
        (contingentPlayPath T
          (roundAwareGameStateStream T initialBoundary
            (evenCommittedController T tracking τ) environment)
          (fun n =>
            evenCommittedController T tracking τ
              (roundAwareGameStateStream T initialBoundary
                (evenCommittedController T tracking τ) environment n))) := by
    have hwin := hτ _ hplayFrom hconsistent
    simpa [CountableParityGame.PlayerWinsPath] using hwin
  have hrun :
      ∀ n : Nat,
        tracking.stateOf
            (roundAwareGameStateStream T initialBoundary
              (evenCommittedController T tracking τ) environment n) =
          A.run
            (roundAwareGameExecution T initialBoundary
              (evenCommittedController T tracking τ) environment) n := by
    intro n
    have h := tracking.stateOf_stateStream_runFrom initialBoundary
      (evenCommittedController T tracking τ) environment n
    rw [hinitial] at h
    exact h
  have haccepts :
      A.Accepts
        (roundAwareGameExecution T initialBoundary
          (evenCommittedController T tracking τ) environment) :=
    (minPriorityEven_contingentPlayPath_iff_accepts T tracking _ _ _ hrun).mp
      hEven
  exact
    (roundAwareGameWins_iff_accepts_of_automaton_equiv T initialBoundary
        (evenCommittedController T tracking τ) environment A hautomaton).mpr
      haccepts

/-- **The full-information anchor, generic form.**  From a realizing
distributed strategy, the round-aware epoch game of any tracked transformer
has a controller winning against every finite environment code. -/
theorem exists_roundAwareWinner_of_realizable
    (initialBoundary : T.boundary)
    (hinitial : tracking.boundaryState initialBoundary = A.initial)
    (hautomaton :
      ∀ word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂),
        T.automaton.Accepts word ↔ A.Accepts word)
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (hσ : ∀ env : EnvironmentSequence In₁ In₂, A.Accepts (execution σ env)) :
    ∃ controller : RoundAwareControllerCode T,
      ∀ environment : EnvironmentCode T,
        roundAwareGameWins T initialBoundary controller environment := by
  obtain ⟨τ, hτ⟩ :=
    exists_evenPositionalWinner_of_realizable T tracking initialBoundary
      hinitial σ hσ
  exact
    ⟨evenCommittedController T tracking τ,
      roundAwareGameWins_evenCommittedController_of_winningFrom T tracking
        initialBoundary hinitial hautomaton τ hτ⟩

end Arena

end FiniteEpochTransformer

namespace DetParityAutomaton

open FiniteEpochTransformer

/-- **The full-information anchor of the theta-bar epoch game** (step (i) of
the finite-state-sufficiency argument for paper `prop:starcomplete`).  If a
distributed strategy realizes the objective automaton on every real
environment sequence, then the round-aware epoch game of the journal-shape
transformer has a (full-information) controller winning from the initial
boundary against **every** finite environment code.  The controller reads the
full game state; factoring it through the two summary observations is exactly
the residual content of `SummaryObservableWinnerCertificate`. -/
theorem exists_fullInfo_roundAwareWinner_of_realizable
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    (A :
      DetParityAutomaton.{max u v w a, max u v w a}
        (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (M : LocalSummaryAutomaton.{u, v, max u v w a} In₁ In₂)
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (hσ : ∀ env : EnvironmentSequence In₁ In₂, A.Accepts (execution σ env)) :
    ∃ controller :
        RoundAwareControllerCode
          (A.summaryEpochTransformer (Out₁ := Out₁) (Out₂ := Out₂) M),
      ∀ environment :
          EnvironmentCode
            (A.summaryEpochTransformer (Out₁ := Out₁) (Out₂ := Out₂) M),
        roundAwareGameWins (A.summaryEpochTransformer M)
          (A.summaryInitialBoundary M) controller environment :=
  exists_roundAwareWinner_of_realizable
    (A.summaryEpochTransformer (Out₁ := Out₁) (Out₂ := Out₂) M)
    (A.epochTransformerTracking.prodFst (M.carrier A))
    (A.summaryInitialBoundary M) rfl (fun _ => Iff.rfl) σ hσ

end DetParityAutomaton

end DistributedSynthesis
