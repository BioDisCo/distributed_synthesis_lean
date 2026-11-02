/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmArenaFold
import Mathlib.Data.Nat.Nth

/-!
# The boundary game's environment moves are exactly arena steps

At every Odd (environment) *block/reversal* position of the boundary game, a target is a
legal `boundaryStep` successor iff it is the `arenaStep` for some environment round: the
three `boundaryStep` disjuncts (continue / close / reverse, each over some input move) are
precisely the three `arenaStep` branches selected by the round's graph.  This is the first
step toward the converse of `accepts_arenaWord_of_winning`: a play consistent with a
committed strategy takes, at every environment position, an arena step, so the whole play
is an arena fold `gamePath` for the environment sequence its moves encode.  (The Even
boundary atom `Sum.inl` and the committed tier `Sum.inr (Sum.inl _)` are the two stutters
where `boundaryStep` and `arenaStep` deliberately differ -- Even commits a plan there --
and are handled separately in the converse.)

At a block/reversal position `arenaStep` reads the plan/chain/control *from the position
itself*, not from the plan family, so the correspondence is independent of `plans`.
-/

namespace DistributedSynthesis

universe u v x y s

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

namespace DetParityAutomaton

variable {A : DetParityAutomaton.{max u v x y, s} (RoundRecord In₁ In₂ Graph Out₁ Out₂)}
variable {C_L C_R C_V : Type max u v x y s}
variable (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)

/-- Environment moves at a within-left-block position are exactly arena steps. -/
theorem boundaryStep_iff_exists_arenaStep_inBlockL
    (plan : LeftBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) A C_L)
    (chain : ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) A C_L C_R C_V)
    (control : C_L) (state minState : A.State)
    (target : BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V) :
    boundaryStep A C_L C_R C_V
        (Sum.inr (Sum.inr (Sum.inl (plan, chain, control, state, minState)))) target ↔
      ∃ envRound : EnvironmentRound In₁ In₂,
        arenaStep plans
            (Sum.inr (Sum.inr (Sum.inl (plan, chain, control, state, minState))))
            envRound = target := by
  constructor
  · rintro (⟨move, rfl⟩ | ⟨move, rfl⟩ | ⟨move, rfl⟩)
    · exact ⟨⟨move.1, move.2, Graph.left⟩, rfl⟩
    · exact ⟨⟨move.1, move.2, Graph.both⟩, rfl⟩
    · exact ⟨⟨move.1, move.2, Graph.right⟩, rfl⟩
  · rintro ⟨envRound, rfl⟩
    simp only [arenaStep]
    cases envRound.graph with
    | left => exact Or.inl ⟨_, rfl⟩
    | right => exact Or.inr (Or.inr ⟨_, rfl⟩)
    | both => exact Or.inr (Or.inl ⟨_, rfl⟩)

/-- Environment moves at a within-right-block position are exactly arena steps. -/
theorem boundaryStep_iff_exists_arenaStep_inBlockR
    (plan : RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) A C_R)
    (chain : ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) A C_L C_R C_V)
    (control : C_R) (state minState : A.State)
    (target : BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V) :
    boundaryStep A C_L C_R C_V
        (Sum.inr (Sum.inr (Sum.inr (Sum.inl (plan, chain, control, state, minState))))) target ↔
      ∃ envRound : EnvironmentRound In₁ In₂,
        arenaStep plans
            (Sum.inr (Sum.inr (Sum.inr (Sum.inl (plan, chain, control, state, minState)))))
            envRound = target := by
  constructor
  · rintro (⟨move, rfl⟩ | ⟨move, rfl⟩ | ⟨move, rfl⟩)
    · exact ⟨⟨move.2, move.1, Graph.right⟩, rfl⟩
    · exact ⟨⟨move.2, move.1, Graph.both⟩, rfl⟩
    · exact ⟨⟨move.2, move.1, Graph.left⟩, rfl⟩
  · rintro ⟨envRound, rfl⟩
    simp only [arenaStep]
    cases envRound.graph with
    | right => exact Or.inl ⟨_, rfl⟩
    | both => exact Or.inr (Or.inl ⟨_, rfl⟩)
    | left => exact Or.inr (Or.inr ⟨_, rfl⟩)

/-- Environment moves at a reversed-left-block position are exactly arena steps. -/
theorem boundaryStep_iff_exists_arenaStep_inRevL
    (chain : ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) A C_L C_R C_V)
    (control : C_V) (entry : A.State × A.State) (state minState : A.State)
    (target : BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V) :
    boundaryStep A C_L C_R C_V
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (chain, control, entry, state, minState))))))
        target ↔
      ∃ envRound : EnvironmentRound In₁ In₂,
        arenaStep plans
            (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (chain, control, entry, state, minState))))))
            envRound = target := by
  constructor
  · rintro (⟨move, rfl⟩ | ⟨move, rfl⟩ | ⟨move, rfl⟩)
    · exact ⟨⟨move.1, move.2, Graph.left⟩, rfl⟩
    · exact ⟨⟨move.1, move.2, Graph.both⟩, rfl⟩
    · exact ⟨⟨move.1, move.2, Graph.right⟩, rfl⟩
  · rintro ⟨envRound, rfl⟩
    simp only [arenaStep]
    cases envRound.graph with
    | left => exact Or.inl ⟨_, rfl⟩
    | right => exact Or.inr (Or.inr ⟨_, rfl⟩)
    | both => exact Or.inr (Or.inl ⟨_, rfl⟩)

/-- Environment moves at a reversed-right-block position are exactly arena steps. -/
theorem boundaryStep_iff_exists_arenaStep_inRevR
    (chain : ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) A C_L C_R C_V)
    (control : C_V) (entry : A.State × A.State) (state minState : A.State)
    (target : BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V) :
    boundaryStep A C_L C_R C_V
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (chain, control, entry, state, minState))))))
        target ↔
      ∃ envRound : EnvironmentRound In₁ In₂,
        arenaStep plans
            (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (chain, control, entry, state, minState))))))
            envRound = target := by
  constructor
  · rintro (⟨move, rfl⟩ | ⟨move, rfl⟩ | ⟨move, rfl⟩)
    · exact ⟨⟨move.1, move.2, Graph.right⟩, rfl⟩
    · exact ⟨⟨move.1, move.2, Graph.both⟩, rfl⟩
    · exact ⟨⟨move.1, move.2, Graph.left⟩, rfl⟩
  · rintro ⟨envRound, rfl⟩
    simp only [arenaStep]
    cases envRound.graph with
    | right => exact Or.inl ⟨_, rfl⟩
    | both => exact Or.inr (Or.inl ⟨_, rfl⟩)
    | left => exact Or.inr (Or.inr ⟨_, rfl⟩)

/-- Environment moves at the committed tier are exactly the boundary resolutions
`committedResolve` -- the block the committed plan opens under the round's graph.  (Unlike
a block position, `arenaStep` self-loops at the committed tier; the game opens there, so
the target map is `committedResolve`, which is also `arenaStep` at the *preceding* `Sum.inl`
boundary, `arenaStep_bnd`.) -/
theorem boundaryStep_iff_exists_committedResolve
    (state state' : A.State)
    (plan : BoundaryPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
      A C_L C_R C_V)
    (target : BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V) :
    boundaryStep A C_L C_R C_V (Sum.inr (Sum.inl ((state, state'), plan))) target ↔
      ∃ envRound : EnvironmentRound In₁ In₂,
        committedResolve plan state envRound = target := by
  constructor
  · rintro (⟨move, rfl⟩ | ⟨move, rfl⟩ | ⟨move, rfl⟩)
    · exact ⟨⟨move.1, move.2, Graph.both⟩, rfl⟩
    · exact ⟨⟨move.1, move.2, Graph.left⟩, rfl⟩
    · exact ⟨⟨move.2, move.1, Graph.right⟩, rfl⟩
  · rintro ⟨envRound, rfl⟩
    simp only [committedResolve]
    cases envRound.graph with
    | both => exact Or.inl ⟨_, rfl⟩
    | left => exact Or.inr (Or.inl ⟨_, rfl⟩)
    | right => exact Or.inr (Or.inr ⟨_, rfl⟩)

/-! ### The unified game step

`gameAux`'s transition is: at an Even boundary atom commit `P`'s plan (no environment round
consumed); at the committed tier resolve to the opened block via `committedResolve`; at every
block/reversal position take the `arenaStep`.  We package this as one function `gameStepOf`,
turning the six-way case split into the two-way Even/Odd split the reconstruction needs. -/

/-- The unified one-step game transition read by `gameAux`. -/
def gameStepOf
    (P : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (pos : BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V)
    (envRound : EnvironmentRound In₁ In₂) :
    BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V :=
  match pos with
  | Sum.inl atom => Sum.inr (Sum.inl ((atom.1, atom.1), P atom))
  | Sum.inr (Sum.inl ((state, _), plan)) => committedResolve plan state envRound
  | Sum.inr (Sum.inr rest) =>
      arenaStep P (Sum.inr (Sum.inr rest)) envRound

/-- `gamePath` advances by the unified step, reading the environment at the current clock. -/
theorem gamePath_succ_eq
    (P : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) (k : Nat) :
    gamePath P env (k + 1) =
      gameStepOf P (gamePath P env k) (env (gameClock P env k)) := by
  rw [gamePath, gameAux, gameAux_pair]
  rcases gamePath P env k with atom | ⟨pair, plan⟩ | blockL | blockR | revL | revR
  · rcases atom with ⟨state, minState⟩; rfl
  · rcases pair with ⟨state, state'⟩; rfl
  · rfl
  · rfl
  · rfl
  · rfl

/-- The clock advances by one except at an Even boundary atom. -/
theorem gameClock_succ_eq
    (P : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) (k : Nat) :
    gameClock P env (k + 1) =
      gameClock P env k +
        Sum.elim (fun _ => 0) (fun _ => 1) (gamePath P env k) := by
  rw [gameClock, gameAux, gameAux_pair]
  rcases gamePath P env k with atom | ⟨pair, plan⟩ | blockL | blockR | revL | revR
  · rcases atom with ⟨state, minState⟩; rfl
  · rcases pair with ⟨state, state'⟩; rfl
  · rfl
  · rfl
  · rfl
  · rfl

/-- The game clock counts the Odd (environment-consuming) steps so far. -/
theorem gameClock_eq_count
    (P : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) (k : Nat) :
    gameClock P env k =
      Nat.count (fun j => (gamePath P env j).isRight = true) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [gameClock_succ_eq, ih, Nat.count_succ]
      rcases hp : gamePath P env k with atom | rest <;>
        simp only [hp, Sum.elim_inl, Sum.elim_inr, Sum.isRight_inl, Sum.isRight_inr,
          if_true, add_right_inj, reduceCtorEq, if_false]

/-- At every Odd (non-boundary-atom) position, the legal environment moves are exactly the
unified game steps: the five per-position bridges, packaged. -/
theorem boundaryStep_iff_exists_gameStepOf
    (P : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (pos : BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V)
    (target : BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V)
    (hpos : ∀ atom, pos ≠ Sum.inl atom) :
    boundaryStep A C_L C_R C_V pos target ↔
      ∃ envRound : EnvironmentRound In₁ In₂,
        gameStepOf P pos envRound = target := by
  rcases pos with atom | ⟨⟨state, state'⟩, plan⟩ |
    ⟨plan, chain, control, state, minState⟩ |
    ⟨plan, chain, control, state, minState⟩ |
    ⟨chain, control, entry, state, minState⟩ |
    ⟨chain, control, entry, state, minState⟩
  · exact absurd rfl (hpos atom)
  · exact boundaryStep_iff_exists_committedResolve state state' plan target
  · exact boundaryStep_iff_exists_arenaStep_inBlockL P plan chain control state minState target
  · exact boundaryStep_iff_exists_arenaStep_inBlockR P plan chain control state minState target
  · exact boundaryStep_iff_exists_arenaStep_inRevL P chain control entry state minState target
  · exact boundaryStep_iff_exists_arenaStep_inRevR P chain control entry state minState target

/-! ### Priority transfer: a game path is min-even iff its arena word is accepted -/

section Objective

variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
  [DecidableEq In₁] [DecidableEq In₂] [DecidableEq A.State]
  [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
  [Fintype C_L] [DecidableEq C_L] [Inhabited C_L]
  [Fintype C_R] [DecidableEq C_R] [Inhabited C_R]
  [Fintype C_V] [DecidableEq C_V] [Inhabited C_V]

/-- The objective transfer, both directions: a boundary-game path is min-priority-even iff
the arena word it folds is accepted by the objective automaton.  The forward direction is
the core of `accepts_arenaWord_of_winning`; both directions come from the recurring-priority
transfer, generalized off any winning hypothesis to an arbitrary plan family. -/
theorem minPriorityEven_gamePath_iff_accepts
    (env : EnvironmentSequence In₁ In₂) :
    (DetParityAutomaton.boundaryGame A C_L C_R C_V).MinPriorityEven
        (gamePath plans env) ↔
      A.Accepts (arenaWord plans env) := by
  rw [DetParityAutomaton.accepts_iff_natSeqMinEvenParity]
  exact
    natSeqMinEvenParity_iff_of_recurring_transfer
      (fun k => boundaryPriority A C_L C_R C_V (gamePath plans env k))
      (fun t => A.priority (A.run (arenaWord plans env) t))
      (fun w hw => seenInfinitelyOften_run_of_gamePath plans env hw)
      (fun v hv n => by
        obtain ⟨t, htn, hvt⟩ := hv n
        obtain ⟨k, hkt, hkp⟩ := exists_gamePriority_emission plans env t
        exact ⟨k, by omega, Nat.le_of_eq (hkp.trans hvt)⟩)

/-! ### Local structure of a consistent play

Every step of a play consistent with `committingStrategy P` is one of the two shapes: at an
Even boundary atom the strategy commits `P`'s plan; at every other (Odd) position the play
takes an environment move, i.e. an arena step (blocks/reversals) or a boundary resolution
(committed tier).  These are the per-step building blocks of the converse of
`accepts_arenaWord_of_winning`. -/

/-- At an Even boundary atom, a play consistent with `committingStrategy P` commits `P`'s
plan (the Even move fixed by the strategy). -/
theorem committingStrategy_bnd_step
    (P : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (path : Nat -> BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V) (n : Nat)
    (state minState : A.State)
    (hcons :
      CountableParityGame.PositionalStrategy.Consistent
        (G := DetParityAutomaton.boundaryGame A C_L C_R C_V)
        (committingStrategy P) path)
    (hpath : path n = Sum.inl (state, minState)) :
    path (n + 1) = Sum.inr (Sum.inl ((state, state), P (state, minState))) := by
  have howner :
      (DetParityAutomaton.boundaryGame A C_L C_R C_V).owner (path n) =
        ParityPlayer.even := by
    rw [hpath]; simp [DetParityAutomaton.boundaryGame, boundaryOwner]
  rw [hcons n howner, hpath]; rfl

/-- `Nat.count` depends only on the predicate's values below the bound. -/
theorem count_congr_lt {p q : ℕ → Prop} [DecidablePred p] [DecidablePred q]
    (n : ℕ) (h : ∀ i < n, (p i ↔ q i)) : Nat.count p n = Nat.count q n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Nat.count_succ, Nat.count_succ, ih (fun i hi => h i (Nat.lt_succ_of_lt hi))]
      by_cases hpn : p n
      · rw [if_pos hpn, if_pos ((h n (Nat.lt_succ_self n)).mp hpn)]
      · rw [if_neg hpn, if_neg (fun hq => hpn ((h n (Nat.lt_succ_self n)).mpr hq))]

/-- **The reconstruction (converse core).**  Every play consistent with `committingStrategy P`
from the initial boundary *is* the game path `gamePath P env` for the environment sequence its
environment moves encode.  The environment round consumed at each Odd step is extracted by the
unified bridge; assembled by `Nat.nth` over the Odd (`isRight`) steps, it reproduces the play
because the game clock counts exactly those steps (`gameClock_eq_count`, `Nat.nth_count`). -/
theorem exists_env_gamePath_eq_of_consistent
    (P : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (path : Nat -> BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V)
    (hstart : path 0 = Sum.inl (A.initial, A.initial))
    (hstep : ∀ k, boundaryStep A C_L C_R C_V (path k) (path (k + 1)))
    (hcons :
      CountableParityGame.PositionalStrategy.Consistent
        (G := DetParityAutomaton.boundaryGame A C_L C_R C_V)
        (committingStrategy P) path) :
    ∃ env : EnvironmentSequence In₁ In₂, ∀ k, path k = gamePath P env k := by
  have hround : ∀ k, (path k).isRight = true ->
      ∃ r : EnvironmentRound In₁ In₂, gameStepOf P (path k) r = path (k + 1) := by
    intro k hk
    have hne : ∀ atom, path k ≠ Sum.inl atom := by
      intro atom heq; rw [heq] at hk; simp at hk
    exact (boundaryStep_iff_exists_gameStepOf P (path k) (path (k + 1)) hne).mp (hstep k)
  set isR : ℕ → Prop := fun k => (path k).isRight = true with hisRdef
  set roundAt : ℕ → EnvironmentRound In₁ In₂ :=
    fun k => if hk : isR k then (hround k hk).choose else ⟨default, default, Graph.left⟩
    with hroundAt
  set env : EnvironmentSequence In₁ In₂ := fun t => roundAt (Nat.nth isR t) with henv
  refine ⟨env, ?_⟩
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => rw [hstart]; rfl
    | Nat.succ k' =>
      have ihk' : path k' = gamePath P env k' := ih k' (Nat.lt_succ_self k')
      rw [gamePath_succ_eq, ← ihk']
      rcases hpk : path k' with ⟨s, m⟩ | rest
      · rw [committingStrategy_bnd_step P path k' s m hcons hpk]; rfl
      · have hkOdd : isR k' := by simp [hisRdef, hpk]
        have hround' := (hround k' hkOdd).choose_spec
        have hclock : gameClock P env k' = Nat.count isR k' := by
          rw [gameClock_eq_count]
          exact count_congr_lt k' (fun j hj => by
            simp only [hisRdef]; rw [← ih j (Nat.lt_succ_of_lt hj)])
        rw [← hpk, hclock]
        simp only [henv, Nat.nth_count hkOdd, hroundAt]
        rw [dif_pos hkOdd]
        exact hround'.symm

/-- **The converse of `accepts_arenaWord_of_winning`.**  If the arena word of a committed plan
family is accepted on *every* environment, then the committing positional strategy is winning
from the initial boundary: every consistent play is a game path (`exists_env_gamePath_eq_of_consistent`),
and each game path is min-even because its arena word is accepted (`minPriorityEven_gamePath_iff_accepts`). -/
theorem winningFrom_committingStrategy_of_accepts
    (P : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (hacc : ∀ env : EnvironmentSequence In₁ In₂, A.Accepts (arenaWord P env)) :
    CountableParityGame.PositionalStrategy.WinningFrom
      (G := DetParityAutomaton.boundaryGame A C_L C_R C_V)
      (committingStrategy P) (Sum.inl (A.initial, A.initial)) := by
  intro path hplay hcons
  obtain ⟨hstart, hstep⟩ := hplay
  obtain ⟨env, henv⟩ :=
    exists_env_gamePath_eq_of_consistent P path hstart hstep hcons
  rw [show path = gamePath P env from funext henv]
  exact (minPriorityEven_gamePath_iff_accepts P env).mpr (hacc env)

end Objective

end DetParityAutomaton

end DistributedSynthesis
