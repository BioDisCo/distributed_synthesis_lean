/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmZielonkaCountableParity

/-!
# Observation-based positional strategies and belief updates

`ObservationBasedPositional` requires a positional strategy to respect an
observation map. `fmExtraction_of_injective_obs` proves the existence of such
a winning strategy when the observation map is injective, using positional
determinacy of countable parity games.

`ActionObservationParityGame` supplies a state/action/environment model,
memoryless observation-based strategies, and their winning predicate.
For finite state and environment spaces, the belief update collects exactly
the successors compatible with an action and a received observation.
The file proves its membership, observation-consistency, and arena-totality
properties. It does not assert a general parity-winning transfer from the
belief arena.
-/

namespace DistributedSynthesis

namespace CountableParityGame

universe u w

variable (G : CountableParityGame.{u}) {Obs : Type w}

/-- A positional strategy is **observation-based** for an observation map `obs` when it respects the
observation quotient: positions the player cannot distinguish (same `obs`) move to positions it cannot
distinguish.  This is the memoryless, `obs`-reproducible strategy the summary-observability certificate
demands (`obs` := the process's summary; indistinguishable positions differ only by the hidden bit). -/
def ObservationBasedPositional {player : ParityPlayer}
    (obs : G.Position -> Obs) (s : G.PositionalStrategy player) : Prop :=
  ∀ p q : G.Position, obs p = obs q -> obs (s.move p) = obs (s.move q)

/-- **The finite-memory extraction target**: from every position of the player's winning region, a
*single* observation-based positional strategy wins.  For the θ̄-game with `obs` the process summary,
this is exactly `SummaryObservableWinnerCertificate` (a memoryless summary-observable winner exists
whenever the objective is realizable). -/
def FiniteMemoryExtractionTarget
    (obs : G.Position -> Obs) (player : ParityPlayer) : Prop :=
  ∃ s : G.PositionalStrategy player,
    G.ObservationBasedPositional obs s ∧
      PositionalStrategy.WinningOn (G := G) s (G.WinningRegion player)

/-- **Base case (perfect information): the extraction holds when the observation is injective.**  If
`obs` distinguishes every position, the observation quotient is trivial, so the uniform positional
winner supplied by the proved determinacy (`uniformPositionalDeterminacy`) is vacuously
observation-based.  The substantive project is the non-injective (genuinely blind) case, handled by the
hierarchical knowledge construction; this base case fixes the framework and the determinacy engine. -/
theorem fmExtraction_of_injective_obs
    (obs : G.Position -> Obs) (hinj : Function.Injective obs)
    (player : ParityPlayer) :
    G.FiniteMemoryExtractionTarget obs player := by
  obtain ⟨s, hs⟩ := G.uniformPositionalDeterminacy player
  exact ⟨s, fun p q hpq => by rw [hinj hpq], hs⟩

end CountableParityGame

/-!
## The action-observation game model

An imperfect-information turn-based parity game: at a protagonist position the protagonist picks an
`Action` seeing only the `Obs`ervation; the environment then picks an `Env` response (resolving the
hidden information) and the play advances by `next`.  The objective is parity on the visited states.

We give the model its semantics by **embedding it into a `CountableParityGame`** (`toGame`), so plays,
the parity winning condition, and -- crucially -- the proved positional determinacy all transfer for
free.  A protagonist position is a `State`; an environment position is a `State × Action` (the state
together with the action just committed).  This is the arena on which the belief construction and the
finite-memory extraction will run.
-/

/-- An imperfect-information turn-based parity game with explicit actions and observations. -/
structure ActionObservationParityGame where
  State : Type u
  Action : Type u
  Env : Type u
  Obs : Type v
  [stateCountable : Countable State]
  [actionCountable : Countable Action]
  [actionInhabited : Inhabited Action]
  [envInhabited : Inhabited Env]
  /-- What the protagonist observes at a state (its summary). -/
  obs : State -> Obs
  /-- The deterministic successor given the protagonist's action and the environment's response. -/
  next : State -> Action -> Env -> State
  /-- The parity priority of a state. -/
  priority : State -> Nat
  priority_finite : Set.Finite (Set.range priority)

namespace ActionObservationParityGame

variable (M : ActionObservationParityGame.{u, v})

attribute [instance] stateCountable actionCountable actionInhabited envInhabited

/-- A position of the embedded game: a protagonist `State` (`Sum.inl`) or an environment
`State × Action` (`Sum.inr`, the committed action awaiting the environment's response). -/
abbrev Pos := M.State ⊕ (M.State × M.Action)

/-- The embedding of the action-observation game into a `CountableParityGame`.  Protagonist positions
are owned by `even`, environment positions by `odd`; a protagonist commits an action (moving to the
paired environment position), and the environment picks a response (moving to the next state).  Both
position kinds carry the priority of their underlying state, so the min-priority-infinitely-often
condition is the parity objective on the visited states. -/
def toGame : CountableParityGame.{u} where
  Position := M.Pos
  positionCountable := inferInstance
  owner := Sum.elim (fun _ => ParityPlayer.even) (fun _ => ParityPlayer.odd)
  step p q :=
    match p, q with
    | Sum.inl s, Sum.inr sa => sa.1 = s
    | Sum.inr sa, Sum.inl s' => ∃ e : M.Env, s' = M.next sa.1 sa.2 e
    | _, _ => False
  step_total p := by
    cases p with
    | inl s => exact ⟨Sum.inr (s, default), rfl⟩
    | inr sa => exact ⟨Sum.inl (M.next sa.1 sa.2 default), default, rfl⟩
  priority := Sum.elim M.priority fun sa => M.priority sa.1
  priority_finite := by
    apply M.priority_finite.subset
    rintro _ ⟨p, rfl⟩
    cases p with
    | inl s => exact ⟨s, rfl⟩
    | inr sa => exact ⟨sa.1, rfl⟩

/-- The observation lifted to embedded positions: a protagonist position shows its state's
observation; environment positions are transient (they carry no protagonist choice) and are sent to a
default, so the protagonist's observable is exactly `obs` at its own positions. -/
def posObs [Inhabited M.Obs] : M.Pos -> M.Obs :=
  Sum.elim M.obs fun _ => default

/-- A **memoryless observation-based** protagonist strategy: it commits an action as a function of the
current observation alone.  This is the summary-observable strategy the certificate demands (`Obs` is
the process summary). -/
abbrev MStrategy := M.Obs -> M.Action

/-- The positional strategy on the embedded game induced by a memoryless observation-based strategy:
at a protagonist position `s` it commits action `m (obs s)`; environment positions (owned by `odd`)
get an arbitrary legal move it never uses.  By construction its action depends only on the
observation, so it is summary-observable. -/
def toPositional (m : M.MStrategy) :
    M.toGame.PositionalStrategy ParityPlayer.even where
  move p :=
    match p with
    | Sum.inl s => Sum.inr (s, m (M.obs s))
    | Sum.inr sa => Sum.inl (M.next sa.1 sa.2 default)
  legal p hp := by
    cases p with
    | inl s => exact rfl
    | inr sa => exact absurd hp (by simp [toGame])

/-- A memoryless observation-based strategy **wins** from a start state when its induced positional
strategy wins the embedded game from the protagonist position. -/
def MWins (m : M.MStrategy) (start : M.State) : Prop :=
  CountableParityGame.PositionalStrategy.WinningFrom (G := M.toGame)
    (M.toPositional m) (Sum.inl start)

/-- **The finite-memory determinacy target for the action-observation game.**  Whenever the
protagonist wins from `start` by *any* strategy (i.e. the position is in its winning region), it wins
by a memoryless observation-based one.  For the θ̄-game with `obs` the process summary, this is exactly
`SummaryObservableWinnerCertificate`.  The perfect-information case is the base case above; the
substantive project is this target for a genuinely blind (non-injective) `obs`, via the hierarchical
knowledge/belief construction on `toGame` and the proved positional determinacy. -/
def FiniteMemoryDeterminacy (start : M.State) : Prop :=
  Sum.inl start ∈ M.toGame.WinningRegion ParityPlayer.even ->
    ∃ m : M.MStrategy, M.MWins m start

/-!
### The knowledge (belief) construction -- foundation

For a finite game the protagonist's **knowledge** after a run of observations is the set of states
consistent with what it observed.  A move by the protagonist (action `a`) followed by the next
observation `o` updates the knowledge to the states reachable under `a` that show `o` (`beliefUpdate`).
The foundational correctness property is `mem_beliefUpdate`: the *actual* next state always lies in the
updated knowledge -- the belief soundly over-approximates the true state.  For the ≤1-bit hierarchical
case (`thm:onebitfringe`) every reachable knowledge set has at most two elements, so the belief game
over these finite sets is finite; positional determinacy on it, then transfer, is the remaining core.
-/

variable [Fintype M.State] [DecidableEq M.State] [Fintype M.Env] [DecidableEq M.Obs]

/-- The one-step reachable set from a state under a fixed protagonist action, over all environment
responses. -/
def successors (s : M.State) (a : M.Action) : Finset M.State :=
  Finset.univ.image fun e : M.Env => M.next s a e

/-- The **belief update**: from knowledge set `B`, after the protagonist plays `a` and the next
observation is `o`, the new knowledge is the states reachable from `B` under `a` that show `o`. -/
def beliefUpdate (B : Finset M.State) (a : M.Action) (o : M.Obs) : Finset M.State :=
  (B.biUnion fun s => M.successors s a).filter fun s' => M.obs s' = o

omit [Fintype M.State] in
/-- **Soundness of the belief update**: whenever the actual current state lies in the knowledge set,
the actual next state lies in the updated knowledge.  So along any play the true state is always in the
current belief -- the invariant that makes an observation-based strategy on beliefs faithful. -/
theorem mem_beliefUpdate (B : Finset M.State) (a : M.Action) (e : M.Env)
    {s : M.State} (hs : s ∈ B) :
    M.next s a e ∈ M.beliefUpdate B a (M.obs (M.next s a e)) := by
  unfold beliefUpdate successors
  refine Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨s, hs, ?_⟩, rfl⟩
  exact Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩

omit [Fintype M.State] in
/-- Every state in a belief update shows the update's observation and is reachable from the belief:
the belief update contains exactly the observation-`o` one-step successors of `B`. -/
theorem beliefUpdate_subset_obs (B : Finset M.State) (a : M.Action) (o : M.Obs)
    {s' : M.State} (hs' : s' ∈ M.beliefUpdate B a o) :
    M.obs s' = o := by
  simp only [beliefUpdate, Finset.mem_filter] at hs'
  exact hs'.2

/-!
### The belief game -- arena

A **belief** is a nonempty knowledge set.  The belief game's arena mirrors `toGame` but over beliefs:
a protagonist belief position commits an action; an environment belief-action position advances to any
belief obtainable as a `beliefUpdate` under some observation.  Ownership matches `toGame` (protagonist
`even`, environment `odd`), and the arena is total (`beliefStep_total`), the environment successor
existing because the actual next state always lands in some nonempty updated belief (`mem_beliefUpdate`).

This builds the arena; **the remaining crux is the parity condition** -- a priority on beliefs whose
min-infinitely-often coincides with the protagonist winning against *every* actual play consistent with
its observations.  For ≤1-bit hierarchical games that lifting is sound (the hidden bit is resolved
infinitely often, collapsing the belief to a singleton), and proving it is the genuine
Berwanger-specific step; it is deliberately not asserted here. -/

/-- A **belief**: a nonempty knowledge set. -/
abbrev Belief := {B : Finset M.State // B.Nonempty}

/-- Belief-game positions: a protagonist belief (`Sum.inl`) or an environment belief-action pair. -/
abbrev BeliefPos := M.Belief ⊕ (M.Belief × M.Action)

/-- The belief-game arena: the protagonist commits an action; the environment advances to any belief
reachable as a `beliefUpdate` under some observation. -/
def beliefStep : M.BeliefPos -> M.BeliefPos -> Prop
  | Sum.inl B, Sum.inr Ba => Ba.1 = B
  | Sum.inr Ba, Sum.inl B' => ∃ o : M.Obs, B'.1 = M.beliefUpdate Ba.1.1 Ba.2 o
  | _, _ => False

/-- Ownership in the belief game: protagonist beliefs to `even`, environment positions to `odd`. -/
def beliefOwner : M.BeliefPos -> ParityPlayer :=
  Sum.elim (fun _ => ParityPlayer.even) fun _ => ParityPlayer.odd

omit [Fintype M.State] in
/-- **The belief arena is total.**  From a protagonist belief the default action advances; from an
environment position the actual next state (from some state in the nonempty belief) lands in a nonempty
updated belief (`mem_beliefUpdate`), so an environment successor always exists. -/
theorem beliefStep_total (p : M.BeliefPos) : ∃ q, M.beliefStep p q := by
  cases p with
  | inl B => exact ⟨Sum.inr (B, default), rfl⟩
  | inr Ba =>
    obtain ⟨s, hs⟩ := Ba.1.2
    exact
      ⟨Sum.inl ⟨M.beliefUpdate Ba.1.1 Ba.2 (M.obs (M.next s Ba.2 default)),
          ⟨M.next s Ba.2 default, M.mem_beliefUpdate Ba.1.1 Ba.2 default hs⟩⟩,
        M.obs (M.next s Ba.2 default), rfl⟩

end ActionObservationParityGame

end DistributedSynthesis
