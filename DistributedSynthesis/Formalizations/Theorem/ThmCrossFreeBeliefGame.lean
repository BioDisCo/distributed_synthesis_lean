/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmDynamicHierarchyFiniteState
import DistributedSynthesis.Formalizations.Theorem.ThmDynamicHierarchyCrossing
import DistributedSynthesis.Formalizations.Theorem.ThmBundleDeterminization

/-!
# Belief updates and membership

A belief is the set of game states compatible with a player's observations.
The update uses that player's action and next observation, quantifies over
the partner's action and the environment move, and filters by the observed
value. The membership invariant proves that the true state of any
compatible distributed play remains in the tracked belief.
These results concern state tracking; they do not assert a parity-winning
strategy transfer.
-/

namespace DistributedSynthesis

universe u

namespace FiniteConcurrentGame

variable (G : FiniteConcurrentGame.{u})

open Classical

/-- A belief: the finite set of game states a player considers possible. -/
abbrev Belief := Finset G.State

/-- The initial belief: the game start is common knowledge. -/
def beliefInitial : G.Belief := {G.initial}

/-- Player one's belief update.  Player one commits its own action `a1` and then
observes `o1`; it does not see the partner's action or Nature's move, so the
successor ranges over both and is filtered by the observation seen. -/
noncomputable def beliefStep1 (K : G.Belief) (a1 : G.Action1)
    (o1 : G.Observation1) : G.Belief :=
  Finset.univ.filter fun t =>
    (∃ s ∈ K, ∃ (a2 : G.Action2) (env : G.Nature), G.next s a1 a2 env = t) ∧
      G.observe1 t = o1

/-- Player two's belief update: the orientation mirror of `beliefStep1`. -/
noncomputable def beliefStep2 (K : G.Belief) (a2 : G.Action2)
    (o2 : G.Observation2) : G.Belief :=
  Finset.univ.filter fun t =>
    (∃ s ∈ K, ∃ (a1 : G.Action1) (env : G.Nature), G.next s a1 a2 env = t) ∧
      G.observe2 t = o2

theorem mem_beliefStep1 (K : G.Belief) (a1 : G.Action1) (o1 : G.Observation1)
    (t : G.State) :
    t ∈ G.beliefStep1 K a1 o1 ↔
      (∃ s ∈ K, ∃ (a2 : G.Action2) (env : G.Nature), G.next s a1 a2 env = t) ∧
        G.observe1 t = o1 := by
  simp [beliefStep1]

theorem mem_beliefStep2 (K : G.Belief) (a2 : G.Action2) (o2 : G.Observation2)
    (t : G.State) :
    t ∈ G.beliefStep2 K a2 o2 ↔
      (∃ s ∈ K, ∃ (a1 : G.Action1) (env : G.Nature), G.next s a1 a2 env = t) ∧
        G.observe2 t = o2 := by
  simp [beliefStep2]

/-- Player one's belief trajectory along a real distributed play: start from the
common initial belief and update by player one's own action and observed letter
at each round. -/
noncomputable def beliefAlong1 (strategy : G.HistoryProductStrategy)
    (nature : Nat -> G.Nature) : Nat -> G.Belief
  | 0 => G.beliefInitial
  | n + 1 =>
      G.beliefStep1 (beliefAlong1 strategy nature n)
        (strategy.1 (G.strategyState strategy nature n).2.1)
        (G.observe1 (G.strategyState strategy nature (n + 1)).1)

/-- Player two's belief trajectory: the mirror of `beliefAlong1`. -/
noncomputable def beliefAlong2 (strategy : G.HistoryProductStrategy)
    (nature : Nat -> G.Nature) : Nat -> G.Belief
  | 0 => G.beliefInitial
  | n + 1 =>
      G.beliefStep2 (beliefAlong2 strategy nature n)
        (strategy.2 (G.strategyState strategy nature n).2.2)
        (G.observe2 (G.strategyState strategy nature (n + 1)).1)

/-- **Invariant (I1), player one.**  Along any real distributed play, the true
current state is a live member of player one's tracked belief. -/
theorem mem_beliefAlong1 (strategy : G.HistoryProductStrategy)
    (nature : Nat -> G.Nature) (n : Nat) :
    (G.strategyState strategy nature n).1 ∈ G.beliefAlong1 strategy nature n := by
  induction n with
  | zero => simp [beliefAlong1, beliefInitial, strategyState]
  | succ n ih =>
      rw [beliefAlong1, mem_beliefStep1]
      refine ⟨⟨(G.strategyState strategy nature n).1, ih,
        strategy.2 (G.strategyState strategy nature n).2.2, nature n, rfl⟩, rfl⟩

/-- **Invariant (I1), player two.**  The orientation mirror of
`mem_beliefAlong1`. -/
theorem mem_beliefAlong2 (strategy : G.HistoryProductStrategy)
    (nature : Nat -> G.Nature) (n : Nat) :
    (G.strategyState strategy nature n).1 ∈ G.beliefAlong2 strategy nature n := by
  induction n with
  | zero => simp [beliefAlong2, beliefInitial, strategyState]
  | succ n ih =>
      rw [beliefAlong2, mem_beliefStep2]
      refine ⟨⟨(G.strategyState strategy nature n).1, ih,
        strategy.1 (G.strategyState strategy nature n).2.1, nature n, rfl⟩, rfl⟩

/-! ### Leadership at the belief level (I2 foundation)

Which player leads is a function of the belief alone: player one leads when, among
the states the belief admits, player one's observation determines player two's.
This is the belief-level image of `OneDeterminesTwoAt`, and it is what the
belief-game transition reads to decide whose action is committed directly and
whose is committed as an observation-indexed table.  It is monotone: refining
the belief (a subset) can only make determination easier, which is the shape of
clause (I2) -- leadership, once established, is preserved as the belief shrinks
between the tie points where it may hand over. -/

/-- Player one determines player two on the belief `K`: any two admitted states
sharing player one's observation share player two's. -/
def determinesOnBelief1 (K : G.Belief) : Prop :=
  ∀ s ∈ K, ∀ t ∈ K, G.observe1 s = G.observe1 t -> G.observe2 s = G.observe2 t

/-- Player two determines player one on the belief `K`: the orientation mirror. -/
def determinesOnBelief2 (K : G.Belief) : Prop :=
  ∀ s ∈ K, ∀ t ∈ K, G.observe2 s = G.observe2 t -> G.observe1 s = G.observe1 t

/-- The belief is hierarchical when one player determines the other on it: the
belief-level comparability of information, the invariant a crossing-free game
maintains. -/
def beliefHierarchical (K : G.Belief) : Prop :=
  G.determinesOnBelief1 K ∨ G.determinesOnBelief2 K

/-- **Leadership is monotone under refinement.**  If player one determines player
two on `K'`, it still does on any subset `K` -- the shape of clause (I2). -/
theorem determinesOnBelief1_mono {K K' : G.Belief} (h : K ⊆ K')
    (hd : G.determinesOnBelief1 K') : G.determinesOnBelief1 K :=
  fun s hs t ht hobs => hd s (h hs) t (h ht) hobs

/-- The orientation mirror of `determinesOnBelief1_mono`. -/
theorem determinesOnBelief2_mono {K K' : G.Belief} (h : K ⊆ K')
    (hd : G.determinesOnBelief2 K') : G.determinesOnBelief2 K :=
  fun s hs t ht hobs => hd s (h hs) t (h ht) hobs

/-- Determination on a belief is decidable, so a finite belief game can branch on
the leader.  (Classical, matching the noncomputable belief construction; a
computable instance would ask `DecidableEq` on the observation types.) -/
noncomputable instance decidableDeterminesOnBelief1 (K : G.Belief) :
    Decidable (G.determinesOnBelief1 K) := by
  classical
  unfold determinesOnBelief1
  infer_instance

noncomputable instance decidableDeterminesOnBelief2 (K : G.Belief) :
    Decidable (G.determinesOnBelief2 K) := by
  classical
  unfold determinesOnBelief2
  infer_instance

/-! ### Parity coherence (I4) via the universal-run bundle

The belief game cannot score parity by a minimum over the belief set: a limit
condition does not distribute over a set.  Instead the objective is carried by
the proven bundle determinization (`ThmBundleDeterminization.lean`): a finite
thread system whose runs are the state trajectories consistent with the
observation word, and whose universal parity automaton accepts exactly the
words on which **every** consistent trajectory is min-even.  Clause (I4) is that
the real play is one such trajectory, so bundle acceptance of the play's own
observation word forces the real play to win.

Threads carry the committed own-action and the observed letter; the partner's
action and Nature are the hidden resolution.  A resolution whose induced
observation disagrees with the letter falls to an even sink, so only fully
consistent trajectories carry the game's parity. -/

/-- Player one's bundle thread step: from a live state, apply the committed own
action `letter.1` and the hidden partner action and Nature; keep the successor
only if its observation matches the observed letter `letter.2`, otherwise fall
to the even sink `none`. -/
noncomputable def beliefThreadStep1
    (st : Option G.State) (letter : G.Action1 × G.Observation1)
    (res : G.Action2 × G.Nature) : Option G.State :=
  match st with
  | some s =>
      if G.observe1 (G.next s letter.1 res.1 res.2) = letter.2 then
        some (G.next s letter.1 res.1 res.2)
      else none
  | none => none

/-- Player one's bundle thread system over the alphabet of committed own action
and observed letter. -/
noncomputable def beliefThreadSystem1 :
    FiniteThreadSystem.{u, u, u} (G.Action1 × G.Observation1) where
  State := Option G.State
  stateFinite := inferInstance
  initial := some G.initial
  Resolution := G.Action2 × G.Nature
  step := G.beliefThreadStep1
  priority := fun st =>
    match st with
    | some s => G.priority s
    | none => 0

/-- The universal-run bundle DPA of player one's thread system: it accepts an
observation word iff every consistent state trajectory is min-even. -/
noncomputable def beliefBundle1 :
    DetParityAutomaton.{u, u} (G.Action1 × G.Observation1) :=
  G.beliefThreadSystem1.universalRunDPA

/-- The observation word emitted by a real distributed play, tracking player
one: at each round, the committed own action and player one's next observation. -/
def beliefLetterWord1 (strategy : G.HistoryProductStrategy)
    (nature : Nat -> G.Nature) : OmegaWord (G.Action1 × G.Observation1) :=
  fun n =>
    (strategy.1 (G.strategyState strategy nature n).2.1,
      G.observe1 (G.strategyState strategy nature (n + 1)).1)

/-- **The belief is a Moore memory.**  Folding the belief update over a finite
sequence of observed letters computes the belief; this is the finite state a
Moore controller carries.  Its agreement with the play-driven trajectory
(`beliefAlong1_eq_beliefFold1`) is what lets a belief-game winner be read back
as a finite-memory strategy. -/
noncomputable def beliefFold1 (letters : List (G.Action1 × G.Observation1)) :
    G.Belief :=
  letters.foldl (fun K letter => G.beliefStep1 K letter.1 letter.2) G.beliefInitial

/-- The play-driven belief trajectory is the Moore fold of the observed letters:
the belief at round `n` is a function of the first `n` letters alone. -/
theorem beliefAlong1_eq_beliefFold1 (strategy : G.HistoryProductStrategy)
    (nature : Nat -> G.Nature) (n : Nat) :
    G.beliefAlong1 strategy nature n =
      G.beliefFold1 ((List.range n).map (G.beliefLetterWord1 strategy nature)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [beliefAlong1, ih]
      simp only [beliefFold1, beliefLetterWord1, List.range_succ, List.map_append,
        List.map_cons, List.map_nil, List.foldl_append, List.foldl_cons,
        List.foldl_nil]

/-- The real play as a thread of the bundle: the true state at each round. -/
def realThread1 (strategy : G.HistoryProductStrategy)
    (nature : Nat -> G.Nature) : Nat -> Option G.State :=
  fun n => some (G.strategyState strategy nature n).1

/-- **The real play is a consistent bundle thread.**  It starts at the initial
state and each round is realized by the partner's committed action and Nature's
move, with the observation matching the emitted letter. -/
theorem realThread1_isRun (strategy : G.HistoryProductStrategy)
    (nature : Nat -> G.Nature) :
    G.beliefThreadSystem1.IsRun (G.beliefLetterWord1 strategy nature)
      (G.realThread1 strategy nature) := by
  refine ⟨rfl, ?_⟩
  intro n
  refine ⟨(strategy.2 (G.strategyState strategy nature n).2.2, nature n), ?_⟩
  show G.realThread1 strategy nature (n + 1) =
    G.beliefThreadStep1 (G.realThread1 strategy nature n)
      (G.beliefLetterWord1 strategy nature n) _
  simp only [realThread1, beliefThreadStep1, beliefLetterWord1]
  have hcond : G.observe1 (G.next (G.strategyState strategy nature n).1
        (strategy.1 (G.strategyState strategy nature n).2.1)
        (strategy.2 (G.strategyState strategy nature n).2.2) (nature n)) =
      G.observe1 (G.strategyState strategy nature (n + 1)).1 := rfl
  rw [if_pos hcond]
  rfl

/-- The bundle priority of the real thread is the game priority of the real
state. -/
theorem beliefThreadSystem1_priority_realThread1
    (strategy : G.HistoryProductStrategy) (nature : Nat -> G.Nature) (n : Nat) :
    G.beliefThreadSystem1.priority (G.realThread1 strategy nature n) =
      G.priority (G.strategyState strategy nature n).1 := rfl

/-- `ParityAccepts` (the game winning condition) is the bundle's
`NatSeqMinEvenParity`; they differ only in spelling evenness. -/
theorem parityAccepts_iff_natSeqMinEvenParity (s : Nat -> Nat) :
    ParityAccepts s ↔ NatSeqMinEvenParity s := by
  unfold ParityAccepts NatSeqMinEvenParity DetParityAutomaton.NatEven
    PriorityInfinitelyOften NatSeqSeenInfinitelyOften
  constructor
  · rintro ⟨p, hp, hinf, hmin⟩
    exact ⟨p, ⟨p / 2, by omega⟩, hinf, hmin⟩
  · rintro ⟨p, ⟨m, hm⟩, hinf, hmin⟩
    exact ⟨p, by omega, hinf, hmin⟩

/-- **Invariant (I4), player one, soundness direction.**  If the bundle DPA
accepts the observation word of a real play, that play wins: the real play is a
consistent thread, so the universal min-even condition applies to it. -/
theorem beliefBundle1_accepts_wins (strategy : G.HistoryProductStrategy)
    (nature : Nat -> G.Nature)
    (h : G.beliefBundle1.Accepts (G.beliefLetterWord1 strategy nature)) :
    ParityAccepts (fun n => G.priority (G.strategyState strategy nature n).1) := by
  rw [parityAccepts_iff_natSeqMinEvenParity]
  have hbundle :=
    (G.beliefThreadSystem1.universalRunDPA_accepts_iff
      (G.beliefLetterWord1 strategy nature)).mp h
      (G.realThread1 strategy nature) (G.realThread1_isRun strategy nature)
  have hfun : (fun n => G.priority (G.strategyState strategy nature n).1) =
      fun n => G.beliefThreadSystem1.priority (G.realThread1 strategy nature n) :=
    funext fun n =>
      (G.beliefThreadSystem1_priority_realThread1 strategy nature n).symm
  rw [hfun]
  exact hbundle

/-- Player two's bundle thread step: the orientation mirror of
`beliefThreadStep1`, with player two's action committed and player one's action
hidden. -/
noncomputable def beliefThreadStep2
    (st : Option G.State) (letter : G.Action2 × G.Observation2)
    (res : G.Action1 × G.Nature) : Option G.State :=
  match st with
  | some s =>
      if G.observe2 (G.next s res.1 letter.1 res.2) = letter.2 then
        some (G.next s res.1 letter.1 res.2)
      else none
  | none => none

/-- Player two's bundle thread system. -/
noncomputable def beliefThreadSystem2 :
    FiniteThreadSystem.{u, u, u} (G.Action2 × G.Observation2) where
  State := Option G.State
  stateFinite := inferInstance
  initial := some G.initial
  Resolution := G.Action1 × G.Nature
  step := G.beliefThreadStep2
  priority := fun st =>
    match st with
    | some s => G.priority s
    | none => 0

/-- Player two's universal-run bundle DPA. -/
noncomputable def beliefBundle2 :
    DetParityAutomaton.{u, u} (G.Action2 × G.Observation2) :=
  G.beliefThreadSystem2.universalRunDPA

/-- Player two's observation word along a real play. -/
def beliefLetterWord2 (strategy : G.HistoryProductStrategy)
    (nature : Nat -> G.Nature) : OmegaWord (G.Action2 × G.Observation2) :=
  fun n =>
    (strategy.2 (G.strategyState strategy nature n).2.2,
      G.observe2 (G.strategyState strategy nature (n + 1)).1)

/-- **The real play is a consistent player-two bundle thread.** -/
theorem realThread1_isRun2 (strategy : G.HistoryProductStrategy)
    (nature : Nat -> G.Nature) :
    G.beliefThreadSystem2.IsRun (G.beliefLetterWord2 strategy nature)
      (G.realThread1 strategy nature) := by
  refine ⟨rfl, ?_⟩
  intro n
  refine ⟨(strategy.1 (G.strategyState strategy nature n).2.1, nature n), ?_⟩
  show G.realThread1 strategy nature (n + 1) =
    G.beliefThreadStep2 (G.realThread1 strategy nature n)
      (G.beliefLetterWord2 strategy nature n) _
  simp only [realThread1, beliefThreadStep2, beliefLetterWord2]
  have hcond : G.observe2 (G.next (G.strategyState strategy nature n).1
        (strategy.1 (G.strategyState strategy nature n).2.1)
        (strategy.2 (G.strategyState strategy nature n).2.2) (nature n)) =
      G.observe2 (G.strategyState strategy nature (n + 1)).1 := rfl
  rw [if_pos hcond]
  rfl

theorem beliefThreadSystem2_priority_realThread1
    (strategy : G.HistoryProductStrategy) (nature : Nat -> G.Nature) (n : Nat) :
    G.beliefThreadSystem2.priority (G.realThread1 strategy nature n) =
      G.priority (G.strategyState strategy nature n).1 := rfl

/-- **Invariant (I4), player two, soundness direction.**  The orientation mirror
of `beliefBundle1_accepts_wins`. -/
theorem beliefBundle2_accepts_wins (strategy : G.HistoryProductStrategy)
    (nature : Nat -> G.Nature)
    (h : G.beliefBundle2.Accepts (G.beliefLetterWord2 strategy nature)) :
    ParityAccepts (fun n => G.priority (G.strategyState strategy nature n).1) := by
  rw [parityAccepts_iff_natSeqMinEvenParity]
  have hbundle :=
    (G.beliefThreadSystem2.universalRunDPA_accepts_iff
      (G.beliefLetterWord2 strategy nature)).mp h
      (G.realThread1 strategy nature) (G.realThread1_isRun2 strategy nature)
  have hfun : (fun n => G.priority (G.strategyState strategy nature n).1) =
      fun n => G.beliefThreadSystem2.priority (G.realThread1 strategy nature n) :=
    funext fun n =>
      (G.beliefThreadSystem2_priority_realThread1 strategy nature n).symm
  rw [hfun]
  exact hbundle

/-- Player two's belief as a Moore memory: the fold of the belief update over the
observed player-two letters. -/
noncomputable def beliefFold2 (letters : List (G.Action2 × G.Observation2)) :
    G.Belief :=
  letters.foldl (fun K letter => G.beliefStep2 K letter.1 letter.2) G.beliefInitial

/-- Player two's play-driven belief is the Moore fold of its observed letters:
the mirror of `beliefAlong1_eq_beliefFold1`. -/
theorem beliefAlong2_eq_beliefFold2 (strategy : G.HistoryProductStrategy)
    (nature : Nat -> G.Nature) (n : Nat) :
    G.beliefAlong2 strategy nature n =
      G.beliefFold2 ((List.range n).map (G.beliefLetterWord2 strategy nature)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [beliefAlong2, ih]
      simp only [beliefFold2, beliefLetterWord2, List.range_succ, List.map_append,
        List.map_cons, List.map_nil, List.foldl_append, List.foldl_cons,
        List.foldl_nil]

/-! ### The two-belief unified bundle (arena core)

The arena bundle must carry the follower's own belief so the follower's action
is committed as a function of that belief (obs-measurable, with memory), the
flattened Peterson--Reif structure.  A thread is `(state, K1, K2)`: the game
state and both players' current beliefs.  A letter chooses the leader
orientation, the leader's action, the follower's action *table indexed by the
follower's belief*, and the leader's observed letter; the hidden resolution is
only Nature.  Both beliefs advance every round; the follower's action reads its
own belief, so a positional winner reads back to an observation-measurable
distributed strategy. -/

/-- The unified arena letter: player one leads (`inl`) with leader action, a
follower table over player two's belief, and player one's observed letter; or
player two leads (`inr`), the orientation mirror. -/
abbrev BeliefLetterU :=
  (G.Action1 × (G.Belief -> G.Action2) × G.Observation1) ⊕
    (G.Action2 × (G.Belief -> G.Action1) × G.Observation2)

/-- The two-belief thread step.  Both beliefs advance; the follower's action is
its own-belief table; the successor survives only if the leader's observation
matches the emitted letter, else it falls to the even sink `none`. -/
noncomputable def beliefThreadStepU
    (st : Option (G.State × G.Belief × G.Belief))
    (letter : G.BeliefLetterU) (env : G.Nature) :
    Option (G.State × G.Belief × G.Belief) :=
  match st with
  | some (s, K1, K2) =>
      match letter with
      | .inl (a1, t2, o1) =>
          let t := G.next s a1 (t2 K2) env
          if G.observe1 t = o1 then
            some (t, G.beliefStep1 K1 a1 (G.observe1 t),
              G.beliefStep2 K2 (t2 K2) (G.observe2 t))
          else none
      | .inr (a2, t1, o2) =>
          let t := G.next s (t1 K1) a2 env
          if G.observe2 t = o2 then
            some (t, G.beliefStep1 K1 (t1 K1) (G.observe1 t),
              G.beliefStep2 K2 a2 (G.observe2 t))
          else none
  | none => none

/-- The two-belief unified thread system over the arena letter alphabet. -/
noncomputable def beliefThreadSystemU :
    FiniteThreadSystem.{u, u, u} G.BeliefLetterU where
  State := Option (G.State × G.Belief × G.Belief)
  stateFinite := inferInstance
  initial := some (G.initial, G.beliefInitial, G.beliefInitial)
  Resolution := G.Nature
  step := G.beliefThreadStepU
  priority := fun st =>
    match st with
    | some sKK => G.priority sKK.1
    | none => 0

/-- The unified universal-run bundle DPA: it accepts an arena letter word iff
every consistent two-belief thread is min-even.  This is the single coherent
parity condition of the belief-game arena. -/
noncomputable def beliefBundleU :
    DetParityAutomaton.{u, u} G.BeliefLetterU :=
  G.beliefThreadSystemU.universalRunDPA

/-! ### The belief-game arena positions and leader

The arena carries the **live thread set** (the subset-construction memory over
`(state, K1, K2)`) so the leader can be read off it, together with the bundle
DPA state that scores parity.  The leader on a thread set is the leader on its
state projection: player one leads when its observation determines player two's
among the possible states.  Even's move is forced into the leader orientation;
the follower half is a table over the follower's belief, keeping the extracted
strategy observation-measurable. -/

/-- The live thread set: the subset-construction memory over `(state, K1, K2)`. -/
abbrev ArenaBelief := Finset (G.State × G.Belief × G.Belief)

/-- The leader on a thread set: player one (`true`) when its observation
determines player two's among the possible states. -/
noncomputable def leaderOfArena (T : G.ArenaBelief) : Bool :=
  decide (G.determinesOnBelief1 (T.image fun p => p.1))

/-- Even's committed move: the leader's action together with the follower's
belief-indexed action table, in the leader's orientation. -/
abbrev EvenMove :=
  (G.Action1 × (G.Belief -> G.Action2)) ⊕ (G.Action2 × (G.Belief -> G.Action1))

/-- Arena positions: an Even (coordinator) position carries the thread set and
the bundle state; an Odd (environment) position additionally carries Even's
committed move, before the environment reveals the leader's next observation. -/
abbrev ArenaPos :=
  (G.ArenaBelief × G.beliefBundleU.State) ⊕
    (G.ArenaBelief × G.beliefBundleU.State × G.EvenMove)

/-- The subset-construction update of the thread set under an assembled arena
letter: the live successors of the current threads.  The threads carrying the
even sink are dropped, so only observation-consistent successors survive. -/
noncomputable def arenaBeliefStep (T : G.ArenaBelief)
    (letter : G.BeliefLetterU) : G.ArenaBelief :=
  Finset.univ.filter fun new =>
    ∃ thread ∈ T, ∃ env : G.Nature,
      G.beliefThreadStepU (some thread) letter env = some new

/-- The arena letter assembled from Even's committed move and the leader's
revealed observation, in the orientation forced by the current leader. -/
def arenaLetter (move : G.EvenMove)
    (o1 : G.Observation1) (o2 : G.Observation2) : G.BeliefLetterU :=
  match move with
  | .inl (a1, t2) => .inl (a1, t2, o1)
  | .inr (a2, t1) => .inr (a2, t1, o2)

/-- Even's move is well-oriented for a thread set when it commits in the leader's
orientation: player one's action-and-table when player one leads, else player
two's.  This is the constraint the arena step imposes on Even. -/
def EvenMoveOriented (T : G.ArenaBelief) (move : G.EvenMove) : Prop :=
  match move with
  | .inl _ => G.leaderOfArena T = true
  | .inr _ => G.leaderOfArena T = false

/-- The arena edge relation.  From an Even position the coordinator commits a
well-oriented move, reaching an Odd position; from an Odd position the
environment reveals the leader's observation, advancing the thread set and the
bundle state by the assembled letter. -/
def arenaStepRel : G.ArenaPos -> G.ArenaPos -> Prop
  | Sum.inl (T, d), Sum.inr (T', d', move) =>
      T' = T ∧ d' = d ∧ G.EvenMoveOriented T move
  | Sum.inr (T, d, move), Sum.inl (T', d') =>
      ∃ (o1 : G.Observation1) (o2 : G.Observation2),
        T' = G.arenaBeliefStep T (G.arenaLetter move o1 o2) ∧
          d' = G.beliefBundleU.step d (G.arenaLetter move o1 o2)
  | _, _ => False

/-- The arena priority of a position: the parity assigned by the bundle DPA to
its current state.  Even and Odd positions carrying the same bundle state score
alike, so the priority sequence of a play doubles the bundle run -- which leaves
its min-even parity unchanged. -/
noncomputable def arenaPriority : G.ArenaPos -> Nat
  | Sum.inl (_, d) => G.beliefBundleU.priority d
  | Sum.inr (_, d, _) => G.beliefBundleU.priority d

section Arena

variable [Inhabited G.Action1] [Inhabited G.Action2]
  [Inhabited G.Observation1] [Inhabited G.Observation2]

/-- **The belief-game arena** as a countable parity game: Even (the coordinator)
owns thread-set-and-bundle positions and commits oriented moves; Odd (the
environment) owns move-carrying positions and reveals the leader's observation;
parity is the bundle DPA's.  Even wins iff every consistent two-belief thread is
min-even, i.e. the coordinator forces the coalition to win. -/
noncomputable def beliefArena : CountableParityGame.{u} where
  Position := G.ArenaPos
  positionCountable := inferInstance
  owner := fun p =>
    match p with
    | Sum.inl _ => ParityPlayer.even
    | Sum.inr _ => ParityPlayer.odd
  step := G.arenaStepRel
  step_total := by
    intro p
    rcases p with ⟨T, d⟩ | ⟨T, d, move⟩
    · cases hb : G.leaderOfArena T
      · exact ⟨Sum.inr (T, d, Sum.inr (default, fun _ => default)),
          rfl, rfl, hb⟩
      · exact ⟨Sum.inr (T, d, Sum.inl (default, fun _ => default)),
          rfl, rfl, hb⟩
    · exact ⟨Sum.inl (G.arenaBeliefStep T (G.arenaLetter move default default),
        G.beliefBundleU.step d (G.arenaLetter move default default)),
        default, default, rfl, rfl⟩
  priority := G.arenaPriority
  priority_finite := Set.finite_range _

end Arena

/-! ### Soundness core: the unified bundle transfers parity to every thread

The readback of an arena winner into a distributed strategy rests on the same
universal-bundle fact as the per-player warm-ups, now for the two-belief system:
if the unified bundle accepts an arena letter word, every consistent thread --
in particular the real play under the extracted strategy -- is min-even.  The
extraction of the strategy itself, and the observation-measurability of its
follower half across leadership handoffs (clause I3), is the remaining readback
work. -/

/-- **The unified bundle transfers parity to every consistent thread.**  If the
two-belief bundle accepts an arena letter word, every run of the thread system
over that word is min-even.  This is `universalRunDPA_accepts_iff` at the arena
bundle. -/
theorem beliefBundleU_accepts_run_minEven
    (word : OmegaWord G.BeliefLetterU)
    (q : Nat -> G.beliefThreadSystemU.State)
    (hrun : G.beliefThreadSystemU.IsRun word q)
    (h : G.beliefBundleU.Accepts word) :
    NatSeqMinEvenParity
      (fun n => G.beliefThreadSystemU.priority (q n)) :=
  (G.beliefThreadSystemU.universalRunDPA_accepts_iff word).mp h q hrun

/-- The priority a run of live states scores is the game priority of those
states, so a consistent run of real states inherits the game's parity. -/
theorem beliefBundleU_accepts_states_win
    (word : OmegaWord G.BeliefLetterU)
    (states : Nat -> G.State) (beliefs : Nat -> G.Belief × G.Belief)
    (hrun : G.beliefThreadSystemU.IsRun word
      (fun n => some (states n, beliefs n)))
    (h : G.beliefBundleU.Accepts word) :
    ParityAccepts (fun n => G.priority (states n)) := by
  rw [parityAccepts_iff_natSeqMinEvenParity]
  have hmin := G.beliefBundleU_accepts_run_minEven word
    (fun n => some (states n, beliefs n)) hrun h
  have hfun : (fun n => G.priority (states n)) =
      fun n => G.beliefThreadSystemU.priority (some (states n, beliefs n)) :=
    rfl
  rw [hfun]
  exact hmin

/-! ### The real play of a belief-measurable strategy is a consistent thread

A distributed strategy is **belief-measurable** when each player's action along a
play is a function of that player's own belief (`hmeas1`/`hmeas2`).  The extracted
strategy will be of this shape.  Its real play, carrying both Moore beliefs, is a
consistent thread of the unified bundle for any leader sequence: the follower's
belief-table reproduces the real follower action, so the thread survives every
round.  Composed with `beliefBundleU_accepts_states_win`, this is soundness for a
belief-measurable strategy. -/

/-- The arena letter word emitted by a real play under a belief-measurable
strategy, in the orientation of a given leader sequence. -/
noncomputable def beliefLetterWordU (strategy : G.HistoryProductStrategy)
    (nature : Nat -> G.Nature) (f1 : G.Belief -> G.Action1)
    (f2 : G.Belief -> G.Action2) (leaderSeq : Nat -> Bool) :
    OmegaWord G.BeliefLetterU :=
  fun n =>
    match leaderSeq n with
    | true =>
        Sum.inl (strategy.1 (G.strategyState strategy nature n).2.1, f2,
          G.observe1 (G.strategyState strategy nature (n + 1)).1)
    | false =>
        Sum.inr (strategy.2 (G.strategyState strategy nature n).2.2, f1,
          G.observe2 (G.strategyState strategy nature (n + 1)).1)

/-- The real play as a two-belief thread: the true state and both Moore beliefs. -/
noncomputable def realThreadU (strategy : G.HistoryProductStrategy)
    (nature : Nat -> G.Nature) : Nat -> Option (G.State × G.Belief × G.Belief) :=
  fun n =>
    some ((G.strategyState strategy nature n).1,
      G.beliefAlong1 strategy nature n, G.beliefAlong2 strategy nature n)

/-- **The real play of a belief-measurable strategy is a consistent unified
thread.**  For any leader sequence, the follower's belief-table reproduces the
real follower action, so the thread survives every round. -/
theorem realThreadU_isRun (strategy : G.HistoryProductStrategy)
    (nature : Nat -> G.Nature) (f1 : G.Belief -> G.Action1)
    (f2 : G.Belief -> G.Action2) (leaderSeq : Nat -> Bool)
    (hmeas1 : ∀ n, f1 (G.beliefAlong1 strategy nature n) =
      strategy.1 (G.strategyState strategy nature n).2.1)
    (hmeas2 : ∀ n, f2 (G.beliefAlong2 strategy nature n) =
      strategy.2 (G.strategyState strategy nature n).2.2) :
    G.beliefThreadSystemU.IsRun
      (G.beliefLetterWordU strategy nature f1 f2 leaderSeq)
      (G.realThreadU strategy nature) := by
  refine ⟨rfl, ?_⟩
  intro n
  refine ⟨nature n, ?_⟩
  show G.realThreadU strategy nature (n + 1) =
    G.beliefThreadStepU (G.realThreadU strategy nature n)
      (G.beliefLetterWordU strategy nature f1 f2 leaderSeq n) (nature n)
  cases hL : leaderSeq n
  · simp only [realThreadU, beliefLetterWordU, hL, beliefThreadStepU]
    rw [hmeas1 n]
    have hcond : G.observe2 (G.next (G.strategyState strategy nature n).1
          (strategy.1 (G.strategyState strategy nature n).2.1)
          (strategy.2 (G.strategyState strategy nature n).2.2) (nature n)) =
        G.observe2 (G.strategyState strategy nature (n + 1)).1 := rfl
    rw [if_pos hcond]
    rfl
  · simp only [realThreadU, beliefLetterWordU, hL, beliefThreadStepU]
    rw [hmeas2 n]
    have hcond : G.observe1 (G.next (G.strategyState strategy nature n).1
          (strategy.1 (G.strategyState strategy nature n).2.1)
          (strategy.2 (G.strategyState strategy nature n).2.2) (nature n)) =
        G.observe1 (G.strategyState strategy nature (n + 1)).1 := rfl
    rw [if_pos hcond]
    rfl

/-- **Soundness for a belief-measurable strategy.**  If the unified bundle
accepts the arena letter word of a belief-measurable strategy's play (for some
leader sequence), that play satisfies the parity objective.  This composes
`realThreadU_isRun` with the bundle parity transfer; what remains for full
soundness is the extraction of such a strategy from an arena winner (the
observation-measurable readback, clause I3). -/
theorem beliefMeasurable_strategy_wins (strategy : G.HistoryProductStrategy)
    (nature : Nat -> G.Nature) (f1 : G.Belief -> G.Action1)
    (f2 : G.Belief -> G.Action2) (leaderSeq : Nat -> Bool)
    (hmeas1 : ∀ n, f1 (G.beliefAlong1 strategy nature n) =
      strategy.1 (G.strategyState strategy nature n).2.1)
    (hmeas2 : ∀ n, f2 (G.beliefAlong2 strategy nature n) =
      strategy.2 (G.strategyState strategy nature n).2.2)
    (h : G.beliefBundleU.Accepts
      (G.beliefLetterWordU strategy nature f1 f2 leaderSeq)) :
    ParityAccepts (fun n => G.priority (G.strategyState strategy nature n).1) :=
  G.beliefBundleU_accepts_states_win
    (G.beliefLetterWordU strategy nature f1 f2 leaderSeq)
    (fun n => (G.strategyState strategy nature n).1)
    (fun n => (G.beliefAlong1 strategy nature n, G.beliefAlong2 strategy nature n))
    (G.realThreadU_isRun strategy nature f1 f2 leaderSeq hmeas1 hmeas2)
    h

/-! ### The belief-measurable strategy from belief output functions

Given belief output functions `f1`, `f2`, the belief-measurable strategy reads
its own belief off its view (a Moore fold of its observations, dropping the
initial one), then outputs `f_i` of it.  Along any play its belief is exactly
`beliefAlong_i` (`beliefAlong1_measurableStrategy`), so the measurability
premises `hmeas_i` hold by construction.  This is the finite-state distributed
strategy the extraction commits; supplying `f1`, `f2` from an arena winner in an
observation-measurable way is the remaining clause I3. -/

/-- Player one's belief read off its own view: the Moore fold of the transition
observations (dropping the initial observation). -/
noncomputable def measurableBelief1 (f1 : G.Belief -> G.Action1)
    (obs : List G.Observation1) : G.Belief :=
  obs.foldl (fun K o => G.beliefStep1 K (f1 K) o) G.beliefInitial

/-- Player two's belief read off its own view. -/
noncomputable def measurableBelief2 (f2 : G.Belief -> G.Action2)
    (obs : List G.Observation2) : G.Belief :=
  obs.foldl (fun K o => G.beliefStep2 K (f2 K) o) G.beliefInitial

/-- The belief-measurable distributed strategy of `f1`, `f2`: each player outputs
its function applied to its own view-computed belief. -/
noncomputable def measurableStrategy (f1 : G.Belief -> G.Action1)
    (f2 : G.Belief -> G.Action2) : G.HistoryProductStrategy :=
  (fun view => f1 (G.measurableBelief1 f1 view.tail),
    fun view => f2 (G.measurableBelief2 f2 view.tail))

theorem view1_ne_nil (strategy : G.HistoryProductStrategy)
    (nature : Nat -> G.Nature) (n : Nat) :
    (G.strategyState strategy nature n).2.1 ≠ [] := by
  induction n with
  | zero => simp [strategyState]
  | succ n _ =>
      show (G.strategyState strategy nature n).2.1 ++ [_] ≠ []
      simp

theorem view1_tail_succ (strategy : G.HistoryProductStrategy)
    (nature : Nat -> G.Nature) (n : Nat) :
    (G.strategyState strategy nature (n + 1)).2.1.tail =
      (G.strategyState strategy nature n).2.1.tail ++
        [G.observe1 (G.strategyState strategy nature (n + 1)).1] := by
  have hview : (G.strategyState strategy nature (n + 1)).2.1 =
      (G.strategyState strategy nature n).2.1 ++
        [G.observe1 (G.strategyState strategy nature (n + 1)).1] := rfl
  rw [hview]
  rcases List.exists_cons_of_ne_nil (G.view1_ne_nil strategy nature n) with
    ⟨a, l, hal⟩
  rw [hal]
  rfl

/-- **The measurable strategy's belief is `beliefAlong1`.**  Along its own play,
player one's view-computed belief equals the play-driven Moore belief, so the
strategy's action is `f1` of that belief. -/
theorem beliefAlong1_measurableStrategy (f1 : G.Belief -> G.Action1)
    (f2 : G.Belief -> G.Action2) (nature : Nat -> G.Nature) (n : Nat) :
    G.beliefAlong1 (G.measurableStrategy f1 f2) nature n =
      G.measurableBelief1 f1
        (G.strategyState (G.measurableStrategy f1 f2) nature n).2.1.tail := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [beliefAlong1, ih, view1_tail_succ]
      simp only [measurableStrategy, measurableBelief1, List.foldl_append,
        List.foldl_cons, List.foldl_nil]

theorem view2_ne_nil (strategy : G.HistoryProductStrategy)
    (nature : Nat -> G.Nature) (n : Nat) :
    (G.strategyState strategy nature n).2.2 ≠ [] := by
  induction n with
  | zero => simp [strategyState]
  | succ n _ =>
      show (G.strategyState strategy nature n).2.2 ++ [_] ≠ []
      simp

theorem view2_tail_succ (strategy : G.HistoryProductStrategy)
    (nature : Nat -> G.Nature) (n : Nat) :
    (G.strategyState strategy nature (n + 1)).2.2.tail =
      (G.strategyState strategy nature n).2.2.tail ++
        [G.observe2 (G.strategyState strategy nature (n + 1)).1] := by
  have hview : (G.strategyState strategy nature (n + 1)).2.2 =
      (G.strategyState strategy nature n).2.2 ++
        [G.observe2 (G.strategyState strategy nature (n + 1)).1] := rfl
  rw [hview]
  rcases List.exists_cons_of_ne_nil (G.view2_ne_nil strategy nature n) with
    ⟨a, l, hal⟩
  rw [hal]
  rfl

/-- The player-two mirror of `beliefAlong1_measurableStrategy`. -/
theorem beliefAlong2_measurableStrategy (f1 : G.Belief -> G.Action1)
    (f2 : G.Belief -> G.Action2) (nature : Nat -> G.Nature) (n : Nat) :
    G.beliefAlong2 (G.measurableStrategy f1 f2) nature n =
      G.measurableBelief2 f2
        (G.strategyState (G.measurableStrategy f1 f2) nature n).2.2.tail := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [beliefAlong2, ih, view2_tail_succ]
      simp only [measurableStrategy, measurableBelief2, List.foldl_append,
        List.foldl_cons, List.foldl_nil]

/-- The measurability premise holds for the measurable strategy: player one's
committed action is `f1` of its play-driven belief. -/
theorem hmeas1_measurableStrategy (f1 : G.Belief -> G.Action1)
    (f2 : G.Belief -> G.Action2) (nature : Nat -> G.Nature) (n : Nat) :
    f1 (G.beliefAlong1 (G.measurableStrategy f1 f2) nature n) =
      (G.measurableStrategy f1 f2).1
        (G.strategyState (G.measurableStrategy f1 f2) nature n).2.1 := by
  rw [beliefAlong1_measurableStrategy]
  rfl

/-- The player-two mirror of `hmeas1_measurableStrategy`. -/
theorem hmeas2_measurableStrategy (f1 : G.Belief -> G.Action1)
    (f2 : G.Belief -> G.Action2) (nature : Nat -> G.Nature) (n : Nat) :
    f2 (G.beliefAlong2 (G.measurableStrategy f1 f2) nature n) =
      (G.measurableStrategy f1 f2).2
        (G.strategyState (G.measurableStrategy f1 f2) nature n).2.2 := by
  rw [beliefAlong2_measurableStrategy]
  rfl

/-- **The extraction reduction.**  If, for belief output functions `f1`, `f2`,
the unified bundle accepts the measurable strategy's arena word on every
environment (for some leader sequence), then the objective is realizable -- by
the finite-state, observation-measurable strategy `measurableStrategy f1 f2`.
The hypothesis is exactly this bundle acceptance, i.e. that an arena
winner is observation-measurable (clause I3). -/
theorem historyRealizable_of_measurableBundleAccepts
    (f1 : G.Belief -> G.Action1) (f2 : G.Belief -> G.Action2)
    (h : ∀ nature : Nat -> G.Nature, ∃ leaderSeq : Nat -> Bool,
      G.beliefBundleU.Accepts
        (G.beliefLetterWordU (G.measurableStrategy f1 f2) nature f1 f2 leaderSeq)) :
    G.HistoryRealizable :=
  ⟨G.measurableStrategy f1 f2, fun nature => by
    obtain ⟨leaderSeq, hacc⟩ := h nature
    exact G.beliefMeasurable_strategy_wins (G.measurableStrategy f1 f2) nature
      f1 f2 leaderSeq (G.hmeas1_measurableStrategy f1 f2 nature)
      (G.hmeas2_measurableStrategy f1 f2 nature) hacc⟩

/-! ### Finite Moore implementation of the belief-output special case -/

/-- Player one's belief fold as a Moore controller.  `none` is the state before
the mandatory initial observation; reading that observation initializes the
actual belief. -/
noncomputable def beliefController1 (f1 : G.Belief → G.Action1) :
    MooreController G.Observation1 G.Action1 where
  Memory := Option G.Belief
  memoryFinite := inferInstance
  initial := none
  update memory observation :=
    match memory with
    | none => some G.beliefInitial
    | some K => some (G.beliefStep1 K (f1 K) observation)
  output memory :=
    match memory with
    | none => f1 G.beliefInitial
    | some K => f1 K

/-- Player two's mirror belief controller. -/
noncomputable def beliefController2 (f2 : G.Belief → G.Action2) :
    MooreController G.Observation2 G.Action2 where
  Memory := Option G.Belief
  memoryFinite := inferInstance
  initial := none
  update memory observation :=
    match memory with
    | none => some G.beliefInitial
    | some K => some (G.beliefStep2 K (f2 K) observation)
  output memory :=
    match memory with
    | none => f2 G.beliefInitial
    | some K => f2 K

theorem beliefController1_foldl_some (f1 : G.Belief → G.Action1)
    (K : G.Belief) (observations : List G.Observation1) :
    observations.foldl (G.beliefController1 f1).update (some K) =
      some (observations.foldl
        (fun K observation => G.beliefStep1 K (f1 K) observation) K) := by
  induction observations generalizing K with
  | nil => rfl
  | cons observation observations ih =>
      simp only [List.foldl_cons, beliefController1]
      exact ih _

theorem beliefController2_foldl_some (f2 : G.Belief → G.Action2)
    (K : G.Belief) (observations : List G.Observation2) :
    observations.foldl (G.beliefController2 f2).update (some K) =
      some (observations.foldl
        (fun K observation => G.beliefStep2 K (f2 K) observation) K) := by
  induction observations generalizing K with
  | nil => rfl
  | cons observation observations ih =>
      simp only [List.foldl_cons, beliefController2]
      exact ih _

theorem beliefController1_run_cons (f1 : G.Belief → G.Action1)
    (observation : G.Observation1) (tail : List G.Observation1) :
    (G.beliefController1 f1).run (observation :: tail) =
      some (G.measurableBelief1 f1 tail) := by
  rw [MooreController.run_eq_foldl]
  simp only [List.foldl_cons, beliefController1, measurableBelief1]
  exact G.beliefController1_foldl_some f1 G.beliefInitial tail

theorem beliefController2_run_cons (f2 : G.Belief → G.Action2)
    (observation : G.Observation2) (tail : List G.Observation2) :
    (G.beliefController2 f2).run (observation :: tail) =
      some (G.measurableBelief2 f2 tail) := by
  rw [MooreController.run_eq_foldl]
  simp only [List.foldl_cons, beliefController2, measurableBelief2]
  exact G.beliefController2_foldl_some f2 G.beliefInitial tail

theorem beliefController1_strategy (f1 : G.Belief → G.Action1) :
    (G.beliefController1 f1).strategy =
      fun observations => f1 (G.measurableBelief1 f1 observations.tail) := by
  funext observations
  cases observations with
  | nil => rfl
  | cons observation tail =>
      simp only [MooreController.strategy, List.tail_cons]
      rw [G.beliefController1_run_cons]
      rfl

theorem beliefController2_strategy (f2 : G.Belief → G.Action2) :
    (G.beliefController2 f2).strategy =
      fun observations => f2 (G.measurableBelief2 f2 observations.tail) := by
  funext observations
  cases observations with
  | nil => rfl
  | cons observation tail =>
      simp only [MooreController.strategy, List.tail_cons]
      rw [G.beliefController2_run_cons]
      rfl

/-- The measurable belief strategy is implemented exactly by finite Moore
controllers, including the convention for the initial observation. -/
noncomputable def measurableFiniteStrategy
    (f1 : G.Belief → G.Action1) (f2 : G.Belief → G.Action2) :
    G.FiniteStateProductStrategy where
  one := G.beliefController1 f1
  two := G.beliefController2 f2

theorem measurableFiniteStrategy_toHistory
    (f1 : G.Belief → G.Action1) (f2 : G.Belief → G.Action2) :
    (G.measurableFiniteStrategy f1 f2).toHistory =
      G.measurableStrategy f1 f2 := by
  apply Prod.ext
  · exact G.beliefController1_strategy f1
  · exact G.beliefController2_strategy f2

/-- Finite-state strengthening of `historyRealizable_of_measurableBundleAccepts`.
Once I3 supplies belief-output functions and bundle acceptance, no further
finite-memory argument is needed. -/
theorem finiteStateRealizable_of_measurableBundleAccepts
    (f1 : G.Belief → G.Action1) (f2 : G.Belief → G.Action2)
    (h : ∀ nature : Nat → G.Nature, ∃ leaderSeq : Nat → Bool,
      G.beliefBundleU.Accepts
        (G.beliefLetterWordU (G.measurableStrategy f1 f2) nature f1 f2 leaderSeq)) :
    G.FiniteStateRealizable := by
  refine ⟨G.measurableFiniteStrategy f1 f2, ?_⟩
  rw [FiniteStateStrategyWins, G.measurableFiniteStrategy_toHistory]
  intro nature
  obtain ⟨leaderSeq, hacc⟩ := h nature
  exact G.beliefMeasurable_strategy_wins (G.measurableStrategy f1 f2) nature
    f1 f2 leaderSeq (G.hmeas1_measurableStrategy f1 f2 nature)
    (G.hmeas2_measurableStrategy f1 f2 nature) hacc

/-! ### The honest arena readback boundary

The belief-only functions above are a useful special case, but they are not a
large enough target for an arbitrary positional arena winner: its move may also
depend on the live-thread set and on the universal bundle's parity-monitor
state.  The actual Berwanger conclusion is therefore stated below directly in
terms of finite Moore controllers.  This prevents the I3 proof from silently
assuming that the controller is memoryless on its current belief.
-/

/-- The live singleton thread at the start of the belief arena. -/
def arenaInitialThreads : G.ArenaBelief :=
  {(G.initial, G.beliefInitial, G.beliefInitial)}

/-- The canonical initial Even position of the belief arena. -/
noncomputable def arenaInitialPosition : G.ArenaPos :=
  Sum.inl (G.arenaInitialThreads, G.beliefBundleU.initial)

@[simp]
theorem mem_arenaInitialThreads (thread : G.State × G.Belief × G.Belief) :
    thread ∈ G.arenaInitialThreads ↔
      thread = (G.initial, G.beliefInitial, G.beliefInitial) := by
  simp [arenaInitialThreads]

theorem arenaInitialThreads_nonempty : G.arenaInitialThreads.Nonempty := by
  exact ⟨(G.initial, G.beliefInitial, G.beliefInitial), by simp⟩

/-! #### The handoff topology supplied by `CrossFree`

When the determining direction changes across one generated move, at least one
endpoint is a tie.  This is the precise local fact a readback memory uses to
transfer coordinator state: a strict one-to-two (or two-to-one) jump is ruled
out, so the old and new leader overlap at an endpoint where both complete
views determine each other.
-/

theorem crossFree_one_to_two_handoff_tie
    (hcross : G.CrossFree) (history : G.PlayHistory)
    (actionOne : G.Action1) (actionTwo : G.Action2) (nature : G.Nature)
    (hsourceOne : G.OneDeterminesTwoAt history)
    (htargetTwo : G.TwoDeterminesOneAt
      (history.step actionOne actionTwo nature)) :
    G.TwoDeterminesOneAt history ∨
      G.OneDeterminesTwoAt (history.step actionOne actionTwo nature) := by
  by_cases hsourceTwo : G.TwoDeterminesOneAt history
  · exact Or.inl hsourceTwo
  by_cases htargetOne : G.OneDeterminesTwoAt
      (history.step actionOne actionTwo nature)
  · exact Or.inr htargetOne
  exfalso
  exact hcross history actionOne actionTwo nature
    (Or.inl ⟨⟨hsourceOne, hsourceTwo⟩, ⟨htargetTwo, htargetOne⟩⟩)

theorem crossFree_two_to_one_handoff_tie
    (hcross : G.CrossFree) (history : G.PlayHistory)
    (actionOne : G.Action1) (actionTwo : G.Action2) (nature : G.Nature)
    (hsourceTwo : G.TwoDeterminesOneAt history)
    (htargetOne : G.OneDeterminesTwoAt
      (history.step actionOne actionTwo nature)) :
    G.OneDeterminesTwoAt history ∨
      G.TwoDeterminesOneAt (history.step actionOne actionTwo nature) := by
  by_cases hsourceOne : G.OneDeterminesTwoAt history
  · exact Or.inl hsourceOne
  by_cases htargetTwo : G.TwoDeterminesOneAt
      (history.step actionOne actionTwo nature)
  · exact Or.inr htargetTwo
  exfalso
  exact hcross history actionOne actionTwo nature
    (Or.inr ⟨⟨hsourceTwo, hsourceOne⟩, ⟨htargetOne, htargetTwo⟩⟩)

/-- At an information tie, the two complete perfect-recall observation
relations coincide.  This is the semantic datum transferred at a handoff. -/
theorem observations_equiv_of_determination_tie
    (history : G.PlayHistory)
    (hone : G.OneDeterminesTwoAt history)
    (htwo : G.TwoDeterminesOneAt history)
    (alternative : G.PlayHistory) :
    alternative.observations1 = history.observations1 ↔
      alternative.observations2 = history.observations2 := by
  exact ⟨hone alternative, htwo alternative⟩

/-- A one-to-two leadership handoff in a crossing-free arena exposes an
endpoint at which either local perfect-recall view determines exactly the same
information class. -/
theorem crossFree_one_to_two_handoff_view_equiv
    (hcross : G.CrossFree) (history : G.PlayHistory)
    (actionOne : G.Action1) (actionTwo : G.Action2) (nature : G.Nature)
    (hsourceOne : G.OneDeterminesTwoAt history)
    (htargetTwo : G.TwoDeterminesOneAt
      (history.step actionOne actionTwo nature)) :
    (∀ alternative : G.PlayHistory,
        alternative.observations1 = history.observations1 ↔
        alternative.observations2 = history.observations2) ∨
      (∀ alternative : G.PlayHistory,
        alternative.observations1 =
            (history.step actionOne actionTwo nature).observations1 ↔
          alternative.observations2 =
            (history.step actionOne actionTwo nature).observations2) := by
  rcases G.crossFree_one_to_two_handoff_tie hcross history actionOne actionTwo
    nature hsourceOne htargetTwo with hsourceTwo | htargetOne
  · exact Or.inl fun alternative =>
      G.observations_equiv_of_determination_tie history hsourceOne hsourceTwo
        alternative
  · exact Or.inr fun alternative =>
      G.observations_equiv_of_determination_tie
        (history.step actionOne actionTwo nature) htargetOne htargetTwo alternative

/-- Orientation mirror of `crossFree_one_to_two_handoff_view_equiv`. -/
theorem crossFree_two_to_one_handoff_view_equiv
    (hcross : G.CrossFree) (history : G.PlayHistory)
    (actionOne : G.Action1) (actionTwo : G.Action2) (nature : G.Nature)
    (hsourceTwo : G.TwoDeterminesOneAt history)
    (htargetOne : G.OneDeterminesTwoAt
      (history.step actionOne actionTwo nature)) :
    (∀ alternative : G.PlayHistory,
        alternative.observations1 = history.observations1 ↔
        alternative.observations2 = history.observations2) ∨
      (∀ alternative : G.PlayHistory,
        alternative.observations1 =
            (history.step actionOne actionTwo nature).observations1 ↔
          alternative.observations2 =
            (history.step actionOne actionTwo nature).observations2) := by
  rcases G.crossFree_two_to_one_handoff_tie hcross history actionOne actionTwo
    nature hsourceTwo htargetOne with hsourceOne | htargetTwo
  · exact Or.inl fun alternative =>
      G.observations_equiv_of_determination_tie history hsourceOne hsourceTwo
        alternative
  · exact Or.inr fun alternative =>
      G.observations_equiv_of_determination_tie
        (history.step actionOne actionTwo nature) htargetOne htargetTwo alternative

/-- Distributed realizability must put the canonical belief position in the
Even winning region.  This is the completeness half of the belief reduction. -/
def BeliefArenaCompleteness
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2] : Prop :=
  G.HistoryRealizable →
    G.arenaInitialPosition ∈
      G.beliefArena.WinningRegion ParityPlayer.even

/-- Read the committed action/table pair out of an arena positional strategy
at an Even position.  The fallback branch is unreachable by legality. -/
noncomputable def arenaCommittedMove
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2]
    (τ : G.beliefArena.PositionalStrategy ParityPlayer.even)
    (T : G.ArenaBelief) (d : G.beliefBundleU.State) : G.EvenMove :=
  match τ.move (Sum.inl (T, d)) with
  | Sum.inr (_, _, move) => move
  | Sum.inl _ => default

/-- Legality forces an Even arena winner's move to preserve the current live
thread set and bundle state and to carry a correctly oriented commitment. -/
theorem beliefArena_even_move_shape
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2]
    (τ : G.beliefArena.PositionalStrategy ParityPlayer.even)
    (T : G.ArenaBelief) (d : G.beliefBundleU.State) :
    τ.move (Sum.inl (T, d)) =
        Sum.inr (T, d, G.arenaCommittedMove τ T d) ∧
      G.EvenMoveOriented T (G.arenaCommittedMove τ T d) := by
  have hlegal := τ.legal (Sum.inl (T, d)) (by
    simp [beliefArena])
  change G.arenaStepRel (Sum.inl (T, d))
    (τ.move (Sum.inl (T, d))) at hlegal
  cases hmove : τ.move (Sum.inl (T, d)) with
  | inl next =>
      rw [hmove] at hlegal
      simp [arenaStepRel] at hlegal
  | inr next =>
      rcases next with ⟨T', d', move⟩
      rw [hmove] at hlegal
      simp only [arenaStepRel] at hlegal
      rcases hlegal with ⟨rfl, rfl, horiented⟩
      simp only [arenaCommittedMove, hmove]
      exact ⟨trivial, horiented⟩

theorem arenaCommittedMove_eq_inl_of_leaderOne
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2]
    (τ : G.beliefArena.PositionalStrategy ParityPlayer.even)
    (T : G.ArenaBelief) (d : G.beliefBundleU.State)
    (hleader : G.leaderOfArena T = true) :
    ∃ (action : G.Action1) (table : G.Belief → G.Action2),
      G.arenaCommittedMove τ T d = Sum.inl (action, table) := by
  have horiented := (G.beliefArena_even_move_shape τ T d).2
  cases hmove : G.arenaCommittedMove τ T d with
  | inl move => exact ⟨move.1, move.2, rfl⟩
  | inr move =>
      rw [hmove] at horiented
      simp only [EvenMoveOriented] at horiented
      rw [hleader] at horiented
      contradiction

theorem arenaCommittedMove_eq_inr_of_leaderTwo
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2]
    (τ : G.beliefArena.PositionalStrategy ParityPlayer.even)
    (T : G.ArenaBelief) (d : G.beliefBundleU.State)
    (hleader : G.leaderOfArena T = false) :
    ∃ (action : G.Action2) (table : G.Belief → G.Action1),
      G.arenaCommittedMove τ T d = Sum.inr (action, table) := by
  have horiented := (G.beliefArena_even_move_shape τ T d).2
  cases hmove : G.arenaCommittedMove τ T d with
  | inl move =>
      rw [hmove] at horiented
      simp only [EvenMoveOriented] at horiented
      rw [hleader] at horiented
      contradiction
  | inr move => exact ⟨move.1, move.2, rfl⟩

/-! #### Second-order local memory for I3

A player cannot in general store a single arena state while it is the
follower: the finer leader history may distinguish several `(T,d)` states that
the follower cannot.  The finite local memory therefore stores the set of all
arena states compatible with the player's own view.  At a handoff, `CrossFree`
and the tie equivalence are used to prove that the newly relevant action is
uniform over this set.
-/

/-- The state carried at an Even arena position, without the outer sum tag. -/
abbrev ReadbackArenaState := G.ArenaBelief × G.beliefBundleU.State

/-- A player's second-order belief about the current Even arena state. -/
abbrev ReadbackKnowledge := Finset G.ReadbackArenaState

/-- The canonical singleton second-order belief. -/
noncomputable def readbackKnowledgeInitial : G.ReadbackKnowledge :=
  {(G.arenaInitialThreads, G.beliefBundleU.initial)}

/-- One complete arena round from an Even state, after the positional winner's
commitment and the pair of observations selected at the Odd half-step. -/
noncomputable def readbackArenaStep
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2]
    (τ : G.beliefArena.PositionalStrategy ParityPlayer.even)
    (state : G.ReadbackArenaState)
    (o1 : G.Observation1) (o2 : G.Observation2) : G.ReadbackArenaState :=
  let move := G.arenaCommittedMove τ state.1 state.2
  let letter := G.arenaLetter move o1 o2
  (G.arenaBeliefStep state.1 letter, G.beliefBundleU.step state.2 letter)

/-- Player one's local update: retain every next arena state obtainable with
the observation `o1`, existentially hiding player two's observation. -/
noncomputable def readbackKnowledgeStep1
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2]
    (τ : G.beliefArena.PositionalStrategy ParityPlayer.even)
    (R : G.ReadbackKnowledge) (o1 : G.Observation1) : G.ReadbackKnowledge :=
  Finset.univ.filter fun next =>
    ∃ previous ∈ R, ∃ o2 : G.Observation2,
      G.readbackArenaStep τ previous o1 o2 = next

/-- Player two's mirror update. -/
noncomputable def readbackKnowledgeStep2
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2]
    (τ : G.beliefArena.PositionalStrategy ParityPlayer.even)
    (R : G.ReadbackKnowledge) (o2 : G.Observation2) : G.ReadbackKnowledge :=
  Finset.univ.filter fun next =>
    ∃ previous ∈ R, ∃ o1 : G.Observation1,
      G.readbackArenaStep τ previous o1 o2 = next

theorem mem_readbackKnowledgeStep1
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2]
    (τ : G.beliefArena.PositionalStrategy ParityPlayer.even)
    (R : G.ReadbackKnowledge) (o1 : G.Observation1)
    (next : G.ReadbackArenaState) :
    next ∈ G.readbackKnowledgeStep1 τ R o1 ↔
      ∃ previous ∈ R, ∃ o2 : G.Observation2,
        G.readbackArenaStep τ previous o1 o2 = next := by
  simp [readbackKnowledgeStep1]

theorem mem_readbackKnowledgeStep2
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2]
    (τ : G.beliefArena.PositionalStrategy ParityPlayer.even)
    (R : G.ReadbackKnowledge) (o2 : G.Observation2)
    (next : G.ReadbackArenaState) :
    next ∈ G.readbackKnowledgeStep2 τ R o2 ↔
      ∃ previous ∈ R, ∃ o1 : G.Observation1,
        G.readbackArenaStep τ previous o1 o2 = next := by
  simp [readbackKnowledgeStep2]

@[simp]
theorem readbackKnowledgeInitial_nonempty :
    G.readbackKnowledgeInitial.Nonempty := by
  exact ⟨(G.arenaInitialThreads, G.beliefBundleU.initial), by
    simp [readbackKnowledgeInitial]⟩

/-- The actual arena successor remains in player one's second-order belief. -/
theorem mem_readbackKnowledgeStep1_of_actual
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2]
    (τ : G.beliefArena.PositionalStrategy ParityPlayer.even)
    (R : G.ReadbackKnowledge) (previous : G.ReadbackArenaState)
    (hprevious : previous ∈ R) (o1 : G.Observation1) (o2 : G.Observation2) :
    G.readbackArenaStep τ previous o1 o2 ∈
      G.readbackKnowledgeStep1 τ R o1 := by
  rw [G.mem_readbackKnowledgeStep1]
  exact ⟨previous, hprevious, o2, rfl⟩

/-- Player two's mirror actual-successor membership. -/
theorem mem_readbackKnowledgeStep2_of_actual
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2]
    (τ : G.beliefArena.PositionalStrategy ParityPlayer.even)
    (R : G.ReadbackKnowledge) (previous : G.ReadbackArenaState)
    (hprevious : previous ∈ R) (o1 : G.Observation1) (o2 : G.Observation2) :
    G.readbackArenaStep τ previous o1 o2 ∈
      G.readbackKnowledgeStep2 τ R o2 := by
  rw [G.mem_readbackKnowledgeStep2]
  exact ⟨previous, hprevious, o1, rfl⟩

/-- Player one's action prescribed by an arena commitment at a candidate arena
state: the direct action while leading, or the follower table evaluated at its
own first-order belief. -/
noncomputable def readbackCandidateAction1
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2]
    (τ : G.beliefArena.PositionalStrategy ParityPlayer.even)
    (K1 : G.Belief) (state : G.ReadbackArenaState) : G.Action1 :=
  match G.arenaCommittedMove τ state.1 state.2 with
  | Sum.inl (action, _) => action
  | Sum.inr (_, table) => table K1

/-- Player two's mirror candidate action. -/
noncomputable def readbackCandidateAction2
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2]
    (τ : G.beliefArena.PositionalStrategy ParityPlayer.even)
    (K2 : G.Belief) (state : G.ReadbackArenaState) : G.Action2 :=
  match G.arenaCommittedMove τ state.1 state.2 with
  | Sum.inl (_, table) => table K2
  | Sum.inr (action, _) => action

/-- I3's exact local obligation for player one: every arena state compatible
with its local view prescribes the same action. -/
def ReadbackUniform1
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2]
    (τ : G.beliefArena.PositionalStrategy ParityPlayer.even)
    (K1 : G.Belief) (R : G.ReadbackKnowledge) : Prop :=
  ∀ left ∈ R, ∀ right ∈ R,
    G.readbackCandidateAction1 τ K1 left =
      G.readbackCandidateAction1 τ K1 right

/-- Player two's mirror uniformity obligation. -/
def ReadbackUniform2
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2]
    (τ : G.beliefArena.PositionalStrategy ParityPlayer.even)
    (K2 : G.Belief) (R : G.ReadbackKnowledge) : Prop :=
  ∀ left ∈ R, ∀ right ∈ R,
    G.readbackCandidateAction2 τ K2 left =
      G.readbackCandidateAction2 τ K2 right

theorem readbackKnowledgeInitial_uniform1
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2]
    (τ : G.beliefArena.PositionalStrategy ParityPlayer.even) :
    G.ReadbackUniform1 τ G.beliefInitial G.readbackKnowledgeInitial := by
  intro left hleft right hright
  simp [readbackKnowledgeInitial] at hleft hright
  subst left
  subst right
  rfl

theorem readbackKnowledgeInitial_uniform2
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2]
    (τ : G.beliefArena.PositionalStrategy ParityPlayer.even) :
    G.ReadbackUniform2 τ G.beliefInitial G.readbackKnowledgeInitial := by
  intro left hleft right hright
  simp [readbackKnowledgeInitial] at hleft hright
  subst left
  subst right
  rfl

/-- Choose player one's locally prescribed action.  Reachable I3 uniformity
makes the representative irrelevant. -/
noncomputable def readbackOutput1
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2]
    (τ : G.beliefArena.PositionalStrategy ParityPlayer.even)
    (K1 : G.Belief) (R : G.ReadbackKnowledge) : G.Action1 :=
  if h : R.Nonempty then
    G.readbackCandidateAction1 τ K1 h.choose
  else default

/-- Player two's mirror output. -/
noncomputable def readbackOutput2
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2]
    (τ : G.beliefArena.PositionalStrategy ParityPlayer.even)
    (K2 : G.Belief) (R : G.ReadbackKnowledge) : G.Action2 :=
  if h : R.Nonempty then
    G.readbackCandidateAction2 τ K2 h.choose
  else default

theorem readbackOutput1_eq_candidate
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2]
    (τ : G.beliefArena.PositionalStrategy ParityPlayer.even)
    (K1 : G.Belief) (R : G.ReadbackKnowledge)
    (huniform : G.ReadbackUniform1 τ K1 R)
    (state : G.ReadbackArenaState) (hstate : state ∈ R) :
    G.readbackOutput1 τ K1 R =
      G.readbackCandidateAction1 τ K1 state := by
  have hnonempty : R.Nonempty := ⟨state, hstate⟩
  rw [readbackOutput1, dif_pos hnonempty]
  exact huniform hnonempty.choose hnonempty.choose_spec state hstate

theorem readbackOutput2_eq_candidate
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2]
    (τ : G.beliefArena.PositionalStrategy ParityPlayer.even)
    (K2 : G.Belief) (R : G.ReadbackKnowledge)
    (huniform : G.ReadbackUniform2 τ K2 R)
    (state : G.ReadbackArenaState) (hstate : state ∈ R) :
    G.readbackOutput2 τ K2 R =
      G.readbackCandidateAction2 τ K2 state := by
  have hnonempty : R.Nonempty := ⟨state, hstate⟩
  rw [readbackOutput2, dif_pos hnonempty]
  exact huniform hnonempty.choose hnonempty.choose_spec state hstate

/-- Player one's concrete finite second-order readback controller. -/
noncomputable def arenaReadbackController1
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2]
    (τ : G.beliefArena.PositionalStrategy ParityPlayer.even) :
    MooreController G.Observation1 G.Action1 where
  Memory := Option (G.Belief × G.ReadbackKnowledge)
  memoryFinite := inferInstance
  initial := none
  update memory observation :=
    match memory with
    | none => some (G.beliefInitial, G.readbackKnowledgeInitial)
    | some (K1, R) =>
        let action := G.readbackOutput1 τ K1 R
        some (G.beliefStep1 K1 action observation,
          G.readbackKnowledgeStep1 τ R observation)
  output memory :=
    match memory with
    | none => default
    | some (K1, R) => G.readbackOutput1 τ K1 R

/-- Player two's mirror second-order readback controller. -/
noncomputable def arenaReadbackController2
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2]
    (τ : G.beliefArena.PositionalStrategy ParityPlayer.even) :
    MooreController G.Observation2 G.Action2 where
  Memory := Option (G.Belief × G.ReadbackKnowledge)
  memoryFinite := inferInstance
  initial := none
  update memory observation :=
    match memory with
    | none => some (G.beliefInitial, G.readbackKnowledgeInitial)
    | some (K2, R) =>
        let action := G.readbackOutput2 τ K2 R
        some (G.beliefStep2 K2 action observation,
          G.readbackKnowledgeStep2 τ R observation)
  output memory :=
    match memory with
    | none => default
    | some (K2, R) => G.readbackOutput2 τ K2 R

/-- The finite controller pair extracted syntactically from an arena winner.
Its winning proof is exactly reachable I3 uniformity plus the arena simulation. -/
noncomputable def arenaReadbackFiniteStrategy
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2]
    (τ : G.beliefArena.PositionalStrategy ParityPlayer.even) :
    G.FiniteStateProductStrategy where
  one := G.arenaReadbackController1 τ
  two := G.arenaReadbackController2 τ

/-- The exact I3 invariant for a positional arena strategy: at every local
memory reachable by either player's own observation word, all compatible arena
states prescribe the same local action. -/
def ArenaStrategyLocallyUniform
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2]
    (τ : G.beliefArena.PositionalStrategy ParityPlayer.even) : Prop :=
  (∀ (observations : List G.Observation1) (K1 : G.Belief)
      (R : G.ReadbackKnowledge),
      (G.arenaReadbackController1 τ).run observations = some (K1, R) →
        G.ReadbackUniform1 τ K1 R) ∧
    (∀ (observations : List G.Observation2) (K2 : G.Belief)
      (R : G.ReadbackKnowledge),
      (G.arenaReadbackController2 τ).run observations = some (K2, R) →
        G.ReadbackUniform2 τ K2 R)

theorem arenaReadbackController1_run_singleton
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2]
    (τ : G.beliefArena.PositionalStrategy ParityPlayer.even)
    (observation : G.Observation1) :
    (G.arenaReadbackController1 τ).run [observation] =
      some (G.beliefInitial, G.readbackKnowledgeInitial) := by
  rfl

theorem arenaReadbackController2_run_singleton
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2]
    (τ : G.beliefArena.PositionalStrategy ParityPlayer.even)
    (observation : G.Observation2) :
    (G.arenaReadbackController2 τ).run [observation] =
      some (G.beliefInitial, G.readbackKnowledgeInitial) := by
  rfl

/-- I3 holds at the initial local memories; the remaining induction is exactly
the same-leader preservation and tie-handoff uniformization argument. -/
theorem arenaReadback_initial_uniform
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2]
    (τ : G.beliefArena.PositionalStrategy ParityPlayer.even) :
    G.ReadbackUniform1 τ G.beliefInitial G.readbackKnowledgeInitial ∧
      G.ReadbackUniform2 τ G.beliefInitial G.readbackKnowledgeInitial :=
  ⟨G.readbackKnowledgeInitial_uniform1 τ,
    G.readbackKnowledgeInitial_uniform2 τ⟩

/-- Under local uniformity, the action emitted by player one's concrete Moore
controller agrees with the arena commitment at every compatible arena state. -/
theorem arenaReadbackController1_output_eq_candidate
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2]
    (τ : G.beliefArena.PositionalStrategy ParityPlayer.even)
    (huniform : G.ArenaStrategyLocallyUniform τ)
    (observations : List G.Observation1) (K1 : G.Belief)
    (R : G.ReadbackKnowledge)
    (hrun : (G.arenaReadbackController1 τ).run observations = some (K1, R))
    (state : G.ReadbackArenaState) (hstate : state ∈ R) :
    (G.arenaReadbackController1 τ).strategy observations =
      G.readbackCandidateAction1 τ K1 state := by
  rw [MooreController.strategy, hrun]
  exact G.readbackOutput1_eq_candidate τ K1 R
    (huniform.1 observations K1 R hrun) state hstate

/-- Player two's mirror output agreement. -/
theorem arenaReadbackController2_output_eq_candidate
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2]
    (τ : G.beliefArena.PositionalStrategy ParityPlayer.even)
    (huniform : G.ArenaStrategyLocallyUniform τ)
    (observations : List G.Observation2) (K2 : G.Belief)
    (R : G.ReadbackKnowledge)
    (hrun : (G.arenaReadbackController2 τ).run observations = some (K2, R))
    (state : G.ReadbackArenaState) (hstate : state ∈ R) :
    (G.arenaReadbackController2 τ).strategy observations =
      G.readbackCandidateAction2 τ K2 state := by
  rw [MooreController.strategy, hrun]
  exact G.readbackOutput2_eq_candidate τ K2 R
    (huniform.2 observations K2 R hrun) state hstate

/-- The history strategy implemented by the second-order readback controllers. -/
noncomputable def arenaReadbackHistoryStrategy
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2]
    (τ : G.beliefArena.PositionalStrategy ParityPlayer.even) :
    G.HistoryProductStrategy :=
  (G.arenaReadbackFiniteStrategy τ).toHistory

/-- The actual Even-arena state reconstructed along a play of the readback
controllers.  Each round advances with the two observations produced by the
real game play. -/
noncomputable def readbackArenaAlong
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2]
    (τ : G.beliefArena.PositionalStrategy ParityPlayer.even)
    (nature : Nat → G.Nature) : Nat → G.ReadbackArenaState
  | 0 => (G.arenaInitialThreads, G.beliefBundleU.initial)
  | n + 1 =>
      G.readbackArenaStep τ (readbackArenaAlong τ nature n)
        (G.observe1 (G.strategyState
          (G.arenaReadbackHistoryStrategy τ) nature (n + 1)).1)
        (G.observe2 (G.strategyState
          (G.arenaReadbackHistoryStrategy τ) nature (n + 1)).1)

/-- I1 at the second-order level: along the concrete readback play, the actual
arena state remains in both players' locally tracked sets.  This theorem uses
only the locally observable subset updates; uniformity is needed later to
identify the real actions with the arena commitment. -/
theorem readbackArenaAlong_mem_localKnowledge
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2]
    (τ : G.beliefArena.PositionalStrategy ParityPlayer.even)
    (nature : Nat → G.Nature) (n : Nat) :
    ∃ (K1 : G.Belief) (R1 : G.ReadbackKnowledge)
      (K2 : G.Belief) (R2 : G.ReadbackKnowledge),
      (G.arenaReadbackController1 τ).run
          (G.strategyState (G.arenaReadbackHistoryStrategy τ) nature n).2.1 =
        some (K1, R1) ∧
      (G.arenaReadbackController2 τ).run
          (G.strategyState (G.arenaReadbackHistoryStrategy τ) nature n).2.2 =
        some (K2, R2) ∧
      G.readbackArenaAlong τ nature n ∈ R1 ∧
      G.readbackArenaAlong τ nature n ∈ R2 ∧
      K1 = G.beliefAlong1 (G.arenaReadbackHistoryStrategy τ) nature n ∧
      K2 = G.beliefAlong2 (G.arenaReadbackHistoryStrategy τ) nature n := by
  induction n with
  | zero =>
      refine ⟨G.beliefInitial, G.readbackKnowledgeInitial,
        G.beliefInitial, G.readbackKnowledgeInitial, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rfl
      · rfl
      · simp [readbackArenaAlong, readbackKnowledgeInitial]
      · simp [readbackArenaAlong, readbackKnowledgeInitial]
      · rfl
      · rfl
  | succ n ih =>
      obtain ⟨K1, R1, K2, R2, hrun1, hrun2, hmem1, hmem2, hK1, hK2⟩ := ih
      let nextState := G.strategyState
        (G.arenaReadbackHistoryStrategy τ) nature (n + 1)
      let o1 := G.observe1 nextState.1
      let o2 := G.observe2 nextState.1
      let K1' := G.beliefStep1 K1 (G.readbackOutput1 τ K1 R1) o1
      let K2' := G.beliefStep2 K2 (G.readbackOutput2 τ K2 R2) o2
      let R1' := G.readbackKnowledgeStep1 τ R1 o1
      let R2' := G.readbackKnowledgeStep2 τ R2 o2
      refine ⟨K1', R1', K2', R2', ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [show nextState.2.1 =
            (G.strategyState (G.arenaReadbackHistoryStrategy τ) nature n).2.1 ++
              [o1] by rfl,
          MooreController.run_append_singleton, hrun1]
        rfl
      · rw [show nextState.2.2 =
            (G.strategyState (G.arenaReadbackHistoryStrategy τ) nature n).2.2 ++
              [o2] by rfl,
          MooreController.run_append_singleton, hrun2]
        rfl
      · simpa [R1', o1, o2, readbackArenaAlong] using
          (G.mem_readbackKnowledgeStep1_of_actual τ R1
            (G.readbackArenaAlong τ nature n) hmem1 o1 o2)
      · simpa [R2', o1, o2, readbackArenaAlong] using
          (G.mem_readbackKnowledgeStep2_of_actual τ R2
            (G.readbackArenaAlong τ nature n) hmem2 o1 o2)
      · rw [beliefAlong1, ← hK1]
        change G.beliefStep1 K1 (G.readbackOutput1 τ K1 R1) o1 =
          G.beliefStep1 K1
            ((G.arenaReadbackController1 τ).strategy
              (G.strategyState (G.arenaReadbackHistoryStrategy τ) nature n).2.1) o1
        rw [MooreController.strategy, hrun1]
        rfl
      · rw [beliefAlong2, ← hK2]
        change G.beliefStep2 K2 (G.readbackOutput2 τ K2 R2) o2 =
          G.beliefStep2 K2
            ((G.arenaReadbackController2 τ).strategy
              (G.strategyState (G.arenaReadbackHistoryStrategy τ) nature n).2.2) o2
        rw [MooreController.strategy, hrun2]
        rfl

/-- The bundle letter used by the reconstructed arena path in round `n`. -/
noncomputable def readbackArenaLetterAlong
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2]
    (τ : G.beliefArena.PositionalStrategy ParityPlayer.even)
    (nature : Nat → G.Nature) (n : Nat) : G.BeliefLetterU :=
  G.arenaLetter
    (G.arenaCommittedMove τ (G.readbackArenaAlong τ nature n).1
      (G.readbackArenaAlong τ nature n).2)
    (G.observe1 (G.strategyState (G.arenaReadbackHistoryStrategy τ)
      nature (n + 1)).1)
    (G.observe2 (G.strategyState (G.arenaReadbackHistoryStrategy τ)
      nature (n + 1)).1)

noncomputable def readbackArenaEvenAlong
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2]
    (τ : G.beliefArena.PositionalStrategy ParityPlayer.even)
    (nature : Nat → G.Nature) (n : Nat) : G.ArenaPos :=
  Sum.inl (G.readbackArenaAlong τ nature n)

noncomputable def readbackArenaOddAlong
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2]
    (τ : G.beliefArena.PositionalStrategy ParityPlayer.even)
    (nature : Nat → G.Nature) (n : Nat) : G.ArenaPos :=
  let state := G.readbackArenaAlong τ nature n
  Sum.inr (state.1, state.2,
    G.arenaCommittedMove τ state.1 state.2)

/-- Interleave the Even arena states and their committed Odd half-steps. -/
noncomputable def readbackArenaPath
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2]
    (τ : G.beliefArena.PositionalStrategy ParityPlayer.even)
    (nature : Nat → G.Nature) : Nat → G.ArenaPos :=
  interleavePlay (G.readbackArenaEvenAlong τ nature)
    (G.readbackArenaOddAlong τ nature)

theorem readbackArena_even_step
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2]
    (τ : G.beliefArena.PositionalStrategy ParityPlayer.even)
    (nature : Nat → G.Nature) (n : Nat) :
    G.arenaStepRel (G.readbackArenaEvenAlong τ nature n)
      (G.readbackArenaOddAlong τ nature n) := by
  let state := G.readbackArenaAlong τ nature n
  change G.arenaStepRel (Sum.inl state)
    (Sum.inr (state.1, state.2,
      G.arenaCommittedMove τ state.1 state.2))
  exact ⟨rfl, rfl, (G.beliefArena_even_move_shape τ state.1 state.2).2⟩

theorem readbackArena_odd_step
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2]
    (τ : G.beliefArena.PositionalStrategy ParityPlayer.even)
    (nature : Nat → G.Nature) (n : Nat) :
    G.arenaStepRel (G.readbackArenaOddAlong τ nature n)
      (G.readbackArenaEvenAlong τ nature (n + 1)) := by
  let state := G.readbackArenaAlong τ nature n
  let o1 := G.observe1 (G.strategyState (G.arenaReadbackHistoryStrategy τ)
    nature (n + 1)).1
  let o2 := G.observe2 (G.strategyState (G.arenaReadbackHistoryStrategy τ)
    nature (n + 1)).1
  change G.arenaStepRel
    (Sum.inr (state.1, state.2,
      G.arenaCommittedMove τ state.1 state.2))
    (Sum.inl (G.readbackArenaAlong τ nature (n + 1)))
  refine ⟨o1, o2, ?_, ?_⟩
  · rfl
  · rfl

theorem readbackArenaPath_play
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2]
    (τ : G.beliefArena.PositionalStrategy ParityPlayer.even)
    (nature : Nat → G.Nature) :
    G.beliefArena.Play (G.readbackArenaPath τ nature) := by
  exact interleavePlay_play G.arenaStepRel
    (G.readbackArenaEvenAlong τ nature)
    (G.readbackArenaOddAlong τ nature)
    (G.readbackArena_even_step τ nature)
    (G.readbackArena_odd_step τ nature)

theorem readbackArenaPath_from_initial
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2]
    (τ : G.beliefArena.PositionalStrategy ParityPlayer.even)
    (nature : Nat → G.Nature) :
    G.beliefArena.PlayFrom G.arenaInitialPosition
      (G.readbackArenaPath τ nature) := by
  constructor
  · rfl
  · exact G.readbackArenaPath_play τ nature

theorem readbackArenaPath_consistent
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2]
    (τ : G.beliefArena.PositionalStrategy ParityPlayer.even)
    (nature : Nat → G.Nature) :
    CountableParityGame.PositionalStrategy.Consistent τ
      (G.readbackArenaPath τ nature) := by
  intro k howner
  rcases Nat.mod_two_eq_zero_or_one k with hk | hk
  · rw [readbackArenaPath,
      interleavePlay_of_mod_eq_zero _ _ hk,
      interleavePlay_of_mod_eq_one _ _ (by omega : (k + 1) % 2 = 1),
      (by omega : (k + 1) / 2 = k / 2)]
    let state := G.readbackArenaAlong τ nature (k / 2)
    change G.readbackArenaOddAlong τ nature (k / 2) =
      τ.move (G.readbackArenaEvenAlong τ nature (k / 2))
    exact (G.beliefArena_even_move_shape τ state.1 state.2).1.symm
  · rw [readbackArenaPath,
      interleavePlay_of_mod_eq_one _ _ hk] at howner
    simp [readbackArenaOddAlong, beliefArena] at howner

/-- The bundle component of the reconstructed arena state is exactly the DPA
run on the reconstructed arena letters. -/
theorem readbackArenaAlong_bundle_run
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2]
    (τ : G.beliefArena.PositionalStrategy ParityPlayer.even)
    (nature : Nat → G.Nature) (n : Nat) :
    (G.readbackArenaAlong τ nature n).2 =
      G.beliefBundleU.run (G.readbackArenaLetterAlong τ nature) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change G.beliefBundleU.step
          (G.readbackArenaAlong τ nature n).2
          (G.readbackArenaLetterAlong τ nature n) =
        G.beliefBundleU.step
          (G.beliefBundleU.run (G.readbackArenaLetterAlong τ nature) n)
          (G.readbackArenaLetterAlong τ nature n)
      rw [ih]

theorem readbackArenaPath_priority_halved
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2]
    (τ : G.beliefArena.PositionalStrategy ParityPlayer.even)
    (nature : Nat → G.Nature) (k : Nat) :
    G.arenaPriority (G.readbackArenaPath τ nature k) =
      G.beliefBundleU.priority
        (G.readbackArenaAlong τ nature (k / 2)).2 := by
  apply interleavePlay_priority G.arenaPriority
    (G.readbackArenaEvenAlong τ nature)
    (G.readbackArenaOddAlong τ nature)
    (fun n => G.beliefBundleU.priority
      (G.readbackArenaAlong τ nature n).2)
  · intro n
    rfl
  · intro n
    rfl

/-- A winning arena strategy forces acceptance of the concrete reconstructed
bundle word on every Nature sequence. -/
theorem beliefBundleU_accepts_readbackArenaLetterAlong_of_winner
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2]
    (τ : G.beliefArena.PositionalStrategy ParityPlayer.even)
    (hwin : CountableParityGame.PositionalStrategy.WinningFrom
      (G := G.beliefArena) τ G.arenaInitialPosition)
    (nature : Nat → G.Nature) :
    G.beliefBundleU.Accepts (G.readbackArenaLetterAlong τ nature) := by
  have harena := hwin (G.readbackArenaPath τ nature)
    (G.readbackArenaPath_from_initial τ nature)
    (G.readbackArenaPath_consistent τ nature)
  change NatSeqMinEvenParity
    (fun k => G.arenaPriority (G.readbackArenaPath τ nature k)) at harena
  have hhalf : NatSeqMinEvenParity (fun n =>
      G.beliefBundleU.priority (G.readbackArenaAlong τ nature n).2) :=
    (natSeqMinEvenParity_halved
      (G.readbackArenaPath_priority_halved τ nature)).mp harena
  change NatSeqMinEvenParity (fun n => G.beliefBundleU.priority
    (G.beliefBundleU.run (G.readbackArenaLetterAlong τ nature) n))
  simpa only [G.readbackArenaAlong_bundle_run τ nature] using hhalf

/-- Under I3 local uniformity, the concrete readback-controller play is a
surviving thread of the arena's unified bundle word. -/
theorem readbackRealThread_isRun
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2]
    (τ : G.beliefArena.PositionalStrategy ParityPlayer.even)
    (huniform : G.ArenaStrategyLocallyUniform τ)
    (nature : Nat → G.Nature) :
    G.beliefThreadSystemU.IsRun (G.readbackArenaLetterAlong τ nature)
      (G.realThreadU (G.arenaReadbackHistoryStrategy τ) nature) := by
  refine ⟨rfl, ?_⟩
  intro n
  refine ⟨nature n, ?_⟩
  obtain ⟨K1, R1, K2, R2, hrun1, hrun2, hmem1, hmem2, hK1, hK2⟩ :=
    G.readbackArenaAlong_mem_localKnowledge τ nature n
  have ha1 := G.arenaReadbackController1_output_eq_candidate τ huniform
    (G.strategyState (G.arenaReadbackHistoryStrategy τ) nature n).2.1
    K1 R1 hrun1 (G.readbackArenaAlong τ nature n) hmem1
  have ha2 := G.arenaReadbackController2_output_eq_candidate τ huniform
    (G.strategyState (G.arenaReadbackHistoryStrategy τ) nature n).2.2
    K2 R2 hrun2 (G.readbackArenaAlong τ nature n) hmem2
  have ha1' :
      (G.arenaReadbackHistoryStrategy τ).1
          (G.strategyState (G.arenaReadbackHistoryStrategy τ) nature n).2.1 =
        G.readbackCandidateAction1 τ K1
          (G.readbackArenaAlong τ nature n) := by
    exact ha1
  have ha2' :
      (G.arenaReadbackHistoryStrategy τ).2
          (G.strategyState (G.arenaReadbackHistoryStrategy τ) nature n).2.2 =
        G.readbackCandidateAction2 τ K2
          (G.readbackArenaAlong τ nature n) := by
    exact ha2
  cases hmove : G.arenaCommittedMove τ
      (G.readbackArenaAlong τ nature n).1
      (G.readbackArenaAlong τ nature n).2 with
  | inl move =>
      have hone :
          (G.arenaReadbackHistoryStrategy τ).1
              (G.strategyState (G.arenaReadbackHistoryStrategy τ) nature n).2.1 =
            move.1 := by
        simpa [readbackCandidateAction1, hmove] using ha1'
      have htwo :
          (G.arenaReadbackHistoryStrategy τ).2
              (G.strategyState (G.arenaReadbackHistoryStrategy τ) nature n).2.2 =
            move.2 K2 := by
        simpa [readbackCandidateAction2, hmove] using ha2'
      rw [hK2] at htwo
      simp only [realThreadU, readbackArenaLetterAlong, hmove,
        arenaLetter, beliefThreadSystemU, beliefThreadStepU]
      rw [← hone, ← htwo]
      have hnext : G.next
          (G.strategyState (G.arenaReadbackHistoryStrategy τ) nature n).1
          ((G.arenaReadbackHistoryStrategy τ).1
            (G.strategyState (G.arenaReadbackHistoryStrategy τ) nature n).2.1)
          ((G.arenaReadbackHistoryStrategy τ).2
            (G.strategyState (G.arenaReadbackHistoryStrategy τ) nature n).2.2)
          (nature n) =
        (G.strategyState (G.arenaReadbackHistoryStrategy τ) nature (n + 1)).1 := rfl
      rw [hnext, if_pos rfl]
      rfl
  | inr move =>
      have hone :
          (G.arenaReadbackHistoryStrategy τ).1
              (G.strategyState (G.arenaReadbackHistoryStrategy τ) nature n).2.1 =
            move.2 K1 := by
        simpa [readbackCandidateAction1, hmove] using ha1'
      have htwo :
          (G.arenaReadbackHistoryStrategy τ).2
              (G.strategyState (G.arenaReadbackHistoryStrategy τ) nature n).2.2 =
            move.1 := by
        simpa [readbackCandidateAction2, hmove] using ha2'
      rw [hK1] at hone
      simp only [realThreadU, readbackArenaLetterAlong, hmove,
        arenaLetter, beliefThreadSystemU, beliefThreadStepU]
      rw [← hone, ← htwo]
      have hnext : G.next
          (G.strategyState (G.arenaReadbackHistoryStrategy τ) nature n).1
          ((G.arenaReadbackHistoryStrategy τ).1
            (G.strategyState (G.arenaReadbackHistoryStrategy τ) nature n).2.1)
          ((G.arenaReadbackHistoryStrategy τ).2
            (G.strategyState (G.arenaReadbackHistoryStrategy τ) nature n).2.2)
          (nature n) =
        (G.strategyState (G.arenaReadbackHistoryStrategy τ) nature (n + 1)).1 := rfl
      rw [hnext, if_pos rfl]
      rfl

/-- **I3 soundness target.**  A *locally uniform* positional arena winner reads
back through the concrete second-order Moore controllers and wins the original
game.  Local uniformity cannot be dropped for an arbitrary perfect-information
winner: its moves may otherwise disagree at arena states indistinguishable to
the follower. -/
def BeliefArenaWinnerReadback
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2] : Prop :=
  ∀ τ : G.beliefArena.PositionalStrategy ParityPlayer.even,
    CountableParityGame.PositionalStrategy.WinningFrom
        (G := G.beliefArena) τ G.arenaInitialPosition →
      G.ArenaStrategyLocallyUniform τ →
        G.FiniteStateStrategyWins (G.arenaReadbackFiniteStrategy τ)

/-- **The remaining Berwanger completeness target.**  A distributed
perfect-recall winner induces a positional arena winner whose commitments are
uniform on every second-order local information set.  This direct formulation
is essential: the unrestricted perfect-information arena may have a
non-uniform winner even when no uniform winner exists, so mere winning-region
membership is not a sound premise for uniformization. -/
def BeliefArenaUniformCompleteness
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2] : Prop :=
  G.HistoryRealizable →
    ∃ τ : G.beliefArena.PositionalStrategy ParityPlayer.even,
      CountableParityGame.PositionalStrategy.WinningFrom
          (G := G.beliefArena) τ G.arenaInitialPosition ∧
        G.ArenaStrategyLocallyUniform τ

/-- **I3 readback soundness is complete.**  A locally uniform arena winner's
second-order Moore controllers generate a real thread of the accepted unified
bundle word, hence win the original parity objective. -/
theorem beliefArenaWinnerReadback
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2] :
    G.BeliefArenaWinnerReadback := by
  intro τ hwin huniform nature
  exact G.beliefBundleU_accepts_states_win
    (G.readbackArenaLetterAlong τ nature)
    (fun n => (G.strategyState (G.arenaReadbackHistoryStrategy τ) nature n).1)
    (fun n => (G.beliefAlong1 (G.arenaReadbackHistoryStrategy τ) nature n,
      G.beliefAlong2 (G.arenaReadbackHistoryStrategy τ) nature n))
    (G.readbackRealThread_isRun τ huniform nature)
    (G.beliefBundleU_accepts_readbackArenaLetterAlong_of_winner τ hwin nature)

/-- The Berwanger finite-memory extraction follows immediately from the two
honest semantic halves: completeness of the belief reduction and I3 readback
of its positional winner.  Positional determinacy itself is already proved in
the repository. -/
theorem finiteStateRealizable_of_beliefArena_core
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2]
    (hcomplete : G.BeliefArenaUniformCompleteness)
    (hreadback : G.BeliefArenaWinnerReadback) :
    G.HistoryRealizable → G.FiniteStateRealizable := by
  intro hreal
  obtain ⟨τ, hτ, huniform⟩ := hcomplete hreal
  exact ⟨G.arenaReadbackFiniteStrategy τ, hreadback τ hτ huniform⟩

/-- With I3 readback now discharged, finite-memory extraction has exactly one
remaining semantic premise: uniform completeness of the belief arena. -/
theorem finiteStateRealizable_of_beliefArena_uniformCompleteness
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2]
    (hcomplete : G.BeliefArenaUniformCompleteness) :
    G.HistoryRealizable → G.FiniteStateRealizable :=
  G.finiteStateRealizable_of_beliefArena_core hcomplete
    G.beliefArenaWinnerReadback

end FiniteConcurrentGame

end DistributedSynthesis
