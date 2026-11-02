/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Definition.DefOmegaAutomata
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Countable
import Mathlib.Tactic

/-!
# Countable parity games

This file starts the reusable Zielonka-style backend for parity games on
countable finitely-coloured arenas.  The definitions are deliberately generic:
they are not tied to the APA support game.

The completed theorem target is memoryless determinacy for countable parity
games with finitely many priorities.  The material proved here is the common
semantic substrate needed by that proof: plays, history-dependent and
positional strategies, and prefix-independence of the min-even parity
objective.
-/

namespace DistributedSynthesis

universe u

/-- The two players in a parity game. -/
inductive ParityPlayer where
  | even
  | odd
deriving DecidableEq, Repr

namespace ParityPlayer

/-- The opponent of a parity-game player. -/
def other : ParityPlayer -> ParityPlayer
  | even => odd
  | odd => even

@[simp]
theorem other_even : other even = odd :=
  rfl

@[simp]
theorem other_odd : other odd = even :=
  rfl

@[simp]
theorem other_other (player : ParityPlayer) :
    player.other.other = player := by
  cases player <;> rfl

/-- In a two-player game, any player different from `player` is its opponent. -/
theorem eq_other_of_ne {player owner : ParityPlayer}
    (h : owner ≠ player) :
    owner = player.other := by
  cases player <;> cases owner <;> simp_all [other]

@[simp]
theorem other_ne (player : ParityPlayer) :
    player.other ≠ player := by
  cases player <;> simp [other]

@[simp]
theorem ne_other (player : ParityPlayer) :
    player ≠ player.other := by
  cases player <;> simp [other]

end ParityPlayer

/-- The player favoured by a priority under the min-parity convention. -/
noncomputable def priorityOwner (priority : Nat) : ParityPlayer :=
  by
    classical
    exact
      if DetParityAutomaton.NatEven priority then
        ParityPlayer.even
      else
        ParityPlayer.odd

@[simp]
theorem priorityOwner_of_even
    {priority : Nat}
    (hpriority : DetParityAutomaton.NatEven priority) :
    priorityOwner priority = ParityPlayer.even := by
  classical
  simp [priorityOwner, hpriority]

@[simp]
theorem priorityOwner_of_odd
    {priority : Nat}
    (hpriority : ¬ DetParityAutomaton.NatEven priority) :
    priorityOwner priority = ParityPlayer.odd := by
  classical
  simp [priorityOwner, hpriority]

theorem priorityOwner_eq_even_iff
    {priority : Nat} :
    priorityOwner priority = ParityPlayer.even ↔
      DetParityAutomaton.NatEven priority := by
  classical
  by_cases hpriority : DetParityAutomaton.NatEven priority
  · simp [priorityOwner, hpriority]
  · simp [priorityOwner, hpriority]

theorem priorityOwner_eq_odd_iff
    {priority : Nat} :
    priorityOwner priority = ParityPlayer.odd ↔
      ¬ DetParityAutomaton.NatEven priority := by
  classical
  by_cases hpriority : DetParityAutomaton.NatEven priority
  · simp [priorityOwner, hpriority]
  · simp [priorityOwner, hpriority]

/--
A countable parity game arena with finitely many priorities.

The edge relation is total, so all plays are infinite.  The winning convention
is the same min-even convention used by the automata development: the least
priority seen infinitely often decides the winner.
-/
structure CountableParityGame where
  Position : Type u
  positionCountable : Countable Position
  owner : Position -> ParityPlayer
  step : Position -> Position -> Prop
  step_total : ∀ position : Position, ∃ next : Position, step position next
  priority : Position -> Nat
  priority_finite : Set.Finite (Set.range priority)

attribute [instance] CountableParityGame.positionCountable

namespace CountableParityGame

variable (G : CountableParityGame.{u})

/-- The finite set of priorities that occur in the game. -/
noncomputable def priorityRangeFinset : Finset Nat :=
  G.priority_finite.toFinset

@[simp]
theorem mem_priorityRangeFinset (priority : Nat) :
    priority ∈ G.priorityRangeFinset ↔ priority ∈ Set.range G.priority := by
  exact G.priority_finite.mem_toFinset

/-- The priority range is nonempty whenever a start position is given. -/
theorem priorityRangeFinset_nonempty (start : G.Position) :
    G.priorityRangeFinset.Nonempty := by
  exact ⟨G.priority start, by simp [priorityRangeFinset]⟩

/-- The least priority occurring in the game, using `start` only as a witness of nonemptiness. -/
noncomputable def leastPriorityFrom (start : G.Position) : Nat :=
  G.priorityRangeFinset.min' (G.priorityRangeFinset_nonempty start)

/-- The selected least priority occurs in the game. -/
theorem leastPriorityFrom_mem_range (start : G.Position) :
    G.leastPriorityFrom start ∈ Set.range G.priority := by
  rw [← G.mem_priorityRangeFinset]
  exact Finset.min'_mem G.priorityRangeFinset (G.priorityRangeFinset_nonempty start)

/-- The selected priority is below every occurring priority. -/
theorem leastPriorityFrom_le_priority
    (start position : G.Position) :
    G.leastPriorityFrom start ≤ G.priority position := by
  exact
    Finset.min'_le G.priorityRangeFinset (G.priority position)
      (by simp [priorityRangeFinset])

/-- No priority strictly below the selected least priority occurs. -/
theorem not_priority_lt_leastPriorityFrom
    (start : G.Position)
    {priority : Nat}
    (hlt : priority < G.leastPriorityFrom start) :
    priority ∉ Set.range G.priority := by
  intro hpriority
  have hle :
      G.leastPriorityFrom start ≤ priority := by
    rw [← G.mem_priorityRangeFinset] at hpriority
    exact Finset.min'_le G.priorityRangeFinset priority hpriority
  omega

/-- Positions with a fixed priority. -/
def priorityClass (priority : Nat) : Set G.Position :=
  {position | G.priority position = priority}

/-- A finite prefix ending at time `n`, represented by positions `0, ..., n`. -/
abbrev Prefix (n : Nat) :=
  Fin (n + 1) -> G.Position

/-- The last position of a prefix of length `n + 1`. -/
def prefixLast {n : Nat} (pref : G.Prefix n) : G.Position :=
  pref ⟨n, Nat.lt_succ_self n⟩

/-- A prefix follows the arena edges at every adjacent pair. -/
def PrefixLegal {n : Nat} (pref : G.Prefix n) : Prop :=
  ∀ i : Fin n,
    G.step
      (pref ⟨i.1, by omega⟩)
      (pref ⟨i.1 + 1, by omega⟩)

/-- Infinite plays follow the arena edges at every time. -/
def Play (path : Nat -> G.Position) : Prop :=
  ∀ n : Nat, G.step (path n) (path (n + 1))

/-- Infinite plays from a designated start position. -/
def PlayFrom (start : G.Position) (path : Nat -> G.Position) : Prop :=
  path 0 = start ∧ G.Play path

/-- The finite prefix of an infinite path through time `n`. -/
def prefixOfPath (path : Nat -> G.Position) (n : Nat) : G.Prefix n :=
  fun i => path i.1

@[simp]
theorem prefixLast_prefixOfPath
    (path : Nat -> G.Position)
    (n : Nat) :
    G.prefixLast (G.prefixOfPath path n) = path n :=
  rfl

/-- Prefixes cut from plays are legal prefixes. -/
theorem prefixOfPath_legal
    {path : Nat -> G.Position}
    (hplay : G.Play path)
    (n : Nat) :
    G.PrefixLegal (G.prefixOfPath path n) := by
  intro i
  simpa [prefixOfPath] using hplay i.1

/-- The one-position prefix. -/
def singletonPrefix (position : G.Position) : G.Prefix 0 :=
  fun _ => position

@[simp]
theorem singletonPrefix_apply
    (position : G.Position)
    (i : Fin 1) :
    G.singletonPrefix position i = position :=
  rfl

@[simp]
theorem prefixLast_singletonPrefix
    (position : G.Position) :
    G.prefixLast (G.singletonPrefix position) = position :=
  rfl

/-- Add one position to the front of a finite prefix. -/
def prefixCons
    (position : G.Position)
    {n : Nat}
    (pref : G.Prefix n) :
    G.Prefix (n + 1) :=
  Fin.cons position pref

@[simp]
theorem prefixCons_zero
    (position : G.Position)
    {n : Nat}
    (pref : G.Prefix n) :
    G.prefixCons position pref 0 = position := by
  simp [prefixCons]

@[simp]
theorem prefixCons_succ
    (position : G.Position)
    {n : Nat}
    (pref : G.Prefix n)
    (i : Fin (n + 1)) :
    G.prefixCons position pref i.succ = pref i := by
  simp [prefixCons]

@[simp]
theorem prefixLast_prefixCons
    (position : G.Position)
    {n : Nat}
    (pref : G.Prefix n) :
    G.prefixLast (G.prefixCons position pref) = G.prefixLast pref := by
  simpa [prefixLast] using
    G.prefixCons_succ position pref ⟨n, Nat.lt_succ_self n⟩

/-- A legal prefix remains legal after adding one legal incoming edge. -/
theorem prefixCons_legal
    {position next : G.Position}
    {n : Nat}
    {pref : G.Prefix n}
    (hstep : G.step position next)
    (hfirst : pref 0 = next)
    (hlegal : G.PrefixLegal pref) :
    G.PrefixLegal (G.prefixCons position pref) := by
  intro i
  cases i using Fin.cases with
  | zero =>
      simpa [prefixCons, hfirst] using hstep
  | succ i =>
      simpa [prefixCons] using hlegal i

/-- Drop the first position from a nonempty finite prefix. -/
def prefixTail
    {n : Nat}
    (pref : G.Prefix (n + 1)) :
    G.Prefix n :=
  fun i => pref i.succ

@[simp]
theorem prefixTail_apply
    {n : Nat}
    (pref : G.Prefix (n + 1))
    (i : Fin (n + 1)) :
    G.prefixTail pref i = pref i.succ :=
  rfl

@[simp]
theorem prefixTail_prefixCons
    (position : G.Position)
    {n : Nat}
    (pref : G.Prefix n) :
    G.prefixTail (G.prefixCons position pref) = pref := by
  funext i
  simp [prefixTail, prefixCons]

@[simp]
theorem prefixLast_prefixTail
    {n : Nat}
    (pref : G.Prefix (n + 1)) :
    G.prefixLast (G.prefixTail pref) = G.prefixLast pref := by
  simp [prefixLast, prefixTail]

/-- Tails of legal prefixes are legal. -/
theorem prefixTail_legal
    {n : Nat}
    {pref : G.Prefix (n + 1)}
    (hlegal : G.PrefixLegal pref) :
    G.PrefixLegal (G.prefixTail pref) := by
  intro i
  simpa [prefixTail] using hlegal i.succ

/-- Keep the first `k + 1` positions of a finite prefix of length `n`. -/
def prefixTake
    {n : Nat}
    (pref : G.Prefix n)
    (k : Nat)
    (hk : k ≤ n) :
    G.Prefix k :=
  fun i => pref ⟨i.1, by omega⟩

@[simp]
theorem prefixTake_apply
    {n k : Nat}
    (pref : G.Prefix n)
    (hk : k ≤ n)
    (i : Fin (k + 1)) :
    G.prefixTake pref k hk i = pref ⟨i.1, by omega⟩ :=
  rfl

@[simp]
theorem prefixTake_zero
    {n : Nat}
    (pref : G.Prefix n)
    (hzero : 0 ≤ n) :
    G.prefixTake pref 0 hzero = G.singletonPrefix (pref 0) := by
  funext i
  fin_cases i
  simp [prefixTake, singletonPrefix]

@[simp]
theorem prefixTake_self
    {n : Nat}
    (pref : G.Prefix n)
    (hn : n ≤ n := le_rfl) :
    G.prefixTake pref n hn = pref := by
  funext i
  simp [prefixTake]

/--
Taking `j + 1` positions from a prefix is the same as adding the first
position to the first `j + 1` positions of its tail.
-/
theorem prefixCons_prefixTake_prefixTail
    {n j : Nat}
    (pref : G.Prefix (n + 1))
    (hj : j ≤ n) :
    G.prefixCons (pref 0)
      (G.prefixTake (G.prefixTail pref) j hj) =
        G.prefixTake pref (j + 1) (by omega) := by
  funext i
  cases i using Fin.cases with
  | zero =>
      simp [prefixCons, prefixTake]
  | succ i =>
      simp [prefixCons, prefixTake, prefixTail]

/-- The second position of a prefix with at least two positions. -/
def prefixSecond
    {n : Nat}
    (pref : G.Prefix (n + 1)) :
    G.Position :=
  pref ⟨1, by omega⟩

@[simp]
theorem prefixSecond_prefixOfPath_succ
    (path : Nat -> G.Position)
    (n : Nat) :
    G.prefixSecond (G.prefixOfPath path (n + 1)) = path 1 :=
  rfl

/-- Add one position to the end of a finite prefix. -/
def prefixSnoc
    {n : Nat}
    (pref : G.Prefix n)
    (position : G.Position) :
    G.Prefix (n + 1) :=
  fun i =>
    if hlast : i.1 = n + 1 then
      position
    else
      pref ⟨i.1, by omega⟩

@[simp]
theorem prefixSnoc_castSucc
    {n : Nat}
    (pref : G.Prefix n)
    (position : G.Position)
    (i : Fin (n + 1)) :
    G.prefixSnoc pref position i.castSucc = pref i := by
  change
    (if hlast : i.1 = n + 1 then
      position
    else
      pref ⟨i.1, by omega⟩) = pref i
  have hnot : ¬ i.1 = n + 1 := by
    have hi : i.1 < n + 1 := i.2
    omega
  simp [hnot]

@[simp]
theorem prefixLast_prefixSnoc
    {n : Nat}
    (pref : G.Prefix n)
    (position : G.Position) :
    G.prefixLast (G.prefixSnoc pref position) = position := by
  simp [prefixLast, prefixSnoc]

/-- A legal prefix remains legal after appending one legal outgoing edge. -/
theorem prefixSnoc_legal
    {n : Nat}
    {pref : G.Prefix n}
    {next : G.Position}
    (hlegal : G.PrefixLegal pref)
    (hstep : G.step (G.prefixLast pref) next) :
    G.PrefixLegal (G.prefixSnoc pref next) := by
  intro i
  by_cases hlast : i.1 = n
  · have hsourceNotLast :
        ¬ i.1 = n + 1 := by
        have hi : i.1 < n + 1 := i.2
        omega
    have htargetLast :
        i.1 + 1 = n + 1 := by
        omega
    change
      G.step
        (if h : i.1 = n + 1 then next else pref ⟨i.1, by omega⟩)
        (if h : i.1 + 1 = n + 1 then next else pref ⟨i.1 + 1, by omega⟩)
    simpa [hsourceNotLast, htargetLast, prefixLast, hlast] using
      hstep
  · have hsourceNotLast :
        ¬ i.1 = n + 1 := by
        have hi : i.1 < n + 1 := i.2
        omega
    have htargetNotLast :
        ¬ i.1 + 1 = n + 1 := by
        have hi : i.1 < n + 1 := i.2
        omega
    have hstepOld :
        G.step
          (pref ⟨i.1, by omega⟩)
          (pref ⟨i.1 + 1, by omega⟩) :=
      hlegal ⟨i.1, by omega⟩
    change
      G.step
        (if h : i.1 = n + 1 then next else pref ⟨i.1, by omega⟩)
        (if h : i.1 + 1 = n + 1 then next else pref ⟨i.1 + 1, by omega⟩)
    simpa [hsourceNotLast, htargetNotLast, hlast] using hstepOld

/-- A history-dependent strategy for one player. -/
structure Strategy (player : ParityPlayer) where
  move : ∀ n : Nat, G.Prefix n -> G.Position

namespace Strategy

variable {G}
variable {player : ParityPlayer}

/-- A strategy only prescribes legal moves at positions owned by its player. -/
def Legal (strategy : G.Strategy player) : Prop :=
  ∀ n : Nat, ∀ pref : G.Prefix n,
    G.PrefixLegal pref ->
      G.owner (G.prefixLast pref) = player ->
        G.step (G.prefixLast pref) (strategy.move n pref)

/-- A play is consistent with a history-dependent strategy. -/
def Consistent (strategy : G.Strategy player)
    (path : Nat -> G.Position) : Prop :=
  ∀ n : Nat,
    G.owner (path n) = player ->
      path (n + 1) = strategy.move n (G.prefixOfPath path n)

/--
Residual strategy after a fixed first edge `start -> next`.

On prefixes that really start at `next`, this consults the original strategy on
the prefix with `start` prepended.  On irrelevant prefixes it chooses an
arbitrary legal edge, so the strategy remains globally legal.
-/
noncomputable def residual
    (strategy : G.Strategy player)
    (start next : G.Position) :
    G.Strategy player where
  move n pref :=
    by
      classical
      exact
        if hfirst : pref 0 = next then
          strategy.move (n + 1) (G.prefixCons start pref)
        else
          Classical.choose (G.step_total (G.prefixLast pref))

@[simp]
theorem residual_move_of_first
    (strategy : G.Strategy player)
    (start next : G.Position)
    {n : Nat}
    (pref : G.Prefix n)
    (hfirst : pref 0 = next) :
    (strategy.residual start next).move n pref =
      strategy.move (n + 1) (G.prefixCons start pref) := by
  classical
  simp [residual, hfirst]

theorem residual_legal
    {strategy : G.Strategy player}
    {start next : G.Position}
    (hlegal : strategy.Legal)
    (hstep : G.step start next) :
    (strategy.residual start next).Legal := by
  intro n pref hprefix howner
  classical
  by_cases hfirst : pref 0 = next
  · change
      G.step (G.prefixLast pref)
        (if h : pref 0 = next then
          strategy.move (n + 1) (G.prefixCons start pref)
        else
          Classical.choose (G.step_total (G.prefixLast pref)))
    have hconsLegal :
        G.PrefixLegal (G.prefixCons start pref) :=
      G.prefixCons_legal hstep hfirst hprefix
    have hownerCons :
        G.owner (G.prefixLast (G.prefixCons start pref)) = player := by
      simpa using howner
    simpa [hfirst] using
      hlegal (n + 1) (G.prefixCons start pref) hconsLegal hownerCons
  · change
      G.step (G.prefixLast pref)
        (if h : pref 0 = next then
          strategy.move (n + 1) (G.prefixCons start pref)
        else
          Classical.choose (G.step_total (G.prefixLast pref)))
    simpa [hfirst] using Classical.choose_spec (G.step_total (G.prefixLast pref))

/--
A finite prefix is consistent with a history-dependent strategy when every
player-owned edge in the prefix is exactly the edge prescribed by the strategy
on the preceding finite history.
-/
def PrefixConsistent
    (strategy : G.Strategy player)
    {n : Nat}
    (pref : G.Prefix n) :
    Prop :=
  ∀ i : Fin n,
    G.owner (pref ⟨i.1, by omega⟩) = player ->
      pref ⟨i.1 + 1, by omega⟩ =
        strategy.move i.1
          (G.prefixTake pref i.1 (by omega))

/-- The residual strategy obtained after consuming a finite prefix. -/
noncomputable def residualAlongPrefix
    (strategy : G.Strategy player) :
    ∀ {n : Nat}, G.Prefix n -> G.Strategy player
  | 0, _pref => strategy
  | n + 1, pref =>
      (strategy.residual (pref 0) (G.prefixSecond pref)).residualAlongPrefix
        (G.prefixTail pref)

@[simp]
theorem residualAlongPrefix_zero
    (strategy : G.Strategy player)
    (pref : G.Prefix 0) :
    strategy.residualAlongPrefix pref = strategy :=
  rfl

theorem residualAlongPrefix_succ
    (strategy : G.Strategy player)
    {n : Nat}
    (pref : G.Prefix (n + 1)) :
    strategy.residualAlongPrefix pref =
      (strategy.residual (pref 0) (G.prefixSecond pref)).residualAlongPrefix
        (G.prefixTail pref) :=
  rfl

theorem prefixConsistent_tail
    {strategy : G.Strategy player}
    {n : Nat}
    {pref : G.Prefix (n + 1)}
    (hconsistent : strategy.PrefixConsistent pref) :
    (strategy.residual (pref 0) (G.prefixSecond pref)).PrefixConsistent
      (G.prefixTail pref) := by
  intro i howner
  have horiginal :=
    hconsistent ⟨i.1 + 1, by omega⟩ (by simpa [prefixTail] using howner)
  have hfirst :
      G.prefixTake (G.prefixTail pref) i.1 (by omega) 0 =
        G.prefixSecond pref := by
    simp [prefixTake, prefixTail, prefixSecond]
  calc
    G.prefixTail pref ⟨i.1 + 1, by omega⟩
        = pref ⟨i.1 + 2, by omega⟩ := rfl
    _ = strategy.move (i.1 + 1)
          (G.prefixTake pref (i.1 + 1) (by omega)) := horiginal
    _ = strategy.move (i.1 + 1)
          (G.prefixCons (pref 0)
            (G.prefixTake (G.prefixTail pref) i.1 (by omega))) := by
          rw [G.prefixCons_prefixTake_prefixTail pref (by omega)]
    _ = (strategy.residual (pref 0) (G.prefixSecond pref)).move i.1
          (G.prefixTake (G.prefixTail pref) i.1 (by omega)) := by
          rw [strategy.residual_move_of_first (pref 0) (G.prefixSecond pref)
            (G.prefixTake (G.prefixTail pref) i.1 (by omega)) hfirst]

theorem residualAlongPrefix_move_zero
    (strategy : G.Strategy player) :
    ∀ {n : Nat} (pref : G.Prefix n),
      (strategy.residualAlongPrefix pref).move 0
          (G.singletonPrefix (G.prefixLast pref)) =
        strategy.move n pref
  | 0, pref => by
      have hpref : G.singletonPrefix (G.prefixLast pref) = pref := by
        funext i
        fin_cases i
        simp [prefixLast, singletonPrefix]
      simpa [residualAlongPrefix, hpref]
  | n + 1, pref => by
      have hfirst :
          G.prefixTake (G.prefixTail pref) n (by omega) 0 =
            G.prefixSecond pref := by
        simp [prefixTake, prefixTail, prefixSecond]
      calc
        (strategy.residualAlongPrefix pref).move 0
            (G.singletonPrefix (G.prefixLast pref))
            =
          ((strategy.residual (pref 0) (G.prefixSecond pref)).residualAlongPrefix
              (G.prefixTail pref)).move 0
            (G.singletonPrefix (G.prefixLast (G.prefixTail pref))) := by
              simp [residualAlongPrefix]
        _ = (strategy.residual (pref 0) (G.prefixSecond pref)).move n
              (G.prefixTail pref) := by
              simpa using
                residualAlongPrefix_move_zero
                  (strategy.residual (pref 0) (G.prefixSecond pref))
                  (G.prefixTail pref)
        _ = strategy.move (n + 1)
              (G.prefixCons (pref 0) (G.prefixTail pref)) := by
              rw [strategy.residual_move_of_first (pref 0)
                (G.prefixSecond pref) (G.prefixTail pref)]
              simp [prefixTail, prefixSecond]
        _ = strategy.move (n + 1) pref := by
              congr 1
              funext i
              cases i using Fin.cases with
              | zero =>
                  simp [prefixCons]
              | succ i =>
                  simp [prefixCons, prefixTail]

/--
Strategy that plays a fixed first edge `start -> next`, then delegates to
`strategy` on the remaining history.
-/
noncomputable def prepend
    (strategy : G.Strategy player)
    (start next : G.Position) :
    G.Strategy player where
  move
    | 0, pref =>
        by
          classical
          exact
            if hstart : G.prefixLast pref = start then
              next
            else
              Classical.choose (G.step_total (G.prefixLast pref))
    | n + 1, pref =>
        strategy.move n (G.prefixTail pref)

@[simp]
theorem prepend_move_zero_of_start
    (strategy : G.Strategy player)
    (start next : G.Position)
    (pref : G.Prefix 0)
    (hstart : G.prefixLast pref = start) :
    (strategy.prepend start next).move 0 pref = next := by
  classical
  simp [prepend, hstart]

@[simp]
theorem prepend_move_succ
    (strategy : G.Strategy player)
    (start next : G.Position)
    (n : Nat)
    (pref : G.Prefix (n + 1)) :
    (strategy.prepend start next).move (n + 1) pref =
      strategy.move n (G.prefixTail pref) :=
  rfl

theorem prepend_legal
    {strategy : G.Strategy player}
    {start next : G.Position}
    (hlegal : strategy.Legal)
    (hstep : G.step start next) :
    (strategy.prepend start next).Legal := by
  intro n pref hprefix howner
  cases n with
  | zero =>
      classical
      by_cases hstart : G.prefixLast pref = start
      · change
          G.step (G.prefixLast pref)
            (if h : G.prefixLast pref = start then
              next
            else
              Classical.choose (G.step_total (G.prefixLast pref)))
        simpa [hstart] using hstart ▸ hstep
      · change
          G.step (G.prefixLast pref)
            (if h : G.prefixLast pref = start then
              next
            else
              Classical.choose (G.step_total (G.prefixLast pref)))
        simpa [hstart] using
          Classical.choose_spec (G.step_total (G.prefixLast pref))
  | succ n =>
      have htailLegal :
          G.PrefixLegal (G.prefixTail pref) :=
        G.prefixTail_legal hprefix
      have htailOwner :
          G.owner (G.prefixLast (G.prefixTail pref)) = player := by
        simpa using howner
      simpa [prepend] using
        hlegal n (G.prefixTail pref) htailLegal htailOwner

/--
The finite history generated by a strategy from a start position, with arbitrary
legal opponent moves.
-/
noncomputable def generatedPrefix
    (strategy : G.Strategy player)
    (start : G.Position) :
    ∀ n : Nat, G.Prefix n
  | 0 => G.singletonPrefix start
  | n + 1 =>
      let pref := strategy.generatedPrefix start n
      let current := G.prefixLast pref
      let next :=
        if howner : G.owner current = player then
          strategy.move n pref
        else
          Classical.choose (G.step_total current)
      G.prefixSnoc pref next

@[simp]
theorem generatedPrefix_zero
    (strategy : G.Strategy player)
    (start : G.Position) :
    strategy.generatedPrefix start 0 = G.singletonPrefix start :=
  rfl

theorem generatedPrefix_succ
    (strategy : G.Strategy player)
    (start : G.Position)
    (n : Nat) :
    strategy.generatedPrefix start (n + 1) =
      let pref := strategy.generatedPrefix start n
      let current := G.prefixLast pref
      let next :=
        if howner : G.owner current = player then
          strategy.move n pref
        else
          Classical.choose (G.step_total current)
      G.prefixSnoc pref next :=
  rfl

/-- The infinite path read from the last positions of generated prefixes. -/
noncomputable def generatedPath
    (strategy : G.Strategy player)
    (start : G.Position) :
    Nat -> G.Position :=
  fun n => G.prefixLast (strategy.generatedPrefix start n)

@[simp]
theorem generatedPath_zero
    (strategy : G.Strategy player)
    (start : G.Position) :
    strategy.generatedPath start 0 = start := by
  simp [generatedPath]

theorem generatedPath_succ
    (strategy : G.Strategy player)
    (start : G.Position)
    (n : Nat) :
    strategy.generatedPath start (n + 1) =
      if howner : G.owner (strategy.generatedPath start n) = player then
        strategy.move n (strategy.generatedPrefix start n)
      else
        Classical.choose (G.step_total (strategy.generatedPath start n)) := by
  simp [generatedPath, generatedPrefix_succ]

/-- Every generated finite prefix is legal when the strategy is legal. -/
theorem generatedPrefix_legal
    {strategy : G.Strategy player}
    {start : G.Position}
    (hlegal : strategy.Legal) :
    ∀ n : Nat, G.PrefixLegal (strategy.generatedPrefix start n) := by
  intro n
  induction n with
  | zero =>
      intro i
      exact Fin.elim0 i
  | succ n ih =>
      let pref := strategy.generatedPrefix start n
      let current := G.prefixLast pref
      let next :=
        if howner : G.owner current = player then
          strategy.move n pref
        else
          Classical.choose (G.step_total current)
      have hstep : G.step current next := by
        by_cases howner : G.owner current = player
        · simpa [next, howner] using hlegal n pref ih howner
        · simpa [next, howner] using Classical.choose_spec (G.step_total current)
      simpa [generatedPrefix_succ, pref, current, next] using
        G.prefixSnoc_legal ih hstep

/-- Generated finite prefixes are exactly prefixes of the generated path. -/
theorem generatedPrefix_eq_prefixOfPath
    (strategy : G.Strategy player)
    (start : G.Position) :
    ∀ n : Nat,
      strategy.generatedPrefix start n =
        G.prefixOfPath (strategy.generatedPath start) n := by
  intro n
  induction n with
  | zero =>
      funext i
      fin_cases i
      simp [generatedPath, prefixOfPath]
  | succ n ih =>
      funext i
      cases i using Fin.lastCases with
      | last =>
          rfl
      | cast i =>
          simpa [generatedPrefix_succ, prefixOfPath] using congr_fun ih i

/-- The path generated by a legal strategy is a legal play. -/
theorem generatedPath_play
    {strategy : G.Strategy player}
    {start : G.Position}
    (hlegal : strategy.Legal) :
    G.Play (strategy.generatedPath start) := by
  intro n
  let pref := strategy.generatedPrefix start n
  let current := G.prefixLast pref
  let next :=
    if howner : G.owner current = player then
      strategy.move n pref
    else
      Classical.choose (G.step_total current)
  have hprefixLegal : G.PrefixLegal pref := by
    simpa [pref] using strategy.generatedPrefix_legal hlegal n
  have hstep : G.step current next := by
    by_cases howner : G.owner current = player
    · simpa [next, howner] using hlegal n pref hprefixLegal howner
    · simpa [next, howner] using Classical.choose_spec (G.step_total current)
  have hnext :
      strategy.generatedPath start (n + 1) = next := by
    rw [strategy.generatedPath_succ start n]
    simp [generatedPath, pref, current, next]
  rw [hnext]
  simpa [generatedPath, pref, current] using hstep

/-- The path generated by a strategy is consistent with it. -/
theorem generatedPath_consistent
    (strategy : G.Strategy player)
    (start : G.Position) :
    strategy.Consistent (strategy.generatedPath start) := by
  intro n howner
  calc
    strategy.generatedPath start (n + 1)
        = strategy.move n (strategy.generatedPrefix start n) := by
          simp [generatedPath_succ, howner]
    _ = strategy.move n
          (G.prefixOfPath (strategy.generatedPath start) n) := by
          rw [strategy.generatedPrefix_eq_prefixOfPath start n]

/-- Every legal history-dependent strategy has a consistent play from any start. -/
theorem exists_playFrom_consistent
    {strategy : G.Strategy player}
    {start : G.Position}
    (hlegal : strategy.Legal) :
    ∃ path : Nat -> G.Position,
      G.PlayFrom start path ∧ strategy.Consistent path := by
  refine ⟨strategy.generatedPath start, ?_, ?_⟩
  · constructor
    · simp
    · exact strategy.generatedPath_play hlegal
  · exact strategy.generatedPath_consistent start

/-- Finite history generated by dueling Even and Odd strategies. -/
noncomputable def duelPrefix
    (evenStrategy : G.Strategy ParityPlayer.even)
    (oddStrategy : G.Strategy ParityPlayer.odd)
    (start : G.Position) :
    ∀ n : Nat, G.Prefix n
  | 0 => G.singletonPrefix start
  | n + 1 =>
      let pref := duelPrefix evenStrategy oddStrategy start n
      let current := G.prefixLast pref
      let next :=
        match G.owner current with
        | ParityPlayer.even => evenStrategy.move n pref
        | ParityPlayer.odd => oddStrategy.move n pref
      G.prefixSnoc pref next

@[simp]
theorem duelPrefix_zero
    (evenStrategy : G.Strategy ParityPlayer.even)
    (oddStrategy : G.Strategy ParityPlayer.odd)
    (start : G.Position) :
    duelPrefix (G := G) evenStrategy oddStrategy start 0 =
      G.singletonPrefix start :=
  rfl

theorem duelPrefix_succ
    (evenStrategy : G.Strategy ParityPlayer.even)
    (oddStrategy : G.Strategy ParityPlayer.odd)
    (start : G.Position)
    (n : Nat) :
    duelPrefix (G := G) evenStrategy oddStrategy start (n + 1) =
      let pref := duelPrefix (G := G) evenStrategy oddStrategy start n
      let current := G.prefixLast pref
      let next :=
        match G.owner current with
        | ParityPlayer.even => evenStrategy.move n pref
        | ParityPlayer.odd => oddStrategy.move n pref
      G.prefixSnoc pref next :=
  rfl

/-- Infinite play generated by dueling Even and Odd strategies. -/
noncomputable def duelPath
    (evenStrategy : G.Strategy ParityPlayer.even)
    (oddStrategy : G.Strategy ParityPlayer.odd)
    (start : G.Position) :
    Nat -> G.Position :=
  fun n => G.prefixLast (duelPrefix (G := G) evenStrategy oddStrategy start n)

@[simp]
theorem duelPath_zero
    (evenStrategy : G.Strategy ParityPlayer.even)
    (oddStrategy : G.Strategy ParityPlayer.odd)
    (start : G.Position) :
    duelPath (G := G) evenStrategy oddStrategy start 0 = start := by
  simp [duelPath]

theorem duelPath_succ
    (evenStrategy : G.Strategy ParityPlayer.even)
    (oddStrategy : G.Strategy ParityPlayer.odd)
    (start : G.Position)
    (n : Nat) :
    duelPath (G := G) evenStrategy oddStrategy start (n + 1) =
      match G.owner (duelPath (G := G) evenStrategy oddStrategy start n) with
      | ParityPlayer.even =>
          evenStrategy.move n
            (duelPrefix (G := G) evenStrategy oddStrategy start n)
      | ParityPlayer.odd =>
          oddStrategy.move n
            (duelPrefix (G := G) evenStrategy oddStrategy start n) := by
  simp [duelPath, duelPrefix_succ]

/-- Dueling prefixes are legal when both strategies are legal. -/
theorem duelPrefix_legal
    {evenStrategy : G.Strategy ParityPlayer.even}
    {oddStrategy : G.Strategy ParityPlayer.odd}
    {start : G.Position}
    (hevenLegal : evenStrategy.Legal)
    (hoddLegal : oddStrategy.Legal) :
    ∀ n : Nat,
      G.PrefixLegal
        (duelPrefix (G := G) evenStrategy oddStrategy start n) := by
  intro n
  induction n with
  | zero =>
      intro i
      exact Fin.elim0 i
  | succ n ih =>
      let pref := duelPrefix (G := G) evenStrategy oddStrategy start n
      let current := G.prefixLast pref
      let next :=
        match G.owner current with
        | ParityPlayer.even => evenStrategy.move n pref
        | ParityPlayer.odd => oddStrategy.move n pref
      have hstep : G.step current next := by
        cases howner : G.owner current with
        | even =>
            simpa [next, howner] using hevenLegal n pref ih howner
        | odd =>
            simpa [next, howner] using hoddLegal n pref ih howner
      simpa [duelPrefix_succ, pref, current, next] using
        G.prefixSnoc_legal ih hstep

/-- Dueling prefixes are prefixes of the dueling path. -/
theorem duelPrefix_eq_prefixOfPath
    (evenStrategy : G.Strategy ParityPlayer.even)
    (oddStrategy : G.Strategy ParityPlayer.odd)
    (start : G.Position) :
    ∀ n : Nat,
      duelPrefix (G := G) evenStrategy oddStrategy start n =
        G.prefixOfPath
          (duelPath (G := G) evenStrategy oddStrategy start) n := by
  intro n
  induction n with
  | zero =>
      funext i
      fin_cases i
      simp [duelPath, prefixOfPath]
  | succ n ih =>
      funext i
      cases i using Fin.lastCases with
      | last =>
          rfl
      | cast i =>
          simpa [duelPrefix_succ, prefixOfPath] using congr_fun ih i

/-- The dueling path is a legal play. -/
theorem duelPath_play
    {evenStrategy : G.Strategy ParityPlayer.even}
    {oddStrategy : G.Strategy ParityPlayer.odd}
    {start : G.Position}
    (hevenLegal : evenStrategy.Legal)
    (hoddLegal : oddStrategy.Legal) :
    G.Play (duelPath (G := G) evenStrategy oddStrategy start) := by
  intro n
  let pref := duelPrefix (G := G) evenStrategy oddStrategy start n
  let current := G.prefixLast pref
  let next :=
    match G.owner current with
    | ParityPlayer.even => evenStrategy.move n pref
    | ParityPlayer.odd => oddStrategy.move n pref
  have hprefixLegal : G.PrefixLegal pref := by
    simpa [pref] using
      duelPrefix_legal
        (G := G) (evenStrategy := evenStrategy) (oddStrategy := oddStrategy)
        (start := start) hevenLegal hoddLegal n
  have hstep : G.step current next := by
    cases howner : G.owner current with
    | even =>
        simpa [next, howner] using hevenLegal n pref hprefixLegal howner
    | odd =>
        simpa [next, howner] using hoddLegal n pref hprefixLegal howner
  have hnext :
      duelPath (G := G) evenStrategy oddStrategy start (n + 1) = next := by
    rw [duelPath_succ (G := G) evenStrategy oddStrategy start n]
    simp [duelPath, pref, current, next]
  rw [hnext]
  simpa [duelPath, pref, current] using hstep

/-- The dueling path is consistent with the Even strategy. -/
theorem duelPath_consistent_even
    (evenStrategy : G.Strategy ParityPlayer.even)
    (oddStrategy : G.Strategy ParityPlayer.odd)
    (start : G.Position) :
    evenStrategy.Consistent
      (duelPath (G := G) evenStrategy oddStrategy start) := by
  intro n howner
  calc
    duelPath (G := G) evenStrategy oddStrategy start (n + 1)
        = evenStrategy.move n
            (duelPrefix (G := G) evenStrategy oddStrategy start n) := by
          rw [duelPath_succ]
          simp [howner]
    _ = evenStrategy.move n
          (G.prefixOfPath
            (duelPath (G := G) evenStrategy oddStrategy start) n) := by
          rw [duelPrefix_eq_prefixOfPath]

/-- The dueling path is consistent with the Odd strategy. -/
theorem duelPath_consistent_odd
    (evenStrategy : G.Strategy ParityPlayer.even)
    (oddStrategy : G.Strategy ParityPlayer.odd)
    (start : G.Position) :
    oddStrategy.Consistent
      (duelPath (G := G) evenStrategy oddStrategy start) := by
  intro n howner
  calc
    duelPath (G := G) evenStrategy oddStrategy start (n + 1)
        = oddStrategy.move n
            (duelPrefix (G := G) evenStrategy oddStrategy start n) := by
          rw [duelPath_succ]
          simp [howner]
    _ = oddStrategy.move n
          (G.prefixOfPath
            (duelPath (G := G) evenStrategy oddStrategy start) n) := by
          rw [duelPrefix_eq_prefixOfPath]

/-- Two legal strategies, one for each player, induce a play consistent with both. -/
theorem exists_playFrom_consistent_pair
    {evenStrategy : G.Strategy ParityPlayer.even}
    {oddStrategy : G.Strategy ParityPlayer.odd}
    {start : G.Position}
    (hevenLegal : evenStrategy.Legal)
    (hoddLegal : oddStrategy.Legal) :
    ∃ path : Nat -> G.Position,
      G.PlayFrom start path ∧
        evenStrategy.Consistent path ∧ oddStrategy.Consistent path := by
  refine
    ⟨duelPath (G := G) evenStrategy oddStrategy start, ?_, ?_, ?_⟩
  · constructor
    · simp
    · exact
        duelPath_play
          (G := G) (evenStrategy := evenStrategy) (oddStrategy := oddStrategy)
          (start := start) hevenLegal hoddLegal
  · exact duelPath_consistent_even (G := G) evenStrategy oddStrategy start
  · exact duelPath_consistent_odd (G := G) evenStrategy oddStrategy start

end Strategy

/-- A positional strategy for one player. -/
structure PositionalStrategy (player : ParityPlayer) where
  move : G.Position -> G.Position
  legal : ∀ position : G.Position,
    G.owner position = player -> G.step position (move position)

namespace PositionalStrategy

variable {G}
variable {player : ParityPlayer}

/-- Read a positional strategy as a history-dependent strategy. -/
def toStrategy (strategy : G.PositionalStrategy player) :
    G.Strategy player where
  move n pref := strategy.move (G.prefixLast pref)

/-- A positional strategy is legal as a history-dependent strategy. -/
theorem toStrategy_legal (strategy : G.PositionalStrategy player) :
    strategy.toStrategy.Legal := by
  intro n pref _hprefix howner
  exact strategy.legal (G.prefixLast pref) howner

/-- A play is consistent with a positional strategy. -/
def Consistent (strategy : G.PositionalStrategy player)
    (path : Nat -> G.Position) : Prop :=
  ∀ n : Nat,
    G.owner (path n) = player ->
      path (n + 1) = strategy.move (path n)

/--
A play follows a positional strategy up to the first visit of `target`.  This is
the local consistency notion needed for attractor phases in a combined
Zielonka strategy.
-/
def ConsistentUntil (strategy : G.PositionalStrategy player)
    (target : Set G.Position)
    (path : Nat -> G.Position) : Prop :=
  ∀ n : Nat,
    (∀ k : Nat, k ≤ n -> path k ∉ target) ->
      G.owner (path n) = player ->
        path (n + 1) = strategy.move (path n)

theorem consistentUntil_of_consistent
    (strategy : G.PositionalStrategy player)
    (target : Set G.Position)
    {path : Nat -> G.Position}
    (hconsistent : strategy.Consistent path) :
    strategy.ConsistentUntil target path := by
  intro n _hnotTarget howner
  exact hconsistent n howner

/--
The two consistency notions agree when a positional strategy is viewed as a
history-dependent strategy.
-/
theorem consistent_toStrategy_iff
    (strategy : G.PositionalStrategy player)
    (path : Nat -> G.Position) :
    strategy.toStrategy.Consistent path ↔ strategy.Consistent path := by
  constructor
  · intro h n howner
    simpa [toStrategy, CountableParityGame.prefixLast_prefixOfPath] using
      h n howner
  · intro h n howner
    simpa [toStrategy, CountableParityGame.prefixLast_prefixOfPath] using
      h n howner

end PositionalStrategy

/-- An arbitrary globally legal positional strategy for a player. -/
noncomputable def arbitraryPositionalStrategy
    (player : ParityPlayer) :
    G.PositionalStrategy player where
  move position := Classical.choose (G.step_total position)
  legal position _howner := Classical.choose_spec (G.step_total position)

/-- Priority `p` occurs infinitely often along a path. -/
def PrioritySeenInfinitelyOften
    (path : Nat -> G.Position)
    (p : Nat) :
    Prop :=
  ∀ n : Nat, ∃ k : Nat, n ≤ k ∧ G.priority (path k) = p

/-- The min-even parity objective for player Even. -/
def MinPriorityEven (path : Nat -> G.Position) : Prop :=
  ∃ p : Nat,
    DetParityAutomaton.NatEven p ∧
      G.PrioritySeenInfinitelyOften path p ∧
        ∀ q : Nat, G.PrioritySeenInfinitelyOften path q -> p ≤ q

/-- The complementary min-odd objective for player Odd. -/
def MinPriorityOdd (path : Nat -> G.Position) : Prop :=
  ∃ p : Nat,
    ¬ DetParityAutomaton.NatEven p ∧
      G.PrioritySeenInfinitelyOften path p ∧
        ∀ q : Nat, G.PrioritySeenInfinitelyOften path q -> p ≤ q

/-- The winner of a path according to the min-parity convention. -/
def PlayerWinsPath (player : ParityPlayer)
    (path : Nat -> G.Position) : Prop :=
  match player with
  | ParityPlayer.even => G.MinPriorityEven path
  | ParityPlayer.odd => G.MinPriorityOdd path

/-- Any priority seen infinitely often occurs in the arena. -/
theorem prioritySeenInfinitelyOften_mem_range
    {path : Nat -> G.Position}
    {priority : Nat}
    (hseen : G.PrioritySeenInfinitelyOften path priority) :
    priority ∈ Set.range G.priority := by
  rcases hseen 0 with ⟨k, _hk, hkpriority⟩
  exact ⟨path k, hkpriority⟩

/-- A priority is not seen infinitely often iff it is eventually absent. -/
theorem not_prioritySeenInfinitelyOften_iff_eventually_not
    (path : Nat -> G.Position)
    (priority : Nat) :
    ¬ G.PrioritySeenInfinitelyOften path priority ↔
      ∃ n : Nat,
        ∀ k : Nat, n ≤ k -> G.priority (path k) ≠ priority := by
  constructor
  · intro hnot
    classical
    by_contra hnoEventually
    apply hnot
    intro n
    by_contra hnoHit
    have heventual :
        ∀ k : Nat, n ≤ k -> G.priority (path k) ≠ priority := by
      intro k hk hpriority
      exact hnoHit ⟨k, hk, hpriority⟩
    exact hnoEventually ⟨n, heventual⟩
  · intro heventual hseen
    rcases heventual with ⟨n, hn⟩
    rcases hseen n with ⟨k, hk, hkpriority⟩
    exact hn k hk hkpriority

/--
If `priority` is the least priority seen infinitely often on a path, then the
owner of that priority wins the path.
-/
theorem playerWinsPath_priorityOwner_of_min_seen
    {path : Nat -> G.Position}
    {priority : Nat}
    (hseen : G.PrioritySeenInfinitelyOften path priority)
    (hmin :
      ∀ q : Nat, G.PrioritySeenInfinitelyOften path q -> priority ≤ q) :
    G.PlayerWinsPath (priorityOwner priority) path := by
  classical
  by_cases hpriority : DetParityAutomaton.NatEven priority
  · simpa [PlayerWinsPath, priorityOwner, hpriority, MinPriorityEven] using
      (⟨priority, hpriority, hseen, hmin⟩ :
        G.MinPriorityEven path)
  · simpa [PlayerWinsPath, priorityOwner, hpriority, MinPriorityOdd] using
      (⟨priority, hpriority, hseen, hmin⟩ :
        G.MinPriorityOdd path)

/--
If the globally least arena priority is seen infinitely often, then the player
favoured by that priority wins the path.
-/
theorem playerWinsPath_priorityOwner_of_leastPriority_seen
    (start : G.Position)
    {path : Nat -> G.Position}
    (hseen :
      G.PrioritySeenInfinitelyOften path (G.leastPriorityFrom start)) :
    G.PlayerWinsPath (priorityOwner (G.leastPriorityFrom start)) path := by
  refine
    G.playerWinsPath_priorityOwner_of_min_seen hseen ?_
  intro q hqSeen
  rcases G.prioritySeenInfinitelyOften_mem_range hqSeen with
    ⟨position, hposition⟩
  simpa [← hposition] using
    G.leastPriorityFrom_le_priority start position

/-- If every position has priority `p`, then `p` is seen infinitely often. -/
theorem prioritySeenInfinitelyOften_of_constant_priority
    {path : Nat -> G.Position}
    {p : Nat}
    (hpriority : ∀ position : G.Position, G.priority position = p) :
    G.PrioritySeenInfinitelyOften path p := by
  intro n
  exact ⟨n, le_rfl, hpriority (path n)⟩

/-- In a constant-priority game, any recurrent priority is at least that one. -/
theorem constant_priority_minimal
    {path : Nat -> G.Position}
    {p q : Nat}
    (hpriority : ∀ position : G.Position, G.priority position = p)
    (hseen : G.PrioritySeenInfinitelyOften path q) :
    p ≤ q := by
  rcases hseen 0 with ⟨k, _hk, hkpriority⟩
  have hp : G.priority (path k) = p := hpriority (path k)
  omega

/-- In a constant-priority game, any seen priority is that priority. -/
theorem priority_eq_of_seen_constant
    {path : Nat -> G.Position}
    {p q : Nat}
    (hpriority : ∀ position : G.Position, G.priority position = p)
    (hseen : G.PrioritySeenInfinitelyOften path q) :
    q = p := by
  rcases hseen 0 with ⟨k, _hk, hkpriority⟩
  exact hkpriority.symm.trans (hpriority (path k))

/-- Constant even-priority games satisfy Even's path objective. -/
theorem minPriorityEven_of_constant_priority
    {path : Nat -> G.Position}
    {p : Nat}
    (hpriority : ∀ position : G.Position, G.priority position = p)
    (hpEven : DetParityAutomaton.NatEven p) :
    G.MinPriorityEven path := by
  exact
    ⟨p, hpEven,
      G.prioritySeenInfinitelyOften_of_constant_priority hpriority,
      fun q hseen => G.constant_priority_minimal hpriority hseen⟩

/-- Constant odd-priority games satisfy Odd's path objective. -/
theorem minPriorityOdd_of_constant_priority
    {path : Nat -> G.Position}
    {p : Nat}
    (hpriority : ∀ position : G.Position, G.priority position = p)
    (hpOdd : ¬ DetParityAutomaton.NatEven p) :
    G.MinPriorityOdd path := by
  exact
    ⟨p, hpOdd,
      G.prioritySeenInfinitelyOften_of_constant_priority hpriority,
      fun q hseen => G.constant_priority_minimal hpriority hseen⟩

/--
Some priority is seen infinitely often along any path.

The arena may be countably infinite, but its priority range is finite.  Applying
the infinite pigeonhole principle to the finite priority-range subtype yields a
priority visited infinitely often.
-/
theorem exists_prioritySeenInfinitelyOften
    (path : Nat -> G.Position) :
    ∃ priority : Nat, G.PrioritySeenInfinitelyOften path priority := by
  classical
  let priorityAt : Nat -> G.priorityRangeFinset :=
    fun n => ⟨G.priority (path n), by simp [priorityRangeFinset]⟩
  obtain ⟨priority, hfiber⟩ := Finite.exists_infinite_fiber priorityAt
  have hinfinite :
      (priorityAt ⁻¹' {priority}).Infinite :=
    Set.infinite_coe_iff.mp hfiber
  refine ⟨priority.1, ?_⟩
  intro n
  obtain ⟨k, hkpriority, hnk⟩ := hinfinite.exists_gt n
  have hpriority : priorityAt k = priority := hkpriority
  exact ⟨k, le_of_lt hnk, congr_arg Subtype.val hpriority⟩

/-- A least infinitely-often priority exists along any path. -/
theorem exists_min_prioritySeenInfinitelyOften
    (path : Nat -> G.Position) :
    ∃ priority : Nat,
      G.PrioritySeenInfinitelyOften path priority ∧
        ∀ other : Nat,
          G.PrioritySeenInfinitelyOften path other -> priority ≤ other := by
  classical
  have hex : ∃ priority : Nat, G.PrioritySeenInfinitelyOften path priority :=
    G.exists_prioritySeenInfinitelyOften path
  exact
    ⟨Nat.find hex, Nat.find_spec hex,
      fun other hother => Nat.find_min' hex hother⟩

/-- Every path is won by one of the two parity players. -/
theorem playerWinsPath_even_or_odd
    (path : Nat -> G.Position) :
    G.PlayerWinsPath ParityPlayer.even path ∨
      G.PlayerWinsPath ParityPlayer.odd path := by
  rcases G.exists_min_prioritySeenInfinitelyOften path with
    ⟨priority, hseen, hminimal⟩
  by_cases heven : DetParityAutomaton.NatEven priority
  · exact Or.inl ⟨priority, heven, hseen, hminimal⟩
  · exact Or.inr ⟨priority, heven, hseen, hminimal⟩

/-- The Even and Odd path objectives are disjoint. -/
theorem not_minPriorityEven_and_minPriorityOdd
    (path : Nat -> G.Position) :
    ¬ (G.MinPriorityEven path ∧ G.MinPriorityOdd path) := by
  intro hboth
  rcases hboth.1 with ⟨p, hpEven, hpSeen, hpMin⟩
  rcases hboth.2 with ⟨q, hqOdd, hqSeen, hqMin⟩
  have hpq : p = q := le_antisymm (hpMin q hqSeen) (hqMin p hpSeen)
  exact hqOdd (by simpa [hpq] using hpEven)

/-- A path is not won by both parity players. -/
theorem not_playerWinsPath_even_and_odd
    (path : Nat -> G.Position) :
    ¬ (G.PlayerWinsPath ParityPlayer.even path ∧
        G.PlayerWinsPath ParityPlayer.odd path) :=
  G.not_minPriorityEven_and_minPriorityOdd path

/-- A history-dependent strategy wins from a start position. -/
def Strategy.WinningFrom
    {player : ParityPlayer}
    (strategy : G.Strategy player)
    (start : G.Position) :
    Prop :=
  strategy.Legal ∧
    ∀ path : Nat -> G.Position,
      G.PlayFrom start path ->
        strategy.Consistent path ->
          G.PlayerWinsPath player path

/-- A positional strategy wins from a start position. -/
def PositionalStrategy.WinningFrom
    {player : ParityPlayer}
    (strategy : G.PositionalStrategy player)
    (start : G.Position) :
    Prop :=
  ∀ path : Nat -> G.Position,
      G.PlayFrom start path ->
      strategy.Consistent path ->
        G.PlayerWinsPath player path

/-- A positional strategy wins from every position in a region. -/
def PositionalStrategy.WinningOn
    {player : ParityPlayer}
    (strategy : G.PositionalStrategy player)
    (region : Set G.Position) :
    Prop :=
  ∀ start : G.Position,
    start ∈ region ->
      PositionalStrategy.WinningFrom (G := G) strategy start

/-- Any positional strategy wins for Even in a constant even-priority game. -/
theorem PositionalStrategy.winningFrom_constant_even_priority
    {strategy : G.PositionalStrategy ParityPlayer.even}
    {start : G.Position}
    {p : Nat}
    (hpriority : ∀ position : G.Position, G.priority position = p)
    (hpEven : DetParityAutomaton.NatEven p) :
    PositionalStrategy.WinningFrom (G := G) strategy start := by
  intro path _hplay _hconsistent
  exact G.minPriorityEven_of_constant_priority hpriority hpEven

/-- Any positional strategy wins for Odd in a constant odd-priority game. -/
theorem PositionalStrategy.winningFrom_constant_odd_priority
    {strategy : G.PositionalStrategy ParityPlayer.odd}
    {start : G.Position}
    {p : Nat}
    (hpriority : ∀ position : G.Position, G.priority position = p)
    (hpOdd : ¬ DetParityAutomaton.NatEven p) :
    PositionalStrategy.WinningFrom (G := G) strategy start := by
  intro path _hplay _hconsistent
  exact G.minPriorityOdd_of_constant_priority hpriority hpOdd

/-- A positional winning strategy is also a history-dependent winning strategy. -/
theorem PositionalStrategy.toStrategy_winningFrom
    {player : ParityPlayer}
    {strategy : G.PositionalStrategy player}
    {start : G.Position}
    (hwinning :
      PositionalStrategy.WinningFrom (G := G) strategy start) :
    Strategy.WinningFrom (G := G) strategy.toStrategy start := by
  constructor
  · exact strategy.toStrategy_legal
  · intro path hplay hconsistent
    exact hwinning path hplay
      ((strategy.consistent_toStrategy_iff path).mp hconsistent)

/-- History-dependent winning region for a player. -/
def WinningRegion (player : ParityPlayer) : Set G.Position :=
  {start |
    ∃ strategy : G.Strategy player,
      Strategy.WinningFrom (G := G) strategy start}

/-- Positional winning region for a player. -/
def PositionalWinningRegion (player : ParityPlayer) : Set G.Position :=
  {start |
    ∃ strategy : G.PositionalStrategy player,
      PositionalStrategy.WinningFrom (G := G) strategy start}

/-- In a constant even-priority game, every start is positionally won by Even. -/
theorem positionalWinningRegion_of_constant_even_priority
    {p : Nat}
    (hpriority : ∀ position : G.Position, G.priority position = p)
    (hpEven : DetParityAutomaton.NatEven p) :
    ∀ start : G.Position,
      start ∈ G.PositionalWinningRegion ParityPlayer.even := by
  intro start
  exact
    ⟨G.arbitraryPositionalStrategy ParityPlayer.even,
      PositionalStrategy.winningFrom_constant_even_priority
        (G := G) hpriority hpEven⟩

/-- In a constant odd-priority game, every start is positionally won by Odd. -/
theorem positionalWinningRegion_of_constant_odd_priority
    {p : Nat}
    (hpriority : ∀ position : G.Position, G.priority position = p)
    (hpOdd : ¬ DetParityAutomaton.NatEven p) :
    ∀ start : G.Position,
      start ∈ G.PositionalWinningRegion ParityPlayer.odd := by
  intro start
  exact
    ⟨G.arbitraryPositionalStrategy ParityPlayer.odd,
      PositionalStrategy.winningFrom_constant_odd_priority
        (G := G) hpriority hpOdd⟩

/-- Odd cannot have a winning strategy in a constant even-priority game. -/
theorem not_winningRegion_odd_of_constant_even_priority
    {p : Nat}
    (hpriority : ∀ position : G.Position, G.priority position = p)
    (hpEven : DetParityAutomaton.NatEven p) :
    ∀ start : G.Position,
      start ∉ G.WinningRegion ParityPlayer.odd := by
  intro start hwinningRegion
  rcases hwinningRegion with ⟨strategy, hwinning⟩
  rcases Strategy.exists_playFrom_consistent
      (G := G) (strategy := strategy) (start := start) hwinning.1 with
    ⟨path, hplayFrom, hconsistent⟩
  rcases hwinning.2 path hplayFrom hconsistent with
    ⟨q, hqOdd, hqSeen, _hqMin⟩
  have hq : q = p := G.priority_eq_of_seen_constant hpriority hqSeen
  exact hqOdd (by simpa [hq] using hpEven)

/-- Even cannot have a winning strategy in a constant odd-priority game. -/
theorem not_winningRegion_even_of_constant_odd_priority
    {p : Nat}
    (hpriority : ∀ position : G.Position, G.priority position = p)
    (hpOdd : ¬ DetParityAutomaton.NatEven p) :
    ∀ start : G.Position,
      start ∉ G.WinningRegion ParityPlayer.even := by
  intro start hwinningRegion
  rcases hwinningRegion with ⟨strategy, hwinning⟩
  rcases Strategy.exists_playFrom_consistent
      (G := G) (strategy := strategy) (start := start) hwinning.1 with
    ⟨path, hplayFrom, hconsistent⟩
  rcases hwinning.2 path hplayFrom hconsistent with
    ⟨q, hqEven, hqSeen, _hqMin⟩
  have hq : q = p := G.priority_eq_of_seen_constant hpriority hqSeen
  exact hpOdd (by simpa [hq] using hqEven)

/-- Positional winning is a special case of history-dependent winning. -/
theorem positionalWinningRegion_subset_winningRegion
    (player : ParityPlayer) :
    G.PositionalWinningRegion player ⊆ G.WinningRegion player := by
  intro start hstart
  rcases hstart with ⟨strategy, hwinning⟩
  exact
    ⟨strategy.toStrategy,
      PositionalStrategy.toStrategy_winningFrom
        (G := G) (strategy := strategy) hwinning⟩

/-- Even and Odd cannot both have history-dependent winning strategies. -/
theorem not_winningRegion_even_and_odd
    (start : G.Position) :
    ¬ (start ∈ G.WinningRegion ParityPlayer.even ∧
        start ∈ G.WinningRegion ParityPlayer.odd) := by
  intro hboth
  rcases hboth.1 with ⟨evenStrategy, hevenWinning⟩
  rcases hboth.2 with ⟨oddStrategy, hoddWinning⟩
  rcases
      Strategy.exists_playFrom_consistent_pair
        (G := G)
        (evenStrategy := evenStrategy)
        (oddStrategy := oddStrategy)
        (start := start)
        hevenWinning.1 hoddWinning.1 with
    ⟨path, hplayFrom, hevenConsistent, hoddConsistent⟩
  have hevenPath :
      G.PlayerWinsPath ParityPlayer.even path :=
    hevenWinning.2 path hplayFrom hevenConsistent
  have hoddPath :
      G.PlayerWinsPath ParityPlayer.odd path :=
    hoddWinning.2 path hplayFrom hoddConsistent
  exact
    G.not_playerWinsPath_even_and_odd path
      ⟨hevenPath, hoddPath⟩

theorem not_winningRegion_odd_and_even
    (start : G.Position) :
    ¬ (start ∈ G.WinningRegion ParityPlayer.odd ∧
        start ∈ G.WinningRegion ParityPlayer.even) := by
  intro hboth
  exact G.not_winningRegion_even_and_odd start ⟨hboth.2, hboth.1⟩

/-- A player and its opponent cannot both have history-dependent winning strategies. -/
theorem not_winningRegion_and_other
    (player : ParityPlayer)
    (start : G.Position) :
    ¬ (start ∈ G.WinningRegion player ∧
        start ∈ G.WinningRegion player.other) := by
  cases player with
  | even =>
      exact G.not_winningRegion_even_and_odd start
  | odd =>
      exact G.not_winningRegion_odd_and_even start

/-- Add one position to the front of an infinite path. -/
def pathCons
    (position : G.Position)
    (path : Nat -> G.Position) :
    Nat -> G.Position
  | 0 => position
  | n + 1 => path n

@[simp]
theorem pathCons_zero
    (position : G.Position)
    (path : Nat -> G.Position) :
    G.pathCons position path 0 = position :=
  rfl

@[simp]
theorem pathCons_succ
    (position : G.Position)
    (path : Nat -> G.Position)
    (n : Nat) :
    G.pathCons position path (n + 1) = path n :=
  rfl

/-- A spliced path is legal if the first edge and the tail are legal. -/
theorem play_pathCons
    {position : G.Position}
    {path : Nat -> G.Position}
    (hstep : G.step position (path 0))
    (hplay : G.Play path) :
    G.Play (G.pathCons position path) := by
  intro n
  cases n with
  | zero =>
      simpa using hstep
  | succ n =>
      simpa using hplay n

/-- Prefixes of a spliced path are spliced finite prefixes. -/
@[simp]
theorem prefixOfPath_pathCons_succ
    (position : G.Position)
    (path : Nat -> G.Position)
    (n : Nat) :
    G.prefixOfPath (G.pathCons position path) (n + 1) =
      G.prefixCons position (G.prefixOfPath path n) := by
  funext i
  cases i using Fin.cases with
  | zero =>
      simp [prefixOfPath, prefixCons]
  | succ i =>
      simp [prefixOfPath, prefixCons]

@[simp]
theorem prefixOfPath_pathCons_zero
    (position : G.Position)
    (path : Nat -> G.Position) :
    G.prefixOfPath (G.pathCons position path) 0 =
      G.singletonPrefix position := by
  funext i
  simp [prefixOfPath, singletonPrefix]

/-- Tail of an infinite path after a finite prefix. -/
def pathTail (path : Nat -> G.Position) (offset : Nat) : Nat -> G.Position :=
  fun n => path (offset + n)

@[simp]
theorem pathTail_zero (path : Nat -> G.Position) :
    G.pathTail path 0 = path := by
  funext n
  simp [pathTail]

/-- The one-step tail of a spliced path is the original tail path. -/
@[simp]
theorem pathTail_pathCons_one
    (position : G.Position)
    (path : Nat -> G.Position) :
    G.pathTail (G.pathCons position path) 1 = path := by
  funext n
  simp [pathTail, Nat.add_comm]

@[simp]
theorem prefixTail_prefixOfPath_succ
    (path : Nat -> G.Position)
    (n : Nat) :
    G.prefixTail (G.prefixOfPath path (n + 1)) =
      G.prefixOfPath (G.pathTail path 1) n := by
  funext i
  simp [prefixTail, prefixOfPath, pathTail, Nat.add_comm]

/-- Legal plays remain legal after dropping a finite prefix. -/
theorem play_pathTail
    {path : Nat -> G.Position}
    (hplay : G.Play path)
    (offset : Nat) :
    G.Play (G.pathTail path offset) := by
  intro n
  simpa [pathTail, Nat.add_assoc] using hplay (offset + n)

/-- A tail of a play is a play from the position reached at the cut point. -/
theorem playFrom_pathTail
    {path : Nat -> G.Position}
    (hplay : G.Play path)
    (offset : Nat) :
    G.PlayFrom (path offset) (G.pathTail path offset) := by
  constructor
  · simp [pathTail]
  · exact G.play_pathTail hplay offset

/-- Priority recurrence is invariant under deleting a finite prefix. -/
theorem prioritySeenInfinitelyOften_pathTail_iff
    (path : Nat -> G.Position)
    (offset p : Nat) :
    G.PrioritySeenInfinitelyOften (G.pathTail path offset) p ↔
      G.PrioritySeenInfinitelyOften path p := by
  constructor
  · intro htail n
    rcases htail (n - offset) with ⟨k, hk, hkprio⟩
    refine ⟨offset + k, by omega, ?_⟩
    simpa [pathTail] using hkprio
  · intro hpath n
    rcases hpath (offset + n) with ⟨k, hk, hkprio⟩
    refine ⟨k - offset, by omega, ?_⟩
    have hoffset : offset + (k - offset) = k := by omega
    simpa [pathTail, hoffset] using hkprio

/-- The Even parity objective is prefix-independent. -/
theorem minPriorityEven_pathTail_iff
    (path : Nat -> G.Position)
    (offset : Nat) :
    G.MinPriorityEven (G.pathTail path offset) ↔
      G.MinPriorityEven path := by
  constructor
  · intro h
    rcases h with ⟨p, hpEven, hpSeen, hpMin⟩
    refine ⟨p, hpEven, ?_, ?_⟩
    · exact
        (G.prioritySeenInfinitelyOften_pathTail_iff path offset p).mp hpSeen
    · intro q hq
      exact hpMin q
        ((G.prioritySeenInfinitelyOften_pathTail_iff path offset q).mpr hq)
  · intro h
    rcases h with ⟨p, hpEven, hpSeen, hpMin⟩
    refine ⟨p, hpEven, ?_, ?_⟩
    · exact
        (G.prioritySeenInfinitelyOften_pathTail_iff path offset p).mpr hpSeen
    · intro q hq
      exact hpMin q
        ((G.prioritySeenInfinitelyOften_pathTail_iff path offset q).mp hq)

/-- The Odd parity objective is prefix-independent. -/
theorem minPriorityOdd_pathTail_iff
    (path : Nat -> G.Position)
    (offset : Nat) :
    G.MinPriorityOdd (G.pathTail path offset) ↔
      G.MinPriorityOdd path := by
  constructor
  · intro h
    rcases h with ⟨p, hpOdd, hpSeen, hpMin⟩
    refine ⟨p, hpOdd, ?_, ?_⟩
    · exact
        (G.prioritySeenInfinitelyOften_pathTail_iff path offset p).mp hpSeen
    · intro q hq
      exact hpMin q
        ((G.prioritySeenInfinitelyOften_pathTail_iff path offset q).mpr hq)
  · intro h
    rcases h with ⟨p, hpOdd, hpSeen, hpMin⟩
    refine ⟨p, hpOdd, ?_, ?_⟩
    · exact
        (G.prioritySeenInfinitelyOften_pathTail_iff path offset p).mpr hpSeen
    · intro q hq
      exact hpMin q
        ((G.prioritySeenInfinitelyOften_pathTail_iff path offset q).mp hq)

/-- Either player's parity objective is prefix-independent. -/
theorem playerWinsPath_pathTail_iff
    (player : ParityPlayer)
    (path : Nat -> G.Position)
    (offset : Nat) :
    G.PlayerWinsPath player (G.pathTail path offset) ↔
      G.PlayerWinsPath player path := by
  cases player
  · exact G.minPriorityEven_pathTail_iff path offset
  · exact G.minPriorityOdd_pathTail_iff path offset

namespace PositionalStrategy

variable {G}
variable {player : ParityPlayer}

/-- Positional consistency is preserved by dropping a finite prefix of a play. -/
theorem consistent_pathTail
    {strategy : G.PositionalStrategy player}
    {path : Nat -> G.Position}
    (hconsistent : strategy.Consistent path)
    (offset : Nat) :
    strategy.Consistent (G.pathTail path offset) := by
  intro n hownerTail
  have hownerOriginal :
      G.owner (path (offset + n)) = player := by
    simpa [pathTail] using hownerTail
  have hindex : offset + (n + 1) = (offset + n) + 1 := by
    omega
  calc
    G.pathTail path offset (n + 1)
        = path (offset + (n + 1)) := rfl
    _ = path ((offset + n) + 1) := by
          rw [hindex]
    _ = strategy.move (path (offset + n)) :=
          hconsistent (offset + n) hownerOriginal
    _ = strategy.move (G.pathTail path offset n) := by
          rfl

/--
For a positional strategy, winning transfers to any legal first successor that
is compatible with the strategy at player-owned starts.  This is the one-step
prefix-independence splice used to reason about reachable positions.
-/
theorem winningFrom_successor
    {strategy : G.PositionalStrategy player}
    {start next : G.Position}
    (hwinning :
      PositionalStrategy.WinningFrom (G := G) strategy start)
    (hstep : G.step start next)
    (hmove :
      G.owner start = player -> next = strategy.move start) :
    PositionalStrategy.WinningFrom (G := G) strategy next := by
  intro path hplayFrom hconsistent
  rcases hplayFrom with ⟨hpath0, hplay⟩
  have hsplicedPlayFrom :
      G.PlayFrom start (G.pathCons start path) := by
    constructor
    · rfl
    · exact G.play_pathCons (by simpa [hpath0] using hstep) hplay
  have hsplicedConsistent :
      strategy.Consistent (G.pathCons start path) := by
    intro n howner
    cases n with
    | zero =>
        calc
          G.pathCons start path (0 + 1)
              = path 0 := rfl
          _ = next := hpath0
          _ = strategy.move start := hmove howner
          _ = strategy.move (G.pathCons start path 0) := rfl
    | succ n =>
        have hownerTail :
            G.owner (path n) = player := by
          simpa using howner
        calc
          G.pathCons start path ((n + 1) + 1)
              = path (n + 1) := rfl
          _ = strategy.move (path n) :=
              hconsistent n hownerTail
          _ = strategy.move (G.pathCons start path (n + 1)) := rfl
  have hsplicedWin :
      G.PlayerWinsPath player (G.pathCons start path) :=
    hwinning (G.pathCons start path)
      hsplicedPlayFrom hsplicedConsistent
  have htailWin :
      G.PlayerWinsPath player
        (G.pathTail (G.pathCons start path) 1) :=
    (G.playerWinsPath_pathTail_iff player (G.pathCons start path) 1).mpr
      hsplicedWin
  simpa using htailWin

end PositionalStrategy

/--
If the opponent owns `position` and one positional strategy for `player` wins
from every legal successor, then `position` is positionally winning for
`player`.
-/
theorem positionalWinningRegion_of_opponent_all_successors
    {player : ParityPlayer}
    {position : G.Position}
    (strategy : G.PositionalStrategy player)
    (hstrategy :
      ∀ next : G.Position,
        G.step position next ->
          PositionalStrategy.WinningFrom (G := G) strategy next)
    (howner : G.owner position = player.other) :
    position ∈ G.PositionalWinningRegion player := by
  refine ⟨strategy, ?_⟩
  intro path hplayFrom hconsistent
  rcases hplayFrom with ⟨hpath0, hplay⟩
  have hfirstStep : G.step position (path 1) := by
    simpa [hpath0] using hplay 0
  have htailPlayFrom :
      G.PlayFrom (path 1) (G.pathTail path 1) := by
    constructor
    · simp [pathTail, Nat.add_comm]
    · exact G.play_pathTail hplay 1
  have htailConsistent :
      strategy.Consistent (G.pathTail path 1) :=
    PositionalStrategy.consistent_pathTail hconsistent 1
  have htailWin :
      G.PlayerWinsPath player (G.pathTail path 1) :=
    hstrategy (path 1) hfirstStep
      (G.pathTail path 1) htailPlayFrom htailConsistent
  exact
    (G.playerWinsPath_pathTail_iff player path 1).mp htailWin

namespace Strategy

variable {G}
variable {player : ParityPlayer}

/--
If a tail path follows the residual strategy after the first edge
`start -> next`, then the spliced full path follows the original strategy,
provided the first edge is compatible with the original strategy when `start`
is owned by the strategy player.
-/
theorem consistent_pathCons_of_residual
    {strategy : G.Strategy player}
    {start next : G.Position}
    {path : Nat -> G.Position}
    (hpath0 : path 0 = next)
    (hfirstMove :
      G.owner start = player ->
        next = strategy.move 0 (G.singletonPrefix start))
    (hconsistent :
      (strategy.residual start next).Consistent path) :
    strategy.Consistent (G.pathCons start path) := by
  intro n howner
  cases n with
  | zero =>
      calc
        G.pathCons start path (0 + 1)
            = path 0 := rfl
        _ = next := hpath0
        _ = strategy.move 0 (G.singletonPrefix start) := hfirstMove howner
        _ = strategy.move 0
              (G.prefixOfPath (G.pathCons start path) 0) := by
              simp
  | succ n =>
      have hownerTail : G.owner (path n) = player := by
        simpa using howner
      calc
        G.pathCons start path ((n + 1) + 1)
            = path (n + 1) := rfl
        _ = (strategy.residual start next).move n
              (G.prefixOfPath path n) :=
              hconsistent n hownerTail
        _ = strategy.move (n + 1)
              (G.prefixCons start (G.prefixOfPath path n)) := by
              rw [strategy.residual_move_of_first start next
                (G.prefixOfPath path n)]
              simpa [prefixOfPath] using hpath0
        _ = strategy.move (n + 1)
              (G.prefixOfPath (G.pathCons start path) (n + 1)) := by
              simp

/--
Strategy for the case where the opponent owns the first position and every
legal successor is already winning for `player`.
-/
noncomputable def prependOpponent
    (start : G.Position)
    (successorWinning :
      ∀ next : G.Position,
        G.step start next -> next ∈ G.WinningRegion player) :
    G.Strategy player where
  move
    | 0, pref => Classical.choose (G.step_total (G.prefixLast pref))
    | n + 1, pref =>
        by
          classical
          let first := G.prefixSecond pref
          exact
            if hstep : G.step start first then
              (Classical.choose (successorWinning first hstep)).move n
                (G.prefixTail pref)
            else
              Classical.choose (G.step_total (G.prefixLast pref))

theorem prependOpponent_legal
    {start : G.Position}
    {successorWinning :
      ∀ next : G.Position,
        G.step start next -> next ∈ G.WinningRegion player} :
    (prependOpponent (G := G) (player := player) start successorWinning).Legal := by
  intro n pref hprefix howner
  cases n with
  | zero =>
      exact Classical.choose_spec (G.step_total (G.prefixLast pref))
  | succ n =>
      classical
      let first := G.prefixSecond pref
      by_cases hstep : G.step start first
      · have hchosenWinning :
            Strategy.WinningFrom
              (G := G)
              (Classical.choose (successorWinning first hstep))
              first :=
          Classical.choose_spec (successorWinning first hstep)
        have htailLegal : G.PrefixLegal (G.prefixTail pref) :=
          G.prefixTail_legal hprefix
        have htailOwner :
            G.owner (G.prefixLast (G.prefixTail pref)) = player := by
          simpa using howner
        simpa [prependOpponent, first, hstep] using
          hchosenWinning.1 n (G.prefixTail pref) htailLegal htailOwner
      · change
          G.step (G.prefixLast pref)
            ((prependOpponent start successorWinning).move (n + 1) pref)
        simpa [prependOpponent, first, hstep] using
          Classical.choose_spec (G.step_total (G.prefixLast pref))

/--
If the opponent owns the first position and all legal successors are already
winning for `player`, then the strategy that delegates to the selected
successor-winning strategy wins from the first position.
-/
theorem prependOpponent_winningFrom
    {start : G.Position}
    {successorWinning :
      ∀ next : G.Position,
        G.step start next -> next ∈ G.WinningRegion player}
    (howner : G.owner start = player.other) :
    Strategy.WinningFrom
      (G := G)
      (prependOpponent (G := G) (player := player) start successorWinning)
      start := by
  constructor
  · exact prependOpponent_legal (G := G) (player := player)
  · intro path hplayFrom hconsistent
    rcases hplayFrom with ⟨hpath0, hplay⟩
    have hfirstStep : G.step start (path 1) := by
      simpa [hpath0] using hplay 0
    let selected :=
      Classical.choose (successorWinning (path 1) hfirstStep)
    have hselectedWinning :
        Strategy.WinningFrom (G := G) selected (path 1) :=
      Classical.choose_spec (successorWinning (path 1) hfirstStep)
    have htailPlayFrom :
        G.PlayFrom (path 1) (G.pathTail path 1) := by
      constructor
      · simp [pathTail, Nat.add_comm]
      · exact G.play_pathTail hplay 1
    have htailConsistent : selected.Consistent (G.pathTail path 1) := by
      intro n hownerTail
      have hownerOriginal :
          G.owner (path (n + 1)) = player := by
        simpa [pathTail, Nat.add_comm, Nat.add_assoc] using hownerTail
      calc
        G.pathTail path 1 (n + 1)
            = path ((n + 1) + 1) := by
              simp [pathTail, Nat.add_comm, Nat.add_assoc]
        _ = (prependOpponent (G := G) (player := player) start successorWinning).move
              (n + 1) (G.prefixOfPath path (n + 1)) :=
              hconsistent (n + 1) hownerOriginal
        _ = selected.move n
              (G.prefixTail (G.prefixOfPath path (n + 1))) := by
              simpa [selected, prependOpponent, hfirstStep] using rfl
        _ = selected.move n
              (G.prefixOfPath (G.pathTail path 1) n) := by
              rw [G.prefixTail_prefixOfPath_succ]
    have htailWin :
        G.PlayerWinsPath player (G.pathTail path 1) :=
      hselectedWinning.2 (G.pathTail path 1) htailPlayFrom htailConsistent
    exact
      (G.playerWinsPath_pathTail_iff player path 1).mp htailWin

/--
If `strategy` wins from `next`, then the strategy that first moves from
`start` to `next` and then delegates to `strategy` wins from `start`.
-/
theorem prepend_winningFrom
    {strategy : G.Strategy player}
    {start next : G.Position}
    (howner : G.owner start = player)
    (hstep : G.step start next)
    (hwinning : Strategy.WinningFrom (G := G) strategy next) :
    Strategy.WinningFrom (G := G) (strategy.prepend start next) start := by
  constructor
  · exact strategy.prepend_legal hwinning.1 hstep
  · intro path hplayFrom hconsistent
    rcases hplayFrom with ⟨hpath0, hplay⟩
    have hpath1 : path 1 = next := by
      calc
        path 1 = (strategy.prepend start next).move 0
            (G.prefixOfPath path 0) := by
            simpa using hconsistent 0 (by simpa [hpath0] using howner)
        _ = next := by
            apply strategy.prepend_move_zero_of_start
            simpa [prefixLast_prefixOfPath] using hpath0
    have htailPlayFrom :
        G.PlayFrom next (G.pathTail path 1) := by
      constructor
      · simpa [pathTail, Nat.add_comm] using hpath1
      · exact G.play_pathTail hplay 1
    have htailConsistent :
        strategy.Consistent (G.pathTail path 1) := by
      intro n hownerTail
      have hownerOriginal :
          G.owner (path (n + 1)) = player := by
        simpa [pathTail, Nat.add_comm, Nat.add_assoc] using hownerTail
      calc
        G.pathTail path 1 (n + 1)
            = path ((n + 1) + 1) := by
              simp [pathTail, Nat.add_comm, Nat.add_assoc]
        _ = (strategy.prepend start next).move (n + 1)
              (G.prefixOfPath path (n + 1)) :=
              hconsistent (n + 1) hownerOriginal
        _ = strategy.move n
              (G.prefixTail (G.prefixOfPath path (n + 1))) := by
              rfl
        _ = strategy.move n
              (G.prefixOfPath (G.pathTail path 1) n) := by
              rw [G.prefixTail_prefixOfPath_succ]
    have htailWin :
        G.PlayerWinsPath player (G.pathTail path 1) :=
      hwinning.2 (G.pathTail path 1) htailPlayFrom htailConsistent
    exact
      (G.playerWinsPath_pathTail_iff player path 1).mp htailWin

/--
The residual of a winning strategy after any compatible first edge is winning
from the successor.
-/
theorem residual_winningFrom
    {strategy : G.Strategy player}
    {start next : G.Position}
    (hwinning : Strategy.WinningFrom (G := G) strategy start)
    (hstep : G.step start next)
    (hfirstMove :
      G.owner start = player ->
        next = strategy.move 0 (G.singletonPrefix start)) :
    Strategy.WinningFrom (G := G) (strategy.residual start next) next := by
  constructor
  · exact strategy.residual_legal hwinning.1 hstep
  · intro path hplayFrom hconsistent
    rcases hplayFrom with ⟨hpath0, hplay⟩
    have hsplicedPlayFrom :
        G.PlayFrom start (G.pathCons start path) := by
      constructor
      · rfl
      · exact G.play_pathCons (by simpa [hpath0] using hstep) hplay
    have hsplicedConsistent :
        strategy.Consistent (G.pathCons start path) :=
      Strategy.consistent_pathCons_of_residual hpath0 hfirstMove hconsistent
    have hsplicedWin :
        G.PlayerWinsPath player (G.pathCons start path) :=
      hwinning.2 (G.pathCons start path) hsplicedPlayFrom hsplicedConsistent
    have htailWin :
        G.PlayerWinsPath player
          (G.pathTail (G.pathCons start path) 1) :=
      (G.playerWinsPath_pathTail_iff player (G.pathCons start path) 1).mpr
        hsplicedWin
    simpa using htailWin

/--
Consuming a finite strategy-consistent prefix of a winning strategy leaves a
winning residual strategy at the last position of that prefix.
-/
theorem residualAlongPrefix_winningFrom
    {strategy : G.Strategy player} :
    ∀ {n : Nat} {pref : G.Prefix n},
      Strategy.WinningFrom (G := G) strategy (pref 0) ->
      G.PrefixLegal pref ->
      strategy.PrefixConsistent pref ->
        Strategy.WinningFrom
          (G := G) (strategy.residualAlongPrefix pref) (G.prefixLast pref)
  | 0, pref, hwinning, _hlegal, _hconsistent => by
      simpa [Strategy.residualAlongPrefix, prefixLast] using hwinning
  | n + 1, pref, hwinning, hlegal, hconsistent => by
      have hstep : G.step (pref 0) (G.prefixSecond pref) := by
        simpa [prefixSecond] using hlegal ⟨0, by omega⟩
      have hfirstMove :
          G.owner (pref 0) = player ->
            G.prefixSecond pref =
              strategy.move 0 (G.singletonPrefix (pref 0)) := by
        intro howner
        have hzero := hconsistent ⟨0, by omega⟩ howner
        simpa [prefixSecond] using hzero
      have hresidualWinning :
          Strategy.WinningFrom
            (G := G)
            (strategy.residual (pref 0) (G.prefixSecond pref))
            ((G.prefixTail pref) 0) := by
        simpa [prefixTail, prefixSecond] using
          Strategy.residual_winningFrom
            (G := G) (strategy := strategy)
            hwinning hstep hfirstMove
      exact
        residualAlongPrefix_winningFrom
          (strategy := strategy.residual (pref 0) (G.prefixSecond pref))
          hresidualWinning
          (G.prefixTail_legal hlegal)
          (Strategy.prefixConsistent_tail
            (G := G) (strategy := strategy) hconsistent)

/--
At the end of a strategy-consistent winning prefix, the next move prescribed by
the original winning strategy leads again to the same winning region.
-/
theorem move_mem_winningRegion_of_prefixConsistent
    {strategy : G.Strategy player}
    {n : Nat}
    {pref : G.Prefix n}
    (hwinning :
      Strategy.WinningFrom (G := G) strategy (pref 0))
    (hlegal : G.PrefixLegal pref)
    (hconsistent : strategy.PrefixConsistent pref)
    (howner : G.owner (G.prefixLast pref) = player) :
    strategy.move n pref ∈ G.WinningRegion player := by
  let residualStrategy := strategy.residualAlongPrefix pref
  have hresidualWinning :
      Strategy.WinningFrom
        (G := G) residualStrategy (G.prefixLast pref) :=
    Strategy.residualAlongPrefix_winningFrom
      (G := G) (strategy := strategy)
      hwinning hlegal hconsistent
  have hmove :
      residualStrategy.move 0
          (G.singletonPrefix (G.prefixLast pref)) =
        strategy.move n pref := by
    simpa [residualStrategy] using
      strategy.residualAlongPrefix_move_zero pref
  have hstep :
      G.step (G.prefixLast pref) (strategy.move n pref) :=
    hwinning.1 n pref hlegal howner
  exact
    ⟨residualStrategy.residual (G.prefixLast pref) (strategy.move n pref),
      Strategy.residual_winningFrom
        (G := G) (strategy := residualStrategy)
        hresidualWinning hstep
        (by
          intro _howner
          exact hmove.symm)⟩

end Strategy

/--
If `player` owns `position` and has an edge to a `player`-winning successor,
then `position` itself is `player`-winning.
-/
theorem winningRegion_of_owner_step
    {player : ParityPlayer}
    {position next : G.Position}
    (howner : G.owner position = player)
    (hstep : G.step position next)
    (hnext : next ∈ G.WinningRegion player) :
    position ∈ G.WinningRegion player := by
  rcases hnext with ⟨strategy, hwinning⟩
  exact
    ⟨strategy.prepend position next,
      Strategy.prepend_winningFrom
        (G := G) (strategy := strategy)
        howner hstep hwinning⟩

/--
If the opponent owns `position` and every legal successor is already
`player`-winning, then `position` is `player`-winning.
-/
theorem winningRegion_of_opponent_all_successors
    {player : ParityPlayer}
    {position : G.Position}
    (howner : G.owner position = player.other)
    (hsuccessors :
      ∀ next : G.Position,
        G.step position next -> next ∈ G.WinningRegion player) :
    position ∈ G.WinningRegion player := by
  exact
    ⟨Strategy.prependOpponent
        (G := G) (player := player) position hsuccessors,
      Strategy.prependOpponent_winningFrom
        (G := G) (player := player) howner⟩

/--
The attractor of `target` for `player`: positions from which `player` can force
the play into `target` in finitely many rounds.
-/
inductive Attractor
    (player : ParityPlayer)
    (target : Set G.Position) :
    G.Position -> Prop
  | target {position : G.Position} :
      position ∈ target ->
        Attractor player target position
  | owner {position next : G.Position} :
      G.owner position = player ->
        G.step position next ->
          Attractor player target next ->
            Attractor player target position
  | opponent {position : G.Position} :
      G.owner position = player.other ->
        (∀ next : G.Position,
          G.step position next -> Attractor player target next) ->
          Attractor player target position

/--
A region is a trap for `player` if `player` can keep the play inside it and the
opponent cannot force an exit.
-/
def TrapFor
    (player : ParityPlayer)
    (region : Set G.Position) :
    Prop :=
  ∀ position : G.Position,
    position ∈ region ->
      (G.owner position = player ->
        ∃ next : G.Position, G.step position next ∧ next ∈ region) ∧
      (G.owner position = player.other ->
        ∀ next : G.Position, G.step position next -> next ∈ region)

/--
The history-dependent winning region is a trap for the winning player: at
player-owned winning positions some winning successor exists, and at
opponent-owned winning positions every legal successor is still winning.
-/
theorem winningRegion_trapFor
    (player : ParityPlayer) :
    G.TrapFor player (G.WinningRegion player) := by
  intro position hposition
  rcases hposition with ⟨strategy, hwinning⟩
  constructor
  · intro howner
    let next := strategy.move 0 (G.singletonPrefix position)
    have hprefixLegal : G.PrefixLegal (G.singletonPrefix position) := by
      intro i
      exact Fin.elim0 i
    have hstep : G.step position next := by
      simpa [next] using
        hwinning.1 0 (G.singletonPrefix position) hprefixLegal howner
    refine ⟨next, hstep, ?_⟩
    exact
      ⟨strategy.residual position next,
        Strategy.residual_winningFrom
          (G := G) (strategy := strategy) hwinning hstep
          (by intro _; rfl)⟩
  · intro hownerOther next hstep
    refine
      ⟨strategy.residual position next,
        Strategy.residual_winningFrom
          (G := G) (strategy := strategy) hwinning hstep ?_⟩
    intro howner
    have hcontra : player.other = player := by
      calc
        player.other = G.owner position := hownerOther.symm
        _ = player := howner
    exact False.elim (ParityPlayer.other_ne player hcontra)

/--
The positional winning region is also a trap for the winning player.
-/
theorem positionalWinningRegion_trapFor
    (player : ParityPlayer) :
    G.TrapFor player (G.PositionalWinningRegion player) := by
  intro position hposition
  rcases hposition with ⟨strategy, hwinning⟩
  constructor
  · intro howner
    let next := strategy.move position
    have hstep : G.step position next := by
      simpa [next] using strategy.legal position howner
    refine ⟨next, hstep, ?_⟩
    exact
      ⟨strategy,
        PositionalStrategy.winningFrom_successor
          (G := G) (strategy := strategy) hwinning hstep
          (by intro _; rfl)⟩
  · intro hownerOther next hstep
    refine ⟨strategy, ?_⟩
    exact
      PositionalStrategy.winningFrom_successor
        (G := G) (strategy := strategy) hwinning hstep
        (by
          intro howner
          have hcontra : player.other = player := by
            calc
              player.other = G.owner position := hownerOther.symm
              _ = player := howner
          exact False.elim (ParityPlayer.other_ne player hcontra))

/-- An antitone natural-valued sequence is eventually constant. -/
theorem nat_eventually_constant_of_antitone
    {measure : Nat -> Nat}
    (hanti : Antitone measure) :
    ∃ start value : Nat, ∀ k : Nat, start ≤ k -> measure k = value := by
  classical
  have hnonempty : (Set.range measure).Nonempty := ⟨measure 0, 0, rfl⟩
  obtain ⟨start, hstart⟩ := Nat.sInf_mem hnonempty
  refine ⟨start, sInf (Set.range measure), ?_⟩
  intro k hk
  have hle : measure k ≤ measure start := hanti hk
  have hge : sInf (Set.range measure) ≤ measure k :=
    Nat.sInf_le ⟨k, rfl⟩
  rw [hstart] at hle
  omega

/--
Countable uniformization of positional winning strategies.

If every position in `G.PositionalWinningRegion player` has some positional
winning strategy, then one positional strategy wins from all of them at once.
The strategy chooses, at each position, the least enumerated pointwise strategy
that wins there; along every play this least index is nonincreasing, hence
eventually constant.
-/
theorem exists_strategy_winningOn_positionalWinningRegion
    (player : ParityPlayer) :
    ∃ strategy : G.PositionalStrategy player,
      PositionalStrategy.WinningOn
        (G := G) strategy (G.PositionalWinningRegion player) := by
  classical
  let region : Set G.Position := G.PositionalWinningRegion player
  by_cases hregionNonempty : region.Nonempty
  · have hcount : region.Countable := Set.to_countable region
    rcases hcount.exists_surjective hregionNonempty with
      ⟨enumerate, henumerate⟩
    let chosen : Nat -> G.PositionalStrategy player :=
      fun n => Classical.choose (enumerate n).2
    have chosen_winning :
        ∀ n : Nat,
          PositionalStrategy.WinningFrom
            (G := G) (chosen n) (enumerate n).1 := by
      intro n
      exact Classical.choose_spec (enumerate n).2
    let winsByIndex : Nat -> G.Position -> Prop :=
      fun n position =>
        PositionalStrategy.WinningFrom (G := G) (chosen n) position
    have existsIndex :
        ∀ position : G.Position,
          position ∈ region -> ∃ n : Nat, winsByIndex n position := by
      intro position hposition
      rcases henumerate ⟨position, hposition⟩ with ⟨n, hn⟩
      refine ⟨n, ?_⟩
      have hvalue : (enumerate n).1 = position :=
        congrArg Subtype.val hn
      simpa [winsByIndex, hvalue] using chosen_winning n
    let rank : G.Position -> Nat :=
      fun position =>
        if hposition : position ∈ region then
          Nat.find (existsIndex position hposition)
        else
          0
    have rank_spec :
        ∀ {position : G.Position},
          position ∈ region ->
            winsByIndex (rank position) position := by
      intro position hposition
      simpa [rank, hposition, winsByIndex] using
        Nat.find_spec (existsIndex position hposition)
    have rank_min :
        ∀ {position : G.Position},
          position ∈ region ->
            ∀ n : Nat, winsByIndex n position -> rank position ≤ n := by
      intro position hposition n hwin
      simpa [rank, hposition, winsByIndex] using
        Nat.find_min' (existsIndex position hposition) hwin
    let strategy : G.PositionalStrategy player :=
      { move := fun position =>
          if hposition : position ∈ region then
            (chosen (rank position)).move position
          else
            Classical.choose (G.step_total position)
        legal := by
          intro position howner
          by_cases hposition : position ∈ region
          · change
              G.step position
                (if h : position ∈ region then
                  (chosen (rank position)).move position
                else
                  Classical.choose (G.step_total position))
            simpa [hposition] using
              (chosen (rank position)).legal position howner
          · change
              G.step position
                (if h : position ∈ region then
                  (chosen (rank position)).move position
                else
                  Classical.choose (G.step_total position))
            simpa [hposition] using
              Classical.choose_spec (G.step_total position) }
    refine ⟨strategy, ?_⟩
    intro start hstart path hplayFrom hconsistent
    have hplay : G.Play path := hplayFrom.2
    have hpath_mem : ∀ n : Nat, path n ∈ region := by
      intro n
      induction n with
      | zero =>
          simpa [hplayFrom.1, region] using hstart
      | succ n ih =>
          have hcurrentWin :
              PositionalStrategy.WinningFrom
                (G := G) (chosen (rank (path n))) (path n) := by
            simpa [winsByIndex] using rank_spec (position := path n) ih
          have hnextWin :
              PositionalStrategy.WinningFrom
                (G := G) (chosen (rank (path n))) (path (n + 1)) := by
            exact
              PositionalStrategy.winningFrom_successor
                (G := G) (strategy := chosen (rank (path n)))
                hcurrentWin (hplay n)
                (by
                  intro howner
                  have hglobal :
                      path (n + 1) = strategy.move (path n) :=
                    hconsistent n howner
                  simpa [strategy, ih] using hglobal)
          exact ⟨chosen (rank (path n)), hnextWin⟩
    have hrank_succ_le :
        ∀ n : Nat, rank (path (n + 1)) ≤ rank (path n) := by
      intro n
      have hcurrentWin :
          PositionalStrategy.WinningFrom
            (G := G) (chosen (rank (path n))) (path n) := by
        simpa [winsByIndex] using rank_spec (position := path n) (hpath_mem n)
      have hnextWin :
          PositionalStrategy.WinningFrom
            (G := G) (chosen (rank (path n))) (path (n + 1)) := by
        exact
          PositionalStrategy.winningFrom_successor
            (G := G) (strategy := chosen (rank (path n)))
            hcurrentWin (hplay n)
            (by
              intro howner
              have hglobal :
                  path (n + 1) = strategy.move (path n) :=
                hconsistent n howner
              simpa [strategy, hpath_mem n] using hglobal)
      exact
        rank_min (position := path (n + 1)) (hpath_mem (n + 1))
          (rank (path n)) (by simpa [winsByIndex] using hnextWin)
    have hanti : Antitone (fun n : Nat => rank (path n)) :=
      antitone_nat_of_succ_le hrank_succ_le
    rcases nat_eventually_constant_of_antitone hanti with
      ⟨offset, value, hconstant⟩
    have hrank_offset :
        rank (path offset) = value :=
      hconstant offset le_rfl
    have htailConsistent :
        (chosen (rank (path offset))).Consistent (G.pathTail path offset) := by
      intro n hownerTail
      have hownerOriginal :
          G.owner (path (offset + n)) = player := by
        simpa [pathTail] using hownerTail
      have hglobal :
          path ((offset + n) + 1) = strategy.move (path (offset + n)) :=
        hconsistent (offset + n) hownerOriginal
      have hrank_eq :
          rank (path (offset + n)) = rank (path offset) := by
        have hleft := hconstant (offset + n) (by omega)
        exact hleft.trans hrank_offset.symm
      have hindex : offset + (n + 1) = (offset + n) + 1 := by
        omega
      calc
        G.pathTail path offset (n + 1)
            = path ((offset + n) + 1) := by
              simp [pathTail, hindex]
        _ = strategy.move (path (offset + n)) := hglobal
        _ = (chosen (rank (path offset))).move (path (offset + n)) := by
              simpa [strategy, hpath_mem (offset + n), hrank_eq]
        _ = (chosen (rank (path offset))).move
              (G.pathTail path offset n) := by
              rfl
    have htailPlayFrom :
        G.PlayFrom (path offset) (G.pathTail path offset) :=
      G.playFrom_pathTail hplay offset
    have htailWin :
        G.PlayerWinsPath player (G.pathTail path offset) := by
      have hwinOffset :
          PositionalStrategy.WinningFrom
            (G := G) (chosen (rank (path offset))) (path offset) := by
        simpa [winsByIndex] using
          rank_spec (position := path offset) (hpath_mem offset)
      exact hwinOffset (G.pathTail path offset) htailPlayFrom htailConsistent
    exact
      (G.playerWinsPath_pathTail_iff player path offset).mp htailWin
  · refine ⟨G.arbitraryPositionalStrategy player, ?_⟩
    intro start hstart
    exact False.elim (hregionNonempty ⟨start, by simpa [region] using hstart⟩)

/--
A positional strategy that wins on the positional winning region keeps its own
moves inside that region.
-/
theorem positionalWinningRegion_move_mem_of_winningOn
    {player : ParityPlayer}
    (strategy : G.PositionalStrategy player)
    (hwinningOn :
      PositionalStrategy.WinningOn
        (G := G) strategy (G.PositionalWinningRegion player))
    {position : G.Position}
    (hposition : position ∈ G.PositionalWinningRegion player)
    (howner : G.owner position = player) :
    strategy.move position ∈ G.PositionalWinningRegion player := by
  have hwinning :
      PositionalStrategy.WinningFrom (G := G) strategy position :=
    hwinningOn position hposition
  have hstep : G.step position (strategy.move position) :=
    strategy.legal position howner
  exact
    ⟨strategy,
      PositionalStrategy.winningFrom_successor
        (G := G) (strategy := strategy)
        hwinning hstep (by intro _; rfl)⟩

/--
The complement of a player's history-dependent winning region is a trap for
the other player.  This is the contrapositive closure property used in
Zielonka-style decompositions.
-/
theorem compl_winningRegion_trapFor_other
    (player : ParityPlayer) :
    G.TrapFor player.other
      {position : G.Position | position ∉ G.WinningRegion player} := by
  intro position hnotWinning
  constructor
  · intro hownerOther
    by_contra hnoSuccessor
    have hallSuccessors :
        ∀ next : G.Position,
          G.step position next -> next ∈ G.WinningRegion player := by
      intro next hstep
      by_contra hnextNotWinning
      exact hnoSuccessor ⟨next, hstep, hnextNotWinning⟩
    exact hnotWinning
      (G.winningRegion_of_opponent_all_successors hownerOther hallSuccessors)
  · intro hownerPlayerOther next hstep hnextWinning
    have hownerPlayer : G.owner position = player := by
      simpa using hownerPlayerOther
    exact hnotWinning
      (G.winningRegion_of_owner_step hownerPlayer hstep hnextWinning)

/-- The target set is contained in its attractor. -/
theorem target_subset_attractor
    (player : ParityPlayer)
    (target : Set G.Position) :
    target ⊆ G.Attractor player target := by
  intro position hposition
  exact Attractor.target hposition

/-- A player-owned edge into the attractor puts the source in the attractor. -/
theorem attractor_of_owner_step
    {player : ParityPlayer}
    {target : Set G.Position}
    {position next : G.Position}
    (howner : G.owner position = player)
    (hstep : G.step position next)
    (hnext : G.Attractor player target next) :
    G.Attractor player target position :=
  Attractor.owner howner hstep hnext

/-- An opponent-owned state whose successors are all attracted is attracted. -/
theorem attractor_of_opponent_all
    {player : ParityPlayer}
    {target : Set G.Position}
    {position : G.Position}
    (howner : G.owner position = player.other)
    (hnext :
      ∀ next : G.Position,
        G.step position next -> G.Attractor player target next) :
    G.Attractor player target position :=
  Attractor.opponent howner hnext

/--
Outside a player's attractor, a position owned by that player has no edge into
the attractor.
-/
theorem not_attractor_owner_successor_not
    {player : ParityPlayer}
    {target : Set G.Position}
    {position next : G.Position}
    (hnot : ¬ G.Attractor player target position)
    (howner : G.owner position = player)
    (hstep : G.step position next) :
    ¬ G.Attractor player target next := by
  intro hnext
  exact hnot (G.attractor_of_owner_step howner hstep hnext)

/--
Outside a player's attractor, an opponent-owned position has some successor
that also lies outside the attractor.
-/
theorem not_attractor_opponent_exists_successor_not
    {player : ParityPlayer}
    {target : Set G.Position}
    {position : G.Position}
    (hnot : ¬ G.Attractor player target position)
    (howner : G.owner position = player.other) :
    ∃ next : G.Position,
      G.step position next ∧ ¬ G.Attractor player target next := by
  classical
  by_contra hno
  have hall :
      ∀ next : G.Position,
        G.step position next -> G.Attractor player target next := by
    intro next hstep
    by_contra hnext
    exact hno ⟨next, hstep, hnext⟩
  exact hnot (G.attractor_of_opponent_all howner hall)

/--
The complement of a player's attractor is a trap for the opponent.
-/
theorem compl_attractor_trapFor_other
    (player : ParityPlayer)
    (target : Set G.Position) :
    G.TrapFor player.other {position | ¬ G.Attractor player target position} := by
  intro position hposition
  constructor
  · intro howner
    exact G.not_attractor_opponent_exists_successor_not hposition howner
  · intro howner next hstep
    have hownerPlayer : G.owner position = player := by
      simpa using howner
    exact
      G.not_attractor_owner_successor_not
        hposition hownerPlayer hstep

/--
Equivalently, the complement of the opponent's attractor is a trap for the
current player.
-/
theorem compl_opponent_attractor_trapFor
    (player : ParityPlayer)
    (target : Set G.Position) :
    G.TrapFor player {position | ¬ G.Attractor player.other target position} := by
  simpa using G.compl_attractor_trapFor_other player.other target

/-- A position outside the attractor to a priority class cannot have that priority. -/
theorem priority_ne_of_not_attractor_priorityClass
    {player : ParityPlayer}
    {priority : Nat}
    {position : G.Position}
    (hnot :
      ¬ G.Attractor player (G.priorityClass priority) position) :
    G.priority position ≠ priority := by
  intro hpriority
  exact hnot (Attractor.target hpriority)

/--
Attractor membership equipped with an explicit ordinal derivation rank.
The rank need not be minimal.  It only records enough information to show that
the recursive attractor choices decrease.
-/
inductive AttractorRanked
    (player : ParityPlayer)
    (target : Set G.Position) :
    G.Position -> Ordinal.{u} -> Prop
  | target {position : G.Position} :
      position ∈ target ->
        AttractorRanked player target position 0
  | owner
      {position next : G.Position}
      {nextRank rank : Ordinal.{u}} :
      position ∉ target ->
        G.owner position = player ->
          G.step position next ->
            AttractorRanked player target next nextRank ->
              nextRank < rank ->
                AttractorRanked player target position rank
  | opponent
      {position : G.Position}
      {rank : Ordinal.{u}} :
      position ∉ target ->
        G.owner position = player.other ->
          (successorRank :
            ∀ next : G.Position, G.step position next -> Ordinal.{u}) ->
          (successorRanked :
            ∀ next : G.Position,
              ∀ hstep : G.step position next,
                AttractorRanked player target next
                  (successorRank next hstep)) ->
          (successorLt :
            ∀ next : G.Position,
              ∀ hstep : G.step position next,
                successorRank next hstep < rank) ->
            AttractorRanked player target position rank

/-- A ranked attractor derivation forgets to ordinary attractor membership. -/
theorem attractor_of_attractorRanked
    {player : ParityPlayer}
    {target : Set G.Position}
    {position : G.Position}
    {rank : Ordinal.{u}}
    (hranked : G.AttractorRanked player target position rank) :
    G.Attractor player target position := by
  induction hranked with
  | target htarget =>
      exact Attractor.target htarget
  | owner _hnot howner hstep _hranked hlt ih =>
      exact Attractor.owner howner hstep ih
  | opponent _hnot howner successorRank successorRanked successorLt ih =>
      exact
        Attractor.opponent howner
          (by
            intro next hstep
            exact ih next hstep)

/--
Every ordinary attractor derivation admits some ordinal-ranked derivation.
The opponent constructor uses the supremum of successor ranks.
-/
theorem exists_attractorRanked_of_attractor
    {player : ParityPlayer}
    {target : Set G.Position}
    {position : G.Position}
    (hattractor : G.Attractor player target position) :
    ∃ rank : Ordinal.{u},
      G.AttractorRanked player target position rank := by
  refine
    Attractor.rec
      (motive := fun position _hattractor =>
        ∃ rank : Ordinal.{u},
          G.AttractorRanked player target position rank)
      ?target ?owner ?opponent hattractor
  · exact fun {position} htarget =>
      ⟨0, AttractorRanked.target htarget⟩
  · exact fun {position next} howner hstep _hnext ih => by
      by_cases htarget : position ∈ target
      · exact ⟨0, AttractorRanked.target htarget⟩
      · rcases ih with ⟨nextRank, hnextRanked⟩
        exact
          ⟨Order.succ nextRank,
            AttractorRanked.owner htarget howner hstep hnextRanked
              (Order.lt_succ nextRank)⟩
  · exact fun {position} howner _hall ih => by
      by_cases htarget : position ∈ target
      · exact ⟨0, AttractorRanked.target htarget⟩
      · classical
        let successorRank :
            ∀ next : G.Position, G.step position next -> Ordinal.{u} :=
          fun next hstep => Classical.choose (ih next hstep)
        have successorRanked :
            ∀ next : G.Position,
              ∀ hstep : G.step position next,
                G.AttractorRanked player target next
                  (successorRank next hstep) := by
          intro next hstep
          exact Classical.choose_spec (ih next hstep)
        let rank : Ordinal.{u} :=
          ⨆ edge : {next : G.Position // G.step position next},
            Order.succ (successorRank edge.1 edge.2)
        have successorLt :
            ∀ next : G.Position,
              ∀ hstep : G.step position next,
                successorRank next hstep < rank := by
          intro next hstep
          have hltSucc :
              successorRank next hstep <
                Order.succ (successorRank next hstep) :=
            Order.lt_succ (successorRank next hstep)
          have hleSup :
              Order.succ (successorRank next hstep) ≤ rank := by
            exact
              Ordinal.le_iSup
                (fun edge : {next : G.Position // G.step position next} =>
                  Order.succ (successorRank edge.1 edge.2))
                ⟨next, hstep⟩
          exact lt_of_lt_of_le hltSucc hleSup
        exact
          ⟨rank,
            AttractorRanked.opponent htarget howner
              successorRank successorRanked successorLt⟩

/-- The set of ordinal ranks witnessing ranked attractor membership. -/
def attractorRankSet
    (player : ParityPlayer)
    (target : Set G.Position)
    (position : G.Position) :
    Set Ordinal.{u} :=
  {rank | G.AttractorRanked player target position rank}

theorem attractorRankSet_nonempty
    {player : ParityPlayer}
    {target : Set G.Position}
    {position : G.Position}
    (hattractor : G.Attractor player target position) :
    (G.attractorRankSet player target position).Nonempty := by
  rcases G.exists_attractorRanked_of_attractor hattractor with
    ⟨rank, hranked⟩
  exact ⟨rank, hranked⟩

/--
The least ordinal rank of an attracted position, and `0` outside the attractor.
-/
noncomputable def leastAttractorRank
    (player : ParityPlayer)
    (target : Set G.Position)
    (position : G.Position) :
    Ordinal.{u} :=
  by
    classical
    exact
      if hattractor : G.Attractor player target position then
        Ordinal.lt_wf.min
          (G.attractorRankSet player target position)
          (G.attractorRankSet_nonempty hattractor)
      else
        0

theorem leastAttractorRank_ranked
    {player : ParityPlayer}
    {target : Set G.Position}
    {position : G.Position}
    (hattractor : G.Attractor player target position) :
    G.AttractorRanked player target position
      (G.leastAttractorRank player target position) := by
  classical
  simpa [leastAttractorRank, hattractor, attractorRankSet] using
    Ordinal.lt_wf.min_mem
      (G.attractorRankSet player target position)
      (G.attractorRankSet_nonempty hattractor)

theorem leastAttractorRank_le_of_ranked
    {player : ParityPlayer}
    {target : Set G.Position}
    {position : G.Position}
    {rank : Ordinal.{u}}
    (hranked : G.AttractorRanked player target position rank) :
    G.leastAttractorRank player target position ≤ rank := by
  classical
  have hattractor : G.Attractor player target position :=
    G.attractor_of_attractorRanked hranked
  have hnotLt :
      ¬ rank < G.leastAttractorRank player target position := by
    simpa [leastAttractorRank, hattractor, attractorRankSet] using
      Ordinal.lt_wf.not_lt_min
        (G.attractorRankSet player target position)
        (x := rank)
        hranked
  exact not_lt.mp hnotLt

/-- Progress exposed by any ranked derivation at a player-owned non-target node. -/
theorem attractorRanked_owner_progress
    {player : ParityPlayer}
    {target : Set G.Position}
    {position : G.Position}
    {rank : Ordinal.{u}}
    (hranked : G.AttractorRanked player target position rank)
    (hnotTarget : position ∉ target)
    (howner : G.owner position = player) :
    ∃ (next : G.Position) (nextRank : Ordinal.{u}),
      G.step position next ∧
        G.AttractorRanked player target next nextRank ∧
          nextRank < rank := by
  cases hranked with
  | target htarget =>
      exact False.elim (hnotTarget htarget)
  | owner hnotRank hownerRank hstep hnextRanked hlt =>
      exact ⟨_, _, hstep, hnextRanked, hlt⟩
  | opponent hnotRank hownerRank successorRank successorRanked successorLt =>
      have hcontra : player = player.other := by
        calc
          player = G.owner position := howner.symm
          _ = player.other := hownerRank
      exact False.elim (ParityPlayer.ne_other player hcontra)

/-- Progress exposed by any ranked derivation at an opponent-owned non-target node. -/
theorem attractorRanked_opponent_progress
    {player : ParityPlayer}
    {target : Set G.Position}
    {position : G.Position}
    {rank : Ordinal.{u}}
    (hranked : G.AttractorRanked player target position rank)
    (hnotTarget : position ∉ target)
    (howner : G.owner position = player.other) :
    ∀ next : G.Position,
      G.step position next ->
        ∃ nextRank : Ordinal.{u},
          G.AttractorRanked player target next nextRank ∧
            nextRank < rank := by
  cases hranked with
  | target htarget =>
      exact False.elim (hnotTarget htarget)
  | owner hnotRank hownerRank hstep hnextRanked hlt =>
      have hcontra : player = player.other := by
        calc
          player = G.owner position := hownerRank.symm
          _ = player.other := howner
      exact False.elim (ParityPlayer.ne_other player hcontra)
  | opponent hnotRank hownerRank successorRank successorRanked successorLt =>
      intro next hstep
      exact
        ⟨successorRank next hstep,
          successorRanked next hstep,
          successorLt next hstep⟩

/--
An ordinal progress certificate for a player's attractor.  Outside the target,
player-owned attractor positions have a legal attracted successor of smaller
rank, and opponent-owned attractor positions have all legal successors
attracted with smaller rank.
-/
structure AttractorRank
    (player : ParityPlayer)
    (target : Set G.Position) where
  rank : G.Position -> Ordinal.{u}
  owner_progress :
    ∀ position : G.Position,
      G.Attractor player target position ->
        position ∉ target ->
          G.owner position = player ->
            ∃ next : G.Position,
              G.step position next ∧
                G.Attractor player target next ∧
                  rank next < rank position
  opponent_progress :
    ∀ position : G.Position,
      G.Attractor player target position ->
        position ∉ target ->
          G.owner position = player.other ->
            ∀ next : G.Position,
              G.step position next ->
                G.Attractor player target next ∧ rank next < rank position

/-- The least ranked derivation gives an ordinal progress certificate. -/
noncomputable def attractorRank
    (player : ParityPlayer)
    (target : Set G.Position) :
    G.AttractorRank player target where
  rank := G.leastAttractorRank player target
  owner_progress := by
    intro position hattractor hnotTarget howner
    have hranked :
        G.AttractorRanked player target position
          (G.leastAttractorRank player target position) :=
      G.leastAttractorRank_ranked hattractor
    rcases
        G.attractorRanked_owner_progress hranked hnotTarget howner with
      ⟨next, nextRank, hstep, hnextRanked, hlt⟩
    refine ⟨next, hstep, G.attractor_of_attractorRanked hnextRanked, ?_⟩
    exact
      lt_of_le_of_lt
        (G.leastAttractorRank_le_of_ranked hnextRanked) hlt
  opponent_progress := by
    intro position hattractor hnotTarget hownerOther next hstep
    have hranked :
        G.AttractorRanked player target position
          (G.leastAttractorRank player target position) :=
      G.leastAttractorRank_ranked hattractor
    rcases
        G.attractorRanked_opponent_progress
          hranked hnotTarget hownerOther next hstep with
      ⟨nextRank, hnextRanked, hlt⟩
    exact
      ⟨G.attractor_of_attractorRanked hnextRanked,
        lt_of_le_of_lt
          (G.leastAttractorRank_le_of_ranked hnextRanked) hlt⟩

/--
The positional attractor strategy induced by an ordinal progress certificate.
At player-owned attracted positions outside the target it chooses a strictly
rank-decreasing attracted successor; elsewhere it uses an arbitrary legal move.
-/
noncomputable def attractorRankStrategy
    {player : ParityPlayer}
    {target : Set G.Position}
    (rank : G.AttractorRank player target) :
    G.PositionalStrategy player where
  move position :=
    by
      classical
      exact
        if hprogress :
            G.Attractor player target position ∧
              position ∉ target ∧ G.owner position = player then
          Classical.choose
            (rank.owner_progress position hprogress.1 hprogress.2.1
              hprogress.2.2)
        else
          Classical.choose (G.step_total position)
  legal := by
    intro position howner
    classical
    by_cases hprogress :
        G.Attractor player target position ∧
          position ∉ target ∧ G.owner position = player
    · change
        G.step position
          (if h :
              G.Attractor player target position ∧
                position ∉ target ∧ G.owner position = player then
            Classical.choose
              (rank.owner_progress position h.1 h.2.1 h.2.2)
          else
            Classical.choose (G.step_total position))
      simpa [hprogress] using
        (Classical.choose_spec
          (rank.owner_progress position hprogress.1 hprogress.2.1
            hprogress.2.2)).1
    · change
        G.step position
          (if h :
              G.Attractor player target position ∧
                position ∉ target ∧ G.owner position = player then
            Classical.choose
              (rank.owner_progress position h.1 h.2.1 h.2.2)
          else
            Classical.choose (G.step_total position))
      simpa [hprogress] using
        Classical.choose_spec (G.step_total position)

theorem attractorRankStrategy_move_progress
    {player : ParityPlayer}
    {target : Set G.Position}
    (rank : G.AttractorRank player target)
    {position : G.Position}
    (hattractor : G.Attractor player target position)
    (hnotTarget : position ∉ target)
    (howner : G.owner position = player) :
    G.step position ((G.attractorRankStrategy rank).move position) ∧
      G.Attractor player target ((G.attractorRankStrategy rank).move position) ∧
        rank.rank ((G.attractorRankStrategy rank).move position) <
          rank.rank position := by
  classical
  have hprogress :
      G.Attractor player target position ∧
        position ∉ target ∧ G.owner position = player :=
    ⟨hattractor, hnotTarget, howner⟩
  simpa [attractorRankStrategy, hprogress] using
    Classical.choose_spec
      (rank.owner_progress position hattractor hnotTarget howner)

/--
The strategy induced by an attractor rank reaches the target in finitely many
steps from every attracted start.  The proof is by well-founded induction on
the ordinal rank of the current position.
-/
theorem attractorRankStrategy_reaches_target
    {player : ParityPlayer}
    {target : Set G.Position}
    (rank : G.AttractorRank player target)
    {start : G.Position}
    (hstart : G.Attractor player target start)
    {path : Nat -> G.Position}
    (hplayFrom : G.PlayFrom start path)
    (hconsistent :
      (G.attractorRankStrategy rank).Consistent path) :
    ∃ n : Nat, path n ∈ target := by
  let strategy := G.attractorRankStrategy rank
  let P : Ordinal -> Prop :=
    fun ordinal =>
      ∀ {position : G.Position},
        rank.rank position = ordinal ->
          G.Attractor player target position ->
            ∀ {path : Nat -> G.Position},
              G.PlayFrom position path ->
                strategy.Consistent path ->
                  ∃ n : Nat, path n ∈ target
  have hP : ∀ ordinal : Ordinal, P ordinal := by
    intro ordinal
    induction ordinal using WellFoundedLT.induction with
    | ind ordinal ih =>
        intro position hrank hattractor path hpathFrom hpathConsistent
        rcases hpathFrom with ⟨hpath0, hplay⟩
        by_cases htarget : position ∈ target
        · exact ⟨0, by simpa [hpath0] using htarget⟩
        by_cases howner : G.owner position = player
        · have hmoveProgress :
              G.step position (strategy.move position) ∧
                G.Attractor player target (strategy.move position) ∧
                  rank.rank (strategy.move position) < rank.rank position := by
            simpa [strategy] using
              G.attractorRankStrategy_move_progress
                rank hattractor htarget howner
          have hpath1 :
              path 1 = strategy.move position := by
            simpa [strategy, hpath0] using
              hpathConsistent 0 (by simpa [hpath0] using howner)
          have hpath1Attractor :
              G.Attractor player target (path 1) := by
            simpa [hpath1] using hmoveProgress.2.1
          have hpath1Rank :
              rank.rank (path 1) < ordinal := by
            rw [hpath1]
            simpa [hrank] using hmoveProgress.2.2
          have htailPlayFrom :
              G.PlayFrom (path 1) (G.pathTail path 1) := by
            constructor
            · simp [pathTail, Nat.add_comm]
            · exact G.play_pathTail hplay 1
          have htailConsistent :
              strategy.Consistent (G.pathTail path 1) := by
            intro n htailOwner
            have hownerOriginal :
                G.owner (path (1 + n)) = player := by
              simpa [pathTail] using htailOwner
            calc
              G.pathTail path 1 (n + 1)
                  = path (1 + (n + 1)) := rfl
              _ = path ((1 + n) + 1) := by rfl
              _ = strategy.move (path (1 + n)) :=
                    hpathConsistent (1 + n) hownerOriginal
              _ = strategy.move (G.pathTail path 1 n) := by
                    rfl
          rcases
              ih (rank.rank (path 1)) hpath1Rank
                rfl hpath1Attractor htailPlayFrom htailConsistent with
            ⟨n, hn⟩
          exact
            ⟨1 + n, by simpa [pathTail, Nat.add_comm, Nat.add_assoc] using hn⟩
        · have hownerOther : G.owner position = player.other :=
            ParityPlayer.eq_other_of_ne howner
          have hstep1 : G.step position (path 1) := by
            simpa [hpath0] using hplay 0
          have hprogress :=
            rank.opponent_progress position hattractor htarget hownerOther
              (path 1) hstep1
          have hpath1Rank :
              rank.rank (path 1) < ordinal := by
            simpa [hrank] using hprogress.2
          have htailPlayFrom :
              G.PlayFrom (path 1) (G.pathTail path 1) := by
            constructor
            · simp [pathTail, Nat.add_comm]
            · exact G.play_pathTail hplay 1
          have htailConsistent :
              strategy.Consistent (G.pathTail path 1) := by
            intro n htailOwner
            have hownerOriginal :
                G.owner (path (1 + n)) = player := by
              simpa [pathTail] using htailOwner
            calc
              G.pathTail path 1 (n + 1)
                  = path (1 + (n + 1)) := rfl
              _ = path ((1 + n) + 1) := by rfl
              _ = strategy.move (path (1 + n)) :=
                    hpathConsistent (1 + n) hownerOriginal
              _ = strategy.move (G.pathTail path 1 n) := by
                    rfl
          rcases
              ih (rank.rank (path 1)) hpath1Rank
                  rfl hprogress.1 htailPlayFrom htailConsistent with
            ⟨n, hn⟩
          exact
            ⟨1 + n, by simpa [pathTail, Nat.add_comm, Nat.add_assoc] using hn⟩
  exact hP (rank.rank start) rfl hstart hplayFrom hconsistent

/--
Local version of `attractorRankStrategy_reaches_target`: the play only has to
follow the attractor strategy while the target has not yet been seen.
-/
theorem attractorRankStrategy_reaches_target_until
    {player : ParityPlayer}
    {target : Set G.Position}
    (rank : G.AttractorRank player target)
    {start : G.Position}
    (hstart : G.Attractor player target start)
    {path : Nat -> G.Position}
    (hplayFrom : G.PlayFrom start path)
    (hconsistent :
      (G.attractorRankStrategy rank).ConsistentUntil target path) :
    ∃ n : Nat, path n ∈ target := by
  let strategy := G.attractorRankStrategy rank
  let P : Ordinal -> Prop :=
    fun ordinal =>
      ∀ {position : G.Position},
        rank.rank position = ordinal ->
          G.Attractor player target position ->
            ∀ {path : Nat -> G.Position},
              G.PlayFrom position path ->
                strategy.ConsistentUntil target path ->
                  ∃ n : Nat, path n ∈ target
  have hP : ∀ ordinal : Ordinal, P ordinal := by
    intro ordinal
    induction ordinal using WellFoundedLT.induction with
    | ind ordinal ih =>
        intro position hrank hattractor path hpathFrom hpathConsistent
        rcases hpathFrom with ⟨hpath0, hplay⟩
        by_cases htarget : position ∈ target
        · exact ⟨0, by simpa [hpath0] using htarget⟩
        by_cases howner : G.owner position = player
        · have hmoveProgress :
              G.step position (strategy.move position) ∧
                G.Attractor player target (strategy.move position) ∧
                  rank.rank (strategy.move position) < rank.rank position := by
            simpa [strategy] using
              G.attractorRankStrategy_move_progress
                rank hattractor htarget howner
          have hnotTarget0 :
              ∀ k : Nat, k ≤ 0 -> path k ∉ target := by
            intro k hk
            have hk0 : k = 0 := by omega
            simpa [hk0, hpath0] using htarget
          have hpath1 :
              path 1 = strategy.move position := by
            simpa [strategy, hpath0] using
              hpathConsistent 0 hnotTarget0
                (by simpa [hpath0] using howner)
          have hpath1Attractor :
              G.Attractor player target (path 1) := by
            simpa [hpath1] using hmoveProgress.2.1
          have hpath1Rank :
              rank.rank (path 1) < ordinal := by
            rw [hpath1]
            simpa [hrank] using hmoveProgress.2.2
          have htailPlayFrom :
              G.PlayFrom (path 1) (G.pathTail path 1) := by
            constructor
            · simp [pathTail, Nat.add_comm]
            · exact G.play_pathTail hplay 1
          have htailConsistent :
              strategy.ConsistentUntil target (G.pathTail path 1) := by
            intro n htailNoTarget htailOwner
            have hownerOriginal :
                G.owner (path (1 + n)) = player := by
              simpa [pathTail] using htailOwner
            have horiginalNoTarget :
                ∀ k : Nat, k ≤ 1 + n -> path k ∉ target := by
              intro k hk
              cases k with
              | zero =>
                  simpa [hpath0] using htarget
              | succ k =>
                  have hkTail : k ≤ n := by omega
                  simpa [pathTail, Nat.add_comm, Nat.add_assoc] using
                    htailNoTarget k hkTail
            calc
              G.pathTail path 1 (n + 1)
                  = path (1 + (n + 1)) := rfl
              _ = path ((1 + n) + 1) := by rfl
              _ = strategy.move (path (1 + n)) :=
                    hpathConsistent (1 + n)
                      horiginalNoTarget hownerOriginal
              _ = strategy.move (G.pathTail path 1 n) := by
                    rfl
          rcases
              ih (rank.rank (path 1)) hpath1Rank
                rfl hpath1Attractor htailPlayFrom htailConsistent with
            ⟨n, hn⟩
          exact
            ⟨1 + n, by simpa [pathTail, Nat.add_comm, Nat.add_assoc] using hn⟩
        · have hownerOther : G.owner position = player.other :=
            ParityPlayer.eq_other_of_ne howner
          have hstep1 : G.step position (path 1) := by
            simpa [hpath0] using hplay 0
          have hprogress :=
            rank.opponent_progress position hattractor htarget hownerOther
              (path 1) hstep1
          have hpath1Rank :
              rank.rank (path 1) < ordinal := by
            simpa [hrank] using hprogress.2
          have htailPlayFrom :
              G.PlayFrom (path 1) (G.pathTail path 1) := by
            constructor
            · simp [pathTail, Nat.add_comm]
            · exact G.play_pathTail hplay 1
          have htailConsistent :
              strategy.ConsistentUntil target (G.pathTail path 1) := by
            intro n htailNoTarget htailOwner
            have hownerOriginal :
                G.owner (path (1 + n)) = player := by
              simpa [pathTail] using htailOwner
            have horiginalNoTarget :
                ∀ k : Nat, k ≤ 1 + n -> path k ∉ target := by
              intro k hk
              cases k with
              | zero =>
                  simpa [hpath0] using htarget
              | succ k =>
                  have hkTail : k ≤ n := by omega
                  simpa [pathTail, Nat.add_comm, Nat.add_assoc] using
                    htailNoTarget k hkTail
            calc
              G.pathTail path 1 (n + 1)
                  = path (1 + (n + 1)) := rfl
              _ = path ((1 + n) + 1) := by rfl
              _ = strategy.move (path (1 + n)) :=
                    hpathConsistent (1 + n)
                      horiginalNoTarget hownerOriginal
              _ = strategy.move (G.pathTail path 1 n) := by
                    rfl
          rcases
              ih (rank.rank (path 1)) hpath1Rank
                rfl hprogress.1 htailPlayFrom htailConsistent with
            ⟨n, hn⟩
          exact
            ⟨1 + n, by simpa [pathTail, Nat.add_comm, Nat.add_assoc] using hn⟩
  exact hP (rank.rank start) rfl hstart hplayFrom hconsistent

/--
The canonical positional strategy for a player's attractor, using the least
ordinal rank construction above.
-/
noncomputable def attractorStrategy
    (player : ParityPlayer)
    (target : Set G.Position) :
    G.PositionalStrategy player :=
  G.attractorRankStrategy (G.attractorRank player target)

/-- The canonical attractor strategy makes ranked progress outside the target. -/
theorem attractorStrategy_move_progress
    {player : ParityPlayer}
    {target : Set G.Position}
    {position : G.Position}
    (hattractor : G.Attractor player target position)
    (hnotTarget : position ∉ target)
    (howner : G.owner position = player) :
    G.step position ((G.attractorStrategy player target).move position) ∧
      G.Attractor player target
        ((G.attractorStrategy player target).move position) ∧
        (G.attractorRank player target).rank
            ((G.attractorStrategy player target).move position) <
          (G.attractorRank player target).rank position := by
  exact
    G.attractorRankStrategy_move_progress
      (G.attractorRank player target) hattractor hnotTarget howner

/-- The canonical attractor strategy reaches the target from every attracted start. -/
theorem attractorStrategy_reaches_target
    {player : ParityPlayer}
    {target : Set G.Position}
    {start : G.Position}
    (hstart : G.Attractor player target start)
    {path : Nat -> G.Position}
    (hplayFrom : G.PlayFrom start path)
    (hconsistent :
      (G.attractorStrategy player target).Consistent path) :
    ∃ n : Nat, path n ∈ target := by
  exact
    G.attractorRankStrategy_reaches_target
      (G.attractorRank player target) hstart hplayFrom hconsistent

/--
Local version for the canonical attractor strategy: it suffices to follow the
strategy until the first target visit.
-/
theorem attractorStrategy_reaches_target_until
    {player : ParityPlayer}
    {target : Set G.Position}
    {start : G.Position}
    (hstart : G.Attractor player target start)
    {path : Nat -> G.Position}
    (hplayFrom : G.PlayFrom start path)
    (hconsistent :
      (G.attractorStrategy player target).ConsistentUntil target path) :
    ∃ n : Nat, path n ∈ target := by
  exact
    G.attractorRankStrategy_reaches_target_until
      (G.attractorRank player target) hstart hplayFrom hconsistent

/--
Strategy that uses `targetStrategy` once the play is in `target`, and otherwise
uses the canonical attractor strategy toward `target`.
-/
noncomputable def attractorThenStrategy
    {player : ParityPlayer}
    (target : Set G.Position)
    (targetStrategy : G.PositionalStrategy player) :
    G.PositionalStrategy player where
  move position :=
    by
      classical
      exact
        if position ∈ target then
          targetStrategy.move position
        else
          (G.attractorStrategy player target).move position
  legal := by
    intro position howner
    classical
    by_cases hposition : position ∈ target
    · change
        G.step position
          (if h : position ∈ target then
            targetStrategy.move position
          else
            (G.attractorStrategy player target).move position)
      simpa [hposition] using targetStrategy.legal position howner
    · change
        G.step position
          (if h : position ∈ target then
            targetStrategy.move position
          else
            (G.attractorStrategy player target).move position)
      simpa [hposition] using
        (G.attractorStrategy player target).legal position howner

@[simp]
theorem attractorThenStrategy_move_inside
    {player : ParityPlayer}
    {target : Set G.Position}
    (targetStrategy : G.PositionalStrategy player)
    {position : G.Position}
    (hposition : position ∈ target) :
    (G.attractorThenStrategy target targetStrategy).move position =
      targetStrategy.move position := by
  classical
  simp [attractorThenStrategy, hposition]

@[simp]
theorem attractorThenStrategy_move_outside
    {player : ParityPlayer}
    {target : Set G.Position}
    (targetStrategy : G.PositionalStrategy player)
    {position : G.Position}
    (hposition : position ∉ target) :
    (G.attractorThenStrategy target targetStrategy).move position =
      (G.attractorStrategy player target).move position := by
  classical
  simp [attractorThenStrategy, hposition]

/--
The attractor-then-target strategy keeps player-owned positions inside the
attractor, provided the target strategy keeps player-owned target positions in
the target.
-/
theorem attractorThenStrategy_move_attractor_mem
    {player : ParityPlayer}
    {target : Set G.Position}
    (targetStrategy : G.PositionalStrategy player)
    (hmoveMem :
      ∀ position : G.Position,
        position ∈ target ->
          G.owner position = player ->
            targetStrategy.move position ∈ target)
    {position : G.Position}
    (hattractor : G.Attractor player target position)
    (howner : G.owner position = player) :
    (G.attractorThenStrategy target targetStrategy).move position ∈
      {position : G.Position | G.Attractor player target position} := by
  by_cases htarget : position ∈ target
  · rw [G.attractorThenStrategy_move_inside targetStrategy htarget]
    exact G.target_subset_attractor player target
      (hmoveMem position htarget howner)
  · rw [G.attractorThenStrategy_move_outside targetStrategy htarget]
    exact
      (G.attractorStrategy_move_progress hattractor htarget howner).2.1

/--
Opponent-owned successors of an attracted position remain attracted when the
target itself is closed under opponent-owned successors.
-/
theorem attractor_opponent_successor_mem_of_target_invariant
    {player : ParityPlayer}
    {target : Set G.Position}
    (htargetOpponentMem :
      ∀ position : G.Position,
        position ∈ target ->
          G.owner position = player.other ->
            ∀ next : G.Position, G.step position next -> next ∈ target)
    {position next : G.Position}
    (hattractor : G.Attractor player target position)
    (howner : G.owner position = player.other)
    (hstep : G.step position next) :
    G.Attractor player target next := by
  by_cases htarget : position ∈ target
  · exact G.target_subset_attractor player target
      (htargetOpponentMem position htarget howner next hstep)
  · exact
      ((G.attractorRank player target).opponent_progress
        position hattractor htarget howner next hstep).1

theorem attractorThenStrategy_consistentUntil
    {player : ParityPlayer}
    {target : Set G.Position}
    (targetStrategy : G.PositionalStrategy player)
    {path : Nat -> G.Position}
    (hconsistent :
      (G.attractorThenStrategy target targetStrategy).Consistent path) :
    (G.attractorStrategy player target).ConsistentUntil target path := by
  intro n hnotTarget howner
  have hnot : path n ∉ target := hnotTarget n le_rfl
  calc
    path (n + 1)
        = (G.attractorThenStrategy target targetStrategy).move (path n) :=
          hconsistent n howner
    _ = (G.attractorStrategy player target).move (path n) := by
          rw [G.attractorThenStrategy_move_outside targetStrategy hnot]

/--
After the attractor-then-target strategy reaches an invariant target, all later
positions remain in the target.
-/
theorem attractorThenStrategy_tail_mem
    {player : ParityPlayer}
    {target : Set G.Position}
    (targetStrategy : G.PositionalStrategy player)
    (hmoveMem :
      ∀ position : G.Position,
        position ∈ target ->
          G.owner position = player ->
            targetStrategy.move position ∈ target)
    (hopponentMem :
      ∀ position : G.Position,
        position ∈ target ->
          G.owner position = player.other ->
            ∀ next : G.Position, G.step position next -> next ∈ target)
    {path : Nat -> G.Position}
    (hplay : G.Play path)
    (hconsistent :
      (G.attractorThenStrategy target targetStrategy).Consistent path)
    {offset : Nat}
    (hoffset : path offset ∈ target) :
    ∀ n : Nat, G.pathTail path offset n ∈ target := by
  intro n
  induction n with
  | zero =>
      simpa [pathTail] using hoffset
  | succ n ih =>
      by_cases howner : G.owner (G.pathTail path offset n) = player
      · have hownerOriginal :
            G.owner (path (offset + n)) = player := by
          simpa [pathTail] using howner
        have hnext :
            path ((offset + n) + 1) =
              (G.attractorThenStrategy target targetStrategy).move
                (path (offset + n)) :=
          hconsistent (offset + n) hownerOriginal
        have hindex : offset + (n + 1) = (offset + n) + 1 := by
          omega
        have hnextTarget :
            targetStrategy.move (path (offset + n)) ∈ target :=
          hmoveMem (path (offset + n)) (by simpa [pathTail] using ih)
            hownerOriginal
        simpa [pathTail, hindex, hnext,
          G.attractorThenStrategy_move_inside targetStrategy
            (by simpa [pathTail] using ih)] using hnextTarget
      · have hownerOther :
            G.owner (G.pathTail path offset n) = player.other :=
          ParityPlayer.eq_other_of_ne howner
        have hownerOriginal :
            G.owner (path (offset + n)) = player.other := by
          simpa [pathTail] using hownerOther
        have hstep :
            G.step (path (offset + n)) (path ((offset + n) + 1)) :=
          hplay (offset + n)
        have hindex : offset + (n + 1) = (offset + n) + 1 := by
          omega
        have hnextTarget :
            path ((offset + n) + 1) ∈ target :=
          hopponentMem (path (offset + n))
            (by simpa [pathTail] using ih)
            hownerOriginal (path ((offset + n) + 1)) hstep
        simpa [pathTail, hindex] using hnextTarget

theorem attractorThenStrategy_tail_consistent
    {player : ParityPlayer}
    {target : Set G.Position}
    (targetStrategy : G.PositionalStrategy player)
    {path : Nat -> G.Position}
    (hconsistent :
      (G.attractorThenStrategy target targetStrategy).Consistent path)
    {offset : Nat}
    (hmem : ∀ n : Nat, G.pathTail path offset n ∈ target) :
    targetStrategy.Consistent (G.pathTail path offset) := by
  intro n hownerTail
  have hownerOriginal :
      G.owner (path (offset + n)) = player := by
    simpa [pathTail] using hownerTail
  have hindex : offset + (n + 1) = (offset + n) + 1 := by
    omega
  calc
    G.pathTail path offset (n + 1)
        = path (offset + (n + 1)) := rfl
    _ = path ((offset + n) + 1) := by
          rw [hindex]
    _ = (G.attractorThenStrategy target targetStrategy).move
          (path (offset + n)) :=
          hconsistent (offset + n) hownerOriginal
    _ = targetStrategy.move (path (offset + n)) := by
          rw [G.attractorThenStrategy_move_inside targetStrategy
            (by simpa [pathTail] using hmem n)]
    _ = targetStrategy.move (G.pathTail path offset n) := by
          rfl

/--
If `targetStrategy` wins on an invariant target, then the attractor-then-target
strategy wins from every position in the attractor of that target.
-/
theorem attractorThenStrategy_winningFrom
    {player : ParityPlayer}
    {target : Set G.Position}
    (targetStrategy : G.PositionalStrategy player)
    (htargetWinning :
      ∀ position : G.Position,
        position ∈ target ->
          PositionalStrategy.WinningFrom
            (G := G) targetStrategy position)
    (hmoveMem :
      ∀ position : G.Position,
        position ∈ target ->
          G.owner position = player ->
            targetStrategy.move position ∈ target)
    (hopponentMem :
      ∀ position : G.Position,
        position ∈ target ->
          G.owner position = player.other ->
            ∀ next : G.Position, G.step position next -> next ∈ target)
    {start : G.Position}
    (hstart : G.Attractor player target start) :
    PositionalStrategy.WinningFrom
      (G := G) (G.attractorThenStrategy target targetStrategy) start := by
  intro path hplayFrom hconsistent
  rcases hplayFrom with ⟨hpath0, hplay⟩
  have hreach :
      ∃ n : Nat, path n ∈ target :=
    G.attractorStrategy_reaches_target_until hstart
      ⟨hpath0, hplay⟩
      (G.attractorThenStrategy_consistentUntil targetStrategy hconsistent)
  rcases hreach with ⟨offset, hoffset⟩
  let tail := G.pathTail path offset
  have hmem : ∀ n : Nat, tail n ∈ target := by
    intro n
    simpa [tail] using
      G.attractorThenStrategy_tail_mem targetStrategy
        hmoveMem hopponentMem hplay hconsistent hoffset n
  have htailPlayFrom : G.PlayFrom (path offset) tail := by
    simpa [tail] using G.playFrom_pathTail hplay offset
  have htailConsistent : targetStrategy.Consistent tail := by
    simpa [tail] using
      G.attractorThenStrategy_tail_consistent
        targetStrategy hconsistent
        (by
          intro n
          simpa [tail] using hmem n)
  have htailWin : G.PlayerWinsPath player tail :=
    htargetWinning (path offset) hoffset tail
      htailPlayFrom htailConsistent
  exact
    (G.playerWinsPath_pathTail_iff player path offset).mp
      (by simpa [tail] using htailWin)

/--
The attractor to a positional winning region is again contained in that
positional winning region.  Countability supplies one uniform positional
strategy on the target winning region.
-/
theorem attractor_positionalWinningRegion_subset
    (player : ParityPlayer) :
    {position : G.Position |
      G.Attractor player (G.PositionalWinningRegion player) position} ⊆
      G.PositionalWinningRegion player := by
  rcases G.exists_strategy_winningOn_positionalWinningRegion player with
    ⟨targetStrategy, htargetStrategy⟩
  intro position hposition
  refine ⟨G.attractorThenStrategy
    (G.PositionalWinningRegion player) targetStrategy, ?_⟩
  exact
    G.attractorThenStrategy_winningFrom
      targetStrategy htargetStrategy
      (by
        intro position hposition howner
        exact
          G.positionalWinningRegion_move_mem_of_winningOn
            targetStrategy htargetStrategy hposition howner)
      (by
        intro position hposition howner next hstep
        exact
          ((G.positionalWinningRegion_trapFor player)
            position hposition).2 howner next hstep)
      hposition

/--
The complement of a positional winning region is a trap for the other player.
This is the countable replacement for repeatedly removing opponent-attractor
regions in the finite Zielonka proof.
-/
theorem compl_positionalWinningRegion_trapFor_other
    (player : ParityPlayer) :
    G.TrapFor player.other
      {position : G.Position | position ∉ G.PositionalWinningRegion player} := by
  intro position hnotWinning
  constructor
  · intro hownerOther
    by_contra hnoSuccessor
    have hallSuccessors :
        ∀ next : G.Position,
          G.step position next ->
            G.Attractor player (G.PositionalWinningRegion player) next := by
      intro next hstep
      have hnextWinning : next ∈ G.PositionalWinningRegion player := by
        by_contra hnextNotWinning
        exact hnoSuccessor ⟨next, hstep, hnextNotWinning⟩
      exact CountableParityGame.Attractor.target hnextWinning
    have hattractor :
        G.Attractor player (G.PositionalWinningRegion player) position :=
      G.attractor_of_opponent_all hownerOther hallSuccessors
    exact hnotWinning
      (G.attractor_positionalWinningRegion_subset player hattractor)
  · intro hownerPlayer next hstep hnextWinning
    have hattractor :
        G.Attractor player (G.PositionalWinningRegion player) position :=
      G.attractor_of_owner_step (by simpa using hownerPlayer) hstep
        (CountableParityGame.Attractor.target hnextWinning)
    exact hnotWinning
      (G.attractor_positionalWinningRegion_subset player hattractor)

/--
Restrict the game to a trap.  The trap condition supplies totality of the
restricted edge relation: positions owned by `player` have an in-trap move, and
positions owned by the opponent have no edge leaving the trap.
-/
noncomputable def restrictToTrap
    (player : ParityPlayer)
    (region : Set G.Position)
    (htrap : G.TrapFor player region) :
    CountableParityGame where
  Position := {position : G.Position // position ∈ region}
  positionCountable := inferInstance
  owner position := G.owner position.1
  step source target := G.step source.1 target.1
  step_total := by
    intro position
    by_cases howner : G.owner position.1 = player
    · rcases (htrap position.1 position.2).1 howner with
        ⟨next, hstep, hnextRegion⟩
      exact ⟨⟨next, hnextRegion⟩, hstep⟩
    · have hownerOther : G.owner position.1 = player.other :=
        ParityPlayer.eq_other_of_ne howner
      rcases G.step_total position.1 with ⟨next, hstep⟩
      have hnextRegion :=
        (htrap position.1 position.2).2 hownerOther next hstep
      exact ⟨⟨next, hnextRegion⟩, hstep⟩
  priority position := G.priority position.1
  priority_finite := by
    refine G.priority_finite.subset ?_
    intro priority hpriority
    rcases hpriority with ⟨position, rfl⟩
    exact ⟨position.1, rfl⟩

@[simp]
theorem restrictToTrap_owner
    (player : ParityPlayer)
    (region : Set G.Position)
    (htrap : G.TrapFor player region)
    (position : (G.restrictToTrap player region htrap).Position) :
    (G.restrictToTrap player region htrap).owner position =
      G.owner position.1 :=
  rfl

@[simp]
theorem restrictToTrap_step
    (player : ParityPlayer)
    (region : Set G.Position)
    (htrap : G.TrapFor player region)
    (source target : (G.restrictToTrap player region htrap).Position) :
    (G.restrictToTrap player region htrap).step source target =
      G.step source.1 target.1 :=
  rfl

@[simp]
theorem restrictToTrap_priority
    (player : ParityPlayer)
    (region : Set G.Position)
    (htrap : G.TrapFor player region)
    (position : (G.restrictToTrap player region htrap).Position) :
    (G.restrictToTrap player region htrap).priority position =
      G.priority position.1 :=
  rfl

/-- The priority range of a trap subgame is included in the original range. -/
theorem restrictToTrap_priorityRangeFinset_subset
    (player : ParityPlayer)
    (region : Set G.Position)
    (htrap : G.TrapFor player region) :
    (G.restrictToTrap player region htrap).priorityRangeFinset ⊆
      G.priorityRangeFinset := by
  intro priority hpriority
  rw [mem_priorityRangeFinset] at hpriority ⊢
  rcases hpriority with ⟨position, hposition⟩
  exact ⟨position.1, hposition⟩

/--
If a trap subgame omits an original priority, then its priority range is a
proper subset of the original priority range.
-/
theorem restrictToTrap_priorityRangeFinset_ssubset_of_omits
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player region}
    {priority : Nat}
    (hpriority : priority ∈ Set.range G.priority)
    (homit :
      ∀ position : G.Position,
        position ∈ region -> G.priority position ≠ priority) :
    (G.restrictToTrap player region htrap).priorityRangeFinset ⊂
      G.priorityRangeFinset := by
  constructor
  · exact G.restrictToTrap_priorityRangeFinset_subset player region htrap
  · intro hreverse
    have hpriorityOriginal :
        priority ∈ G.priorityRangeFinset := by
      rw [mem_priorityRangeFinset]
      exact hpriority
    have hpriorityRestricted :
        priority ∈
          (G.restrictToTrap player region htrap).priorityRangeFinset :=
      hreverse hpriorityOriginal
    rw [mem_priorityRangeFinset] at hpriorityRestricted
    rcases hpriorityRestricted with ⟨position, hpositionPriority⟩
    exact homit position.1 position.2 (by simpa using hpositionPriority)

/--
If a trap subgame omits an original priority, then it has strictly fewer
occurring priorities.
-/
theorem restrictToTrap_priorityRangeFinset_card_lt_of_omits
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player region}
    {priority : Nat}
    (hpriority : priority ∈ Set.range G.priority)
    (homit :
      ∀ position : G.Position,
        position ∈ region -> G.priority position ≠ priority) :
    (G.restrictToTrap player region htrap).priorityRangeFinset.card <
      G.priorityRangeFinset.card :=
  Finset.card_lt_card
    (G.restrictToTrap_priorityRangeFinset_ssubset_of_omits
      hpriority homit)

/--
The complement of the attractor to priority `p` is a trap that omits priority
`p`, hence its restricted game has strictly fewer priorities whenever `p`
occurs in the original game.
-/
theorem restrict_compl_attractor_priorityClass_card_lt
    {player : ParityPlayer}
    {priority : Nat}
    (hpriority : priority ∈ Set.range G.priority) :
    (G.restrictToTrap player.other
        {position | ¬ G.Attractor player (G.priorityClass priority) position}
        (G.compl_attractor_trapFor_other player (G.priorityClass priority))).priorityRangeFinset.card <
      G.priorityRangeFinset.card := by
  exact
    G.restrictToTrap_priorityRangeFinset_card_lt_of_omits
      (player := player.other)
      (region :=
        {position | ¬ G.Attractor player (G.priorityClass priority) position})
      (htrap := G.compl_attractor_trapFor_other player (G.priorityClass priority))
      hpriority
      (by
        intro position hposition
        exact G.priority_ne_of_not_attractor_priorityClass hposition)

/-- Lift a path in a trap-restricted game back to the original arena. -/
def liftTrapPath
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player region}
    (path : Nat -> (G.restrictToTrap player region htrap).Position) :
    Nat -> G.Position :=
  fun n => (path n).1

@[simp]
theorem liftTrapPath_apply
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player region}
    (path : Nat -> (G.restrictToTrap player region htrap).Position)
    (n : Nat) :
    G.liftTrapPath path n = (path n).1 :=
  rfl

/-- Lift a finite prefix in a trap-restricted game back to the original arena. -/
def liftTrapPrefix
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player region}
    {n : Nat}
    (pref : (G.restrictToTrap player region htrap).Prefix n) :
    G.Prefix n :=
  fun i => (pref i).1

@[simp]
theorem liftTrapPrefix_apply
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player region}
    {n : Nat}
    (pref : (G.restrictToTrap player region htrap).Prefix n)
    (i : Fin (n + 1)) :
    G.liftTrapPrefix pref i = (pref i).1 :=
  rfl

@[simp]
theorem prefixLast_liftTrapPrefix
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player region}
    {n : Nat}
    (pref : (G.restrictToTrap player region htrap).Prefix n) :
    G.prefixLast (G.liftTrapPrefix pref) =
      ((G.restrictToTrap player region htrap).prefixLast pref).1 :=
  rfl

/-- Legal restricted prefixes lift to legal original prefixes. -/
theorem liftTrapPrefix_legal
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player region}
    {n : Nat}
    {pref : (G.restrictToTrap player region htrap).Prefix n}
    (hlegal :
      (G.restrictToTrap player region htrap).PrefixLegal pref) :
    G.PrefixLegal (G.liftTrapPrefix pref) := by
  intro i
  simpa [liftTrapPrefix] using hlegal i

@[simp]
theorem liftTrapPrefix_prefixOfPath
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player region}
    (path : Nat -> (G.restrictToTrap player region htrap).Position)
    (n : Nat) :
    G.liftTrapPrefix
        ((G.restrictToTrap player region htrap).prefixOfPath path n) =
      G.prefixOfPath (G.liftTrapPath path) n := by
  funext i
  rfl

/-- Legal plays in the restricted game lift to legal plays in the original game. -/
theorem restrictToTrap_play_lift
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player region}
    {path : Nat -> (G.restrictToTrap player region htrap).Position}
    (hplay : (G.restrictToTrap player region htrap).Play path) :
    G.Play (G.liftTrapPath path) := by
  intro n
  simpa [liftTrapPath] using hplay n

/-- Plays from a restricted start lift to plays from the original start. -/
theorem restrictToTrap_playFrom_lift
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player region}
    {start : (G.restrictToTrap player region htrap).Position}
    {path : Nat -> (G.restrictToTrap player region htrap).Position}
    (hplay :
      (G.restrictToTrap player region htrap).PlayFrom start path) :
    G.PlayFrom start.1 (G.liftTrapPath path) := by
  constructor
  · simpa [liftTrapPath] using congrArg Subtype.val hplay.1
  · exact G.restrictToTrap_play_lift hplay.2

/--
Priorities seen infinitely often in a restricted play are exactly the priorities
seen infinitely often in its lifted original play.
-/
theorem restrictToTrap_prioritySeenInfinitelyOften_lift_iff
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player region}
    (path : Nat -> (G.restrictToTrap player region htrap).Position)
    (priority : Nat) :
    (G.restrictToTrap player region htrap).PrioritySeenInfinitelyOften path priority ↔
      G.PrioritySeenInfinitelyOften (G.liftTrapPath path) priority := by
  rfl

/-- The Even objective is preserved by lifting restricted plays. -/
theorem restrictToTrap_minPriorityEven_lift_iff
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player region}
    (path : Nat -> (G.restrictToTrap player region htrap).Position) :
    (G.restrictToTrap player region htrap).MinPriorityEven path ↔
      G.MinPriorityEven (G.liftTrapPath path) := by
  rfl

/-- The Odd objective is preserved by lifting restricted plays. -/
theorem restrictToTrap_minPriorityOdd_lift_iff
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player region}
    (path : Nat -> (G.restrictToTrap player region htrap).Position) :
    (G.restrictToTrap player region htrap).MinPriorityOdd path ↔
      G.MinPriorityOdd (G.liftTrapPath path) := by
  rfl

/-- Either player's parity objective is preserved by lifting restricted plays. -/
theorem restrictToTrap_playerWinsPath_lift_iff
    {trapPlayer player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor trapPlayer region}
    (path : Nat -> (G.restrictToTrap trapPlayer region htrap).Position) :
    (G.restrictToTrap trapPlayer region htrap).PlayerWinsPath player path ↔
      G.PlayerWinsPath player (G.liftTrapPath path) := by
  cases player <;> rfl

/--
Restrict a history-dependent `player` strategy to a region that is a trap for
`player.other`.  At player-owned legal prefixes the original move is forced to
remain in the region by the trap property; elsewhere the strategy may choose
any restricted legal successor.
-/
noncomputable def restrictToOpponentTrapStrategy
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player.other region}
    (strategy : G.Strategy player)
    (hlegal : strategy.Legal) :
    (G.restrictToTrap player.other region htrap).Strategy player where
  move n pref :=
    by
      classical
      let source := (G.restrictToTrap player.other region htrap).prefixLast pref
      exact
        if hprefix :
            (G.restrictToTrap player.other region htrap).PrefixLegal pref then
          if howner :
              (G.restrictToTrap player.other region htrap).owner source = player then
            ⟨strategy.move n (G.liftTrapPrefix pref), by
              have horiginalLegal :
                  G.PrefixLegal (G.liftTrapPrefix pref) :=
                G.liftTrapPrefix_legal hprefix
              have hstep :
                  G.step source.1
                    (strategy.move n (G.liftTrapPrefix pref)) := by
                simpa [source] using
                  hlegal n (G.liftTrapPrefix pref) horiginalLegal howner
              have hownerTrap :
                  G.owner source.1 = player.other.other := by
                simpa [source] using howner
              exact (htrap source.1 source.2).2 hownerTrap
                (strategy.move n (G.liftTrapPrefix pref)) hstep⟩
          else
            Classical.choose
              ((G.restrictToTrap player.other region htrap).step_total source)
        else
          Classical.choose
            ((G.restrictToTrap player.other region htrap).step_total source)

theorem restrictToOpponentTrapStrategy_legal
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player.other region}
    {strategy : G.Strategy player}
    {hlegal : strategy.Legal} :
    Strategy.Legal
      (G := G.restrictToTrap player.other region htrap)
      (G.restrictToOpponentTrapStrategy strategy hlegal) := by
  intro n pref hprefix howner
  classical
  let source := (G.restrictToTrap player.other region htrap).prefixLast pref
  have hownerSource : G.owner source.1 = player := by
    simpa [source] using howner
  have hownerOriginal :
      G.owner (G.prefixLast (G.liftTrapPrefix pref)) = player := by
    simpa [source] using hownerSource
  change
    (G.restrictToTrap player.other region htrap).step source
      ((if hp :
          (G.restrictToTrap player.other region htrap).PrefixLegal pref then
        if ho :
            (G.restrictToTrap player.other region htrap).owner source = player then
          ⟨strategy.move n (G.liftTrapPrefix pref), _⟩
        else
          Classical.choose
            ((G.restrictToTrap player.other region htrap).step_total source)
      else
        Classical.choose
          ((G.restrictToTrap player.other region htrap).step_total source)) :
        (G.restrictToTrap player.other region htrap).Position)
  simpa [restrictToOpponentTrapStrategy, source, hprefix, hownerSource] using
    hlegal n (G.liftTrapPrefix pref)
      (G.liftTrapPrefix_legal hprefix) hownerOriginal

theorem restrictToOpponentTrapStrategy_consistent_lift
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player.other region}
    {strategy : G.Strategy player}
    {hlegal : strategy.Legal}
    {path : Nat -> (G.restrictToTrap player.other region htrap).Position}
    (hplay :
      (G.restrictToTrap player.other region htrap).Play path)
    (hconsistent :
      (G.restrictToOpponentTrapStrategy strategy hlegal).Consistent path) :
    strategy.Consistent (G.liftTrapPath path) := by
  intro n howner
  have hprefix :
      (G.restrictToTrap player.other region htrap).PrefixLegal
        ((G.restrictToTrap player.other region htrap).prefixOfPath path n) :=
    (G.restrictToTrap player.other region htrap).prefixOfPath_legal hplay n
  have hownerRestricted :
      (G.restrictToTrap player.other region htrap).owner (path n) = player := by
    simpa [liftTrapPath] using howner
  have hownerOriginal :
      G.owner ((path n).1) = player := by
    simpa using hownerRestricted
  have hstepConsistent :
      path (n + 1) =
        (G.restrictToOpponentTrapStrategy strategy hlegal).move n
          ((G.restrictToTrap player.other region htrap).prefixOfPath path n) :=
    hconsistent n hownerRestricted
  apply congrArg Subtype.val at hstepConsistent
  simpa [liftTrapPath, restrictToOpponentTrapStrategy, hprefix,
    hownerRestricted, hownerOriginal] using hstepConsistent

/--
A history-dependent winning strategy restricts to any trap for the opponent of
the strategy player.
-/
theorem restrictToOpponentTrapStrategy_winningFrom
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player.other region}
    {strategy : G.Strategy player}
    {start : (G.restrictToTrap player.other region htrap).Position}
    (hwinning : Strategy.WinningFrom (G := G) strategy start.1) :
    Strategy.WinningFrom
      (G := G.restrictToTrap player.other region htrap)
      (G.restrictToOpponentTrapStrategy strategy hwinning.1)
      start := by
  constructor
  · exact G.restrictToOpponentTrapStrategy_legal
  · intro path hplayFrom hconsistent
    have hliftPlayFrom :
        G.PlayFrom start.1 (G.liftTrapPath path) :=
      G.restrictToTrap_playFrom_lift hplayFrom
    have hliftConsistent :
        strategy.Consistent (G.liftTrapPath path) :=
      G.restrictToOpponentTrapStrategy_consistent_lift
        hplayFrom.2 hconsistent
    have hliftWin :
        G.PlayerWinsPath player (G.liftTrapPath path) :=
      hwinning.2 (G.liftTrapPath path) hliftPlayFrom hliftConsistent
    exact
      (G.restrictToTrap_playerWinsPath_lift_iff path).mpr hliftWin

/--
If an original winning position lies in a trap for the opponent, then the
corresponding restricted position is winning in the trap subgame.
-/
theorem restrictToOpponentTrap_winningRegion
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player.other region}
    {position : G.Position}
    (hposition : position ∈ region)
    (hwinning : position ∈ G.WinningRegion player) :
    (⟨position, hposition⟩ :
      (G.restrictToTrap player.other region htrap).Position) ∈
        (G.restrictToTrap player.other region htrap).WinningRegion player := by
  rcases hwinning with ⟨strategy, hstrategyWinning⟩
  exact
    ⟨G.restrictToOpponentTrapStrategy strategy hstrategyWinning.1,
      G.restrictToOpponentTrapStrategy_winningFrom hstrategyWinning⟩

/--
Restrict a `player` strategy to a trap for `player` by following the original
strategy whenever its next move remains in the trap, and using an arbitrary
restricted legal move otherwise.
-/
noncomputable def restrictStrategyToTrapWithFallback
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player region}
    (strategy : G.Strategy player) :
    (G.restrictToTrap player region htrap).Strategy player where
  move n pref :=
    by
      classical
      let subgame := G.restrictToTrap player region htrap
      let source := subgame.prefixLast pref
      exact
        if hprefix : subgame.PrefixLegal pref then
          if howner : subgame.owner source = player then
            if hmove :
                strategy.move n (G.liftTrapPrefix pref) ∈ region then
              ⟨strategy.move n (G.liftTrapPrefix pref), hmove⟩
            else
              Classical.choose (subgame.step_total source)
          else
            Classical.choose (subgame.step_total source)
        else
          Classical.choose (subgame.step_total source)

theorem restrictStrategyToTrapWithFallback_legal
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player region}
    {strategy : G.Strategy player}
    (hlegal : strategy.Legal) :
    Strategy.Legal
      (G := G.restrictToTrap player region htrap)
      (G.restrictStrategyToTrapWithFallback strategy) := by
  intro n pref hprefix howner
  classical
  let subgame := G.restrictToTrap player region htrap
  let source := subgame.prefixLast pref
  have hownerOriginal :
      G.owner (G.prefixLast (G.liftTrapPrefix pref)) = player := by
    simpa [subgame, source] using howner
  have hownerSourceOriginal :
      G.owner source.1 = player := by
    simpa [subgame, source] using howner
  by_cases hmove : strategy.move n (G.liftTrapPrefix pref) ∈ region
  · change
      subgame.step source
        ((if hp : subgame.PrefixLegal pref then
          if ho : subgame.owner source = player then
            if hm : strategy.move n (G.liftTrapPrefix pref) ∈ region then
              ⟨strategy.move n (G.liftTrapPrefix pref), hm⟩
            else
              Classical.choose (subgame.step_total source)
          else
            Classical.choose (subgame.step_total source)
        else
          Classical.choose (subgame.step_total source)) : subgame.Position)
    simpa [subgame, source, hprefix, hownerSourceOriginal, hmove] using
      hlegal n (G.liftTrapPrefix pref)
        (G.liftTrapPrefix_legal hprefix) hownerOriginal
  · change
      subgame.step source
        ((if hp : subgame.PrefixLegal pref then
          if ho : subgame.owner source = player then
            if hm : strategy.move n (G.liftTrapPrefix pref) ∈ region then
              ⟨strategy.move n (G.liftTrapPrefix pref), hm⟩
            else
              Classical.choose (subgame.step_total source)
          else
            Classical.choose (subgame.step_total source)
        else
          Classical.choose (subgame.step_total source)) : subgame.Position)
    simpa [subgame, source, hprefix, hownerSourceOriginal, hmove] using
      Classical.choose_spec (subgame.step_total source)

theorem restrictStrategyToTrapWithFallback_consistent_lift
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player region}
    {strategy : G.Strategy player}
    {path : Nat -> (G.restrictToTrap player region htrap).Position}
    (hplay :
      (G.restrictToTrap player region htrap).Play path)
    (hconsistent :
      (G.restrictStrategyToTrapWithFallback strategy).Consistent path)
    (hmoveMem :
      ∀ n : Nat,
        G.owner (G.liftTrapPath path n) = player ->
          strategy.move n
            (G.liftTrapPrefix
              ((G.restrictToTrap player region htrap).prefixOfPath path n)) ∈
            region) :
    strategy.Consistent (G.liftTrapPath path) := by
  intro n howner
  classical
  let subgame := G.restrictToTrap player region htrap
  let pref := subgame.prefixOfPath path n
  let source := subgame.prefixLast pref
  have hprefix : subgame.PrefixLegal pref :=
    subgame.prefixOfPath_legal hplay n
  have hownerRestricted : subgame.owner (path n) = player := by
    simpa [liftTrapPath] using howner
  have hownerSource : subgame.owner source = player := by
    simpa [subgame, source, pref, prefixLast_prefixOfPath] using
      hownerRestricted
  have hownerSourceOriginal :
      G.owner source.1 = player := by
    simpa [subgame, source] using hownerSource
  have hstepConsistent :
      path (n + 1) =
        (G.restrictStrategyToTrapWithFallback strategy).move n pref :=
    hconsistent n hownerRestricted
  have hmove :
      strategy.move n (G.liftTrapPrefix pref) ∈ region := by
    simpa [pref] using hmoveMem n howner
  have hownerPath : G.owner (path n).1 = player := by
    simpa [liftTrapPath] using howner
  have hmovePath :
      strategy.move n (G.prefixOfPath (G.liftTrapPath path) n) ∈ region := by
    simpa [pref] using hmove
  apply congrArg Subtype.val at hstepConsistent
  simpa [restrictStrategyToTrapWithFallback, subgame, pref, source,
    hprefix, hownerPath, hownerSourceOriginal, hmove, hmovePath, liftTrapPath] using
    hstepConsistent

/--
If the complement of an opponent attractor is disjoint from the opponent's
winning area, then an original `player`-winning position in that complement is
also winning in the restricted complement subgame.
-/
theorem restrict_compl_opponent_attractor_winningRegion
    {player : ParityPlayer}
    {target : Set G.Position}
    (hattractorNotWinning :
      ∀ {position : G.Position},
        G.Attractor player.other target position ->
          position ∉ G.WinningRegion player)
    {position : G.Position}
    (hremaining :
      position ∈
        {position : G.Position |
          ¬ G.Attractor player.other target position})
    (hwinning : position ∈ G.WinningRegion player) :
    (⟨position, hremaining⟩ :
      (G.restrictToTrap player
        {position : G.Position |
          ¬ G.Attractor player.other target position}
        (G.compl_opponent_attractor_trapFor player target)).Position) ∈
      (G.restrictToTrap player
        {position : G.Position |
          ¬ G.Attractor player.other target position}
        (G.compl_opponent_attractor_trapFor player target)).WinningRegion
        player := by
  let region : Set G.Position :=
    {position : G.Position |
      ¬ G.Attractor player.other target position}
  let htrap : G.TrapFor player region :=
    G.compl_opponent_attractor_trapFor player target
  let subgame := G.restrictToTrap player region htrap
  rcases hwinning with ⟨strategy, hstrategyWinning⟩
  let restricted := G.restrictStrategyToTrapWithFallback
    (region := region) (htrap := htrap) strategy
  refine ⟨restricted, ?_⟩
  constructor
  · exact G.restrictStrategyToTrapWithFallback_legal hstrategyWinning.1
  · intro path hplayFrom hconsistent
    let lifted := G.liftTrapPath path
    have hliftPlayFrom : G.PlayFrom position lifted := by
      simpa [subgame, region, htrap, lifted] using
        G.restrictToTrap_playFrom_lift hplayFrom
    have hprefixStart :
        ∀ n : Nat,
          (G.prefixOfPath lifted n) 0 = position := by
      intro n
      simpa [prefixOfPath, lifted] using hliftPlayFrom.1
    have hplayOriginal : G.Play lifted := hliftPlayFrom.2
    have move_mem_region_of_prefix
        (n : Nat)
        (hprefixConsistent :
          strategy.PrefixConsistent (G.prefixOfPath lifted n))
        (howner : G.owner (lifted n) = player) :
        strategy.move n (G.prefixOfPath lifted n) ∈ region := by
      have hstartWinning :
          Strategy.WinningFrom
            (G := G) strategy ((G.prefixOfPath lifted n) 0) := by
        simpa [hprefixStart n] using hstrategyWinning
      have hmoveWinning :
          strategy.move n (G.prefixOfPath lifted n) ∈
            G.WinningRegion player := by
        exact
          Strategy.move_mem_winningRegion_of_prefixConsistent
            (G := G) (strategy := strategy)
            hstartWinning
            (G.prefixOfPath_legal hplayOriginal n)
            hprefixConsistent
            (by simpa [prefixLast_prefixOfPath] using howner)
      change
        ¬ G.Attractor player.other target
          (strategy.move n (G.prefixOfPath lifted n))
      intro hattractor
      exact (hattractorNotWinning hattractor) hmoveWinning
    have hprefixConsistent :
        ∀ n : Nat,
          strategy.PrefixConsistent (G.prefixOfPath lifted n) := by
      intro n
      induction n with
      | zero =>
          intro i
          exact Fin.elim0 i
      | succ n ih =>
          intro i howner
          cases i using Fin.lastCases with
          | cast i =>
              have hih :=
                ih i (by simpa [prefixOfPath] using howner)
              simpa [prefixOfPath, prefixTake] using hih
          | last =>
            have hownerLast : G.owner (lifted n) = player := by
              simpa [prefixOfPath] using howner
            have hmoveRegion :
                strategy.move n (G.prefixOfPath lifted n) ∈ region :=
              move_mem_region_of_prefix n ih hownerLast
            have hstepN :
                lifted (n + 1) =
                  strategy.move n (G.prefixOfPath lifted n) := by
              have hprefixSub :
                  subgame.PrefixLegal (subgame.prefixOfPath path n) :=
                subgame.prefixOfPath_legal hplayFrom.2 n
              have hownerRestricted : subgame.owner (path n) = player := by
                simpa [subgame, lifted, liftTrapPath] using hownerLast
              have hstepConsistent :
                  path (n + 1) = restricted.move n (subgame.prefixOfPath path n) :=
                hconsistent n hownerRestricted
              apply congrArg Subtype.val at hstepConsistent
              have hownerPath : G.owner (path n).1 = player := by
                simpa [subgame] using hownerRestricted
              have hmoveLifted :
                  strategy.move n
                      (G.liftTrapPrefix (subgame.prefixOfPath path n)) ∈
                    region := by
                simpa [subgame, lifted] using hmoveRegion
              have hmovePath :
                  strategy.move n (G.prefixOfPath (G.liftTrapPath path) n) ∈
                    region := by
                simpa [subgame, lifted] using hmoveRegion
              simpa [restricted, restrictStrategyToTrapWithFallback, subgame,
                hprefixSub, hownerPath, hmoveLifted, hmovePath, lifted,
                prefixOfPath, prefixTake] using hstepConsistent
            simpa [prefixOfPath, prefixTake] using hstepN
    have hliftConsistent : strategy.Consistent lifted := by
      intro n howner
      have hstep :=
        hprefixConsistent (n + 1) ⟨n, by omega⟩
          (by simpa [prefixOfPath] using howner)
      simpa [prefixOfPath, prefixTake] using hstep
    have hliftWin : G.PlayerWinsPath player lifted :=
      hstrategyWinning.2 lifted hliftPlayFrom hliftConsistent
    exact
      (G.restrictToTrap_playerWinsPath_lift_iff
        (trapPlayer := player) (player := player)
        (region := region) (htrap := htrap) path).mpr
        (by simpa [lifted] using hliftWin)

/-- Turn an original path known to remain in the trap into a restricted path. -/
def restrictOriginalPathToTrap
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player region}
    (path : Nat -> G.Position)
    (hmem : ∀ n : Nat, path n ∈ region) :
    Nat -> (G.restrictToTrap player region htrap).Position :=
  fun n => ⟨path n, hmem n⟩

@[simp]
theorem restrictOriginalPathToTrap_apply
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player region}
    (path : Nat -> G.Position)
    (hmem : ∀ n : Nat, path n ∈ region)
    (n : Nat) :
    G.restrictOriginalPathToTrap (htrap := htrap) path hmem n =
      ⟨path n, hmem n⟩ :=
  rfl

@[simp]
theorem liftTrapPath_restrictOriginalPathToTrap
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player region}
    (path : Nat -> G.Position)
    (hmem : ∀ n : Nat, path n ∈ region) :
    G.liftTrapPath
        (G.restrictOriginalPathToTrap (htrap := htrap) path hmem) =
      path := by
  funext n
  rfl

/-- Original plays that stay in the trap restrict to legal plays of the subgame. -/
theorem restrictOriginalPathToTrap_play
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player region}
    {path : Nat -> G.Position}
    (hplay : G.Play path)
    (hmem : ∀ n : Nat, path n ∈ region) :
    (G.restrictToTrap player region htrap).Play
      (G.restrictOriginalPathToTrap (htrap := htrap) path hmem) := by
  intro n
  simpa [restrictOriginalPathToTrap] using hplay n

/--
Lift a positional strategy on a trap subgame to the whole game.  Outside the
trap, the lifted strategy chooses an arbitrary legal successor; those choices do
not matter for starts inside the trap.
-/
noncomputable def liftTrapPositionalStrategy
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player region}
    (strategy :
      (G.restrictToTrap player region htrap).PositionalStrategy player) :
    G.PositionalStrategy player where
  move position :=
    by
      classical
      exact
        if hposition : position ∈ region then
          (strategy.move ⟨position, hposition⟩).1
        else
          Classical.choose (G.step_total position)
  legal := by
    intro position howner
    classical
    by_cases hposition : position ∈ region
    · change
        G.step position
          (if h : position ∈ region then
            (strategy.move ⟨position, h⟩).1
          else
            Classical.choose (G.step_total position))
      simpa [hposition] using
        strategy.legal ⟨position, hposition⟩ howner
    · change
        G.step position
          (if h : position ∈ region then
            (strategy.move ⟨position, h⟩).1
          else
            Classical.choose (G.step_total position))
      simpa [hposition] using
        Classical.choose_spec (G.step_total position)

@[simp]
theorem liftTrapPositionalStrategy_move_inside
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player region}
    (strategy :
      (G.restrictToTrap player region htrap).PositionalStrategy player)
    {position : G.Position}
    (hposition : position ∈ region) :
    (G.liftTrapPositionalStrategy strategy).move position =
      (strategy.move ⟨position, hposition⟩).1 := by
  classical
  simp [liftTrapPositionalStrategy, hposition]

/-- Inside the trap, the lifted strategy's chosen move remains inside. -/
theorem liftTrapPositionalStrategy_move_mem
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player region}
    (strategy :
      (G.restrictToTrap player region htrap).PositionalStrategy player)
    {position : G.Position}
    (hposition : position ∈ region) :
    (G.liftTrapPositionalStrategy strategy).move position ∈ region := by
  rw [G.liftTrapPositionalStrategy_move_inside strategy hposition]
  exact (strategy.move ⟨position, hposition⟩).2

/--
Any play that starts inside the trap and follows the lifted strategy remains
inside the trap forever.
-/
theorem liftTrapPositionalStrategy_consistent_mem
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player region}
    (strategy :
      (G.restrictToTrap player region htrap).PositionalStrategy player)
    {start : G.Position}
    {path : Nat -> G.Position}
    (hstart : path 0 = start)
    (hstartMem : start ∈ region)
    (hplay : G.Play path)
    (hconsistent :
      (G.liftTrapPositionalStrategy strategy).Consistent path) :
    ∀ n : Nat, path n ∈ region := by
  intro n
  induction n with
  | zero =>
      simpa [hstart] using hstartMem
  | succ n ih =>
      by_cases howner : G.owner (path n) = player
      · have hnext :
            path (n + 1) =
              (G.liftTrapPositionalStrategy strategy).move (path n) :=
          hconsistent n howner
        rw [hnext]
        exact G.liftTrapPositionalStrategy_move_mem strategy ih
      · have hownerOther : G.owner (path n) = player.other :=
          ParityPlayer.eq_other_of_ne howner
        exact (htrap (path n) ih).2 hownerOther (path (n + 1)) (hplay n)

/--
Consistency with a lifted trap strategy restricts to consistency with the
original trap strategy.
-/
theorem restrictOriginalPathToTrap_consistent
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player region}
    (strategy :
      (G.restrictToTrap player region htrap).PositionalStrategy player)
    {path : Nat -> G.Position}
    (hmem : ∀ n : Nat, path n ∈ region)
    (hconsistent :
      (G.liftTrapPositionalStrategy strategy).Consistent path) :
    strategy.Consistent
      (G.restrictOriginalPathToTrap (htrap := htrap) path hmem) := by
  intro n howner
  apply Subtype.ext
  exact
    calc
      path (n + 1)
          = (G.liftTrapPositionalStrategy strategy).move (path n) :=
            hconsistent n howner
      _ = (strategy.move ⟨path n, hmem n⟩).1 := by
            rw [G.liftTrapPositionalStrategy_move_inside strategy (hmem n)]

/--
Splice a positional strategy for a trap subgame with a fallback strategy used
outside the trap.  This is the positional-strategy combinator needed by
Zielonka decompositions when a recursive strategy is used inside a trap for
the opponent and an attractor strategy is used outside.
-/
noncomputable def spliceOpponentTrapPositionalStrategy
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player.other region}
    (fallback : G.PositionalStrategy player)
    (inside :
      (G.restrictToTrap player.other region htrap).PositionalStrategy player) :
    G.PositionalStrategy player where
  move position :=
    by
      classical
      exact
        if hposition : position ∈ region then
          (inside.move ⟨position, hposition⟩).1
        else
          fallback.move position
  legal := by
    intro position howner
    classical
    by_cases hposition : position ∈ region
    · change
        G.step position
          (if h : position ∈ region then
            (inside.move ⟨position, h⟩).1
          else
            fallback.move position)
      simpa [hposition] using
        inside.legal ⟨position, hposition⟩ howner
    · change
        G.step position
          (if h : position ∈ region then
            (inside.move ⟨position, h⟩).1
          else
            fallback.move position)
      simpa [hposition] using fallback.legal position howner

@[simp]
theorem spliceOpponentTrapPositionalStrategy_move_inside
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player.other region}
    (fallback : G.PositionalStrategy player)
    (inside :
      (G.restrictToTrap player.other region htrap).PositionalStrategy player)
    {position : G.Position}
    (hposition : position ∈ region) :
    (G.spliceOpponentTrapPositionalStrategy fallback inside).move position =
      (inside.move ⟨position, hposition⟩).1 := by
  classical
  simp [spliceOpponentTrapPositionalStrategy, hposition]

@[simp]
theorem spliceOpponentTrapPositionalStrategy_move_outside
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player.other region}
    (fallback : G.PositionalStrategy player)
    (inside :
      (G.restrictToTrap player.other region htrap).PositionalStrategy player)
    {position : G.Position}
    (hposition : position ∉ region) :
    (G.spliceOpponentTrapPositionalStrategy fallback inside).move position =
      fallback.move position := by
  classical
  simp [spliceOpponentTrapPositionalStrategy, hposition]

/--
If a play remains in the opponent trap, consistency with the spliced strategy
restricts to consistency with the subgame strategy.
-/
theorem spliceOpponentTrapPositionalStrategy_restrict_consistent
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player.other region}
    (fallback : G.PositionalStrategy player)
    (inside :
      (G.restrictToTrap player.other region htrap).PositionalStrategy player)
    {path : Nat -> G.Position}
    (hmem : ∀ n : Nat, path n ∈ region)
    (hconsistent :
      (G.spliceOpponentTrapPositionalStrategy fallback inside).Consistent path) :
    inside.Consistent
      (G.restrictOriginalPathToTrap (htrap := htrap) path hmem) := by
  intro n howner
  apply Subtype.ext
  exact
    calc
      path (n + 1)
          = (G.spliceOpponentTrapPositionalStrategy fallback inside).move
              (path n) :=
            hconsistent n howner
      _ = (inside.move ⟨path n, hmem n⟩).1 := by
            rw [G.spliceOpponentTrapPositionalStrategy_move_inside
              fallback inside (hmem n)]

/--
If a play following a spliced strategy eventually stays in the opponent trap,
then a winning proof for the inside strategy on that tail wins the original
path by prefix-independence.
-/
theorem spliceOpponentTrapPositionalStrategy_wins_of_eventually_in_region
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player.other region}
    (fallback : G.PositionalStrategy player)
    (inside :
      (G.restrictToTrap player.other region htrap).PositionalStrategy player)
    {path : Nat -> G.Position}
    (hplay : G.Play path)
    (hconsistent :
      (G.spliceOpponentTrapPositionalStrategy fallback inside).Consistent path)
    (offset : Nat)
    (hmem : ∀ n : Nat, G.pathTail path offset n ∈ region)
    (hinsideWinning :
      PositionalStrategy.WinningFrom
        (G := G.restrictToTrap player.other region htrap)
        inside
        ⟨path offset, by simpa [pathTail] using hmem 0⟩) :
    G.PlayerWinsPath player path := by
  let tail := G.pathTail path offset
  let restrictedTail :=
    G.restrictOriginalPathToTrap (htrap := htrap) tail hmem
  have htailPlay : G.Play tail := by
    simpa [tail] using G.play_pathTail hplay offset
  have htailPlayFrom :
      (G.restrictToTrap player.other region htrap).PlayFrom
        ⟨path offset, by simpa [tail, pathTail] using hmem 0⟩
        restrictedTail := by
    constructor
    · apply Subtype.ext
      simp [restrictedTail, restrictOriginalPathToTrap, tail, pathTail]
    · exact G.restrictOriginalPathToTrap_play htailPlay hmem
  have htailConsistentSpliced :
      (G.spliceOpponentTrapPositionalStrategy fallback inside).Consistent
        tail := by
    intro n hownerTail
    have hownerOriginal :
        G.owner (path (offset + n)) = player := by
      simpa [tail, pathTail] using hownerTail
    have hindex : offset + (n + 1) = (offset + n) + 1 := by
      omega
    calc
      tail (n + 1)
          = path (offset + (n + 1)) := rfl
      _ = path ((offset + n) + 1) := by
            rw [hindex]
      _ = (G.spliceOpponentTrapPositionalStrategy fallback inside).move
            (path (offset + n)) :=
            hconsistent (offset + n) hownerOriginal
      _ = (G.spliceOpponentTrapPositionalStrategy fallback inside).move
            (tail n) := by
            rfl
  have hrestrictedConsistent :
      inside.Consistent restrictedTail := by
    simpa [restrictedTail, tail] using
      G.spliceOpponentTrapPositionalStrategy_restrict_consistent
        fallback inside hmem htailConsistentSpliced
  have hrestrictedWin :
      (G.restrictToTrap player.other region htrap).PlayerWinsPath
        player restrictedTail :=
    hinsideWinning restrictedTail htailPlayFrom hrestrictedConsistent
  have htailWin : G.PlayerWinsPath player tail := by
    have hliftWin :
        G.PlayerWinsPath player (G.liftTrapPath restrictedTail) :=
      ((G.restrictToTrap_playerWinsPath_lift_iff restrictedTail).mp
        hrestrictedWin)
    simpa [restrictedTail, tail] using hliftWin
  exact
    (G.playerWinsPath_pathTail_iff player path offset).mp htailWin

/--
Splice an outside strategy with a strategy for the opponent inside a trap for
`player`.  This is the dual splice needed in the second Zielonka case: while
the play remains in the remaining `player`-trap, use the recursive opponent
strategy; after leaving, use the outside opponent strategy.
-/
noncomputable def spliceTrapForOpponentPositionalStrategy
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player region}
    (outside : G.PositionalStrategy player.other)
    (inside :
      (G.restrictToTrap player region htrap).PositionalStrategy player.other) :
    G.PositionalStrategy player.other where
  move position :=
    by
      classical
      exact
        if hposition : position ∈ region then
          (inside.move ⟨position, hposition⟩).1
        else
          outside.move position
  legal := by
    intro position howner
    classical
    by_cases hposition : position ∈ region
    · change
        G.step position
          (if h : position ∈ region then
            (inside.move ⟨position, h⟩).1
          else
            outside.move position)
      simpa [hposition] using
        inside.legal ⟨position, hposition⟩ howner
    · change
        G.step position
          (if h : position ∈ region then
            (inside.move ⟨position, h⟩).1
          else
            outside.move position)
      simpa [hposition] using outside.legal position howner

@[simp]
theorem spliceTrapForOpponentPositionalStrategy_move_inside
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player region}
    (outside : G.PositionalStrategy player.other)
    (inside :
      (G.restrictToTrap player region htrap).PositionalStrategy player.other)
    {position : G.Position}
    (hposition : position ∈ region) :
    (G.spliceTrapForOpponentPositionalStrategy outside inside).move position =
      (inside.move ⟨position, hposition⟩).1 := by
  classical
  simp [spliceTrapForOpponentPositionalStrategy, hposition]

@[simp]
theorem spliceTrapForOpponentPositionalStrategy_move_outside
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player region}
    (outside : G.PositionalStrategy player.other)
    (inside :
      (G.restrictToTrap player region htrap).PositionalStrategy player.other)
    {position : G.Position}
    (hposition : position ∉ region) :
    (G.spliceTrapForOpponentPositionalStrategy outside inside).move position =
      outside.move position := by
  classical
  simp [spliceTrapForOpponentPositionalStrategy, hposition]

theorem spliceTrapForOpponentPositionalStrategy_restrict_consistent
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player region}
    (outside : G.PositionalStrategy player.other)
    (inside :
      (G.restrictToTrap player region htrap).PositionalStrategy player.other)
    {path : Nat -> G.Position}
    (hmem : ∀ n : Nat, path n ∈ region)
    (hconsistent :
      (G.spliceTrapForOpponentPositionalStrategy outside inside).Consistent
        path) :
    inside.Consistent
      (G.restrictOriginalPathToTrap (htrap := htrap) path hmem) := by
  intro n howner
  apply Subtype.ext
  exact
    calc
      path (n + 1)
          = (G.spliceTrapForOpponentPositionalStrategy outside inside).move
              (path n) :=
            hconsistent n howner
      _ = (inside.move ⟨path n, hmem n⟩).1 := by
            rw [G.spliceTrapForOpponentPositionalStrategy_move_inside
              outside inside (hmem n)]

theorem spliceTrapForOpponentPositionalStrategy_wins_of_always_in_region
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player region}
    (outside : G.PositionalStrategy player.other)
    (inside :
      (G.restrictToTrap player region htrap).PositionalStrategy player.other)
    {path : Nat -> G.Position}
    (hplay : G.Play path)
    (hconsistent :
      (G.spliceTrapForOpponentPositionalStrategy outside inside).Consistent
        path)
    (hmem : ∀ n : Nat, path n ∈ region)
    (hinsideWinning :
      PositionalStrategy.WinningFrom
        (G := G.restrictToTrap player region htrap)
        inside
        ⟨path 0, hmem 0⟩) :
    G.PlayerWinsPath player.other path := by
  let restricted :=
    G.restrictOriginalPathToTrap (htrap := htrap) path hmem
  have hrestrictedPlayFrom :
      (G.restrictToTrap player region htrap).PlayFrom
        ⟨path 0, hmem 0⟩ restricted := by
    constructor
    · apply Subtype.ext
      simp [restricted, restrictOriginalPathToTrap]
    · exact G.restrictOriginalPathToTrap_play hplay hmem
  have hrestrictedConsistent :
      inside.Consistent restricted := by
    simpa [restricted] using
      G.spliceTrapForOpponentPositionalStrategy_restrict_consistent
        outside inside hmem hconsistent
  have hrestrictedWin :
      (G.restrictToTrap player region htrap).PlayerWinsPath
        player.other restricted :=
    hinsideWinning restricted hrestrictedPlayFrom hrestrictedConsistent
  have hliftWin :
      G.PlayerWinsPath player.other (G.liftTrapPath restricted) :=
    ((G.restrictToTrap_playerWinsPath_lift_iff restricted).mp
      hrestrictedWin)
  simpa [restricted] using hliftWin

/--
If the outside of a `player`-trap is invariant for an outside opponent
strategy, then the dual splice wins whenever the play either stays in the trap
or eventually exits to the outside.
-/
theorem spliceTrapForOpponentPositionalStrategy_wins
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player region}
    (outside : G.PositionalStrategy player.other)
    (inside :
      (G.restrictToTrap player region htrap).PositionalStrategy player.other)
    (hinsideWinning :
      ∀ position : G.Position,
        ∀ hposition : position ∈ region,
          PositionalStrategy.WinningFrom
            (G := G.restrictToTrap player region htrap)
            inside ⟨position, hposition⟩)
    (houtsideWinning :
      ∀ position : G.Position,
        position ∉ region ->
          PositionalStrategy.WinningFrom (G := G) outside position)
    (houtsideMoveMem :
      ∀ position : G.Position,
        position ∉ region ->
          G.owner position = player.other ->
            outside.move position ∉ region)
    (houtsideOpponentMem :
      ∀ position : G.Position,
        position ∉ region ->
          G.owner position = player ->
            ∀ next : G.Position, G.step position next -> next ∉ region)
    {path : Nat -> G.Position}
    (hplay : G.Play path)
    (hconsistent :
      (G.spliceTrapForOpponentPositionalStrategy outside inside).Consistent
        path) :
    G.PlayerWinsPath player.other path := by
  classical
  by_cases hstay : ∀ n : Nat, path n ∈ region
  · exact
      G.spliceTrapForOpponentPositionalStrategy_wins_of_always_in_region
        outside inside hplay hconsistent hstay
        (hinsideWinning (path 0) (hstay 0))
  · have hexit : ∃ n : Nat, path n ∉ region := by
      push Not at hstay
      exact hstay
    let offset := Nat.find hexit
    have hoffset : path offset ∉ region := Nat.find_spec hexit
    have htailOutside :
        ∀ n : Nat, G.pathTail path offset n ∉ region := by
      intro n
      induction n with
      | zero =>
          simpa [pathTail] using hoffset
      | succ n ih =>
          by_cases howner : G.owner (G.pathTail path offset n) = player.other
          · have hownerOriginal :
                G.owner (path (offset + n)) = player.other := by
              simpa [pathTail] using howner
            have hnext :
                path ((offset + n) + 1) =
                  (G.spliceTrapForOpponentPositionalStrategy outside inside).move
                    (path (offset + n)) :=
              hconsistent (offset + n) hownerOriginal
            have houtsideNext :
                outside.move (path (offset + n)) ∉ region :=
              houtsideMoveMem (path (offset + n))
                (by simpa [pathTail] using ih) hownerOriginal
            have hindex : offset + (n + 1) = (offset + n) + 1 := by
              omega
            simpa [pathTail, hindex, hnext,
              G.spliceTrapForOpponentPositionalStrategy_move_outside
                outside inside (by simpa [pathTail] using ih)] using
              houtsideNext
          · have hownerPlayer :
                G.owner (G.pathTail path offset n) = player := by
              simpa using ParityPlayer.eq_other_of_ne howner
            have hownerOriginal :
                G.owner (path (offset + n)) = player := by
              simpa [pathTail] using hownerPlayer
            have hstep :
                G.step (path (offset + n)) (path ((offset + n) + 1)) :=
              hplay (offset + n)
            have hindex : offset + (n + 1) = (offset + n) + 1 := by
              omega
            have houtsideNext :
                path ((offset + n) + 1) ∉ region :=
              houtsideOpponentMem (path (offset + n))
                (by simpa [pathTail] using ih)
                hownerOriginal (path ((offset + n) + 1)) hstep
            simpa [pathTail, hindex] using houtsideNext
    have htailConsistent :
        outside.Consistent (G.pathTail path offset) := by
      intro n hownerTail
      have hownerOriginal :
          G.owner (path (offset + n)) = player.other := by
        simpa [pathTail] using hownerTail
      have hnext :
          path ((offset + n) + 1) =
            (G.spliceTrapForOpponentPositionalStrategy outside inside).move
              (path (offset + n)) :=
        hconsistent (offset + n) hownerOriginal
      have hindex : offset + (n + 1) = (offset + n) + 1 := by
        omega
      calc
        G.pathTail path offset (n + 1)
            = path ((offset + n) + 1) := by
              simp [pathTail, hindex]
        _ = (G.spliceTrapForOpponentPositionalStrategy outside inside).move
              (path (offset + n)) := hnext
        _ = outside.move (path (offset + n)) := by
              rw [G.spliceTrapForOpponentPositionalStrategy_move_outside
                outside inside (by simpa [pathTail] using htailOutside n)]
        _ = outside.move (G.pathTail path offset n) := by
              rfl
    have htailPlayFrom :
        G.PlayFrom (path offset) (G.pathTail path offset) :=
      G.playFrom_pathTail hplay offset
    have htailWin :
        G.PlayerWinsPath player.other (G.pathTail path offset) :=
      houtsideWinning (path offset) hoffset
        (G.pathTail path offset) htailPlayFrom htailConsistent
    exact
      (G.playerWinsPath_pathTail_iff player.other path offset).mp htailWin

/--
Start-local dual splice.  Unlike
`spliceTrapForOpponentPositionalStrategy_wins`, the inside strategy only has to
win from the given start if that start is in the trap.  This is the form needed
for the second Zielonka branch, where the recursive opponent strategy wins only
on the opponent's recursive winning region inside the remaining trap.
-/
theorem spliceTrapForOpponentPositionalStrategy_winningFrom
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player region}
    (outside : G.PositionalStrategy player.other)
    (inside :
      (G.restrictToTrap player region htrap).PositionalStrategy player.other)
    {start : G.Position}
    (hinsideWinning :
      ∀ hstart : start ∈ region,
        PositionalStrategy.WinningFrom
          (G := G.restrictToTrap player region htrap)
          inside ⟨start, hstart⟩)
    (houtsideWinning :
      ∀ position : G.Position,
        position ∉ region ->
          PositionalStrategy.WinningFrom (G := G) outside position)
    (houtsideMoveMem :
      ∀ position : G.Position,
        position ∉ region ->
          G.owner position = player.other ->
            outside.move position ∉ region)
    (houtsideOpponentMem :
      ∀ position : G.Position,
        position ∉ region ->
          G.owner position = player ->
            ∀ next : G.Position, G.step position next -> next ∉ region) :
    PositionalStrategy.WinningFrom
      (G := G)
      (G.spliceTrapForOpponentPositionalStrategy outside inside)
      start := by
  classical
  intro path hplayFrom hconsistent
  rcases hplayFrom with ⟨hpath0, hplay⟩
  subst start
  by_cases hstay : ∀ n : Nat, path n ∈ region
  · exact
      G.spliceTrapForOpponentPositionalStrategy_wins_of_always_in_region
        outside inside hplay hconsistent hstay
        (hinsideWinning (hstay 0))
  · have hexit : ∃ n : Nat, path n ∉ region := by
      push Not at hstay
      exact hstay
    let offset := Nat.find hexit
    have hoffset : path offset ∉ region := Nat.find_spec hexit
    have htailOutside :
        ∀ n : Nat, G.pathTail path offset n ∉ region := by
      intro n
      induction n with
      | zero =>
          simpa [pathTail] using hoffset
      | succ n ih =>
          by_cases howner : G.owner (G.pathTail path offset n) = player.other
          · have hownerOriginal :
                G.owner (path (offset + n)) = player.other := by
              simpa [pathTail] using howner
            have hnext :
                path ((offset + n) + 1) =
                  (G.spliceTrapForOpponentPositionalStrategy outside inside).move
                    (path (offset + n)) :=
              hconsistent (offset + n) hownerOriginal
            have houtsideNext :
                outside.move (path (offset + n)) ∉ region :=
              houtsideMoveMem (path (offset + n))
                (by simpa [pathTail] using ih) hownerOriginal
            have hindex : offset + (n + 1) = (offset + n) + 1 := by
              omega
            simpa [pathTail, hindex, hnext,
              G.spliceTrapForOpponentPositionalStrategy_move_outside
                outside inside (by simpa [pathTail] using ih)] using
              houtsideNext
          · have hownerPlayer :
                G.owner (G.pathTail path offset n) = player := by
              simpa using ParityPlayer.eq_other_of_ne howner
            have hownerOriginal :
                G.owner (path (offset + n)) = player := by
              simpa [pathTail] using hownerPlayer
            have hstep :
                G.step (path (offset + n)) (path ((offset + n) + 1)) :=
              hplay (offset + n)
            have hindex : offset + (n + 1) = (offset + n) + 1 := by
              omega
            have houtsideNext :
                path ((offset + n) + 1) ∉ region :=
              houtsideOpponentMem (path (offset + n))
                (by simpa [pathTail] using ih)
                hownerOriginal (path ((offset + n) + 1)) hstep
            simpa [pathTail, hindex] using houtsideNext
    have htailConsistent :
        outside.Consistent (G.pathTail path offset) := by
      intro n hownerTail
      have hownerOriginal :
          G.owner (path (offset + n)) = player.other := by
        simpa [pathTail] using hownerTail
      have hnext :
          path ((offset + n) + 1) =
            (G.spliceTrapForOpponentPositionalStrategy outside inside).move
              (path (offset + n)) :=
        hconsistent (offset + n) hownerOriginal
      have hindex : offset + (n + 1) = (offset + n) + 1 := by
        omega
      calc
        G.pathTail path offset (n + 1)
            = path ((offset + n) + 1) := by
              simp [pathTail, hindex]
        _ = (G.spliceTrapForOpponentPositionalStrategy outside inside).move
              (path (offset + n)) := hnext
        _ = outside.move (path (offset + n)) := by
              rw [G.spliceTrapForOpponentPositionalStrategy_move_outside
                outside inside (by simpa [pathTail] using htailOutside n)]
        _ = outside.move (G.pathTail path offset n) := by
              rfl
    have htailPlayFrom :
        G.PlayFrom (path offset) (G.pathTail path offset) :=
      G.playFrom_pathTail hplay offset
    have htailWin :
        G.PlayerWinsPath player.other (G.pathTail path offset) :=
      houtsideWinning (path offset) hoffset
        (G.pathTail path offset) htailPlayFrom htailConsistent
    exact
      (G.playerWinsPath_pathTail_iff player.other path offset).mp htailWin

/--
If the remaining core is defined as the complement of the opponent's original
positional winning region, then an opponent positional win inside that core
lifts back to an original opponent positional win by splicing with the uniform
outside strategy on the already-winning complement.
-/
theorem lift_coreOpponentPositionalWinningRegion
    {player : ParityPlayer}
    {core : Set G.Position}
    {hcoreTrap : G.TrapFor player core}
    (hcoreDef :
      core = {position : G.Position |
        position ∉ G.PositionalWinningRegion player.other})
    {start : G.Position}
    (hstart : start ∈ core)
    (hsubWinning :
      (⟨start, hstart⟩ :
        (G.restrictToTrap player core hcoreTrap).Position) ∈
          (G.restrictToTrap player core hcoreTrap).PositionalWinningRegion
            player.other) :
    start ∈ G.PositionalWinningRegion player.other := by
  classical
  rcases hsubWinning with ⟨inside, hinsideWinning⟩
  rcases G.exists_strategy_winningOn_positionalWinningRegion player.other with
    ⟨outside, houtsideWinningOn⟩
  let strategy : G.PositionalStrategy player.other :=
    G.spliceTrapForOpponentPositionalStrategy
      (player := player) (region := core) (htrap := hcoreTrap)
      outside inside
  refine ⟨strategy, ?_⟩
  simpa [strategy] using
    G.spliceTrapForOpponentPositionalStrategy_winningFrom
      (player := player) (region := core) (htrap := hcoreTrap)
      outside inside
      (start := start)
      (by
        intro hstartCore
        simpa using hinsideWinning)
      (by
        intro position hnotCore
        have hposition :
            position ∈ G.PositionalWinningRegion player.other := by
          simpa [hcoreDef] using hnotCore
        exact houtsideWinningOn position hposition)
      (by
        intro position hnotCore howner
        have hposition :
            position ∈ G.PositionalWinningRegion player.other := by
          simpa [hcoreDef] using hnotCore
        have hmove :
            outside.move position ∈
              G.PositionalWinningRegion player.other :=
          G.positionalWinningRegion_move_mem_of_winningOn
            outside houtsideWinningOn hposition howner
        simpa [hcoreDef] using hmove)
      (by
        intro position hnotCore howner next hstep
        have hposition :
            position ∈ G.PositionalWinningRegion player.other := by
          simpa [hcoreDef] using hnotCore
        have hnext :
            next ∈ G.PositionalWinningRegion player.other :=
          ((G.positionalWinningRegion_trapFor player.other)
            position hposition).2 (by simpa using howner) next hstep
        simpa [hcoreDef] using hnext)

/--
For the Zielonka splice using an attractor outside the recursive trap, every
prefix before the first target visit remains inside the attractor.
-/
theorem spliceAttractor_prefix_attractor
    {player : ParityPlayer}
    {target : Set G.Position}
    (inside :
      (G.restrictToTrap player.other
        {position : G.Position | ¬ G.Attractor player target position}
        (G.compl_attractor_trapFor_other player target)).PositionalStrategy
          player)
    {start : G.Position}
    {path : Nat -> G.Position}
    (hstart : G.Attractor player target start)
    (hplayFrom : G.PlayFrom start path)
    (hconsistent :
      (G.spliceOpponentTrapPositionalStrategy
        (G.attractorStrategy player target) inside).Consistent path) :
    ∀ n : Nat,
      (∀ k : Nat, k ≤ n -> path k ∉ target) ->
        G.Attractor player target (path n) := by
  rcases hplayFrom with ⟨hpath0, hplay⟩
  intro n
  induction n with
  | zero =>
      intro _hnotTarget
      simpa [hpath0] using hstart
  | succ n ih =>
      intro hnotTarget
      have hnotTargetPrefix :
          ∀ k : Nat, k ≤ n -> path k ∉ target := by
        intro k hk
        exact hnotTarget k (by omega)
      have hattractorN :
          G.Attractor player target (path n) :=
        ih hnotTargetPrefix
      have hnotTargetN : path n ∉ target :=
        hnotTarget n (by omega)
      by_cases howner : G.owner (path n) = player
      · have hnext :
            path (n + 1) =
              (G.spliceOpponentTrapPositionalStrategy
                (G.attractorStrategy player target) inside).move (path n) :=
          hconsistent n howner
        have hnotRegion :
            path n ∉
              {position : G.Position | ¬ G.Attractor player target position} := by
          intro hnotAttractor
          exact hnotAttractor hattractorN
        have hprogress :=
          G.attractorStrategy_move_progress
            hattractorN hnotTargetN howner
        rw [hnext]
        rw [G.spliceOpponentTrapPositionalStrategy_move_outside
          (G.attractorStrategy player target) inside hnotRegion]
        exact hprogress.2.1
      · have hownerOther : G.owner (path n) = player.other :=
          ParityPlayer.eq_other_of_ne howner
        have hprogress :=
          (G.attractorRank player target).opponent_progress
            (path n) hattractorN hnotTargetN hownerOther
            (path (n + 1)) (hplay n)
        exact hprogress.1

/--
The same splice follows the attractor strategy, in the local sense needed by
`attractorStrategy_reaches_target_until`.
-/
theorem spliceAttractor_consistentUntil
    {player : ParityPlayer}
    {target : Set G.Position}
    (inside :
      (G.restrictToTrap player.other
        {position : G.Position | ¬ G.Attractor player target position}
        (G.compl_attractor_trapFor_other player target)).PositionalStrategy
          player)
    {start : G.Position}
    {path : Nat -> G.Position}
    (hstart : G.Attractor player target start)
    (hplayFrom : G.PlayFrom start path)
    (hconsistent :
      (G.spliceOpponentTrapPositionalStrategy
        (G.attractorStrategy player target) inside).Consistent path) :
    (G.attractorStrategy player target).ConsistentUntil target path := by
  intro n hnotTarget howner
  have hattractorN :
      G.Attractor player target (path n) :=
    G.spliceAttractor_prefix_attractor inside hstart hplayFrom
      hconsistent n hnotTarget
  have hnotRegion :
      path n ∉
        {position : G.Position | ¬ G.Attractor player target position} := by
    intro hnotAttractor
    exact hnotAttractor hattractorN
  calc
    path (n + 1)
        = (G.spliceOpponentTrapPositionalStrategy
            (G.attractorStrategy player target) inside).move (path n) :=
          hconsistent n howner
    _ = (G.attractorStrategy player target).move (path n) := by
          rw [G.spliceOpponentTrapPositionalStrategy_move_outside
            (G.attractorStrategy player target) inside hnotRegion]

/--
Consequently, any play following the Zielonka attractor/trap splice from an
attracted start reaches the attractor target in finite time.
-/
theorem spliceAttractor_reaches_target
    {player : ParityPlayer}
    {target : Set G.Position}
    (inside :
      (G.restrictToTrap player.other
        {position : G.Position | ¬ G.Attractor player target position}
        (G.compl_attractor_trapFor_other player target)).PositionalStrategy
          player)
    {start : G.Position}
    {path : Nat -> G.Position}
    (hstart : G.Attractor player target start)
    (hplayFrom : G.PlayFrom start path)
    (hconsistent :
      (G.spliceOpponentTrapPositionalStrategy
        (G.attractorStrategy player target) inside).Consistent path) :
    ∃ n : Nat, path n ∈ target := by
  exact
    G.attractorStrategy_reaches_target_until hstart hplayFrom
      (G.spliceAttractor_consistentUntil inside hstart hplayFrom hconsistent)

/--
Favourable-minimum Zielonka splice.  If `priority` is below every arena
priority and is won by `player`, then a strategy that attracts to that priority
outside the complement trap and uses a recursively winning strategy inside the
trap wins from every start.
-/
theorem spliceAttractor_winningFrom_of_inside_winningOn
    {player : ParityPlayer}
    {priority : Nat}
    (hpriorityLeast :
      ∀ position : G.Position, priority ≤ G.priority position)
    (hpriorityOwner : priorityOwner priority = player)
    (inside :
      (G.restrictToTrap player.other
        {position : G.Position |
          ¬ G.Attractor player (G.priorityClass priority) position}
        (G.compl_attractor_trapFor_other player
          (G.priorityClass priority))).PositionalStrategy player)
    (hinsideWinning :
      ∀ (position : G.Position),
        ∀ hposition :
          position ∈
            {position : G.Position |
              ¬ G.Attractor player (G.priorityClass priority) position},
          PositionalStrategy.WinningFrom
            (G := G.restrictToTrap player.other
              {position : G.Position |
                ¬ G.Attractor player (G.priorityClass priority) position}
              (G.compl_attractor_trapFor_other player
                (G.priorityClass priority)))
            inside
            ⟨position, hposition⟩) :
    ∀ start : G.Position,
      PositionalStrategy.WinningFrom
        (G := G)
        (G.spliceOpponentTrapPositionalStrategy
          (G.attractorStrategy player (G.priorityClass priority)) inside)
        start := by
  intro start path hplayFrom hconsistent
  rcases hplayFrom with ⟨_hpath0, hplay⟩
  by_cases hseen : G.PrioritySeenInfinitelyOften path priority
  · have hmin :
        ∀ q : Nat, G.PrioritySeenInfinitelyOften path q -> priority ≤ q := by
      intro q hqSeen
      rcases G.prioritySeenInfinitelyOften_mem_range hqSeen with
        ⟨position, hposition⟩
      simpa [← hposition] using hpriorityLeast position
    have hwinOwner :
        G.PlayerWinsPath (priorityOwner priority) path :=
      G.playerWinsPath_priorityOwner_of_min_seen hseen hmin
    simpa [hpriorityOwner] using hwinOwner
  · rcases
        (G.not_prioritySeenInfinitelyOften_iff_eventually_not
          path priority).mp hseen with
      ⟨offset, hoffset⟩
    let region : Set G.Position :=
      {position : G.Position |
        ¬ G.Attractor player (G.priorityClass priority) position}
    let fallback := G.attractorStrategy player (G.priorityClass priority)
    let spliced :=
      G.spliceOpponentTrapPositionalStrategy fallback inside
    have hmemTail :
        ∀ n : Nat, G.pathTail path offset n ∈ region := by
      intro n
      change
        ¬ G.Attractor player (G.priorityClass priority)
          (G.pathTail path offset n)
      intro hattractor
      let cut := offset + n
      have hattractorCut :
          G.Attractor player (G.priorityClass priority) (path cut) := by
        simpa [cut, pathTail] using hattractor
      have htailPlayFrom :
          G.PlayFrom (path cut) (G.pathTail path cut) :=
        G.playFrom_pathTail hplay cut
      have htailConsistent :
          spliced.Consistent (G.pathTail path cut) := by
        simpa [spliced, fallback] using
          PositionalStrategy.consistent_pathTail
            (G := G)
            (strategy :=
              G.spliceOpponentTrapPositionalStrategy
                (G.attractorStrategy player (G.priorityClass priority))
                inside)
            hconsistent cut
      rcases
          G.spliceAttractor_reaches_target inside
            hattractorCut htailPlayFrom htailConsistent with
        ⟨m, hm⟩
      have hpriorityAt :
          G.priority (path (cut + m)) = priority := by
        simpa [pathTail, priorityClass] using hm
      exact hoffset (cut + m) (by omega) hpriorityAt
    have hinsideStartWinning :
        PositionalStrategy.WinningFrom
          (G := G.restrictToTrap player.other region
            (G.compl_attractor_trapFor_other player
              (G.priorityClass priority)))
          inside
          ⟨path offset, by simpa [region, pathTail] using hmemTail 0⟩ := by
      exact hinsideWinning (path offset)
        (by simpa [region, pathTail] using hmemTail 0)
    simpa [region, fallback, spliced] using
      G.spliceOpponentTrapPositionalStrategy_wins_of_eventually_in_region
        (G.attractorStrategy player (G.priorityClass priority))
        inside hplay hconsistent offset
        (by
          intro n
          simpa [region] using hmemTail n)
        hinsideStartWinning

/--
A positional strategy that wins in a trap subgame wins in the original game
from the corresponding original start position.
-/
theorem liftTrapPositionalStrategy_winningFrom
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player region}
    (strategy :
      (G.restrictToTrap player region htrap).PositionalStrategy player)
    {start : (G.restrictToTrap player region htrap).Position}
    (hwinning :
      PositionalStrategy.WinningFrom
        (G := G.restrictToTrap player region htrap) strategy start) :
    PositionalStrategy.WinningFrom
      (G := G) (G.liftTrapPositionalStrategy strategy) start.1 := by
  intro path hplayFrom hconsistent
  rcases hplayFrom with ⟨hstart, hplay⟩
  let hmem : ∀ n : Nat, path n ∈ region :=
    G.liftTrapPositionalStrategy_consistent_mem
      strategy hstart start.2 hplay hconsistent
  let restrictedPath :=
    G.restrictOriginalPathToTrap (htrap := htrap) path hmem
  have hrestrictedPlay :
      (G.restrictToTrap player region htrap).PlayFrom
        start restrictedPath := by
    constructor
    · apply Subtype.ext
      simpa [restrictedPath, restrictOriginalPathToTrap] using hstart
    · exact G.restrictOriginalPathToTrap_play hplay hmem
  have hrestrictedConsistent :
      strategy.Consistent restrictedPath := by
    simpa [restrictedPath] using
      G.restrictOriginalPathToTrap_consistent strategy hmem hconsistent
  have hrestrictedWin :
      (G.restrictToTrap player region htrap).PlayerWinsPath
        player restrictedPath :=
    hwinning restrictedPath hrestrictedPlay hrestrictedConsistent
  have hliftWin :
      G.PlayerWinsPath player (G.liftTrapPath restrictedPath) :=
    ((G.restrictToTrap_playerWinsPath_lift_iff restrictedPath).mp
      hrestrictedWin)
  simpa [restrictedPath] using hliftWin

/--
Restricted positional winning regions lift back to original positional winning
regions for starts inside the trap.
-/
theorem liftTrap_positionalWinningRegion
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player region}
    {start : (G.restrictToTrap player region htrap).Position}
    (hstart :
      start ∈
        (G.restrictToTrap player region htrap).PositionalWinningRegion player) :
    start.1 ∈ G.PositionalWinningRegion player := by
  rcases hstart with ⟨strategy, hwinning⟩
  exact
    ⟨G.liftTrapPositionalStrategy strategy,
      G.liftTrapPositionalStrategy_winningFrom strategy hwinning⟩

/--
The preceding lifting lemma in a form indexed by an original position and its
membership proof in the trap.
-/
theorem liftTrap_positionalWinningRegion_of_mem
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player region}
    {position : G.Position}
    (hposition : position ∈ region)
    (hstart :
      (⟨position, hposition⟩ :
        (G.restrictToTrap player region htrap).Position) ∈
          (G.restrictToTrap player region htrap).PositionalWinningRegion player) :
    position ∈ G.PositionalWinningRegion player :=
  G.liftTrap_positionalWinningRegion hstart

/--
Original positions corresponding to a player's history-dependent winning region
inside a trap subgame.
-/
def liftedTrapWinningRegion
    {trapPlayer : ParityPlayer}
    (region : Set G.Position)
    (htrap : G.TrapFor trapPlayer region)
    (player : ParityPlayer) :
    Set G.Position :=
  {position |
    ∃ hposition : position ∈ region,
      (⟨position, hposition⟩ :
        (G.restrictToTrap trapPlayer region htrap).Position) ∈
          (G.restrictToTrap trapPlayer region htrap).WinningRegion player}

theorem mem_liftedTrapWinningRegion_iff
    {trapPlayer player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor trapPlayer region}
    {position : G.Position} :
    position ∈ G.liftedTrapWinningRegion region htrap player ↔
      ∃ hposition : position ∈ region,
        (⟨position, hposition⟩ :
          (G.restrictToTrap trapPlayer region htrap).Position) ∈
            (G.restrictToTrap trapPlayer region htrap).WinningRegion player := by
  rfl

/--
A positional strategy that wins on the trap subgame winning region lifts to a
strategy that wins on the corresponding original target set.
-/
theorem liftTrapPositionalStrategy_winningOn_liftedWinningRegion
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player region}
    (strategy :
      (G.restrictToTrap player region htrap).PositionalStrategy player)
    (hwinningOn :
      PositionalStrategy.WinningOn
        (G := G.restrictToTrap player region htrap)
        strategy
        ((G.restrictToTrap player region htrap).WinningRegion player)) :
    PositionalStrategy.WinningOn
      (G := G)
      (G.liftTrapPositionalStrategy strategy)
      (G.liftedTrapWinningRegion region htrap player) := by
  intro position hposition
  rcases hposition with ⟨hmem, hwinRegion⟩
  exact
    G.liftTrapPositionalStrategy_winningFrom strategy
      (hwinningOn ⟨position, hmem⟩ hwinRegion)

/--
Inside a lifted subgame winning region, the lifted positional strategy keeps
player-owned moves in that lifted winning region.
-/
theorem liftTrapPositionalStrategy_liftedWinningRegion_move_mem
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player region}
    (strategy :
      (G.restrictToTrap player region htrap).PositionalStrategy player)
    (hwinningOn :
      PositionalStrategy.WinningOn
        (G := G.restrictToTrap player region htrap)
        strategy
        ((G.restrictToTrap player region htrap).WinningRegion player))
    {position : G.Position}
    (hposition :
      position ∈ G.liftedTrapWinningRegion region htrap player)
    (howner : G.owner position = player) :
    (G.liftTrapPositionalStrategy strategy).move position ∈
      G.liftedTrapWinningRegion region htrap player := by
  rcases hposition with ⟨hmem, hwinRegion⟩
  have hwinning :
      PositionalStrategy.WinningFrom
        (G := G.restrictToTrap player region htrap)
        strategy ⟨position, hmem⟩ :=
    hwinningOn ⟨position, hmem⟩ hwinRegion
  have hstep :
      (G.restrictToTrap player region htrap).step
        ⟨position, hmem⟩
        (strategy.move ⟨position, hmem⟩) :=
    strategy.legal ⟨position, hmem⟩ howner
  have hsuccessorWinning :
      PositionalStrategy.WinningFrom
        (G := G.restrictToTrap player region htrap)
        strategy (strategy.move ⟨position, hmem⟩) :=
    PositionalStrategy.winningFrom_successor
      (G := G.restrictToTrap player region htrap)
      (strategy := strategy)
      hwinning hstep (by intro _; rfl)
  have hsuccessorRegion :
      (strategy.move ⟨position, hmem⟩) ∈
        (G.restrictToTrap player region htrap).WinningRegion player := by
    exact
      (G.restrictToTrap player region htrap).positionalWinningRegion_subset_winningRegion
        player
        ⟨strategy, hsuccessorWinning⟩
  have hmoveEq :
      (G.liftTrapPositionalStrategy strategy).move position =
        (strategy.move ⟨position, hmem⟩).1 :=
    G.liftTrapPositionalStrategy_move_inside strategy hmem
  refine ⟨?_, ?_⟩
  · rw [hmoveEq]
    exact (strategy.move ⟨position, hmem⟩).2
  · simpa [hmoveEq] using hsuccessorRegion

/--
Opponent-owned moves out of a lifted trap-subgame winning region stay in that
lifted winning region.
-/
theorem liftedTrapWinningRegion_opponent_successor_mem
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player region}
    {position next : G.Position}
    (hposition :
      position ∈ G.liftedTrapWinningRegion region htrap player)
    (howner : G.owner position = player.other)
    (hstep : G.step position next) :
    next ∈ G.liftedTrapWinningRegion region htrap player := by
  rcases hposition with ⟨hmem, hwinRegion⟩
  have hnextMem : next ∈ region :=
    (htrap position hmem).2 howner next hstep
  have htrapSubgame :
      (G.restrictToTrap player region htrap).TrapFor player
        ((G.restrictToTrap player region htrap).WinningRegion player) :=
    (G.restrictToTrap player region htrap).winningRegion_trapFor player
  have hnextWin :
      (⟨next, hnextMem⟩ :
        (G.restrictToTrap player region htrap).Position) ∈
        (G.restrictToTrap player region htrap).WinningRegion player := by
    exact
      ((htrapSubgame ⟨position, hmem⟩ hwinRegion).2
        (by simpa using howner))
        ⟨next, hnextMem⟩
        (by simpa using hstep)
  exact ⟨hnextMem, hnextWin⟩

/--
Combining an attractor to the lifted trap-subgame winning region with the
lifted recursive strategy wins throughout that attractor.
-/
theorem attractorThen_liftedTrapWinningRegion_winningFrom
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player region}
    (strategy :
      (G.restrictToTrap player region htrap).PositionalStrategy player)
    (hwinningOn :
      PositionalStrategy.WinningOn
        (G := G.restrictToTrap player region htrap)
        strategy
        ((G.restrictToTrap player region htrap).WinningRegion player))
    {start : G.Position}
    (hstart :
      G.Attractor player
        (G.liftedTrapWinningRegion region htrap player) start) :
    PositionalStrategy.WinningFrom
      (G := G)
      (G.attractorThenStrategy
        (G.liftedTrapWinningRegion region htrap player)
        (G.liftTrapPositionalStrategy strategy))
      start := by
  exact
    G.attractorThenStrategy_winningFrom
      (G.liftTrapPositionalStrategy strategy)
      (G.liftTrapPositionalStrategy_winningOn_liftedWinningRegion
        strategy hwinningOn)
      (by
        intro position hposition howner
        exact
          G.liftTrapPositionalStrategy_liftedWinningRegion_move_mem
            strategy hwinningOn hposition howner)
      (by
        intro position hposition howner next hstep
        exact
          G.liftedTrapWinningRegion_opponent_successor_mem
            hposition howner hstep)
      hstart

theorem attractorThen_liftedTrapWinningRegion_move_attractor_mem
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player region}
    (strategy :
      (G.restrictToTrap player region htrap).PositionalStrategy player)
    (hwinningOn :
      PositionalStrategy.WinningOn
        (G := G.restrictToTrap player region htrap)
        strategy
        ((G.restrictToTrap player region htrap).WinningRegion player))
    {position : G.Position}
    (hattractor :
      G.Attractor player
        (G.liftedTrapWinningRegion region htrap player) position)
    (howner : G.owner position = player) :
    (G.attractorThenStrategy
        (G.liftedTrapWinningRegion region htrap player)
        (G.liftTrapPositionalStrategy strategy)).move position ∈
      {position : G.Position |
        G.Attractor player
          (G.liftedTrapWinningRegion region htrap player) position} := by
  exact
    G.attractorThenStrategy_move_attractor_mem
      (G.liftTrapPositionalStrategy strategy)
      (by
        intro position hposition howner
        exact
          G.liftTrapPositionalStrategy_liftedWinningRegion_move_mem
            strategy hwinningOn hposition howner)
      hattractor howner

theorem attractor_liftedTrapWinningRegion_opponent_successor_mem
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player region}
    {position next : G.Position}
    (hattractor :
      G.Attractor player
        (G.liftedTrapWinningRegion region htrap player) position)
    (howner : G.owner position = player.other)
    (hstep : G.step position next) :
    G.Attractor player
      (G.liftedTrapWinningRegion region htrap player) next := by
  exact
    G.attractor_opponent_successor_mem_of_target_invariant
      (by
        intro position hposition howner next hstep
        exact
          G.liftedTrapWinningRegion_opponent_successor_mem
            hposition howner hstep)
      hattractor howner hstep

/--
If a trap subgame has a uniform positional strategy for `player`, then `player`
has one original positional strategy winning on the attractor to the lifted
subgame winning region.
-/
theorem exists_strategy_winningOn_attractor_liftedTrapWinningRegion
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player region}
    (huniform :
      ∀ p : ParityPlayer,
        ∃ strategy :
          (G.restrictToTrap player region htrap).PositionalStrategy p,
          PositionalStrategy.WinningOn
            (G := G.restrictToTrap player region htrap)
            strategy
            ((G.restrictToTrap player region htrap).WinningRegion p)) :
    ∃ strategy : G.PositionalStrategy player,
      PositionalStrategy.WinningOn
        (G := G)
        strategy
        (G.Attractor player
          (G.liftedTrapWinningRegion region htrap player)) := by
  rcases huniform player with ⟨inside, hinsideWinningOn⟩
  refine
    ⟨G.attractorThenStrategy
        (G.liftedTrapWinningRegion region htrap player)
        (G.liftTrapPositionalStrategy inside),
      ?_⟩
  intro start hstart
  exact
    G.attractorThen_liftedTrapWinningRegion_winningFrom
      inside hinsideWinningOn hstart

theorem attractor_liftedTrapWinningRegion_subset_positionalWinningRegion
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player region}
    (huniform :
      ∀ p : ParityPlayer,
        ∃ strategy :
          (G.restrictToTrap player region htrap).PositionalStrategy p,
          PositionalStrategy.WinningOn
            (G := G.restrictToTrap player region htrap)
            strategy
            ((G.restrictToTrap player region htrap).WinningRegion p)) :
    {position : G.Position |
      G.Attractor player
        (G.liftedTrapWinningRegion region htrap player) position} ⊆
      G.PositionalWinningRegion player := by
  rcases
      G.exists_strategy_winningOn_attractor_liftedTrapWinningRegion
        (player := player) (region := region) (htrap := htrap)
        huniform with
    ⟨strategy, hstrategy⟩
  intro position hposition
  exact ⟨strategy, hstrategy position hposition⟩

/--
No opponent-winning position can lie in the attractor to a player's lifted
trap-subgame winning region, once that subgame has been solved uniformly.
-/
theorem not_winningRegion_other_of_attractor_liftedTrapWinningRegion
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player region}
    (huniform :
      ∀ p : ParityPlayer,
        ∃ strategy :
          (G.restrictToTrap player region htrap).PositionalStrategy p,
          PositionalStrategy.WinningOn
            (G := G.restrictToTrap player region htrap)
            strategy
            ((G.restrictToTrap player region htrap).WinningRegion p))
    {position : G.Position}
    (hattractor :
      G.Attractor player
        (G.liftedTrapWinningRegion region htrap player) position) :
    position ∉ G.WinningRegion player.other := by
  intro hother
  have hpos :
      position ∈ G.PositionalWinningRegion player :=
    G.attractor_liftedTrapWinningRegion_subset_positionalWinningRegion
      (player := player) (region := region) (htrap := htrap)
      huniform hattractor
  have hwin :
      position ∈ G.WinningRegion player :=
    G.positionalWinningRegion_subset_winningRegion player hpos
  exact
    G.not_winningRegion_and_other player position ⟨hwin, hother⟩

/--
Target theorem for the Zielonka development: any history-dependent winning
strategy in a countable finitely-coloured parity game can be replaced by a
positional winning strategy.

The theorem is intentionally left as a definition of the required proposition
until the attractor/decomposition proof below is completed; no unchecked
constant or unproved theorem is introduced.
-/
def PositionalDeterminacyStatement : Prop :=
  ∀ (player : ParityPlayer) (start : G.Position),
    start ∈ G.WinningRegion player ->
      start ∈ G.PositionalWinningRegion player

/--
Full positional determinacy: every position is won by one of the two players
using a positional strategy.
-/
def PositionalGameDeterminedStatement : Prop :=
  ∀ start : G.Position,
    start ∈ G.PositionalWinningRegion ParityPlayer.even ∨
      start ∈ G.PositionalWinningRegion ParityPlayer.odd

/-- The even/odd determinacy statement, viewed from an arbitrary player. -/
theorem positionalGameDetermined_player_or_other
    (hdetermined : G.PositionalGameDeterminedStatement)
    (player : ParityPlayer)
    (start : G.Position) :
    start ∈ G.PositionalWinningRegion player ∨
      start ∈ G.PositionalWinningRegion player.other := by
  cases player with
  | even =>
      simpa using hdetermined start
  | odd =>
      rcases hdetermined start with hEven | hOdd
      · exact Or.inr hEven
      · exact Or.inl hOdd

/--
Uniform form of positional determinacy: for each player there is one positional
strategy that wins from every history-dependent winning position of that
player.  This is the form used by the recursive Zielonka construction.
-/
def UniformPositionalDeterminacyStatement : Prop :=
  ∀ player : ParityPlayer,
    ∃ strategy : G.PositionalStrategy player,
      PositionalStrategy.WinningOn
        (G := G) strategy (G.WinningRegion player)

/-- The uniform statement implies the pointwise positional-determinacy statement. -/
theorem positionalDeterminacy_of_uniform
    (huniform : G.UniformPositionalDeterminacyStatement) :
    G.PositionalDeterminacyStatement := by
  intro player start hwinning
  rcases huniform player with ⟨strategy, hstrategy⟩
  exact ⟨strategy, hstrategy start hwinning⟩

/-- Full positional game determinacy implies positionalization of winning regions. -/
theorem positionalDeterminacy_of_positionalGameDetermined
    (hdetermined : G.PositionalGameDeterminedStatement) :
    G.PositionalDeterminacyStatement := by
  intro player start hwinning
  rcases hdetermined start with hEven | hOdd
  · cases player with
    | even =>
        exact hEven
    | odd =>
        have hevenWinning :
            start ∈ G.WinningRegion ParityPlayer.even :=
          G.positionalWinningRegion_subset_winningRegion ParityPlayer.even hEven
        exact False.elim
          (G.not_winningRegion_even_and_odd start ⟨hevenWinning, hwinning⟩)
  · cases player with
    | even =>
        have hoddWinning :
            start ∈ G.WinningRegion ParityPlayer.odd :=
          G.positionalWinningRegion_subset_winningRegion ParityPlayer.odd hOdd
        exact False.elim
          (G.not_winningRegion_even_and_odd start ⟨hwinning, hoddWinning⟩)
    | odd =>
        exact hOdd

/--
Pointwise positional determinacy implies the uniform form on countable arenas:
first turn every history-winning position into a positional-winning position,
then uniformize the countable family of pointwise positional strategies.
-/
theorem uniformPositionalDeterminacy_of_positionalDeterminacy
    (hpointwise : G.PositionalDeterminacyStatement) :
    G.UniformPositionalDeterminacyStatement := by
  intro player
  rcases G.exists_strategy_winningOn_positionalWinningRegion player with
    ⟨strategy, hstrategy⟩
  refine ⟨strategy, ?_⟩
  intro start hwinning
  exact hstrategy start (hpointwise player start hwinning)

/-- Full positional game determinacy also gives the uniform statement on countable arenas. -/
theorem uniformPositionalDeterminacy_of_positionalGameDetermined
    (hdetermined : G.PositionalGameDeterminedStatement) :
    G.UniformPositionalDeterminacyStatement :=
  G.uniformPositionalDeterminacy_of_positionalDeterminacy
    (G.positionalDeterminacy_of_positionalGameDetermined hdetermined)

/-- On countable arenas, the pointwise and uniform positionalization statements are equivalent. -/
theorem uniformPositionalDeterminacy_iff_positionalDeterminacy :
    G.UniformPositionalDeterminacyStatement ↔
      G.PositionalDeterminacyStatement := by
  constructor
  · exact G.positionalDeterminacy_of_uniform
  · exact G.uniformPositionalDeterminacy_of_positionalDeterminacy

/--
Attractor-to-lifted-winning-region theorem with a pointwise subgame
positional-determinacy hypothesis.
-/
theorem exists_strategy_winningOn_attractor_liftedTrapWinningRegion_of_pointwise
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player region}
    (hpointwise :
      (G.restrictToTrap player region htrap).PositionalDeterminacyStatement) :
    ∃ strategy : G.PositionalStrategy player,
      PositionalStrategy.WinningOn
        (G := G)
        strategy
        (G.Attractor player
          (G.liftedTrapWinningRegion region htrap player)) := by
  exact
    G.exists_strategy_winningOn_attractor_liftedTrapWinningRegion
      (CountableParityGame.uniformPositionalDeterminacy_of_positionalDeterminacy
        (G := G.restrictToTrap player region htrap)
        hpointwise)

/--
Attractor-to-lifted-winning-region theorem with a full positional game
determinacy hypothesis on the trap subgame.
-/
theorem exists_strategy_winningOn_attractor_liftedTrapWinningRegion_of_determined
    {player : ParityPlayer}
    {region : Set G.Position}
    {htrap : G.TrapFor player region}
    (hdetermined :
      (G.restrictToTrap player region htrap).PositionalGameDeterminedStatement) :
    ∃ strategy : G.PositionalStrategy player,
      PositionalStrategy.WinningOn
        (G := G)
        strategy
        (G.Attractor player
          (G.liftedTrapWinningRegion region htrap player)) := by
  exact
    G.exists_strategy_winningOn_attractor_liftedTrapWinningRegion
      (CountableParityGame.uniformPositionalDeterminacy_of_positionalGameDetermined
        (G := G.restrictToTrap player region htrap)
        hdetermined)

/--
Recursive favourable-minimum case in uniform form.  If the least priority
favours `player`, and every position outside `player`'s attractor to that
priority remains history-winning for `player`, then the recursive uniform
strategy on the complement trap combines with the attractor strategy to win
from every original position.
-/
theorem exists_strategy_winning_all_of_favorable_minimum
    {player : ParityPlayer}
    {priority : Nat}
    (hpriorityLeast :
      ∀ position : G.Position, priority ≤ G.priority position)
    (hpriorityOwner : priorityOwner priority = player)
    (hsubUniform :
      (G.restrictToTrap player.other
        {position : G.Position |
          ¬ G.Attractor player (G.priorityClass priority) position}
        (G.compl_attractor_trapFor_other player
          (G.priorityClass priority))).UniformPositionalDeterminacyStatement)
    (hregionWinning :
      ∀ position : G.Position,
        position ∈
          {position : G.Position |
            ¬ G.Attractor player (G.priorityClass priority) position} ->
          position ∈ G.WinningRegion player) :
    ∃ strategy : G.PositionalStrategy player,
      ∀ start : G.Position,
        PositionalStrategy.WinningFrom (G := G) strategy start := by
  let region : Set G.Position :=
    {position : G.Position |
      ¬ G.Attractor player (G.priorityClass priority) position}
  let htrap : G.TrapFor player.other region :=
    G.compl_attractor_trapFor_other player (G.priorityClass priority)
  let subgame := G.restrictToTrap player.other region htrap
  rcases hsubUniform player with ⟨inside, hinsideUniform⟩
  have hinsideWinning :
      ∀ (position : G.Position),
        ∀ hposition : position ∈ region,
          PositionalStrategy.WinningFrom
            (G := subgame)
            inside
            ⟨position, hposition⟩ := by
    intro position hposition
    have hrestrictedWinning :
        (⟨position, hposition⟩ : subgame.Position) ∈
          subgame.WinningRegion player := by
      simpa [subgame, region, htrap] using
        G.restrictToOpponentTrap_winningRegion
          (player := player)
          (region := region)
          (htrap := htrap)
          hposition
          (hregionWinning position (by simpa [region] using hposition))
    exact hinsideUniform ⟨position, hposition⟩ hrestrictedWinning
  let strategy :=
    G.spliceOpponentTrapPositionalStrategy
      (G.attractorStrategy player (G.priorityClass priority)) inside
  refine ⟨strategy, ?_⟩
  intro start
  simpa [strategy, region, htrap, subgame] using
    G.spliceAttractor_winningFrom_of_inside_winningOn
      hpriorityLeast hpriorityOwner inside
      (by
        intro position hposition
        exact hinsideWinning position (by simpa [region] using hposition))
      start

/--
Pointwise form of the favourable-minimum splice.  The recursive subgame
hypothesis can be pointwise because countability uniformizes positional
strategies on positional winning regions.
-/
theorem exists_strategy_winning_all_of_favorable_minimum_of_pointwise
    {player : ParityPlayer}
    {priority : Nat}
    (hpriorityLeast :
      ∀ position : G.Position, priority ≤ G.priority position)
    (hpriorityOwner : priorityOwner priority = player)
    (hsubPointwise :
      (G.restrictToTrap player.other
        {position : G.Position |
          ¬ G.Attractor player (G.priorityClass priority) position}
        (G.compl_attractor_trapFor_other player
          (G.priorityClass priority))).PositionalDeterminacyStatement)
    (hregionWinning :
      ∀ position : G.Position,
        position ∈
          {position : G.Position |
            ¬ G.Attractor player (G.priorityClass priority) position} ->
          position ∈ G.WinningRegion player) :
    ∃ strategy : G.PositionalStrategy player,
      ∀ start : G.Position,
        PositionalStrategy.WinningFrom (G := G) strategy start := by
  exact
    G.exists_strategy_winning_all_of_favorable_minimum
      hpriorityLeast hpriorityOwner
      ((G.restrictToTrap player.other
        {position : G.Position |
          ¬ G.Attractor player (G.priorityClass priority) position}
        (G.compl_attractor_trapFor_other player
          (G.priorityClass priority))).uniformPositionalDeterminacy_of_positionalDeterminacy
        hsubPointwise)
      hregionWinning

/--
Favourable-minimum branch when the recursive complement subgame has no
opponent-winning position.  A positional-determined complement then gives one
inside strategy for all complement positions, and the attractor/inside splice
wins from every original position.
-/
theorem exists_strategy_winning_all_of_favorable_minimum_of_no_opponent_target
    {player : ParityPlayer}
    {priority : Nat}
    (hpriorityLeast :
      ∀ position : G.Position, priority ≤ G.priority position)
    (hpriorityOwner : priorityOwner priority = player)
    (hsubDetermined :
      (G.restrictToTrap player.other
        {position : G.Position |
          ¬ G.Attractor player (G.priorityClass priority) position}
        (G.compl_attractor_trapFor_other player
          (G.priorityClass priority))).PositionalGameDeterminedStatement)
    (hnoOpponentTarget :
      ∀ position : G.Position,
        position ∉
          G.liftedTrapWinningRegion
            {position : G.Position |
              ¬ G.Attractor player (G.priorityClass priority) position}
            (G.compl_attractor_trapFor_other player
              (G.priorityClass priority))
            player.other) :
    ∃ strategy : G.PositionalStrategy player,
      ∀ start : G.Position,
        PositionalStrategy.WinningFrom (G := G) strategy start := by
  let region : Set G.Position :=
    {position : G.Position |
      ¬ G.Attractor player (G.priorityClass priority) position}
  let htrap : G.TrapFor player.other region :=
    G.compl_attractor_trapFor_other player (G.priorityClass priority)
  let subgame := G.restrictToTrap player.other region htrap
  rcases subgame.exists_strategy_winningOn_positionalWinningRegion player with
    ⟨inside, hinsideOnPositional⟩
  have hinsideWinning :
      ∀ (position : G.Position),
        ∀ hposition : position ∈ region,
          PositionalStrategy.WinningFrom
            (G := subgame)
            inside
            ⟨position, hposition⟩ := by
    intro position hposition
    have hpositional :
        (⟨position, hposition⟩ : subgame.Position) ∈
          subgame.PositionalWinningRegion player := by
      have hdeterminedPlayer :
          (⟨position, hposition⟩ : subgame.Position) ∈
              subgame.PositionalWinningRegion player ∨
            (⟨position, hposition⟩ : subgame.Position) ∈
              subgame.PositionalWinningRegion player.other := by
        cases player with
        | even =>
            simpa using hsubDetermined ⟨position, hposition⟩
        | odd =>
            rcases hsubDetermined ⟨position, hposition⟩ with hEven | hOdd
            · exact Or.inr hEven
            · exact Or.inl hOdd
      rcases hdeterminedPlayer with hwin | hwin
      · exact hwin
      · have hhistory :
            (⟨position, hposition⟩ : subgame.Position) ∈
              subgame.WinningRegion player.other :=
          subgame.positionalWinningRegion_subset_winningRegion
            player.other hwin
        exact False.elim
          (hnoOpponentTarget position
            (by
              refine ⟨?_, ?_⟩
              · simpa [region] using hposition
              · simpa [subgame, region, htrap] using hhistory))
    exact hinsideOnPositional ⟨position, hposition⟩ hpositional
  let strategy :=
    G.spliceOpponentTrapPositionalStrategy
      (G.attractorStrategy player (G.priorityClass priority)) inside
  refine ⟨strategy, ?_⟩
  intro start
  simpa [strategy, region, htrap, subgame] using
    G.spliceAttractor_winningFrom_of_inside_winningOn
      hpriorityLeast hpriorityOwner inside
      (by
        intro position hposition
        exact hinsideWinning position (by simpa [region] using hposition))
      start

/--
Second-case remaining-region splice.  Once the opponent attractor to its
recursive winning region has been removed, a recursive uniform strategy on the
remaining trap gives one original positional strategy for all original
`player`-winning starts.  The restriction of original winning starts to the
remaining trap subgame is discharged by
`restrict_compl_opponent_attractor_winningRegion`.
-/
theorem exists_strategy_winningOn_second_case_remaining
    {player : ParityPlayer}
    {firstRegion : Set G.Position}
    {hfirstTrap : G.TrapFor player.other firstRegion}
    (hfirstUniform :
      (G.restrictToTrap player.other firstRegion hfirstTrap).UniformPositionalDeterminacyStatement)
    (hremainingUniform :
      (G.restrictToTrap player
        {position : G.Position |
          ¬ G.Attractor player.other
            (G.liftedTrapWinningRegion firstRegion hfirstTrap player.other)
            position}
        (G.compl_opponent_attractor_trapFor player
          (G.liftedTrapWinningRegion firstRegion hfirstTrap player.other))).UniformPositionalDeterminacyStatement) :
    ∃ strategy : G.PositionalStrategy player,
      PositionalStrategy.WinningOn
        (G := G) strategy (G.WinningRegion player) := by
  let target : Set G.Position :=
    G.liftedTrapWinningRegion firstRegion hfirstTrap player.other
  let remaining : Set G.Position :=
    {position : G.Position |
      ¬ G.Attractor player.other target position}
  let hremainingTrap : G.TrapFor player remaining :=
    G.compl_opponent_attractor_trapFor player target
  let remainingGame := G.restrictToTrap player remaining hremainingTrap
  have hremainingUniformLocal :
      remainingGame.UniformPositionalDeterminacyStatement := by
    simpa [remainingGame, remaining, target, hremainingTrap] using
      hremainingUniform
  rcases hremainingUniformLocal player with
    ⟨remainingStrategy, hremainingStrategy⟩
  refine ⟨G.liftTrapPositionalStrategy remainingStrategy, ?_⟩
  intro start hstartWinning
  have hstartRemaining : start ∈ remaining := by
    change ¬ G.Attractor player.other target start
    intro hattractor
    have hnotPlayerWinning :
        start ∉ G.WinningRegion player := by
      simpa [target] using
        G.not_winningRegion_other_of_attractor_liftedTrapWinningRegion
          (player := player.other)
          (region := firstRegion)
          (htrap := hfirstTrap)
          hfirstUniform
          hattractor
    exact hnotPlayerWinning hstartWinning
  have hsubWinning :
      (⟨start, hstartRemaining⟩ : remainingGame.Position) ∈
        remainingGame.WinningRegion player := by
    simpa [remainingGame, remaining, target, hremainingTrap] using
      G.restrict_compl_opponent_attractor_winningRegion
        (player := player)
        (target := target)
        (by
          intro position hattractor
          simpa [target] using
            G.not_winningRegion_other_of_attractor_liftedTrapWinningRegion
              (player := player.other)
              (region := firstRegion)
              (htrap := hfirstTrap)
              hfirstUniform
              hattractor)
        (by simpa [remaining, target] using hstartRemaining)
        hstartWinning
  exact
    G.liftTrapPositionalStrategy_winningFrom remainingStrategy
      (hremainingStrategy ⟨start, hstartRemaining⟩ hsubWinning)

/--
Pointwise form of the second-case splice.  The two recursive subgame
hypotheses can be pointwise and are uniformized internally.
-/
theorem exists_strategy_winningOn_second_case_remaining_of_pointwise
    {player : ParityPlayer}
    {firstRegion : Set G.Position}
    {hfirstTrap : G.TrapFor player.other firstRegion}
    (hfirstPointwise :
      (G.restrictToTrap player.other firstRegion hfirstTrap).PositionalDeterminacyStatement)
    (hremainingPointwise :
      (G.restrictToTrap player
        {position : G.Position |
          ¬ G.Attractor player.other
            (G.liftedTrapWinningRegion firstRegion hfirstTrap player.other)
            position}
        (G.compl_opponent_attractor_trapFor player
          (G.liftedTrapWinningRegion firstRegion hfirstTrap player.other))).PositionalDeterminacyStatement) :
    ∃ strategy : G.PositionalStrategy player,
      PositionalStrategy.WinningOn
        (G := G) strategy (G.WinningRegion player) := by
  exact
    G.exists_strategy_winningOn_second_case_remaining
      (CountableParityGame.uniformPositionalDeterminacy_of_positionalDeterminacy
        (G := G.restrictToTrap player.other firstRegion hfirstTrap)
          hfirstPointwise)
      (CountableParityGame.uniformPositionalDeterminacy_of_positionalDeterminacy
        (G := G.restrictToTrap player
          {position : G.Position |
            ¬ G.Attractor player.other
              (G.liftedTrapWinningRegion firstRegion hfirstTrap player.other)
              position}
          (G.compl_opponent_attractor_trapFor player
            (G.liftedTrapWinningRegion firstRegion hfirstTrap player.other)))
          hremainingPointwise)

/--
The opponent side of the second Zielonka branch.  It consists of the opponent
attractor to the first recursive opponent-winning target, together with the
opponent's winning region in the remaining trap.
-/
def secondCaseOpponentRegion
    {player : ParityPlayer}
    {firstRegion : Set G.Position}
    (hfirstTrap : G.TrapFor player.other firstRegion) :
    Set G.Position :=
  let target : Set G.Position :=
    G.liftedTrapWinningRegion firstRegion hfirstTrap player.other
  let remaining : Set G.Position :=
    {position : G.Position | ¬ G.Attractor player.other target position}
  let hremainingTrap : G.TrapFor player remaining :=
    G.compl_opponent_attractor_trapFor player target
  let remainingGame := G.restrictToTrap player remaining hremainingTrap
  {position : G.Position |
    G.Attractor player.other target position ∨
      ∃ hposition : position ∈ remaining,
        (⟨position, hposition⟩ : remainingGame.Position) ∈
          remainingGame.WinningRegion player.other}

/--
Uniform second-case opponent splice.  The outside component attracts to the
first recursive opponent target and then uses the first recursive strategy;
the inside component is the recursive opponent strategy on the remaining
`player`-trap.
-/
theorem exists_strategy_winningOn_second_case_opponentRegion
    {player : ParityPlayer}
    {firstRegion : Set G.Position}
    {hfirstTrap : G.TrapFor player.other firstRegion}
    (hfirstUniform :
      (G.restrictToTrap player.other firstRegion hfirstTrap).UniformPositionalDeterminacyStatement)
    (hremainingUniform :
      (G.restrictToTrap player
        {position : G.Position |
          ¬ G.Attractor player.other
            (G.liftedTrapWinningRegion firstRegion hfirstTrap player.other)
            position}
        (G.compl_opponent_attractor_trapFor player
          (G.liftedTrapWinningRegion firstRegion hfirstTrap player.other))).UniformPositionalDeterminacyStatement) :
    ∃ strategy : G.PositionalStrategy player.other,
      PositionalStrategy.WinningOn
        (G := G) strategy (G.secondCaseOpponentRegion hfirstTrap) := by
  classical
  let target : Set G.Position :=
    G.liftedTrapWinningRegion firstRegion hfirstTrap player.other
  let remaining : Set G.Position :=
    {position : G.Position | ¬ G.Attractor player.other target position}
  let hremainingTrap : G.TrapFor player remaining :=
    G.compl_opponent_attractor_trapFor player target
  let remainingGame := G.restrictToTrap player remaining hremainingTrap
  have hremainingUniformLocal :
      remainingGame.UniformPositionalDeterminacyStatement := by
    simpa [remainingGame, remaining, target, hremainingTrap] using
      hremainingUniform
  rcases hfirstUniform player.other with
    ⟨firstStrategy, hfirstStrategy⟩
  rcases hremainingUniformLocal player.other with
    ⟨inside, hinsideUniform⟩
  let outside : G.PositionalStrategy player.other :=
    G.attractorThenStrategy target
      (G.liftTrapPositionalStrategy firstStrategy)
  let strategy : G.PositionalStrategy player.other :=
    G.spliceTrapForOpponentPositionalStrategy
      (player := player) (region := remaining) (htrap := hremainingTrap)
      outside inside
  have hattractor_of_not_remaining :
      ∀ {position : G.Position},
        position ∉ remaining ->
          G.Attractor player.other target position := by
    intro position hnotRemaining
    by_contra hnotAttractor
    exact hnotRemaining (by simpa [remaining] using hnotAttractor)
  have houtsideWinning :
      ∀ position : G.Position,
        position ∉ remaining ->
          PositionalStrategy.WinningFrom (G := G) outside position := by
    intro position hnotRemaining
    have hattractor :
        G.Attractor player.other target position :=
      hattractor_of_not_remaining hnotRemaining
    simpa [outside, target] using
      G.attractorThen_liftedTrapWinningRegion_winningFrom
        (player := player.other)
        (region := firstRegion)
        (htrap := hfirstTrap)
        firstStrategy hfirstStrategy
        (by simpa [target] using hattractor)
  have houtsideMoveMem :
      ∀ position : G.Position,
        position ∉ remaining ->
          G.owner position = player.other ->
            outside.move position ∉ remaining := by
    intro position hnotRemaining howner
    have hattractor :
        G.Attractor player.other target position :=
      hattractor_of_not_remaining hnotRemaining
    have hmoveAttractor :
        G.Attractor player.other target (outside.move position) := by
      simpa [outside, target] using
        G.attractorThen_liftedTrapWinningRegion_move_attractor_mem
          (player := player.other)
          (region := firstRegion)
          (htrap := hfirstTrap)
          firstStrategy hfirstStrategy
          (by simpa [target] using hattractor)
          howner
    intro hremainingMove
    have hnotAttractor :
        ¬ G.Attractor player.other target (outside.move position) := by
      simpa [remaining] using hremainingMove
    exact hnotAttractor hmoveAttractor
  have houtsideOpponentMem :
      ∀ position : G.Position,
        position ∉ remaining ->
          G.owner position = player ->
            ∀ next : G.Position, G.step position next -> next ∉ remaining := by
    intro position hnotRemaining howner next hstep
    have hattractor :
        G.Attractor player.other target position :=
      hattractor_of_not_remaining hnotRemaining
    have hnextAttractor :
        G.Attractor player.other target next := by
      simpa [target] using
        G.attractor_liftedTrapWinningRegion_opponent_successor_mem
          (player := player.other)
          (region := firstRegion)
          (htrap := hfirstTrap)
          (by simpa [target] using hattractor)
          (by simpa using howner)
          hstep
    intro hremainingNext
    have hnotAttractor :
        ¬ G.Attractor player.other target next := by
      simpa [remaining] using hremainingNext
    exact hnotAttractor hnextAttractor
  refine ⟨strategy, ?_⟩
  intro start hstart
  have hstartCases :
      G.Attractor player.other target start ∨
        ∃ hposition : start ∈ remaining,
          (⟨start, hposition⟩ : remainingGame.Position) ∈
            remainingGame.WinningRegion player.other := by
    simpa [secondCaseOpponentRegion, target, remaining, hremainingTrap,
      remainingGame] using hstart
  rcases hstartCases with hstartAttractor | hstartRemaining
  · simpa [strategy] using
      G.spliceTrapForOpponentPositionalStrategy_winningFrom
        (player := player) (region := remaining) (htrap := hremainingTrap)
        outside inside
        (start := start)
        (by
          intro hstartRemaining
          have hnotAttractor :
              ¬ G.Attractor player.other target start := by
            simpa [remaining] using hstartRemaining
          exact False.elim (hnotAttractor hstartAttractor))
        houtsideWinning houtsideMoveMem houtsideOpponentMem
  · rcases hstartRemaining with ⟨hstartRemaining, hstartWinning⟩
    simpa [strategy] using
      G.spliceTrapForOpponentPositionalStrategy_winningFrom
        (player := player) (region := remaining) (htrap := hremainingTrap)
        outside inside
        (start := start)
        (by
          intro hstartRegion
          have hstartWinning' :
              (⟨start, hstartRegion⟩ : remainingGame.Position) ∈
                remainingGame.WinningRegion player.other := by
            simpa using hstartWinning
          exact
            hinsideUniform ⟨start, hstartRegion⟩ hstartWinning')
        houtsideWinning houtsideMoveMem houtsideOpponentMem

/-- Pointwise form of the second-case opponent splice. -/
theorem exists_strategy_winningOn_second_case_opponentRegion_of_pointwise
    {player : ParityPlayer}
    {firstRegion : Set G.Position}
    {hfirstTrap : G.TrapFor player.other firstRegion}
    (hfirstPointwise :
      (G.restrictToTrap player.other firstRegion hfirstTrap).PositionalDeterminacyStatement)
    (hremainingPointwise :
      (G.restrictToTrap player
        {position : G.Position |
          ¬ G.Attractor player.other
            (G.liftedTrapWinningRegion firstRegion hfirstTrap player.other)
            position}
        (G.compl_opponent_attractor_trapFor player
          (G.liftedTrapWinningRegion firstRegion hfirstTrap player.other))).PositionalDeterminacyStatement) :
    ∃ strategy : G.PositionalStrategy player.other,
      PositionalStrategy.WinningOn
        (G := G) strategy (G.secondCaseOpponentRegion hfirstTrap) := by
  exact
    G.exists_strategy_winningOn_second_case_opponentRegion
      (CountableParityGame.uniformPositionalDeterminacy_of_positionalDeterminacy
        (G := G.restrictToTrap player.other firstRegion hfirstTrap)
          hfirstPointwise)
      (CountableParityGame.uniformPositionalDeterminacy_of_positionalDeterminacy
        (G := G.restrictToTrap player
          {position : G.Position |
            ¬ G.Attractor player.other
              (G.liftedTrapWinningRegion firstRegion hfirstTrap player.other)
              position}
          (G.compl_opponent_attractor_trapFor player
            (G.liftedTrapWinningRegion firstRegion hfirstTrap player.other)))
          hremainingPointwise)

/--
Second-case partition theorem.  If the first recursive trap subgame and the
remaining trap subgame are positionally determined, then the original game is
positionally determined by the usual Zielonka split: the opponent wins its
attractor/remaining recursive region, and every other start is won by `player`
inside the remaining trap.
-/
theorem positionalGameDetermined_of_second_case
    {player : ParityPlayer}
    {firstRegion : Set G.Position}
    {hfirstTrap : G.TrapFor player.other firstRegion}
    (hfirstDetermined :
      (G.restrictToTrap player.other firstRegion hfirstTrap).PositionalGameDeterminedStatement)
    (hremainingDetermined :
      (G.restrictToTrap player
        {position : G.Position |
          ¬ G.Attractor player.other
            (G.liftedTrapWinningRegion firstRegion hfirstTrap player.other)
            position}
        (G.compl_opponent_attractor_trapFor player
          (G.liftedTrapWinningRegion firstRegion hfirstTrap player.other))).PositionalGameDeterminedStatement) :
    G.PositionalGameDeterminedStatement := by
  classical
  let target : Set G.Position :=
    G.liftedTrapWinningRegion firstRegion hfirstTrap player.other
  let remaining : Set G.Position :=
    {position : G.Position | ¬ G.Attractor player.other target position}
  let hremainingTrap : G.TrapFor player remaining :=
    G.compl_opponent_attractor_trapFor player target
  let remainingGame := G.restrictToTrap player remaining hremainingTrap
  have hfirstUniform :
      (G.restrictToTrap player.other firstRegion hfirstTrap).UniformPositionalDeterminacyStatement :=
    CountableParityGame.uniformPositionalDeterminacy_of_positionalGameDetermined
      (G := G.restrictToTrap player.other firstRegion hfirstTrap)
      hfirstDetermined
  have hremainingDeterminedLocal :
      remainingGame.PositionalGameDeterminedStatement := by
    simpa [remainingGame, remaining, target, hremainingTrap] using
      hremainingDetermined
  have hremainingUniform :
      (G.restrictToTrap player
        {position : G.Position |
          ¬ G.Attractor player.other
            (G.liftedTrapWinningRegion firstRegion hfirstTrap player.other)
            position}
        (G.compl_opponent_attractor_trapFor player
          (G.liftedTrapWinningRegion firstRegion hfirstTrap player.other))).UniformPositionalDeterminacyStatement := by
    have hlocal :
        remainingGame.UniformPositionalDeterminacyStatement :=
      CountableParityGame.uniformPositionalDeterminacy_of_positionalGameDetermined
        (G := remainingGame)
        hremainingDeterminedLocal
    simpa [remainingGame, remaining, target, hremainingTrap] using hlocal
  rcases
      G.exists_strategy_winningOn_second_case_opponentRegion
        (player := player)
        (firstRegion := firstRegion)
        (hfirstTrap := hfirstTrap)
        hfirstUniform hremainingUniform with
    ⟨opponentStrategy, hopponentStrategy⟩
  intro start
  by_cases hopponentRegion :
      start ∈ G.secondCaseOpponentRegion hfirstTrap
  · have hopponentPos :
        start ∈ G.PositionalWinningRegion player.other :=
      ⟨opponentStrategy, hopponentStrategy start hopponentRegion⟩
    cases player with
    | even =>
        exact Or.inr hopponentPos
    | odd =>
        exact Or.inl hopponentPos
  · have hremaining : start ∈ remaining := by
      by_contra hnotRemaining
      have hattractor :
          G.Attractor player.other target start := by
        by_contra hnotAttractor
        exact hnotRemaining (by simpa [remaining] using hnotAttractor)
      have hregion : start ∈ G.secondCaseOpponentRegion hfirstTrap := by
        simpa [secondCaseOpponentRegion, target, remaining, hremainingTrap,
          remainingGame] using
          (Or.inl hattractor :
            G.Attractor player.other target start ∨
              ∃ hposition : start ∈ remaining,
                (⟨start, hposition⟩ : remainingGame.Position) ∈
                  remainingGame.WinningRegion player.other)
      exact hopponentRegion hregion
    have hremainingCases :
        (⟨start, hremaining⟩ : remainingGame.Position) ∈
            remainingGame.PositionalWinningRegion player ∨
          (⟨start, hremaining⟩ : remainingGame.Position) ∈
            remainingGame.PositionalWinningRegion player.other :=
      remainingGame.positionalGameDetermined_player_or_other
        hremainingDeterminedLocal player ⟨start, hremaining⟩
    rcases hremainingCases with hplayerPos | hopponentPos
    · have hplayerOriginal :
          start ∈ G.PositionalWinningRegion player := by
        exact
          G.liftTrap_positionalWinningRegion
            (player := player)
            (region := remaining)
            (htrap := hremainingTrap)
            (start := ⟨start, hremaining⟩)
            hplayerPos
      cases player with
      | even =>
          exact Or.inl hplayerOriginal
      | odd =>
          exact Or.inr hplayerOriginal
    · have hopponentWinning :
          (⟨start, hremaining⟩ : remainingGame.Position) ∈
            remainingGame.WinningRegion player.other :=
        remainingGame.positionalWinningRegion_subset_winningRegion
          player.other hopponentPos
      have hregion : start ∈ G.secondCaseOpponentRegion hfirstTrap := by
        simpa [secondCaseOpponentRegion, target, remaining, hremainingTrap,
          remainingGame] using
          (Or.inr ⟨hremaining, hopponentWinning⟩ :
            G.Attractor player.other target start ∨
              ∃ hposition : start ∈ remaining,
                (⟨start, hposition⟩ : remainingGame.Position) ∈
                  remainingGame.WinningRegion player.other)
      exact False.elim (hopponentRegion hregion)

/--
One favourable-minimum Zielonka step.  The first recursive call is made on the
complement of `player`'s attractor to the least priority.  If that subgame has
no opponent-winning target, `player` wins everywhere; otherwise the second-case
partition theorem combines the first recursive solution with the recursive
solution of the remaining trap.
-/
theorem positionalGameDetermined_of_favorable_minimum_step
    {player : ParityPlayer}
    {priority : Nat}
    (hpriorityLeast :
      ∀ position : G.Position, priority ≤ G.priority position)
    (hpriorityOwner : priorityOwner priority = player)
    (hfirstDetermined :
      (G.restrictToTrap player.other
        {position : G.Position |
          ¬ G.Attractor player (G.priorityClass priority) position}
        (G.compl_attractor_trapFor_other player
          (G.priorityClass priority))).PositionalGameDeterminedStatement)
    (hremainingDetermined :
      (G.restrictToTrap player
        {position : G.Position |
          ¬ G.Attractor player.other
            (G.liftedTrapWinningRegion
              {position : G.Position |
                ¬ G.Attractor player (G.priorityClass priority) position}
              (G.compl_attractor_trapFor_other player
                (G.priorityClass priority))
              player.other)
            position}
        (G.compl_opponent_attractor_trapFor player
          (G.liftedTrapWinningRegion
            {position : G.Position |
              ¬ G.Attractor player (G.priorityClass priority) position}
            (G.compl_attractor_trapFor_other player
              (G.priorityClass priority))
            player.other))).PositionalGameDeterminedStatement) :
    G.PositionalGameDeterminedStatement := by
  classical
  let firstRegion : Set G.Position :=
    {position : G.Position |
      ¬ G.Attractor player (G.priorityClass priority) position}
  let hfirstTrap : G.TrapFor player.other firstRegion :=
    G.compl_attractor_trapFor_other player (G.priorityClass priority)
  by_cases hnoOpponentTarget :
      ∀ position : G.Position,
        position ∉
          G.liftedTrapWinningRegion firstRegion hfirstTrap player.other
  · have hfirstDeterminedLocal :
        (G.restrictToTrap player.other firstRegion hfirstTrap).PositionalGameDeterminedStatement := by
      simpa [firstRegion, hfirstTrap] using hfirstDetermined
    rcases
        G.exists_strategy_winning_all_of_favorable_minimum_of_no_opponent_target
          (player := player)
          (priority := priority)
          hpriorityLeast hpriorityOwner
          hfirstDeterminedLocal
          (by
            intro position hposition
            exact hnoOpponentTarget position (by simpa [firstRegion, hfirstTrap] using hposition)) with
      ⟨strategy, hstrategy⟩
    intro start
    have hplayerPos :
        start ∈ G.PositionalWinningRegion player :=
      ⟨strategy, hstrategy start⟩
    cases player with
    | even =>
        exact Or.inl hplayerPos
    | odd =>
        exact Or.inr hplayerPos
  · have hfirstDeterminedLocal :
        (G.restrictToTrap player.other firstRegion hfirstTrap).PositionalGameDeterminedStatement := by
      simpa [firstRegion, hfirstTrap] using hfirstDetermined
    have hremainingDeterminedLocal :
        (G.restrictToTrap player
          {position : G.Position |
            ¬ G.Attractor player.other
              (G.liftedTrapWinningRegion firstRegion hfirstTrap player.other)
              position}
          (G.compl_opponent_attractor_trapFor player
            (G.liftedTrapWinningRegion firstRegion hfirstTrap player.other))).PositionalGameDeterminedStatement := by
      simpa [firstRegion, hfirstTrap] using hremainingDetermined
    exact
      G.positionalGameDetermined_of_second_case
        (player := player)
        (firstRegion := firstRegion)
        (hfirstTrap := hfirstTrap)
        hfirstDeterminedLocal
        hremainingDeterminedLocal

/--
Uniform base case for the priority induction: if all positions have the same
priority, then each player's winning region has a single positional strategy.
-/
theorem uniformPositionalDeterminacy_of_constant_priority
    {p : Nat}
    (hpriority : ∀ position : G.Position, G.priority position = p) :
    G.UniformPositionalDeterminacyStatement := by
  intro player
  cases player with
  | even =>
      by_cases hpEven : DetParityAutomaton.NatEven p
      · refine ⟨G.arbitraryPositionalStrategy ParityPlayer.even, ?_⟩
        intro start _hwinning
        exact
          PositionalStrategy.winningFrom_constant_even_priority
            (G := G) hpriority hpEven
      · refine ⟨G.arbitraryPositionalStrategy ParityPlayer.even, ?_⟩
        intro start hwinning
        exact False.elim
          (G.not_winningRegion_even_of_constant_odd_priority
            hpriority hpEven start hwinning)
  | odd =>
      by_cases hpEven : DetParityAutomaton.NatEven p
      · refine ⟨G.arbitraryPositionalStrategy ParityPlayer.odd, ?_⟩
        intro start hwinning
        exact False.elim
          (G.not_winningRegion_odd_of_constant_even_priority
            hpriority hpEven start hwinning)
      · refine ⟨G.arbitraryPositionalStrategy ParityPlayer.odd, ?_⟩
        intro start _hwinning
        exact
          PositionalStrategy.winningFrom_constant_odd_priority
            (G := G) hpriority hpEven

/-- Uniform base case when the occurring-priority range is subsingleton. -/
theorem uniformPositionalDeterminacy_of_subsingleton_priority_range
    (hsubsingleton :
      ∀ p ∈ Set.range G.priority,
        ∀ q ∈ Set.range G.priority, p = q) :
    G.UniformPositionalDeterminacyStatement := by
  classical
  by_cases hnonempty : Nonempty G.Position
  · let witness : G.Position := Classical.choice hnonempty
    have hpriority :
        ∀ position : G.Position, G.priority position = G.priority witness := by
      intro position
      exact
        hsubsingleton
          (G.priority position) ⟨position, rfl⟩
          (G.priority witness) ⟨witness, rfl⟩
    exact G.uniformPositionalDeterminacy_of_constant_priority hpriority
  · intro player
    refine ⟨G.arbitraryPositionalStrategy player, ?_⟩
    intro start _hwinning
    exact False.elim (hnonempty ⟨start⟩)

/-- Uniform cardinal form of the base case used by priority induction. -/
theorem uniformPositionalDeterminacy_of_priorityRange_card_le_one
    (hcard : G.priorityRangeFinset.card ≤ 1) :
    G.UniformPositionalDeterminacyStatement := by
  apply G.uniformPositionalDeterminacy_of_subsingleton_priority_range
  intro p hp q hq
  exact
    (Finset.card_le_one.mp hcard)
      p (by simpa [priorityRangeFinset] using hp)
      q (by simpa [priorityRangeFinset] using hq)

/-- Full positional-determinacy base case for constant-priority games. -/
theorem positionalGameDetermined_of_constant_priority
    {p : Nat}
    (hpriority : ∀ position : G.Position, G.priority position = p) :
    G.PositionalGameDeterminedStatement := by
  intro start
  by_cases hpEven : DetParityAutomaton.NatEven p
  · exact Or.inl
      (G.positionalWinningRegion_of_constant_even_priority
        hpriority hpEven start)
  · exact Or.inr
      (G.positionalWinningRegion_of_constant_odd_priority
        hpriority hpEven start)

/-- Full positional-determinacy base case for subsingleton priority ranges. -/
theorem positionalGameDetermined_of_subsingleton_priority_range
    (hsubsingleton :
      ∀ p ∈ Set.range G.priority,
        ∀ q ∈ Set.range G.priority, p = q) :
    G.PositionalGameDeterminedStatement := by
  intro start
  have hpriority :
      ∀ position : G.Position, G.priority position = G.priority start := by
    intro position
    exact
      hsubsingleton
        (G.priority position) ⟨position, rfl⟩
        (G.priority start) ⟨start, rfl⟩
  exact G.positionalGameDetermined_of_constant_priority hpriority start

/-- Cardinal form of the full positional-determinacy base case. -/
theorem positionalGameDetermined_of_priorityRange_card_le_one
    (hcard : G.priorityRangeFinset.card ≤ 1) :
    G.PositionalGameDeterminedStatement := by
  apply G.positionalGameDetermined_of_subsingleton_priority_range
  intro p hp q hq
  exact
    (Finset.card_le_one.mp hcard)
      p (by simpa [priorityRangeFinset] using hp)
      q (by simpa [priorityRangeFinset] using hq)

/--
Base case for the priority induction: if all positions have the same priority,
then history-dependent winning implies positional winning.
-/
theorem positionalDeterminacy_of_constant_priority
    {p : Nat}
    (hpriority : ∀ position : G.Position, G.priority position = p) :
    G.PositionalDeterminacyStatement := by
  intro player start hwinning
  cases player with
  | even =>
      by_cases hpEven : DetParityAutomaton.NatEven p
      · exact
          G.positionalWinningRegion_of_constant_even_priority
            hpriority hpEven start
      · exact False.elim
          (G.not_winningRegion_even_of_constant_odd_priority
            hpriority hpEven start hwinning)
  | odd =>
      by_cases hpEven : DetParityAutomaton.NatEven p
      · exact False.elim
          (G.not_winningRegion_odd_of_constant_even_priority
            hpriority hpEven start hwinning)
      · exact
          G.positionalWinningRegion_of_constant_odd_priority
            hpriority hpEven start

/--
Base case in range form: if the set of priorities used by the arena is a
subsingleton, positionalization follows from the constant-priority theorem.
-/
theorem positionalDeterminacy_of_subsingleton_priority_range
    (hsubsingleton :
      ∀ p ∈ Set.range G.priority,
        ∀ q ∈ Set.range G.priority, p = q) :
    G.PositionalDeterminacyStatement := by
  intro player start hwinning
  have hpriority :
      ∀ position : G.Position, G.priority position = G.priority start := by
    intro position
    exact
      hsubsingleton
        (G.priority position) ⟨position, rfl⟩
        (G.priority start) ⟨start, rfl⟩
  exact
    G.positionalDeterminacy_of_constant_priority
      hpriority player start hwinning

/--
Cardinality form of the base case used by the finite-priority induction.
-/
theorem positionalDeterminacy_of_priorityRange_card_le_one
    (hcard : G.priorityRangeFinset.card ≤ 1) :
    G.PositionalDeterminacyStatement := by
  apply G.positionalDeterminacy_of_subsingleton_priority_range
  intro p hp q hq
  exact
    (Finset.card_le_one.mp hcard)
      p (by simpa [priorityRangeFinset] using hp)
      q (by simpa [priorityRangeFinset] using hq)

/--
Zielonka positional determinacy for countable parity games with finitely many
priorities.

The induction is on the number of occurring priorities.  In the favourable
minimum case, instead of iterating the second recursive call over a finite
position set, the proof takes the complement of the opponent's original
positional winning region as the final core.  Countability supplies a uniform
opponent strategy on the outside region, making the core a trap and making any
opponent win inside the core splice back to an original opponent positional
win, contradiction.
-/
theorem positionalGameDetermined :
    G.PositionalGameDeterminedStatement := by
  classical
  let P : Nat -> Prop :=
    fun n =>
      ∀ H : CountableParityGame.{u},
        H.priorityRangeFinset.card ≤ n ->
          H.PositionalGameDeterminedStatement
  have hP : ∀ n : Nat, P n := by
    intro n
    induction n with
    | zero =>
        intro H hcard
        exact H.positionalGameDetermined_of_priorityRange_card_le_one (by omega)
    | succ n ih =>
        intro H hcard
        by_cases hbase : H.priorityRangeFinset.card ≤ 1
        · exact H.positionalGameDetermined_of_priorityRange_card_le_one hbase
        · have hcardGt : 1 < H.priorityRangeFinset.card := by
            omega
          have hnonempty : H.priorityRangeFinset.Nonempty := by
            exact Finset.card_pos.mp (by omega)
          let priority : Nat := H.priorityRangeFinset.min' hnonempty
          let player : ParityPlayer := priorityOwner priority
          have hpriorityMemFinset :
              priority ∈ H.priorityRangeFinset := by
            simpa [priority] using
              Finset.min'_mem H.priorityRangeFinset hnonempty
          have hpriorityMem :
              priority ∈ Set.range H.priority := by
            exact (H.mem_priorityRangeFinset priority).mp hpriorityMemFinset
          have hpriorityLeast :
              ∀ position : H.Position, priority ≤ H.priority position := by
            intro position
            simpa [priority] using
              Finset.min'_le H.priorityRangeFinset (H.priority position)
                (by simp [priorityRangeFinset])
          have hpriorityOwner : priorityOwner priority = player := rfl
          let core : Set H.Position :=
            {position : H.Position |
              position ∉ H.PositionalWinningRegion player.other}
          let hcoreTrap : H.TrapFor player core := by
            simpa [core] using
              H.compl_positionalWinningRegion_trapFor_other player.other
          let coreGame := H.restrictToTrap player core hcoreTrap
          have hcoreCardLe :
              coreGame.priorityRangeFinset.card ≤
                H.priorityRangeFinset.card := by
            exact
              Finset.card_le_card
                (H.restrictToTrap_priorityRangeFinset_subset
                  player core hcoreTrap)
          have hcoreOpponentLift :
              ∀ start : coreGame.Position,
                start ∈ coreGame.PositionalWinningRegion player.other ->
                  False := by
            intro start hstartOpponent
            have horiginal :
                start.1 ∈ H.PositionalWinningRegion player.other := by
              exact
                H.lift_coreOpponentPositionalWinningRegion
                  (player := player)
                  (core := core)
                  (hcoreTrap := hcoreTrap)
                  (by rfl)
                  start.2
                  (by simpa [coreGame] using hstartOpponent)
            exact start.2 horiginal
          have hcoreAllPlayer :
              ∀ start : coreGame.Position,
                start ∈ coreGame.PositionalWinningRegion player := by
            by_cases hpriorityCore :
                priority ∈ Set.range coreGame.priority
            · let firstRegion : Set coreGame.Position :=
                {position : coreGame.Position |
                  ¬ coreGame.Attractor player
                    (coreGame.priorityClass priority) position}
              let hfirstTrap : coreGame.TrapFor player.other firstRegion :=
                coreGame.compl_attractor_trapFor_other player
                  (coreGame.priorityClass priority)
              let firstGame :=
                coreGame.restrictToTrap player.other firstRegion hfirstTrap
              have hfirstCardLtCore :
                  firstGame.priorityRangeFinset.card <
                    coreGame.priorityRangeFinset.card := by
                simpa [firstGame, firstRegion, hfirstTrap] using
                  coreGame.restrict_compl_attractor_priorityClass_card_lt
                    (player := player) (priority := priority) hpriorityCore
              have hfirstCardLt :
                  firstGame.priorityRangeFinset.card <
                    H.priorityRangeFinset.card := by
                exact lt_of_lt_of_le hfirstCardLtCore hcoreCardLe
              have hfirstDetermined :
                  firstGame.PositionalGameDeterminedStatement :=
                ih firstGame (by omega)
              have hfirstPointwise :
                  firstGame.PositionalDeterminacyStatement :=
                firstGame.positionalDeterminacy_of_positionalGameDetermined
                  hfirstDetermined
              have hnoOpponentTarget :
                  ∀ position : coreGame.Position,
                    position ∉
                      coreGame.liftedTrapWinningRegion
                        firstRegion hfirstTrap player.other := by
                intro position htarget
                rcases htarget with ⟨hpositionFirst, hwinningFirst⟩
                have hfirstPos :
                    (⟨position, hpositionFirst⟩ : firstGame.Position) ∈
                      firstGame.PositionalWinningRegion player.other :=
                  hfirstPointwise player.other
                    ⟨position, hpositionFirst⟩ hwinningFirst
                have hcoreOpponent :
                    position ∈ coreGame.PositionalWinningRegion player.other := by
                  exact
                    coreGame.liftTrap_positionalWinningRegion
                      (player := player.other)
                      (region := firstRegion)
                      (htrap := hfirstTrap)
                      (start := ⟨position, hpositionFirst⟩)
                      hfirstPos
                exact hcoreOpponentLift position hcoreOpponent
              rcases
                  coreGame.exists_strategy_winning_all_of_favorable_minimum_of_no_opponent_target
                    (player := player)
                    (priority := priority)
                    (by
                      intro position
                      simpa [coreGame] using hpriorityLeast position.1)
                    hpriorityOwner
                    hfirstDetermined
                    hnoOpponentTarget with
                ⟨coreStrategy, hcoreStrategy⟩
              intro start
              exact ⟨coreStrategy, hcoreStrategy start⟩
            · have hcoreCardLt :
                  coreGame.priorityRangeFinset.card <
                    H.priorityRangeFinset.card := by
                exact
                  H.restrictToTrap_priorityRangeFinset_card_lt_of_omits
                    (player := player)
                    (region := core)
                    (htrap := hcoreTrap)
                    hpriorityMem
                    (by
                      intro position hposition hpriorityEq
                      exact hpriorityCore
                        ⟨⟨position, hposition⟩, by simpa [coreGame] using hpriorityEq⟩)
              have hcoreDetermined :
                  coreGame.PositionalGameDeterminedStatement :=
                ih coreGame (by omega)
              intro start
              rcases
                  coreGame.positionalGameDetermined_player_or_other
                    hcoreDetermined player start with hplayer | hopponent
              · exact hplayer
              · exact False.elim (hcoreOpponentLift start hopponent)
          intro start
          by_cases hopponent :
              start ∈ H.PositionalWinningRegion player.other
          · cases hplayerEq : player with
            | even =>
                exact Or.inr (by simpa [hplayerEq] using hopponent)
            | odd =>
                exact Or.inl (by simpa [hplayerEq] using hopponent)
          · have hstartCore : start ∈ core := by
              simpa [core] using hopponent
            have hcorePlayer :
                (⟨start, hstartCore⟩ : coreGame.Position) ∈
                  coreGame.PositionalWinningRegion player :=
              hcoreAllPlayer ⟨start, hstartCore⟩
            have hplayerOriginal :
                start ∈ H.PositionalWinningRegion player := by
              exact
                H.liftTrap_positionalWinningRegion
                  (player := player)
                  (region := core)
                  (htrap := hcoreTrap)
                  (start := ⟨start, hstartCore⟩)
                  hcorePlayer
            cases hplayerEq : player with
            | even =>
                exact Or.inl (by simpa [hplayerEq] using hplayerOriginal)
            | odd =>
                exact Or.inr (by simpa [hplayerEq] using hplayerOriginal)
  exact hP G.priorityRangeFinset.card G le_rfl

/-- Pointwise positionalization follows from countable positional game determinacy. -/
theorem positionalDeterminacy :
    G.PositionalDeterminacyStatement :=
  G.positionalDeterminacy_of_positionalGameDetermined
    G.positionalGameDetermined

/-- Uniform positionalization follows by countable uniformization. -/
theorem uniformPositionalDeterminacy :
    G.UniformPositionalDeterminacyStatement :=
  G.uniformPositionalDeterminacy_of_positionalGameDetermined
    G.positionalGameDetermined

/--
Finite-position Zielonka closure.  This is the standard finite-arena descent:
the first recursive call strictly decreases the priority range, while the
second recursive call, when needed, removes a nonempty opponent attractor and
therefore strictly decreases the finite position set.

This finite proof is retained as a sanity-check specialization of the local
Zielonka step; the theorem above is the countable closure.
-/
theorem positionalGameDetermined_of_finite_position
    [Fintype G.Position] :
    G.PositionalGameDeterminedStatement := by
  classical
  let complexity (H : CountableParityGame.{u}) [Fintype H.Position] : Nat :=
    H.priorityRangeFinset.card + Fintype.card H.Position
  let P : Nat -> Prop :=
    fun n =>
      ∀ (H : CountableParityGame.{u}) [Fintype H.Position],
        complexity H ≤ n -> H.PositionalGameDeterminedStatement
  have hP : ∀ n : Nat, P n := by
    intro n
    induction n with
    | zero =>
        intro H _hfinite hcomplexity
        have hcard : H.priorityRangeFinset.card ≤ 1 := by
          have hzero : H.priorityRangeFinset.card = 0 := by
            dsimp [complexity] at hcomplexity
            omega
          omega
        exact H.positionalGameDetermined_of_priorityRange_card_le_one hcard
    | succ n ih =>
        intro H _hfinite hcomplexity
        by_cases hbase : H.priorityRangeFinset.card ≤ 1
        · exact H.positionalGameDetermined_of_priorityRange_card_le_one hbase
        · have hcardGt : 1 < H.priorityRangeFinset.card := by
            omega
          have hnonempty : H.priorityRangeFinset.Nonempty := by
            exact Finset.card_pos.mp (by omega)
          let priority : Nat := H.priorityRangeFinset.min' hnonempty
          let player : ParityPlayer := priorityOwner priority
          have hpriorityMemFinset :
              priority ∈ H.priorityRangeFinset := by
            simpa [priority] using
              Finset.min'_mem H.priorityRangeFinset hnonempty
          have hpriorityMem :
              priority ∈ Set.range H.priority := by
            exact (H.mem_priorityRangeFinset priority).mp hpriorityMemFinset
          have hpriorityLeast :
              ∀ position : H.Position, priority ≤ H.priority position := by
            intro position
            simpa [priority] using
              Finset.min'_le H.priorityRangeFinset (H.priority position)
                (by simp [priorityRangeFinset])
          have hpriorityOwner : priorityOwner priority = player := rfl
          let firstRegion : Set H.Position :=
            {position : H.Position |
              ¬ H.Attractor player (H.priorityClass priority) position}
          let hfirstTrap : H.TrapFor player.other firstRegion :=
            H.compl_attractor_trapFor_other player (H.priorityClass priority)
          let firstGame := H.restrictToTrap player.other firstRegion hfirstTrap
          haveI : Fintype firstGame.Position := by
            dsimp [firstGame, CountableParityGame.restrictToTrap]
            infer_instance
          have hfirstPriorityLt :
              firstGame.priorityRangeFinset.card < H.priorityRangeFinset.card := by
            simpa [firstGame, firstRegion, hfirstTrap] using
              H.restrict_compl_attractor_priorityClass_card_lt
                (player := player) (priority := priority) hpriorityMem
          have hfirstPositionLe :
              Fintype.card firstGame.Position ≤ Fintype.card H.Position := by
            exact
              Fintype.card_le_of_embedding
                (Function.Embedding.subtype
                  (fun position : H.Position => position ∈ firstRegion))
          have hfirstComplexityLt :
              complexity firstGame < complexity H := by
            dsimp [complexity]
            omega
          have hfirstDetermined :
              firstGame.PositionalGameDeterminedStatement := by
            exact ih firstGame (by omega)
          let target : Set H.Position :=
            H.liftedTrapWinningRegion firstRegion hfirstTrap player.other
          by_cases hnoOpponentTarget :
              ∀ position : H.Position, position ∉ target
          · have hfirstDeterminedLocal :
                (H.restrictToTrap player.other firstRegion hfirstTrap).PositionalGameDeterminedStatement := by
              simpa [firstGame] using hfirstDetermined
            rcases
                H.exists_strategy_winning_all_of_favorable_minimum_of_no_opponent_target
                  (player := player)
                  (priority := priority)
                  hpriorityLeast hpriorityOwner
                  hfirstDeterminedLocal
                  (by
                    intro position hposition
                    exact hnoOpponentTarget position
                      (by simpa [target] using hposition)) with
              ⟨strategy, hstrategy⟩
            intro start
            have hplayerPos :
                start ∈ H.PositionalWinningRegion player :=
              ⟨strategy, hstrategy start⟩
            cases hplayerEq : player with
            | even =>
                exact Or.inl (by simpa [hplayerEq] using hplayerPos)
            | odd =>
                exact Or.inr (by simpa [hplayerEq] using hplayerPos)
          · have htargetNonempty : ∃ position : H.Position, position ∈ target := by
              push Not at hnoOpponentTarget
              exact hnoOpponentTarget
            let remaining : Set H.Position :=
              {position : H.Position |
                ¬ H.Attractor player.other target position}
            let hremainingTrap : H.TrapFor player remaining :=
              H.compl_opponent_attractor_trapFor player target
            let remainingGame := H.restrictToTrap player remaining hremainingTrap
            haveI : Fintype remainingGame.Position := by
              dsimp [remainingGame, CountableParityGame.restrictToTrap]
              infer_instance
            rcases htargetNonempty with ⟨targetPosition, htargetPosition⟩
            have hnotRemainingTarget : targetPosition ∉ remaining := by
              intro hremaining
              exact hremaining (CountableParityGame.Attractor.target htargetPosition)
            have hremainingPositionLt :
                Fintype.card remainingGame.Position < Fintype.card H.Position := by
              exact
                Fintype.card_lt_of_injective_of_notMem
                  (fun position : remainingGame.Position => position.1)
                  (by
                    intro left right hleftRight
                    exact Subtype.ext hleftRight)
                  (b := targetPosition)
                  (by
                    intro hmem
                    rcases hmem with ⟨position, hposition⟩
                    have hpositionMem : position.1 ∈ remaining := by
                      simpa [remainingGame, CountableParityGame.restrictToTrap]
                        using position.2
                    exact hnotRemainingTarget
                      (by
                        simpa [hposition] using hpositionMem))
            have hremainingPriorityLe :
                remainingGame.priorityRangeFinset.card ≤
                  H.priorityRangeFinset.card := by
              exact
                Finset.card_le_card
                  (H.restrictToTrap_priorityRangeFinset_subset
                    player remaining hremainingTrap)
            have hremainingComplexityLt :
                complexity remainingGame < complexity H := by
              dsimp [complexity]
              omega
            have hremainingDetermined :
                remainingGame.PositionalGameDeterminedStatement := by
              exact ih remainingGame (by omega)
            have hremainingDeterminedLocal :
                (H.restrictToTrap player
                  {position : H.Position |
                    ¬ H.Attractor player.other
                      (H.liftedTrapWinningRegion firstRegion hfirstTrap player.other)
                      position}
                  (H.compl_opponent_attractor_trapFor player
                    (H.liftedTrapWinningRegion firstRegion hfirstTrap player.other))).PositionalGameDeterminedStatement := by
              simpa [remainingGame, remaining, target, hremainingTrap] using
                hremainingDetermined
            have hfirstDeterminedLocal :
                (H.restrictToTrap player.other firstRegion hfirstTrap).PositionalGameDeterminedStatement := by
              simpa [firstGame] using hfirstDetermined
            exact
              H.positionalGameDetermined_of_favorable_minimum_step
                (player := player)
                (priority := priority)
                hpriorityLeast hpriorityOwner
                hfirstDeterminedLocal
                hremainingDeterminedLocal
  exact hP (complexity G) G (by omega)

end CountableParityGame

end DistributedSynthesis
