/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmUniformizationGame
import DistributedSynthesis.Formalizations.Theorem.ThmJournalBlockMonitors

/-!
# Tracking a winning strategy through the uniformization game

This file builds Even's history strategy of the uniformization game
that tracks a given distributed strategy (step W1 of the heart plan,
first stage): the tracking memory reconstructs the real history of
the play, the strategy commits it at boundaries and answers every
staged position with the tracked strategy's real response, and along
every consistent play the reconstruction is exact
(`tracks_of_consistent`): the memory is a strategy-generated real
history, the position components agree with it, and every stored
output is the tracked strategy's output on the reconstruction.

The staged responses realize the fringe discipline: within a block
the receiver's response is shared between the continue and close
outcomes, the closing stage fixes the subordinate's synchronizing
response together with its hypothetical no-receive response for a
direct reversal, and within a reversed block all four lambda-table
values are staged, each shared across exactly the round types its
process cannot distinguish.

The reconstruction is what makes the later parity transfer possible:
a consistent play of the tracking strategy is, round for round, a
real play of the tracked strategy against the environment sequence
read off the play, so the play's design-D3 priorities are the run
priorities and block minima of an accepted word.  That transfer is
the second stage of W1.
-/

namespace DistributedSynthesis

universe u v x y s

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

/-- The synchronizing environment move of a round. -/
def bothEnvironment (move : In₁ × In₂) : EnvironmentRound In₁ In₂ where
  inputOne := move.1
  inputTwo := move.2
  graph := Graph.both

/--
The receiver of a left round cannot distinguish it from a
synchronizing round: the views agree (`thm:onebitfringe`).
-/
theorem nextView_one_leftEnvironment
    {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂) (move : In₁ × In₂) :
    nextView Proc.one h (leftEnvironment move) =
      nextView Proc.one h (bothEnvironment move) :=
  rfl

/--
The receiver of a right round cannot distinguish it from a
synchronizing round: the views agree (`thm:onebitfringe`).
-/
theorem nextView_two_rightEnvironment
    {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂) (move : In₁ × In₂) :
    nextView Proc.two h (rightEnvironment (move.2, move.1)) =
      nextView Proc.two h (bothEnvironment move) :=
  rfl

/-- A history at which the next block can start: empty, or closed by
a synchronizing round. -/
def BoundaryReady (h : History In₁ In₂ Graph Out₁ Out₂) : Prop :=
  ∀ r ∈ h.getLast?, r.graph = Graph.both

@[simp]
theorem boundaryReady_nil :
    BoundaryReady ([] : History In₁ In₂ Graph Out₁ Out₂) := by
  intro r hr
  simp at hr

theorem boundaryReady_append
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hgraph : r.graph = Graph.both) :
    BoundaryReady (History.append h r) := by
  intro r' hr'
  rw [show History.append h r = h ++ [r] from rfl,
    List.getLast?_concat] at hr'
  simp at hr'
  exact hr' ▸ hgraph

namespace DetParityAutomaton

variable
  {A :
    DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂)}

open UniformizationPosition

section Tracking

variable (σ : StrategyPair In₁ In₂ Out₁ Out₂)
variable [Inhabited In₁] [Inhabited In₂]

/--
One step of the tracking memory: when the two adjacent positions
witness a completed round, replay it as the tracked strategy's round
on the reconstructed history; the second component records the
current position.
-/
def trackUpdate
    (mem :
      History In₁ In₂ Graph Out₁ Out₂ ×
        UniformizationPosition (In₁ := In₁) A)
    (p : UniformizationPosition (In₁ := In₁) A) :
    History In₁ In₂ Graph Out₁ Out₂ ×
      UniformizationPosition (In₁ := In₁) A :=
  match mem.2, p with
  | .openingResolve _ _ move _ _, .bnd _ =>
      (History.append mem.1 (nextRound σ mem.1 (bothEnvironment move)), p)
  | .openingResolve _ _ move _ _, .blockL _ _ _ _ =>
      (History.append mem.1 (nextRound σ mem.1 (leftEnvironment move)), p)
  | .openingResolve _ _ move _ _, .blockR _ _ _ _ =>
      (History.append mem.1
        (nextRound σ mem.1 (rightEnvironment (move.2, move.1))), p)
  | .resolveL _ _ _ _ _ move _, .blockL _ _ _ _ =>
      (History.append mem.1 (nextRound σ mem.1 (leftEnvironment move)), p)
  | .closeResolveL _ _ _ _ _ move _ _, .bnd _ =>
      (History.append mem.1 (nextRound σ mem.1 (bothEnvironment move)), p)
  | .closeResolveL _ _ _ _ _ move _ _, .revCommitR _ _ _ =>
      (History.append mem.1
        (nextRound σ mem.1 (rightEnvironment (move.2, move.1))), p)
  | .resolveR _ _ _ _ _ move _, .blockR _ _ _ _ =>
      (History.append mem.1
        (nextRound σ mem.1 (rightEnvironment (move.2, move.1))), p)
  | .closeResolveR _ _ _ _ _ move _ _, .bnd _ =>
      (History.append mem.1 (nextRound σ mem.1 (bothEnvironment move)), p)
  | .closeResolveR _ _ _ _ _ move _ _, .revCommitL _ _ _ =>
      (History.append mem.1 (nextRound σ mem.1 (leftEnvironment move)), p)
  | .revResolveL _ _ _ _ _ _ _ move _ _, .revBlockL _ _ _ _ _ _ =>
      (History.append mem.1 (nextRound σ mem.1 (leftEnvironment move)), p)
  | .revResolveL _ _ _ _ _ _ _ move _ _, .bnd _ =>
      (History.append mem.1 (nextRound σ mem.1 (bothEnvironment move)), p)
  | .revResolveL _ _ _ _ _ _ _ move _ _, .revCommitR _ _ _ =>
      (History.append mem.1
        (nextRound σ mem.1 (rightEnvironment (move.2, move.1))), p)
  | .revResolveR _ _ _ _ _ _ _ move _ _, .revBlockR _ _ _ _ _ _ =>
      (History.append mem.1
        (nextRound σ mem.1 (rightEnvironment (move.2, move.1))), p)
  | .revResolveR _ _ _ _ _ _ _ move _ _, .bnd _ =>
      (History.append mem.1 (nextRound σ mem.1 (bothEnvironment move)), p)
  | .revResolveR _ _ _ _ _ _ _ move _ _, .revCommitL _ _ _ =>
      (History.append mem.1 (nextRound σ mem.1 (leftEnvironment move)), p)
  | _, _ => (mem.1, p)

omit [Inhabited In₁] [Inhabited In₂] in
theorem trackUpdate_snd
    (mem :
      History In₁ In₂ Graph Out₁ Out₂ ×
        UniformizationPosition (In₁ := In₁) A)
    (p : UniformizationPosition (In₁ := In₁) A) :
    (trackUpdate σ mem p).2 = p := by
  rcases mem with ⟨h, prev⟩
  cases prev <;> cases p <;> rfl

/-- The tracking memory of a game prefix. -/
def trackMemory :
    (n : Nat) ->
      (Fin (n + 1) -> UniformizationPosition (In₁ := In₁) A) ->
        History In₁ In₂ Graph Out₁ Out₂ ×
          UniformizationPosition (In₁ := In₁) A
  | 0, pref => ([], pref ⟨0, Nat.zero_lt_succ 0⟩)
  | n + 1, pref =>
      trackUpdate σ
        (trackMemory n (fun i => pref ⟨i.1, by omega⟩))
        (pref ⟨n + 1, by omega⟩)

/-- The tracking memory along an infinite path. -/
def pathMemory
    (path : Nat -> UniformizationPosition (In₁ := In₁) A) :
    Nat ->
      History In₁ In₂ Graph Out₁ Out₂ ×
        UniformizationPosition (In₁ := In₁) A
  | 0 => ([], path 0)
  | n + 1 => trackUpdate σ (pathMemory path n) (path (n + 1))

section
omit [Inhabited In₁] [Inhabited In₂]

theorem trackMemory_prefixOfPath
    (path : Nat -> UniformizationPosition (In₁ := In₁) A) :
    ∀ n : Nat,
      trackMemory σ n (fun i => path i.1) = pathMemory σ path n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      show
        trackUpdate σ (trackMemory σ n (fun i => path i.1)) (path (n + 1)) =
          trackUpdate σ (pathMemory σ path n) (path (n + 1))
      rw [ih]

theorem pathMemory_snd
    (path : Nat -> UniformizationPosition (In₁ := In₁) A) (n : Nat) :
    (pathMemory σ path n).2 = path n := by
  cases n with
  | zero => rfl
  | succ n => exact trackUpdate_snd σ _ _

/-- The successor memory, with the previous position made explicit. -/
theorem pathMemory_fst_succ
    (path : Nat -> UniformizationPosition (In₁ := In₁) A) (n : Nat) :
    (pathMemory σ path (n + 1)).1 =
      (trackUpdate σ ((pathMemory σ path n).1, path n) (path (n + 1))).1 := by
  have h2 := pathMemory_snd σ path n
  show (trackUpdate σ (pathMemory σ path n) (path (n + 1))).1 = _
  rcases hm : pathMemory σ path n with ⟨H, prev⟩
  rw [hm] at h2
  simp only at h2
  subst h2
  rfl

end

/--
The tracking move: commit the reconstructed history at boundaries and
answer every staged position with the tracked strategy's response on
the reconstruction.
-/
noncomputable def trackingMove [Inhabited Out₁] [Inhabited Out₂]
    (mem : History In₁ In₂ Graph Out₁ Out₂)
    (p : UniformizationPosition (In₁ := In₁) A) :
    UniformizationPosition (In₁ := In₁) A :=
  match p with
  | .bnd atom => .committed atom mem
  | .opening atom h move =>
      .openingResolve atom h move
        (σ.one (nextView Proc.one h (bothEnvironment move)))
        (σ.two (nextView Proc.two h (bothEnvironment move)))
  | .blockL h word state minState =>
      .blockEnvL h word state minState
        (fun inputOne =>
          σ.one
            (nextView Proc.one mem
              (rightEnvironment (default, inputOne))))
  | .recvL h word state minState revTable move =>
      .resolveL h word state minState revTable move
        (σ.one (nextView Proc.one mem (leftEnvironment move)))
  | .closeL h word state minState revTable move outOne =>
      .closeResolveL h word state minState revTable move outOne
        (σ.two (nextView Proc.two mem (bothEnvironment move)))
  | .blockR h word state minState =>
      .blockEnvR h word state minState
        (fun inputTwo =>
          σ.two
            (nextView Proc.two mem
              (leftEnvironment (default, inputTwo))))
  | .recvR h word state minState revTable move =>
      .resolveR h word state minState revTable move
        (σ.two (nextView Proc.two mem (rightEnvironment (move.2, move.1))))
  | .closeR h word state minState revTable move outTwo =>
      .closeResolveR h word state minState revTable move outTwo
        (σ.one (nextView Proc.one mem (bothEnvironment move)))
  | .revCommitL word entryState entryMin =>
      .revBlockL mem word entryState entryMin entryState entryMin
  | .revBlockL hc word entryState entryMin state minState =>
      .revEnvL hc word entryState entryMin state minState
        (fun inputOne =>
          σ.one
            (nextView Proc.one mem
              (rightEnvironment (default, inputOne))))
  | .revRecvL hc word entryState entryMin state minState sendTable
      move =>
      .revResolveL hc word entryState entryMin state minState
        sendTable move
        (σ.one (nextView Proc.one mem (bothEnvironment move)))
        (σ.two (nextView Proc.two mem (bothEnvironment move)))
  | .revCommitR word entryState entryMin =>
      .revBlockR mem word entryState entryMin entryState entryMin
  | .revBlockR hc word entryState entryMin state minState =>
      .revEnvR hc word entryState entryMin state minState
        (fun inputTwo =>
          σ.two
            (nextView Proc.two mem
              (leftEnvironment (default, inputTwo))))
  | .revRecvR hc word entryState entryMin state minState sendTable
      move =>
      .revResolveR hc word entryState entryMin state minState
        sendTable move
        (σ.one (nextView Proc.one mem (bothEnvironment move)))
        (σ.two (nextView Proc.two mem (bothEnvironment move)))
  | other => Classical.choose (uniformizationStep_total σ other)

variable [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂]
variable [Countable In₁] [Countable In₂] [Countable Out₁] [Countable Out₂]

/--
The tracking strategy: Even's history strategy of the uniformization
game induced by a distributed strategy.
-/
noncomputable def trackingStrategy :
    (uniformizationGame A σ).Strategy ParityPlayer.even where
  move n pref :=
    trackingMove σ (trackMemory σ n pref).1
      ((uniformizationGame A σ).prefixLast pref)

theorem trackingStrategy_legal :
    (trackingStrategy (A := A) σ).Legal := by
  intro n pref _hlegal howner
  show
    uniformizationStep σ ((uniformizationGame A σ).prefixLast pref)
      (trackingMove σ (trackMemory σ n pref).1
        ((uniformizationGame A σ).prefixLast pref))
  rcases hpos : (uniformizationGame A σ).prefixLast pref with
    atom | ⟨atom, h⟩ | ⟨atom, h, move⟩ | ⟨atom, h, move, outOne, outTwo⟩ |
    ⟨h, word, state, minState⟩ | ⟨h, word, state, minState, tbl⟩ |
    ⟨h, word, state, minState, tbl, move⟩ |
    ⟨h, word, state, minState, tbl, move, outOne⟩ |
    ⟨h, word, state, minState, tbl, move, outOne⟩ |
    ⟨h, word, state, minState, tbl, move, outOne, outTwo⟩ |
    ⟨h, word, state, minState⟩ | ⟨h, word, state, minState, tbl⟩ |
    ⟨h, word, state, minState, tbl, move⟩ |
    ⟨h, word, state, minState, tbl, move, outTwo⟩ |
    ⟨h, word, state, minState, tbl, move, outTwo⟩ |
    ⟨h, word, state, minState, tbl, move, outTwo, outOne⟩ |
    ⟨word, eqs, ems⟩ | ⟨hc, word, eqs, ems, state, minState⟩ |
    ⟨hc, word, eqs, ems, state, minState, tbl⟩ |
    ⟨hc, word, eqs, ems, state, minState, tbl, move⟩ |
    ⟨hc, word, eqs, ems, state, minState, tbl, move, o1r, o2r⟩ |
    ⟨word, eqs, ems⟩ | ⟨hc, word, eqs, ems, state, minState⟩ |
    ⟨hc, word, eqs, ems, state, minState, tbl⟩ |
    ⟨hc, word, eqs, ems, state, minState, tbl, move⟩ |
    ⟨hc, word, eqs, ems, state, minState, tbl, move, o1r, o2r⟩
  · exact ⟨_, rfl⟩
  · rw [hpos] at howner
    exact absurd howner (by simp [uniformizationGame, uniformizationOwner])
  · exact ⟨_, _, rfl⟩
  · rw [hpos] at howner
    exact absurd howner (by simp [uniformizationGame, uniformizationOwner])
  · exact ⟨_, rfl⟩
  · rw [hpos] at howner
    exact absurd howner (by simp [uniformizationGame, uniformizationOwner])
  · exact ⟨_, rfl⟩
  · rw [hpos] at howner
    exact absurd howner (by simp [uniformizationGame, uniformizationOwner])
  · exact ⟨_, rfl⟩
  · rw [hpos] at howner
    exact absurd howner (by simp [uniformizationGame, uniformizationOwner])
  · exact ⟨_, rfl⟩
  · rw [hpos] at howner
    exact absurd howner (by simp [uniformizationGame, uniformizationOwner])
  · exact ⟨_, rfl⟩
  · rw [hpos] at howner
    exact absurd howner (by simp [uniformizationGame, uniformizationOwner])
  · exact ⟨_, rfl⟩
  · rw [hpos] at howner
    exact absurd howner (by simp [uniformizationGame, uniformizationOwner])
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · rw [hpos] at howner
    exact absurd howner (by simp [uniformizationGame, uniformizationOwner])
  · exact ⟨_, _, rfl⟩
  · rw [hpos] at howner
    exact absurd howner (by simp [uniformizationGame, uniformizationOwner])
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · rw [hpos] at howner
    exact absurd howner (by simp [uniformizationGame, uniformizationOwner])
  · exact ⟨_, _, rfl⟩
  · rw [hpos] at howner
    exact absurd howner (by simp [uniformizationGame, uniformizationOwner])

theorem trackingStrategy_move_eq
    (path : Nat -> UniformizationPosition (In₁ := In₁) A) (n : Nat) :
    (trackingStrategy (A := A) σ).move n
        ((uniformizationGame A σ).prefixOfPath path n) =
      trackingMove σ (pathMemory σ path n).1 (path n) := by
  show
    trackingMove σ (trackMemory σ n (fun i => path i.1)).1 (path n) =
      trackingMove σ (pathMemory σ path n).1 (path n)
  rw [trackMemory_prefixOfPath]

end Tracking

section Invariant

variable (σ : StrategyPair In₁ In₂ Out₁ Out₂)
variable [Inhabited In₁] [Inhabited In₂]

/--
Within-block reconstruction data of a left block: the boundary prefix
is strategy-generated and boundary-ready, and the reconstruction
extends it by the block's rounds, whose sender word is the recorded
one and whose final state is the tracked one.
-/
def TracksBlockL (H h : History In₁ In₂ Graph Out₁ Out₂)
    (word : List In₂) (state : A.State) : Prop :=
  StrategyGeneratedPrefix σ h ∧ BoundaryReady h ∧
    ∃ moves : List (In₁ × In₂),
      moves ≠ [] ∧
        H = extendPrefix σ h (moves.map leftEnvironment) ∧
        word = senderWord moves ∧
        state = A.historyState H

/-- Within-block reconstruction data of a right block: the mirror. -/
def TracksBlockR (H h : History In₁ In₂ Graph Out₁ Out₂)
    (word : List In₁) (state : A.State) : Prop :=
  StrategyGeneratedPrefix σ h ∧ BoundaryReady h ∧
    ∃ moves : List (In₂ × In₁),
      moves ≠ [] ∧
        H = extendPrefix σ h (moves.map rightEnvironment) ∧
        word = senderWord moves ∧
        state = A.historyState H

/--
Reconstruction data at a chain handoff: the reconstruction is the
strategy-generated real history, which already contains the reversal
round, and the frozen entry state is its automaton state.
-/
def TracksRev (H : History In₁ In₂ Graph Out₁ Out₂)
    (state : A.State) : Prop :=
  StrategyGeneratedPrefix σ H ∧ state = A.historyState H

/--
Within-segment reconstruction data of a reversed left block: the
committed virtual view is strategy-generated and contains the
reversal round; the reconstruction extends it by the segment's
continuation rounds; the segment word is the entry direction followed
by the recorded sender word; the frozen entry state is the
commitment's automaton state and the tracked state the
reconstruction's.
-/
def TracksRevL (H hc : History In₁ In₂ Graph Out₁ Out₂)
    (word : List In₂) (entryState state : A.State) : Prop :=
  StrategyGeneratedPrefix σ hc ∧
    entryState = A.historyState hc ∧
    ∃ (d : In₂) (moves : List (In₁ × In₂)),
      word = d :: senderWord moves ∧
        H = extendPrefix σ hc (moves.map leftEnvironment) ∧
        state = A.historyState H

/-- Within-segment reconstruction data of a reversed right block:
the mirror. -/
def TracksRevR (H hc : History In₁ In₂ Graph Out₁ Out₂)
    (word : List In₁) (entryState state : A.State) : Prop :=
  StrategyGeneratedPrefix σ hc ∧
    entryState = A.historyState hc ∧
    ∃ (d : In₁) (moves : List (In₂ × In₁)),
      word = d :: senderWord moves ∧
        H = extendPrefix σ hc (moves.map rightEnvironment) ∧
        state = A.historyState H

/-- The correct per-round reversal table of a left block: process
one's no-receive responses on the reconstruction. -/
def RevTableL (H : History In₁ In₂ Graph Out₁ Out₂)
    (tbl : In₁ -> Out₁) : Prop :=
  tbl = fun inputOne =>
    σ.one (nextView Proc.one H (rightEnvironment (default, inputOne)))

/-- The correct per-round reversal table of a right block: the
mirror. -/
def RevTableR (H : History In₁ In₂ Graph Out₁ Out₂)
    (tbl : In₂ -> Out₂) : Prop :=
  tbl = fun inputTwo =>
    σ.two (nextView Proc.two H (leftEnvironment (default, inputTwo)))

/--
The reconstruction invariant: the memory is the real history of the
play, position components agree with it, and every stored output or
table is the tracked strategy's response on the reconstruction.
-/
def Tracks (H : History In₁ In₂ Graph Out₁ Out₂) :
    UniformizationPosition (In₁ := In₁) A -> Prop
  | .bnd atom =>
      StrategyGeneratedPrefix σ H ∧ BoundaryReady H ∧
        atom.1 = A.historyState H
  | .committed atom h =>
      h = H ∧ StrategyGeneratedPrefix σ H ∧ BoundaryReady H ∧
        atom.1 = A.historyState H
  | .opening atom h _ =>
      h = H ∧ StrategyGeneratedPrefix σ H ∧ BoundaryReady H ∧
        atom.1 = A.historyState H
  | .openingResolve atom h move outOne outTwo =>
      h = H ∧ StrategyGeneratedPrefix σ H ∧ BoundaryReady H ∧
        atom.1 = A.historyState H ∧
        outOne = σ.one (nextView Proc.one H (bothEnvironment move)) ∧
        outTwo = σ.two (nextView Proc.two H (bothEnvironment move))
  | .blockL h word state _ => TracksBlockL σ H h word state
  | .blockEnvL h word state _ tbl =>
      TracksBlockL σ H h word state ∧ RevTableL σ H tbl
  | .recvL h word state _ tbl _ =>
      TracksBlockL σ H h word state ∧ RevTableL σ H tbl
  | .resolveL h word state _ tbl move outOne =>
      TracksBlockL σ H h word state ∧ RevTableL σ H tbl ∧
        outOne = σ.one (nextView Proc.one H (leftEnvironment move))
  | .closeL h word state _ tbl move outOne =>
      TracksBlockL σ H h word state ∧ RevTableL σ H tbl ∧
        outOne = σ.one (nextView Proc.one H (leftEnvironment move))
  | .closeResolveL h word state _ tbl move outOne outTwo =>
      TracksBlockL σ H h word state ∧ RevTableL σ H tbl ∧
        outOne = σ.one (nextView Proc.one H (leftEnvironment move)) ∧
        outTwo = σ.two (nextView Proc.two H (bothEnvironment move))
  | .blockR h word state _ => TracksBlockR σ H h word state
  | .blockEnvR h word state _ tbl =>
      TracksBlockR σ H h word state ∧ RevTableR σ H tbl
  | .recvR h word state _ tbl _ =>
      TracksBlockR σ H h word state ∧ RevTableR σ H tbl
  | .resolveR h word state _ tbl move outTwo =>
      TracksBlockR σ H h word state ∧ RevTableR σ H tbl ∧
        outTwo =
          σ.two (nextView Proc.two H (rightEnvironment (move.2, move.1)))
  | .closeR h word state _ tbl move outTwo =>
      TracksBlockR σ H h word state ∧ RevTableR σ H tbl ∧
        outTwo =
          σ.two (nextView Proc.two H (rightEnvironment (move.2, move.1)))
  | .closeResolveR h word state _ tbl move outTwo outOne =>
      TracksBlockR σ H h word state ∧ RevTableR σ H tbl ∧
        outTwo =
          σ.two
            (nextView Proc.two H (rightEnvironment (move.2, move.1))) ∧
        outOne = σ.one (nextView Proc.one H (bothEnvironment move))
  | .revCommitL word entryState _ =>
      TracksRev σ H entryState ∧ ∃ d : In₂, word = [d]
  | .revBlockL hc word entryState _ state _ =>
      TracksRevL σ H hc word entryState state
  | .revEnvL hc word entryState _ state _ tbl =>
      TracksRevL σ H hc word entryState state ∧ RevTableL σ H tbl
  | .revRecvL hc word entryState _ state _ tbl _ =>
      TracksRevL σ H hc word entryState state ∧ RevTableL σ H tbl
  | .revResolveL hc word entryState _ state _ tbl move o1r o2r =>
      TracksRevL σ H hc word entryState state ∧ RevTableL σ H tbl ∧
        o1r = σ.one (nextView Proc.one H (bothEnvironment move)) ∧
        o2r = σ.two (nextView Proc.two H (bothEnvironment move))
  | .revCommitR word entryState _ =>
      TracksRev σ H entryState ∧ ∃ d : In₁, word = [d]
  | .revBlockR hc word entryState _ state _ =>
      TracksRevR σ H hc word entryState state
  | .revEnvR hc word entryState _ state _ tbl =>
      TracksRevR σ H hc word entryState state ∧ RevTableR σ H tbl
  | .revRecvR hc word entryState _ state _ tbl _ =>
      TracksRevR σ H hc word entryState state ∧ RevTableR σ H tbl
  | .revResolveR hc word entryState _ state _ tbl move o1r o2r =>
      TracksRevR σ H hc word entryState state ∧ RevTableR σ H tbl ∧
        o1r = σ.one (nextView Proc.one H (bothEnvironment move)) ∧
        o2r = σ.two (nextView Proc.two H (bothEnvironment move))

variable [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂]
variable [Countable In₁] [Countable In₂] [Countable Out₁] [Countable Out₂]

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Countable In₁] [Countable In₂] [Countable Out₁] [Countable Out₂] in
/-- Strategy generation extends along block rounds. -/
theorem strategyGenerated_extendPrefix
    {h : History In₁ In₂ Graph Out₁ Out₂}
    (hgen : StrategyGeneratedPrefix σ h)
    (envs : List (EnvironmentRound In₁ In₂)) :
    StrategyGeneratedPrefix σ (extendPrefix σ h envs) := by
  induction envs using List.reverseRecOn with
  | nil => exact hgen
  | append_singleton envs env ih =>
      rw [extendPrefix_snoc]
      exact StrategyGeneratedPrefix.append ih _

/--
Along every play of the tracking strategy, the tracking memory is an
exact reconstruction: the invariant holds at every round.
-/
theorem tracks_of_consistent
    (path : Nat -> UniformizationPosition (In₁ := In₁) A)
    (hplay :
      (uniformizationGame A σ).PlayFrom
        (.bnd (A.initial, A.initial)) path)
    (hcons :
      CountableParityGame.Strategy.Consistent
        (G := uniformizationGame A σ) (trackingStrategy σ) path) :
    ∀ n : Nat, Tracks σ (pathMemory σ path n).1 (path n) := by
  intro n
  induction n with
  | zero =>
      have hstart : path 0 = .bnd (A.initial, A.initial) := hplay.1
      rw [hstart]
      exact ⟨StrategyGeneratedPrefix.empty, boundaryReady_nil, rfl⟩
  | succ n ih =>
      have hstep : uniformizationStep σ (path n) (path (n + 1)) :=
        hplay.2 n
      rw [pathMemory_fst_succ σ path n]
      rcases hpos : path n with
        atom | ⟨atom, h⟩ | ⟨atom, h, move⟩ |
        ⟨atom, h, move, outOne, outTwo⟩ |
        ⟨h, word, state, minState⟩ | ⟨h, word, state, minState, tbl⟩ |
        ⟨h, word, state, minState, tbl, move⟩ |
        ⟨h, word, state, minState, tbl, move, outOne⟩ |
        ⟨h, word, state, minState, tbl, move, outOne⟩ |
        ⟨h, word, state, minState, tbl, move, outOne, outTwo⟩ |
        ⟨h, word, state, minState⟩ | ⟨h, word, state, minState, tbl⟩ |
        ⟨h, word, state, minState, tbl, move⟩ |
        ⟨h, word, state, minState, tbl, move, outTwo⟩ |
        ⟨h, word, state, minState, tbl, move, outTwo⟩ |
        ⟨h, word, state, minState, tbl, move, outTwo, outOne⟩ |
        ⟨word, eqs, ems⟩ | ⟨hc, word, eqs, ems, state, minState⟩ |
        ⟨hc, word, eqs, ems, state, minState, tbl⟩ |
        ⟨hc, word, eqs, ems, state, minState, tbl, move⟩ |
        ⟨hc, word, eqs, ems, state, minState, tbl, move, o1r, o2r⟩ |
        ⟨word, eqs, ems⟩ | ⟨hc, word, eqs, ems, state, minState⟩ |
        ⟨hc, word, eqs, ems, state, minState, tbl⟩ |
        ⟨hc, word, eqs, ems, state, minState, tbl, move⟩ |
        ⟨hc, word, eqs, ems, state, minState, tbl, move, o1r, o2r⟩
      all_goals rw [hpos] at ih hstep
      -- bnd: Even commits the reconstruction
      · have hnext :
            path (n + 1) = .committed atom (pathMemory σ path n).1 := by
          have hmove := hcons n (by rw [hpos]; rfl)
          rw [trackingStrategy_move_eq σ path n, hpos] at hmove
          exact hmove
        rw [hnext]
        exact ⟨rfl, ih.1, ih.2.1, ih.2.2⟩
      -- committed: Odd reveals the move
      · obtain ⟨move, hnext⟩ :
            ∃ move : In₁ × In₂, path (n + 1) = .opening atom h move :=
          hstep
        rw [hnext]
        exact ⟨ih.1, ih.2.1, ih.2.2.1, ih.2.2.2⟩
      -- opening: Even answers with the tracked responses
      · obtain ⟨hh, hgen, hready, hstate⟩ := ih
        subst hh
        have hnext :
            path (n + 1) =
              .openingResolve atom (pathMemory σ path n).1 move
                (σ.one
                  (nextView Proc.one (pathMemory σ path n).1
                    (bothEnvironment move)))
                (σ.two
                  (nextView Proc.two (pathMemory σ path n).1
                    (bothEnvironment move))) := by
          have hmove := hcons n (by rw [hpos]; rfl)
          rw [trackingStrategy_move_eq σ path n, hpos] at hmove
          exact hmove
        rw [hnext]
        exact ⟨rfl, hgen, hready, hstate, rfl, rfl⟩
      -- openingResolve: Odd resolves the graph
      · obtain ⟨hh, hgen, hready, hstate, hone, htwo⟩ := ih
        subst hh
        have hstep' :
            path (n + 1) =
                uOpenBothTarget (A := A) atom move outOne outTwo ∨
              path (n + 1) =
                uOpenLeftTarget σ atom (pathMemory σ path n).1 move outOne ∨
              path (n + 1) =
                uOpenRightTarget σ atom (pathMemory σ path n).1 move
                  outTwo :=
          hstep
        have hrecordBoth :
            bothRoundRecord move outOne outTwo =
              nextRound σ (pathMemory σ path n).1 (bothEnvironment move) := by
          rw [hone, htwo]
          rfl
        rcases hstep' with hnext | hnext | hnext
        · rw [hnext]
          refine
            ⟨StrategyGeneratedPrefix.append hgen (bothEnvironment move),
              boundaryReady_append _ _ rfl, ?_⟩
          show
            A.step atom.1 (bothRoundRecord move outOne outTwo) =
              A.historyState
                (History.append (pathMemory σ path n).1
                  (nextRound σ (pathMemory σ path n).1
                    (bothEnvironment move)))
          rw [A.historyState_append, hstate, hrecordBoth]
        · rw [hnext]
          have hsender :
              blockSenderTwo σ (pathMemory σ path n).1 [] move.2 =
                σ.two
                  (nextView Proc.two (pathMemory σ path n).1
                    (leftEnvironment move)) :=
            blockSenderTwo_eq σ (pathMemory σ path n).1 [] move
          have hrecord :
              leftRoundRecord move outOne
                  (blockSenderTwo σ (pathMemory σ path n).1 [] move.2) =
                nextRound σ (pathMemory σ path n).1 (leftEnvironment move) := by
            rw [hone, hsender]
            rfl
          refine ⟨hgen, hready, [move], by simp, ?_, rfl, ?_⟩
          · rfl
          · show
              A.step atom.1
                  (leftRoundRecord move outOne
                    (blockSenderTwo σ (pathMemory σ path n).1 [] move.2)) =
                A.historyState
                  (History.append (pathMemory σ path n).1
                    (nextRound σ (pathMemory σ path n).1
                      (leftEnvironment move)))
            rw [A.historyState_append, hstate, hrecord]
        · rw [hnext]
          have hsender :
              blockSenderOne σ (pathMemory σ path n).1 [] move.1 =
                σ.one
                  (nextView Proc.one (pathMemory σ path n).1
                    (rightEnvironment (move.2, move.1))) :=
            blockSenderOne_eq σ (pathMemory σ path n).1 [] (move.2, move.1)
          have hrecord :
              rightRoundRecord (move.2, move.1)
                  (blockSenderOne σ (pathMemory σ path n).1 [] move.1)
                  outTwo =
                nextRound σ (pathMemory σ path n).1
                  (rightEnvironment (move.2, move.1)) := by
            rw [htwo, hsender]
            rfl
          refine ⟨hgen, hready, [(move.2, move.1)], by simp, ?_, rfl, ?_⟩
          · rfl
          · show
              A.step atom.1
                  (rightRoundRecord (move.2, move.1)
                    (blockSenderOne σ (pathMemory σ path n).1 [] move.1)
                    outTwo) =
                A.historyState
                  (History.append (pathMemory σ path n).1
                    (nextRound σ (pathMemory σ path n).1
                      (rightEnvironment (move.2, move.1))))
            rw [A.historyState_append, hstate, hrecord]
      -- blockL: Even commits the round's reversal table
      · have hnext :
            path (n + 1) =
              .blockEnvL h word state minState
                (fun inputOne =>
                  σ.one
                    (nextView Proc.one (pathMemory σ path n).1
                      (rightEnvironment (default, inputOne)))) := by
          have hmove := hcons n (by rw [hpos]; rfl)
          rw [trackingStrategy_move_eq σ path n, hpos] at hmove
          exact hmove
        rw [hnext]
        exact ⟨ih, rfl⟩
      -- blockEnvL: Odd reveals the move
      · obtain ⟨move, hnext⟩ :
            ∃ move : In₁ × In₂,
              path (n + 1) = .recvL h word state minState tbl move :=
          hstep
        rw [hnext]
        exact ih
      -- recvL: Even answers with the tracked receiver response
      · have hnext :
            path (n + 1) =
              .resolveL h word state minState tbl move
                (σ.one
                  (nextView Proc.one (pathMemory σ path n).1
                    (leftEnvironment move))) := by
          have hmove := hcons n (by rw [hpos]; rfl)
          rw [trackingStrategy_move_eq σ path n, hpos] at hmove
          exact hmove
        rw [hnext]
        exact ⟨ih.1, ih.2, rfl⟩
      -- resolveL: Odd continues or closes
      · obtain ⟨⟨hgen, hready, moves, hne, hHeq, hword, hstate⟩, htbl,
          hone⟩ := ih
        have hsender :
            blockSenderTwo σ h word move.2 =
              σ.two
                (nextView Proc.two (pathMemory σ path n).1
                  (leftEnvironment move)) := by
          rw [hword, hHeq]
          exact blockSenderTwo_eq σ h moves move
        have hrecord :
            leftRoundRecord move outOne (blockSenderTwo σ h word move.2) =
              nextRound σ (pathMemory σ path n).1 (leftEnvironment move) := by
          rw [hone, hsender]
          rfl
        have hstep' :
            path (n + 1) =
                uContinueLTarget σ h word state minState move outOne ∨
              path (n + 1) =
                .closeL h word state minState tbl move outOne :=
          hstep
        rcases hstep' with hnext | hnext
        · rw [hnext]
          refine ⟨hgen, hready, moves ++ [move], by simp, ?_, ?_, ?_⟩
          · rw [List.map_append, List.map_singleton, extendPrefix_snoc, ← hHeq]
            rfl
          · rw [hword]
            simp [senderWord]
          · show
              A.step state
                  (leftRoundRecord move outOne
                    (blockSenderTwo σ h word move.2)) =
                A.historyState
                  (History.append (pathMemory σ path n).1
                    (nextRound σ (pathMemory σ path n).1
                      (leftEnvironment move)))
            rw [A.historyState_append, hstate, hrecord]
        · rw [hnext]
          exact ⟨⟨hgen, hready, moves, hne, hHeq, hword, hstate⟩, htbl,
            hone⟩
      -- closeL: Even fixes the closing response
      · obtain ⟨⟨hgen, hready, moves, hne, hHeq, hword, hstate⟩, htbl,
          hone⟩ := ih
        have hnext :
            path (n + 1) =
              .closeResolveL h word state minState tbl move outOne
                (σ.two
                  (nextView Proc.two (pathMemory σ path n).1
                    (bothEnvironment move))) := by
          have hmove := hcons n (by rw [hpos]; rfl)
          rw [trackingStrategy_move_eq σ path n, hpos] at hmove
          exact hmove
        rw [hnext]
        exact
          ⟨⟨hgen, hready, moves, hne, hHeq, hword, hstate⟩, htbl, hone,
            rfl⟩
      -- closeResolveL: Odd synchronizes or directly reverses
      · obtain ⟨⟨hgen, hready, moves, hne, hHeq, hword, hstate⟩, htbl,
          hone, htwo⟩ := ih
        have hgenH : StrategyGeneratedPrefix σ (pathMemory σ path n).1 := by
          rw [hHeq]
          exact strategyGenerated_extendPrefix σ hgen _
        have hstep' :
            path (n + 1) =
                uCloseTarget (A := A) state minState move outOne outTwo ∨
              path (n + 1) =
                uRevReverseRTarget (A := A) state minState move
                  (tbl move.1) outTwo :=
          hstep
        rcases hstep' with hnext | hnext
        · rw [hnext]
          have hrecord :
              bothRoundRecord move outOne outTwo =
                nextRound σ (pathMemory σ path n).1
                  (bothEnvironment move) := by
            rw [hone, htwo]
            rfl
          refine
            ⟨StrategyGeneratedPrefix.append hgenH (bothEnvironment move),
              boundaryReady_append _ _ rfl, ?_⟩
          show
            A.step state (bothRoundRecord move outOne outTwo) =
              A.historyState
                (History.append (pathMemory σ path n).1
                  (nextRound σ (pathMemory σ path n).1
                    (bothEnvironment move)))
          rw [A.historyState_append, hstate, hrecord]
        · rw [hnext]
          have hrecord :
              rightRoundRecord (move.2, move.1) (tbl move.1) outTwo =
                nextRound σ (pathMemory σ path n).1
                  (rightEnvironment (move.2, move.1)) := by
            rw [htwo, htbl, ← nextView_two_rightEnvironment]
            rfl
          refine
            ⟨⟨StrategyGeneratedPrefix.append hgenH
                (rightEnvironment (move.2, move.1)), ?_⟩,
              move.1, rfl⟩
          show
            A.step state
                (rightRoundRecord (move.2, move.1) (tbl move.1) outTwo) =
              A.historyState
                (History.append (pathMemory σ path n).1
                  (nextRound σ (pathMemory σ path n).1
                    (rightEnvironment (move.2, move.1))))
          rw [A.historyState_append, hstate, hrecord]
      -- blockR: Even commits the round's reversal table
      · have hnext :
            path (n + 1) =
              .blockEnvR h word state minState
                (fun inputTwo =>
                  σ.two
                    (nextView Proc.two (pathMemory σ path n).1
                      (leftEnvironment (default, inputTwo)))) := by
          have hmove := hcons n (by rw [hpos]; rfl)
          rw [trackingStrategy_move_eq σ path n, hpos] at hmove
          exact hmove
        rw [hnext]
        exact ⟨ih, rfl⟩
      -- blockEnvR: Odd reveals the move
      · obtain ⟨move, hnext⟩ :
            ∃ move : In₁ × In₂,
              path (n + 1) = .recvR h word state minState tbl move :=
          hstep
        rw [hnext]
        exact ih
      -- recvR: Even answers with the tracked receiver response
      · have hnext :
            path (n + 1) =
              .resolveR h word state minState tbl move
                (σ.two
                  (nextView Proc.two (pathMemory σ path n).1
                    (rightEnvironment (move.2, move.1)))) := by
          have hmove := hcons n (by rw [hpos]; rfl)
          rw [trackingStrategy_move_eq σ path n, hpos] at hmove
          exact hmove
        rw [hnext]
        exact ⟨ih.1, ih.2, rfl⟩
      -- resolveR: Odd continues or closes
      · obtain ⟨⟨hgen, hready, moves, hne, hHeq, hword, hstate⟩, htbl,
          htwo⟩ := ih
        have hsender :
            blockSenderOne σ h word move.1 =
              σ.one
                (nextView Proc.one (pathMemory σ path n).1
                  (rightEnvironment (move.2, move.1))) := by
          rw [hword, hHeq]
          exact blockSenderOne_eq σ h moves (move.2, move.1)
        have hrecord :
            rightRoundRecord (move.2, move.1)
                (blockSenderOne σ h word move.1) outTwo =
              nextRound σ (pathMemory σ path n).1
                (rightEnvironment (move.2, move.1)) := by
          rw [htwo, hsender]
          rfl
        have hstep' :
            path (n + 1) =
                uContinueRTarget σ h word state minState move outTwo ∨
              path (n + 1) =
                .closeR h word state minState tbl move outTwo :=
          hstep
        rcases hstep' with hnext | hnext
        · rw [hnext]
          refine ⟨hgen, hready, moves ++ [(move.2, move.1)], by simp, ?_,
            ?_, ?_⟩
          · rw [List.map_append, List.map_singleton, extendPrefix_snoc, ← hHeq]
            rfl
          · rw [hword]
            simp [senderWord]
          · show
              A.step state
                  (rightRoundRecord (move.2, move.1)
                    (blockSenderOne σ h word move.1) outTwo) =
                A.historyState
                  (History.append (pathMemory σ path n).1
                    (nextRound σ (pathMemory σ path n).1
                      (rightEnvironment (move.2, move.1))))
            rw [A.historyState_append, hstate, hrecord]
        · rw [hnext]
          exact ⟨⟨hgen, hready, moves, hne, hHeq, hword, hstate⟩, htbl,
            htwo⟩
      -- closeR: Even fixes the closing response
      · obtain ⟨⟨hgen, hready, moves, hne, hHeq, hword, hstate⟩, htbl,
          htwo⟩ := ih
        have hnext :
            path (n + 1) =
              .closeResolveR h word state minState tbl move outTwo
                (σ.one
                  (nextView Proc.one (pathMemory σ path n).1
                    (bothEnvironment move))) := by
          have hmove := hcons n (by rw [hpos]; rfl)
          rw [trackingStrategy_move_eq σ path n, hpos] at hmove
          exact hmove
        rw [hnext]
        exact
          ⟨⟨hgen, hready, moves, hne, hHeq, hword, hstate⟩, htbl, htwo,
            rfl⟩
      -- closeResolveR: Odd synchronizes or directly reverses
      · obtain ⟨⟨hgen, hready, moves, hne, hHeq, hword, hstate⟩, htbl,
          htwo, hone⟩ := ih
        have hgenH : StrategyGeneratedPrefix σ (pathMemory σ path n).1 := by
          rw [hHeq]
          exact strategyGenerated_extendPrefix σ hgen _
        have hstep' :
            path (n + 1) =
                uCloseTarget (A := A) state minState move outOne outTwo ∨
              path (n + 1) =
                uRevReverseLTarget (A := A) state minState move outOne
                  (tbl move.2) :=
          hstep
        rcases hstep' with hnext | hnext
        · rw [hnext]
          have hrecord :
              bothRoundRecord move outOne outTwo =
                nextRound σ (pathMemory σ path n).1
                  (bothEnvironment move) := by
            rw [hone, htwo, nextView_two_rightEnvironment]
            rfl
          refine
            ⟨StrategyGeneratedPrefix.append hgenH (bothEnvironment move),
              boundaryReady_append _ _ rfl, ?_⟩
          show
            A.step state (bothRoundRecord move outOne outTwo) =
              A.historyState
                (History.append (pathMemory σ path n).1
                  (nextRound σ (pathMemory σ path n).1
                    (bothEnvironment move)))
          rw [A.historyState_append, hstate, hrecord]
        · rw [hnext]
          have hrecord :
              leftRoundRecord move outOne (tbl move.2) =
                nextRound σ (pathMemory σ path n).1
                  (leftEnvironment move) := by
            rw [hone, htbl, ← nextView_one_leftEnvironment]
            rfl
          refine
            ⟨⟨StrategyGeneratedPrefix.append hgenH (leftEnvironment move),
                ?_⟩,
              move.2, rfl⟩
          show
            A.step state (leftRoundRecord move outOne (tbl move.2)) =
              A.historyState
                (History.append (pathMemory σ path n).1
                  (nextRound σ (pathMemory σ path n).1
                    (leftEnvironment move)))
          rw [A.historyState_append, hstate, hrecord]
      -- revCommitL: Even commits the blind side's virtual view
      · obtain ⟨⟨hgen, heqs⟩, d, hword⟩ := ih
        have hnext :
            path (n + 1) =
              .revBlockL (pathMemory σ path n).1 word eqs ems eqs
                ems := by
          have hmove := hcons n (by rw [hpos]; rfl)
          rw [trackingStrategy_move_eq σ path n, hpos] at hmove
          exact hmove
        rw [hnext]
        exact ⟨hgen, heqs, d, [], by rw [hword]; rfl, rfl, heqs⟩
      -- revBlockL: Even commits the round's blind-send table
      · have hnext :
            path (n + 1) =
              .revEnvL hc word eqs ems state minState
                (fun inputOne =>
                  σ.one
                    (nextView Proc.one (pathMemory σ path n).1
                      (rightEnvironment (default, inputOne)))) := by
          have hmove := hcons n (by rw [hpos]; rfl)
          rw [trackingStrategy_move_eq σ path n, hpos] at hmove
          exact hmove
        rw [hnext]
        exact ⟨ih, rfl⟩
      -- revEnvL: Odd reveals the move
      · obtain ⟨move, hnext⟩ :
            ∃ move : In₁ × In₂,
              path (n + 1) =
                .revRecvL hc word eqs ems state minState tbl move :=
          hstep
        rw [hnext]
        exact ih
      -- revRecvL: Even stages the shared receive responses
      · have hnext :
            path (n + 1) =
              .revResolveL hc word eqs ems state minState tbl move
                (σ.one
                  (nextView Proc.one (pathMemory σ path n).1
                    (bothEnvironment move)))
                (σ.two
                  (nextView Proc.two (pathMemory σ path n).1
                    (bothEnvironment move))) := by
          have hmove := hcons n (by rw [hpos]; rfl)
          rw [trackingStrategy_move_eq σ path n, hpos] at hmove
          exact hmove
        rw [hnext]
        exact ⟨ih.1, ih.2, rfl, rfl⟩
      -- revResolveL: Odd continues, closes, or reverses again
      · obtain ⟨⟨hgen, heqs, d, moves, hword, hHeq, hstate⟩, htbl, h1r,
          h2r⟩ := ih
        have hgenH : StrategyGeneratedPrefix σ (pathMemory σ path n).1 := by
          rw [hHeq]
          exact strategyGenerated_extendPrefix σ hgen _
        have hdrop : word.drop 1 = senderWord moves := by
          rw [hword]
          rfl
        have hsender :
            blockSenderTwo σ hc (word.drop 1) move.2 =
              σ.two
                (nextView Proc.two (pathMemory σ path n).1
                  (leftEnvironment move)) := by
          rw [hdrop, hHeq]
          exact blockSenderTwo_eq σ hc moves move
        have hstep' :
            path (n + 1) =
                uRevContinueLTarget σ hc word eqs ems state minState
                  move o1r ∨
              path (n + 1) =
                uCloseTarget (A := A) state minState move o1r o2r ∨
              path (n + 1) =
                uRevReverseRTarget (A := A) state minState move
                  (tbl move.1) o2r :=
          hstep
        rcases hstep' with hnext | hnext | hnext
        · rw [hnext]
          have hrecord :
              leftRoundRecord move o1r
                  (blockSenderTwo σ hc (word.drop 1) move.2) =
                nextRound σ (pathMemory σ path n).1
                  (leftEnvironment move) := by
            rw [h1r, hsender, ← nextView_one_leftEnvironment]
            rfl
          refine ⟨hgen, heqs, d, moves ++ [move], ?_, ?_, ?_⟩
          · rw [hword]
            simp [senderWord]
          · rw [List.map_append, List.map_singleton, extendPrefix_snoc,
              ← hHeq]
            rfl
          · show
              A.step state
                  (leftRoundRecord move o1r
                    (blockSenderTwo σ hc (word.drop 1) move.2)) =
                A.historyState
                  (History.append (pathMemory σ path n).1
                    (nextRound σ (pathMemory σ path n).1
                      (leftEnvironment move)))
            rw [A.historyState_append, hstate, hrecord]
        · rw [hnext]
          have hrecord :
              bothRoundRecord move o1r o2r =
                nextRound σ (pathMemory σ path n).1
                  (bothEnvironment move) := by
            rw [h1r, h2r]
            rfl
          refine
            ⟨StrategyGeneratedPrefix.append hgenH (bothEnvironment move),
              boundaryReady_append _ _ rfl, ?_⟩
          show
            A.step state (bothRoundRecord move o1r o2r) =
              A.historyState
                (History.append (pathMemory σ path n).1
                  (nextRound σ (pathMemory σ path n).1
                    (bothEnvironment move)))
          rw [A.historyState_append, hstate, hrecord]
        · rw [hnext]
          have hrecord :
              rightRoundRecord (move.2, move.1) (tbl move.1) o2r =
                nextRound σ (pathMemory σ path n).1
                  (rightEnvironment (move.2, move.1)) := by
            rw [h2r, htbl, ← nextView_two_rightEnvironment]
            rfl
          refine
            ⟨⟨StrategyGeneratedPrefix.append hgenH
                (rightEnvironment (move.2, move.1)), ?_⟩,
              move.1, rfl⟩
          show
            A.step state
                (rightRoundRecord (move.2, move.1) (tbl move.1) o2r) =
              A.historyState
                (History.append (pathMemory σ path n).1
                  (nextRound σ (pathMemory σ path n).1
                    (rightEnvironment (move.2, move.1))))
          rw [A.historyState_append, hstate, hrecord]
      -- revCommitR: Even commits the blind side's virtual view
      · obtain ⟨⟨hgen, heqs⟩, d, hword⟩ := ih
        have hnext :
            path (n + 1) =
              .revBlockR (pathMemory σ path n).1 word eqs ems eqs
                ems := by
          have hmove := hcons n (by rw [hpos]; rfl)
          rw [trackingStrategy_move_eq σ path n, hpos] at hmove
          exact hmove
        rw [hnext]
        exact ⟨hgen, heqs, d, [], by rw [hword]; rfl, rfl, heqs⟩
      -- revBlockR: Even commits the round's blind-send table
      · have hnext :
            path (n + 1) =
              .revEnvR hc word eqs ems state minState
                (fun inputTwo =>
                  σ.two
                    (nextView Proc.two (pathMemory σ path n).1
                      (leftEnvironment (default, inputTwo)))) := by
          have hmove := hcons n (by rw [hpos]; rfl)
          rw [trackingStrategy_move_eq σ path n, hpos] at hmove
          exact hmove
        rw [hnext]
        exact ⟨ih, rfl⟩
      -- revEnvR: Odd reveals the move
      · obtain ⟨move, hnext⟩ :
            ∃ move : In₁ × In₂,
              path (n + 1) =
                .revRecvR hc word eqs ems state minState tbl move :=
          hstep
        rw [hnext]
        exact ih
      -- revRecvR: Even stages the shared receive responses
      · have hnext :
            path (n + 1) =
              .revResolveR hc word eqs ems state minState tbl move
                (σ.one
                  (nextView Proc.one (pathMemory σ path n).1
                    (bothEnvironment move)))
                (σ.two
                  (nextView Proc.two (pathMemory σ path n).1
                    (bothEnvironment move))) := by
          have hmove := hcons n (by rw [hpos]; rfl)
          rw [trackingStrategy_move_eq σ path n, hpos] at hmove
          exact hmove
        rw [hnext]
        exact ⟨ih.1, ih.2, rfl, rfl⟩
      -- revResolveR: Odd continues, closes, or reverses again
      · obtain ⟨⟨hgen, heqs, d, moves, hword, hHeq, hstate⟩, htbl, h1r,
          h2r⟩ := ih
        have hgenH : StrategyGeneratedPrefix σ (pathMemory σ path n).1 := by
          rw [hHeq]
          exact strategyGenerated_extendPrefix σ hgen _
        have hdrop : word.drop 1 = senderWord moves := by
          rw [hword]
          rfl
        have hsender :
            blockSenderOne σ hc (word.drop 1) move.1 =
              σ.one
                (nextView Proc.one (pathMemory σ path n).1
                  (rightEnvironment (move.2, move.1))) := by
          rw [hdrop, hHeq]
          exact blockSenderOne_eq σ hc moves (move.2, move.1)
        have hstep' :
            path (n + 1) =
                uRevContinueRTarget σ hc word eqs ems state minState
                  move o2r ∨
              path (n + 1) =
                uCloseTarget (A := A) state minState move o1r o2r ∨
              path (n + 1) =
                uRevReverseLTarget (A := A) state minState move o1r
                  (tbl move.2) :=
          hstep
        rcases hstep' with hnext | hnext | hnext
        · rw [hnext]
          have hrecord :
              rightRoundRecord (move.2, move.1)
                  (blockSenderOne σ hc (word.drop 1) move.1) o2r =
                nextRound σ (pathMemory σ path n).1
                  (rightEnvironment (move.2, move.1)) := by
            rw [h2r, hsender, ← nextView_two_rightEnvironment]
            rfl
          refine ⟨hgen, heqs, d, moves ++ [(move.2, move.1)], ?_, ?_, ?_⟩
          · rw [hword]
            simp [senderWord]
          · rw [List.map_append, List.map_singleton, extendPrefix_snoc,
              ← hHeq]
            rfl
          · show
              A.step state
                  (rightRoundRecord (move.2, move.1)
                    (blockSenderOne σ hc (word.drop 1) move.1) o2r) =
                A.historyState
                  (History.append (pathMemory σ path n).1
                    (nextRound σ (pathMemory σ path n).1
                      (rightEnvironment (move.2, move.1))))
            rw [A.historyState_append, hstate, hrecord]
        · rw [hnext]
          have hrecord :
              bothRoundRecord move o1r o2r =
                nextRound σ (pathMemory σ path n).1
                  (bothEnvironment move) := by
            rw [h1r, h2r]
            rfl
          refine
            ⟨StrategyGeneratedPrefix.append hgenH (bothEnvironment move),
              boundaryReady_append _ _ rfl, ?_⟩
          show
            A.step state (bothRoundRecord move o1r o2r) =
              A.historyState
                (History.append (pathMemory σ path n).1
                  (nextRound σ (pathMemory σ path n).1
                    (bothEnvironment move)))
          rw [A.historyState_append, hstate, hrecord]
        · rw [hnext]
          have hrecord :
              leftRoundRecord move o1r (tbl move.2) =
                nextRound σ (pathMemory σ path n).1
                  (leftEnvironment move) := by
            rw [h1r, htbl, ← nextView_one_leftEnvironment]
            rfl
          refine
            ⟨⟨StrategyGeneratedPrefix.append hgenH (leftEnvironment move),
                ?_⟩,
              move.2, rfl⟩
          show
            A.step state (leftRoundRecord move o1r (tbl move.2)) =
              A.historyState
                (History.append (pathMemory σ path n).1
                  (nextRound σ (pathMemory σ path n).1
                    (leftEnvironment move)))
          rw [A.historyState_append, hstate, hrecord]

end Invariant

end DetParityAutomaton

end DistributedSynthesis
