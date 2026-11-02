/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmBlockRestriction
import DistributedSynthesis.Formalizations.Theorem.ThmBoundaryDecomposition

/-!
# The journal block monitors

This file builds the concrete `BlockRecordMonitor` family of the
journal construction: for each boundary state of the objective parity
automaton and each block orientation, the monitor tracks the automaton
state along the realized block rounds together with a state of minimal
priority seen since the boundary.  Its priorities are the automaton
priorities of the current state, so its parity condition on an infinite
block play is the tail parity of the underlying play, and the tracked
minimal state supplies the block minimum that the boundary game emits
at a close.

The main theorems transport global winning to these monitors: if every
real execution of a distributed strategy is accepted, then at every
strategy-generated history the restricted block pair of
`ThmBlockRestriction.lean` wins the block monitor started at the
history's automaton state
(`blockPair_wins_leftBlockMonitor`, `blockPair_wins_rightBlockMonitor`).
Composed with the unconditional sender narrowing
(`block_realizable_iff_implementable_controller_unconditional`), every
such history therefore admits a finite narrowed block controller: the
per-block moves of the boundary game.
-/

namespace DistributedSynthesis

universe u v x y s

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

namespace DetParityAutomaton

variable
  (A :
    DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))

/-- The automaton state reached after a finite history. -/
def historyState (h : History In₁ In₂ Graph Out₁ Out₂) : A.State :=
  h.foldl A.step A.initial

@[simp]
theorem historyState_nil :
    A.historyState ([] : History In₁ In₂ Graph Out₁ Out₂) = A.initial :=
  rfl

@[simp]
theorem historyState_append
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (round : RoundRecord In₁ In₂ Graph Out₁ Out₂) :
    A.historyState (History.append h round) =
      A.step (A.historyState h) round := by
  simp [historyState, History.append]

/-- Runs decompose at any cut point. -/
theorem runFrom_add
    (state : A.State)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (m n : Nat) :
    A.runFrom state word (m + n) =
      A.runFrom (A.runFrom state word m) (fun k => word (m + k)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      show
        A.step (A.runFrom state word (m + n)) (word (m + n)) =
          A.step (A.runFrom (A.runFrom state word m)
            (fun k => word (m + k)) n) (word (m + n))
      rw [ih]

/-- The run state at a finite time is the history state of the prefix. -/
theorem run_wordPrefix
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (n : Nat) :
    A.run word n =
      A.historyState (FiniteEpochTransformer.wordPrefix word n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      show
        A.step (A.run word n) (word n) =
          A.historyState (FiniteEpochTransformer.wordPrefix word (n + 1))
      rw [
        FiniteEpochTransformer.wordPrefix,
        historyState_append,
        ih
      ]

/--
The block monitor of a left block from a boundary state: the automaton
state along the realized left rounds, paired with a state of minimal
priority seen since the boundary.
-/
def leftBlockMonitor (boundary : A.State) :
    BlockRecordMonitor.{u, v, x, y, s} In₁ In₂ Out₁ Out₂ where
  State := A.State × A.State
  stateFinite := inferInstance
  initial := (boundary, boundary)
  step := fun state round =>
    let next := A.step state.1 (realizedRoundRecord round)
    (next, if A.priority next < A.priority state.2 then next else state.2)
  priority := fun state => A.priority state.1

/--
The block monitor of a right block from a boundary state.  Block moves
are receiver-first pairs, so the realized rounds embed through
`realizedRoundRecordRight`.
-/
def rightBlockMonitor (boundary : A.State) :
    BlockRecordMonitor.{v, u, y, x, s} In₂ In₁ Out₂ Out₁ where
  State := A.State × A.State
  stateFinite := inferInstance
  initial := (boundary, boundary)
  step := fun state round =>
    let next := A.step state.1 (realizedRoundRecordRight round)
    (next, if A.priority next < A.priority state.2 then next else state.2)
  priority := fun state => A.priority state.1

/-- The tracked automaton state is the run on the realized rounds. -/
theorem leftBlockMonitor_run_fst
    (boundary : A.State)
    (play : Nat -> RealizedBlockRound In₁ In₂ Out₁ Out₂)
    (n : Nat) :
    ((A.leftBlockMonitor boundary).run play n).1 =
      A.runFrom boundary (fun t => realizedRoundRecord (play t)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      show
        (A.step ((A.leftBlockMonitor boundary).run play n).1
            (realizedRoundRecord (play n)),
          _).1 =
          A.step
            (A.runFrom boundary (fun t => realizedRoundRecord (play t)) n)
            (realizedRoundRecord (play n))
      rw [ih]

theorem rightBlockMonitor_run_fst
    (boundary : A.State)
    (play : Nat -> RealizedBlockRound In₂ In₁ Out₂ Out₁)
    (n : Nat) :
    ((A.rightBlockMonitor boundary).run play n).1 =
      A.runFrom boundary
        (fun t => realizedRoundRecordRight (play t)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      show
        (A.step ((A.rightBlockMonitor boundary).run play n).1
            (realizedRoundRecordRight (play n)),
          _).1 =
          A.step
            (A.runFrom boundary
              (fun t => realizedRoundRecordRight (play t)) n)
            (realizedRoundRecordRight (play n))
      rw [ih]

/--
Transport of global winning to the left block monitor: at every
strategy-generated history, the restricted block pair wins the monitor
started at the history's automaton state.
-/
theorem blockPair_wins_leftBlockMonitor [Inhabited In₁]
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (hσ :
      ∀ env : EnvironmentSequence In₁ In₂, A.Accepts (execution σ env))
    {h : History In₁ In₂ Graph Out₁ Out₂}
    (hgen : StrategyGeneratedPrefix σ h) :
    ∀ env : Nat -> In₁ × In₂,
      (A.leftBlockMonitor (A.historyState h)).WinsPlay
        (pairPlay (blockReceiverOne σ h) (blockSenderTwo σ h) env) := by
  refine
    blockPair_wins_of_acceptance σ hgen (fun word => A.Accepts word) hσ _
      ?_
  intro word play haccepts hprefix htail
  have hstate : A.historyState h = A.run word h.length := by
    rw [run_wordPrefix, hprefix]
  have hrealized :
      (fun t => realizedRoundRecord (play t)) =
        fun t => word (h.length + t) :=
    funext fun t => (htail t).symm
  have hpriority :
      (fun n =>
          (A.leftBlockMonitor (A.historyState h)).priority
            ((A.leftBlockMonitor (A.historyState h)).run play n)) =
        fun n => A.priority (A.run word (h.length + n)) := by
    funext n
    show
      A.priority ((A.leftBlockMonitor (A.historyState h)).run play n).1 =
        A.priority (A.run word (h.length + n))
    rw [
      leftBlockMonitor_run_fst,
      hrealized,
      hstate,
      DetParityAutomaton.run,
      ← runFrom_add
    ]
  show
    NatSeqMinEvenParity
      (fun n =>
        (A.leftBlockMonitor (A.historyState h)).priority
          ((A.leftBlockMonitor (A.historyState h)).run play n))
  rw [hpriority]
  exact (accepts_iff_tail_parity A word h.length).mp haccepts

/--
Transport of global winning to the right block monitor: the mirror of
`blockPair_wins_leftBlockMonitor`.
-/
theorem blockPair_wins_rightBlockMonitor [Inhabited In₂]
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (hσ :
      ∀ env : EnvironmentSequence In₁ In₂, A.Accepts (execution σ env))
    {h : History In₁ In₂ Graph Out₁ Out₂}
    (hgen : StrategyGeneratedPrefix σ h) :
    ∀ env : Nat -> In₂ × In₁,
      (A.rightBlockMonitor (A.historyState h)).WinsPlay
        (pairPlay (blockReceiverTwo σ h) (blockSenderOne σ h) env) := by
  refine
    blockPair_wins_of_acceptance_right σ hgen (fun word => A.Accepts word)
      hσ _ ?_
  intro word play haccepts hprefix htail
  have hstate : A.historyState h = A.run word h.length := by
    rw [run_wordPrefix, hprefix]
  have hrealized :
      (fun t => realizedRoundRecordRight (play t)) =
        fun t => word (h.length + t) :=
    funext fun t => (htail t).symm
  have hpriority :
      (fun n =>
          (A.rightBlockMonitor (A.historyState h)).priority
            ((A.rightBlockMonitor (A.historyState h)).run play n)) =
        fun n => A.priority (A.run word (h.length + n)) := by
    funext n
    show
      A.priority ((A.rightBlockMonitor (A.historyState h)).run play n).1 =
        A.priority (A.run word (h.length + n))
    rw [
      rightBlockMonitor_run_fst,
      hrealized,
      hstate,
      DetParityAutomaton.run,
      ← runFrom_add
    ]
  show
    NatSeqMinEvenParity
      (fun n =>
        (A.rightBlockMonitor (A.historyState h)).priority
          ((A.rightBlockMonitor (A.historyState h)).run play n))
  rw [hpriority]
  exact (accepts_iff_tail_parity A word h.length).mp haccepts

/--
The move supply of the boundary game, left blocks: at every
strategy-generated history of a winning strategy there is a finite
narrowed block controller, over sender branching, all of whose threads
win the left block monitor at the history's automaton state.
-/
theorem exists_narrowedController_left
    [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (hσ :
      ∀ env : EnvironmentSequence In₁ In₂, A.Accepts (execution σ env))
    {h : History In₁ In₂ Graph Out₁ Out₂}
    (hgen : StrategyGeneratedPrefix σ h) :
    ∃ controller :
        TransitionRationalTree.{v, max u v x y s, s} In₂
          (NarrowedBlockLabel In₁ In₂ Out₁ Out₂
            (A.leftBlockMonitor (A.historyState h)).State),
      NarrowedAllThreadsWin (A.leftBlockMonitor (A.historyState h))
        controller.labeledTree :=
  (block_realizable_iff_implementable_controller_unconditional
      (A.leftBlockMonitor (A.historyState h))).mp
    ⟨blockReceiverOne σ h, blockSenderTwo σ h,
      blockPair_wins_leftBlockMonitor A σ hσ hgen⟩

/-- The move supply of the boundary game, right blocks. -/
theorem exists_narrowedController_right
    [Inhabited In₁] [Inhabited In₂] [Inhabited Out₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (hσ :
      ∀ env : EnvironmentSequence In₁ In₂, A.Accepts (execution σ env))
    {h : History In₁ In₂ Graph Out₁ Out₂}
    (hgen : StrategyGeneratedPrefix σ h) :
    ∃ controller :
        TransitionRationalTree.{u, max u v x y s, s} In₁
          (NarrowedBlockLabel In₂ In₁ Out₂ Out₁
            (A.rightBlockMonitor (A.historyState h)).State),
      NarrowedAllThreadsWin (A.rightBlockMonitor (A.historyState h))
        controller.labeledTree :=
  (block_realizable_iff_implementable_controller_unconditional
      (A.rightBlockMonitor (A.historyState h))).mp
    ⟨blockReceiverTwo σ h, blockSenderOne σ h,
      blockPair_wins_rightBlockMonitor A σ hσ hgen⟩

end DetParityAutomaton

end DistributedSynthesis
