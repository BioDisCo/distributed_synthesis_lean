/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmBoundaryGame

/-!
# The arena fold of real plays

This file drives the boundary game of `ThmBoundaryGame.lean` by a real
environment sequence: from a family of committed plans, one per
boundary atom, each environment round advances the arena position
deterministically (the committed tier is collapsed into the boundary
step), and the arena prescribes the outputs of the round
(`arenaRecord`).  The fold therefore produces the emitted round word of
the pasted strategy (`arenaWord`).

On the no-direct fragment the fold never encounters a reversal: a
within-block position was entered by a round of its own orientation
(`arenaFoldSeq_shape`), so a direct reversal would violate
`NoDirectReversalSequence`.  Under that hypothesis the automaton state
stored in the position is exactly the objective automaton's run on the
emitted word (`positionState_arenaFoldSeq`).

This is step H4b of the readback-upgrade plan: together with the
candidate-pair summaries (H4c) it identifies real executions of the
pasted strategy with consistent arena plays, whose parity transfers to
acceptance through `natSeqMinEvenParity_iff_of_recurring_transfer`.
-/

namespace DistributedSynthesis

universe u v x y s

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

/--
No direct reversals: a one-sided round is never followed by a round of
the opposite orientation; dominance changes only through `both` rounds.
-/
def NoDirectReversalSequence (env : EnvironmentSequence In₁ In₂) : Prop :=
  ∀ n : Nat,
    ((env n).graph = Graph.left -> (env (n + 1)).graph ≠ Graph.right) ∧
      ((env n).graph = Graph.right -> (env (n + 1)).graph ≠ Graph.left)

namespace DetParityAutomaton

variable
  (A :
    DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))
  {C_L C_R C_V : Type max u v x y s}

/-- A family of committed plans, one per boundary atom. -/
abbrev PlanFamily (C_L C_R C_V : Type max u v x y s) :=
  A.State × A.State ->
    BoundaryPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
      A C_L C_R C_V

variable {A}

/--
One environment round advances the arena position: at a boundary the
committed tier is collapsed, within a block the round continues or
closes it.  Positions of the committed tier and reversal rounds inside
blocks are junk cases that self-loop; the fold never reaches them on
the no-direct fragment.
-/
def arenaStep (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (position : BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V)
    (envRound : EnvironmentRound In₁ In₂) :
    BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V :=
  match position with
  | Sum.inl (state, minState) =>
      match envRound.graph with
      | Graph.both =>
          A.boundaryBothTarget (plans (state, minState)) state
            (envRound.inputOne, envRound.inputTwo)
      | Graph.left =>
          A.boundaryOpenLeftTarget (plans (state, minState)) state
            (envRound.inputOne, envRound.inputTwo)
      | Graph.right =>
          A.boundaryOpenRightTarget (plans (state, minState)) state
            (envRound.inputTwo, envRound.inputOne)
  | Sum.inr (Sum.inl committed) => Sum.inr (Sum.inl committed)
  | Sum.inr (Sum.inr (Sum.inl (plan, chain, control, state, minState))) =>
      match envRound.graph with
      | Graph.left =>
          A.leftContinueTarget plan chain control state minState
            (envRound.inputOne, envRound.inputTwo)
      | Graph.both =>
          A.leftCloseTarget (C_R := C_R) (C_V := C_V) plan control state
            minState (envRound.inputOne, envRound.inputTwo)
      | Graph.right =>
          A.leftReverseTarget plan chain control state minState
            (envRound.inputOne, envRound.inputTwo)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl
      (plan, chain, control, state, minState)))) =>
      match envRound.graph with
      | Graph.right =>
          A.rightContinueTarget plan chain control state minState
            (envRound.inputTwo, envRound.inputOne)
      | Graph.both =>
          A.rightCloseTarget (C_L := C_L) (C_V := C_V) plan control state
            minState (envRound.inputTwo, envRound.inputOne)
      | Graph.left =>
          A.rightReverseTarget plan chain control state minState
            (envRound.inputTwo, envRound.inputOne)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl
      (chain, control, entry, state, minState))))) =>
      match envRound.graph with
      | Graph.left =>
          A.revLeftContinueTarget chain control entry state minState
            (envRound.inputOne, envRound.inputTwo)
      | Graph.both =>
          A.revLeftCloseTarget chain control entry state minState
            (envRound.inputOne, envRound.inputTwo)
      | Graph.right =>
          A.revLeftReverseTarget chain control entry state minState
            (envRound.inputOne, envRound.inputTwo)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
      (chain, control, entry, state, minState))))) =>
      match envRound.graph with
      | Graph.right =>
          A.revRightContinueTarget chain control entry state minState
            (envRound.inputOne, envRound.inputTwo)
      | Graph.both =>
          A.revRightCloseTarget chain control entry state minState
            (envRound.inputOne, envRound.inputTwo)
      | Graph.left =>
          A.revRightReverseTarget chain control entry state minState
            (envRound.inputOne, envRound.inputTwo)

/-- The record the arena plays at a position on an environment round. -/
def arenaRecord (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (position : BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V)
    (envRound : EnvironmentRound In₁ In₂) :
    RoundRecord In₁ In₂ Graph Out₁ Out₂ :=
  match position with
  | Sum.inl (state, minState) =>
      let plan := plans (state, minState)
      let move := (envRound.inputOne, envRound.inputTwo)
      match envRound.graph with
      | Graph.both =>
          bothRoundRecord move (A.planOpenOne plan state move)
            (A.planOpenTwo plan state move)
      | Graph.left =>
          leftRoundRecord move (A.planOpenOne plan state move)
            ((plan.1.label plan.1.init).1 move.2)
      | Graph.right =>
          rightRoundRecord (move.2, move.1)
            ((plan.2.1.label plan.2.1.init).1 move.1)
            (A.planOpenTwo plan state move)
  | Sum.inr (Sum.inl ((state, _), plan)) =>
      let move := (envRound.inputOne, envRound.inputTwo)
      bothRoundRecord move (A.planOpenOne plan state move)
        (A.planOpenTwo plan state move)
  | Sum.inr (Sum.inr (Sum.inl (plan, chain, control, state, minState))) =>
      let move := (envRound.inputOne, envRound.inputTwo)
      match envRound.graph with
      | Graph.left =>
          leftRoundRecord move
            ((plan.label control).2 (state, minState) move)
            ((plan.label control).1 move.2)
      | Graph.both =>
          bothRoundRecord move
            ((plan.label control).2 (state, minState) move)
            (plan.close control (state, minState) move)
      | Graph.right =>
          rightRoundRecord (move.2, move.1)
            (plan.rev control (state, minState) move.1)
            (plan.close control (state, minState) move)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl
      (plan, chain, control, state, minState)))) =>
      let move := (envRound.inputTwo, envRound.inputOne)
      match envRound.graph with
      | Graph.right =>
          rightRoundRecord move
            ((plan.label control).1 move.2)
            ((plan.label control).2 (state, minState) move)
      | Graph.both =>
          bothRoundRecord (move.2, move.1)
            (plan.close control (state, minState) move)
            ((plan.label control).2 (state, minState) move)
      | Graph.left =>
          leftRoundRecord (move.2, move.1)
            (plan.close control (state, minState) move)
            (plan.rev control (state, minState) move.1)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl
      (chain, control, entry, state, minState))))) =>
      let move := (envRound.inputOne, envRound.inputTwo)
      let staged := chain.labelL control
      match envRound.graph with
      | Graph.left =>
          leftRoundRecord move
            (staged.1 (entry, state, minState) move)
            (staged.2.2.1 entry move.2)
      | Graph.both =>
          bothRoundRecord move
            (staged.1 (entry, state, minState) move)
            (staged.2.2.2 (entry, state, minState) move)
      | Graph.right =>
          rightRoundRecord (move.2, move.1)
            (staged.2.1 (entry, state, minState) move.1)
            (staged.2.2.2 (entry, state, minState) move)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
      (chain, control, entry, state, minState))))) =>
      let move := (envRound.inputOne, envRound.inputTwo)
      let staged := chain.labelR control
      match envRound.graph with
      | Graph.right =>
          rightRoundRecord (move.2, move.1) (staged.2.1 entry move.1)
            (staged.2.2.2 (entry, state, minState) move)
      | Graph.both =>
          bothRoundRecord move
            (staged.1 (entry, state, minState) move)
            (staged.2.2.2 (entry, state, minState) move)
      | Graph.left =>
          leftRoundRecord move
            (staged.1 (entry, state, minState) move)
            (staged.2.2.1 (entry, state, minState) move.2)

/-- The arena position stream along an environment sequence. -/
def arenaFoldSeq (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) :
    Nat -> BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V
  | 0 => Sum.inl (A.initial, A.initial)
  | n + 1 => arenaStep plans (arenaFoldSeq plans env n) (env n)

/-- The word emitted along the arena fold. -/
def arenaWord (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) :
    OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  fun n => arenaRecord plans (arenaFoldSeq plans env n) (env n)

/-- The objective automaton state stored in an arena position. -/
def positionState :
    BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V -> A.State
  | Sum.inl (state, _) => state
  | Sum.inr (Sum.inl ((state, _), _)) => state
  | Sum.inr (Sum.inr (Sum.inl (_, _, _, state, _))) => state
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl (_, _, _, state, _)))) => state
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (_, _, _, state, _))))) =>
      state
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (_, _, _, state, _))))) =>
      state

/-- The fold never rests at the committed tier. -/
theorem arenaFoldSeq_ne_committed
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) :
    ∀ n : Nat, ∀ committed,
      arenaFoldSeq plans env n ≠ Sum.inr (Sum.inl committed) := by
  intro n
  induction n with
  | zero => intro committed h; exact absurd h (by simp [arenaFoldSeq])
  | succ n ih =>
      intro committed h
      show False
      rw [show arenaFoldSeq plans env (n + 1) =
        arenaStep plans (arenaFoldSeq plans env n) (env n) from rfl] at h
      rcases hpos : arenaFoldSeq plans env n with
        ⟨state, minState⟩ | committed' |
        ⟨plan, chain, control, state, minState⟩ |
        ⟨plan, chain, control, state, minState⟩ |
        ⟨chain, control, entry, state, minState⟩ |
        ⟨chain, control, entry, state, minState⟩ <;>
        rw [hpos] at h
      · cases hgraph : (env n).graph <;>
          exact absurd h (by
            simp [arenaStep, hgraph, boundaryBothTarget,
              boundaryOpenLeftTarget, boundaryOpenRightTarget])
      · exact ih committed' hpos
      · cases hgraph : (env n).graph <;>
          exact absurd h (by
            simp [arenaStep, hgraph, leftContinueTarget, leftCloseTarget,
              leftReverseTarget])
      · cases hgraph : (env n).graph <;>
          exact absurd h (by
            simp [arenaStep, hgraph, rightContinueTarget,
              rightCloseTarget, rightReverseTarget])
      · cases hgraph : (env n).graph <;>
          exact absurd h (by
            simp [arenaStep, hgraph, revLeftContinueTarget,
              revLeftCloseTarget, revLeftReverseTarget])
      · cases hgraph : (env n).graph <;>
          exact absurd h (by
            simp [arenaStep, hgraph, revRightContinueTarget,
              revRightCloseTarget, revRightReverseTarget])

/--
The automaton state stored in the fold position is the objective
automaton's run on the emitted word.
-/
theorem positionState_arenaFoldSeq
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) :
    ∀ n : Nat,
      positionState (arenaFoldSeq plans env n) =
        A.run (arenaWord plans env) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      show
        positionState
            (arenaStep plans (arenaFoldSeq plans env n) (env n)) =
          A.step (A.run (arenaWord plans env) n)
            (arenaRecord plans (arenaFoldSeq plans env n) (env n))
      rw [← ih]
      rcases hpos : arenaFoldSeq plans env n with
        ⟨state, minState⟩ | committed |
        ⟨plan, chain, control, state, minState⟩ |
        ⟨plan, chain, control, state, minState⟩ |
        ⟨chain, control, entry, state, minState⟩ |
        ⟨chain, control, entry, state, minState⟩
      · cases hgraph : (env n).graph <;>
          simp [arenaStep, arenaRecord, hgraph, positionState,
            boundaryOpenLeftTarget, boundaryOpenRightTarget,
            boundaryBothTarget]
      · exact
          absurd hpos (arenaFoldSeq_ne_committed plans env n committed)
      · cases hgraph : (env n).graph <;>
          simp [arenaStep, arenaRecord, hgraph, positionState,
            leftContinueTarget, leftCloseTarget, leftReverseTarget]
      · cases hgraph : (env n).graph <;>
          simp [arenaStep, arenaRecord, hgraph, positionState,
            rightContinueTarget, rightCloseTarget, rightReverseTarget]
      · cases hgraph : (env n).graph <;>
          simp [arenaStep, arenaRecord, hgraph, positionState,
            revLeftContinueTarget, revLeftCloseTarget,
            revLeftReverseTarget]
      · cases hgraph : (env n).graph <;>
          simp [arenaStep, arenaRecord, hgraph, positionState,
            revRightContinueTarget, revRightCloseTarget,
            revRightReverseTarget]

/--
Shape of the fold through direct reversals: every position was entered
by a round of its own orientation.  The two left-oriented tiers -- a
within-block left position and a directly-reversed left position -- are
entered by a `left` round; the two right-oriented tiers by a `right`
round.  This holds unconditionally: a direct reversal is no longer
excluded, it merely hands the play to the oppositely-oriented reversed
tier (`leftReverseTarget` enters the reversed-right tier, and so on),
which the invariant tracks rather than rules out.  On the no-direct
fragment the reversed tiers are simply never reached.
-/
theorem arenaFoldSeq_shape
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) :
    ∀ n : Nat,
      (∀ data,
        arenaFoldSeq plans env n =
            Sum.inr (Sum.inr (Sum.inl data)) ->
          ∃ m : Nat, n = m + 1 ∧ (env m).graph = Graph.left) ∧
      (∀ data,
        arenaFoldSeq plans env n =
            Sum.inr (Sum.inr (Sum.inr (Sum.inl data))) ->
          ∃ m : Nat, n = m + 1 ∧ (env m).graph = Graph.right) ∧
      (∀ data,
        arenaFoldSeq plans env n =
            Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl data)))) ->
          ∃ m : Nat, n = m + 1 ∧ (env m).graph = Graph.left) ∧
      (∀ data,
        arenaFoldSeq plans env n =
            Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr data)))) ->
          ∃ m : Nat, n = m + 1 ∧ (env m).graph = Graph.right) := by
  intro n
  cases n with
  | zero =>
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        · intro data h
          exact absurd h (by simp [arenaFoldSeq])
  | succ n =>
      have hsucc :
          arenaFoldSeq plans env (n + 1) =
            arenaStep plans (arenaFoldSeq plans env n) (env n) := rfl
      rcases hpos : arenaFoldSeq plans env n with
        ⟨state, mn⟩ | committed | ⟨plan, chain, control, st, mn⟩ |
        ⟨plan, chain, control, st, mn⟩ |
        ⟨chain, control, ent, st, mn⟩ | ⟨chain, control, ent, st, mn⟩
      · rw [hpos] at hsucc
        cases hgraph : (env n).graph
        · refine ⟨fun data _ => ⟨n, rfl, hgraph⟩, ?_, ?_, ?_⟩ <;>
            · intro data h
              rw [hsucc] at h
              exact absurd h (by
                simp [arenaStep, hgraph, boundaryOpenLeftTarget])
        · refine ⟨?_, fun data _ => ⟨n, rfl, hgraph⟩, ?_, ?_⟩ <;>
            · intro data h
              rw [hsucc] at h
              exact absurd h (by
                simp [arenaStep, hgraph, boundaryOpenRightTarget])
        · refine ⟨?_, ?_, ?_, ?_⟩ <;>
            · intro data h
              rw [hsucc] at h
              exact absurd h (by
                simp [arenaStep, hgraph, boundaryBothTarget])
      · exact
          absurd hpos (arenaFoldSeq_ne_committed plans env n committed)
      · rw [hpos] at hsucc
        cases hgraph : (env n).graph
        · refine ⟨fun data _ => ⟨n, rfl, hgraph⟩, ?_, ?_, ?_⟩ <;>
            · intro data h
              rw [hsucc] at h
              exact absurd h (by
                simp [arenaStep, hgraph, leftContinueTarget])
        · refine ⟨?_, ?_, ?_, fun data _ => ⟨n, rfl, hgraph⟩⟩ <;>
            · intro data h
              rw [hsucc] at h
              exact absurd h (by
                simp [arenaStep, hgraph, leftReverseTarget])
        · refine ⟨?_, ?_, ?_, ?_⟩ <;>
            · intro data h
              rw [hsucc] at h
              exact absurd h (by
                simp [arenaStep, hgraph, leftCloseTarget])
      · rw [hpos] at hsucc
        cases hgraph : (env n).graph
        · refine ⟨?_, ?_, fun data _ => ⟨n, rfl, hgraph⟩, ?_⟩ <;>
            · intro data h
              rw [hsucc] at h
              exact absurd h (by
                simp [arenaStep, hgraph, rightReverseTarget])
        · refine ⟨?_, fun data _ => ⟨n, rfl, hgraph⟩, ?_, ?_⟩ <;>
            · intro data h
              rw [hsucc] at h
              exact absurd h (by
                simp [arenaStep, hgraph, rightContinueTarget])
        · refine ⟨?_, ?_, ?_, ?_⟩ <;>
            · intro data h
              rw [hsucc] at h
              exact absurd h (by
                simp [arenaStep, hgraph, rightCloseTarget])
      · rw [hpos] at hsucc
        cases hgraph : (env n).graph
        · refine ⟨?_, ?_, fun data _ => ⟨n, rfl, hgraph⟩, ?_⟩ <;>
            · intro data h
              rw [hsucc] at h
              exact absurd h (by
                simp [arenaStep, hgraph, revLeftContinueTarget])
        · refine ⟨?_, ?_, ?_, fun data _ => ⟨n, rfl, hgraph⟩⟩ <;>
            · intro data h
              rw [hsucc] at h
              exact absurd h (by
                simp [arenaStep, hgraph, revLeftReverseTarget])
        · refine ⟨?_, ?_, ?_, ?_⟩ <;>
            · intro data h
              rw [hsucc] at h
              exact absurd h (by
                simp [arenaStep, hgraph, revLeftCloseTarget])
      · rw [hpos] at hsucc
        cases hgraph : (env n).graph
        · refine ⟨?_, ?_, fun data _ => ⟨n, rfl, hgraph⟩, ?_⟩ <;>
            · intro data h
              rw [hsucc] at h
              exact absurd h (by
                simp [arenaStep, hgraph, revRightReverseTarget])
        · refine ⟨?_, ?_, ?_, fun data _ => ⟨n, rfl, hgraph⟩⟩ <;>
            · intro data h
              rw [hsucc] at h
              exact absurd h (by
                simp [arenaStep, hgraph, revRightContinueTarget])
        · refine ⟨?_, ?_, ?_, ?_⟩ <;>
            · intro data h
              rw [hsucc] at h
              exact absurd h (by
                simp [arenaStep, hgraph, revRightCloseTarget])

/--
Fragment specialization of `arenaFoldSeq_shape`: on the no-direct
fragment the two directly-reversed tiers are never reached.  A
reversal round leaves a within-block position for the oppositely
oriented reversed tier, but by the orientation invariant that position
was entered by a round of the block's own orientation, so a reversal
round would be a direct reversal that `NoDirectReversalSequence`
forbids; the reversed tiers are therefore empty and, once entered,
could only self-perpetuate.  This is the exact fact the fragment
journal readback consumes; it becomes vacuous once the reversed tiers
are tracked for real.
-/
theorem arenaFoldSeq_reversed_unreachable_of_noDirect
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂)
    (hnodirect : NoDirectReversalSequence env) :
    ∀ n : Nat,
      (∀ data,
        arenaFoldSeq plans env n ≠
          Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl data))))) ∧
      (∀ data,
        arenaFoldSeq plans env n ≠
          Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr data))))) := by
  intro n
  induction n with
  | zero =>
      refine ⟨?_, ?_⟩ <;>
        · intro data h
          exact absurd h (by simp [arenaFoldSeq])
  | succ n ih =>
      obtain ⟨ihRL, ihRR⟩ := ih
      have hsucc :
          arenaFoldSeq plans env (n + 1) =
            arenaStep plans (arenaFoldSeq plans env n) (env n) := rfl
      rcases hpos : arenaFoldSeq plans env n with
        ⟨state, mn⟩ | committed | ⟨plan, chain, control, st, mn⟩ |
        ⟨plan, chain, control, st, mn⟩ |
        ⟨chain, control, ent, st, mn⟩ | ⟨chain, control, ent, st, mn⟩
      · rw [hpos] at hsucc
        cases hgraph : (env n).graph <;>
          refine ⟨?_, ?_⟩ <;>
            · intro data h
              rw [hsucc] at h
              exact absurd h (by
                simp [arenaStep, hgraph, boundaryOpenLeftTarget,
                  boundaryOpenRightTarget, boundaryBothTarget])
      · exact
          absurd hpos (arenaFoldSeq_ne_committed plans env n committed)
      · rw [hpos] at hsucc
        obtain ⟨m, hm, hmLeft⟩ :=
          (arenaFoldSeq_shape plans env n).1
            (plan, chain, control, st, mn) hpos
        cases hgraph : (env n).graph
        · refine ⟨?_, ?_⟩ <;>
            · intro data h
              rw [hsucc] at h
              exact absurd h (by
                simp [arenaStep, hgraph, leftContinueTarget])
        · subst hm
          exact absurd hgraph ((hnodirect m).1 hmLeft)
        · refine ⟨?_, ?_⟩ <;>
            · intro data h
              rw [hsucc] at h
              exact absurd h (by
                simp [arenaStep, hgraph, leftCloseTarget])
      · rw [hpos] at hsucc
        obtain ⟨m, hm, hmRight⟩ :=
          (arenaFoldSeq_shape plans env n).2.1
            (plan, chain, control, st, mn) hpos
        cases hgraph : (env n).graph
        · subst hm
          exact absurd hgraph ((hnodirect m).2 hmRight)
        · refine ⟨?_, ?_⟩ <;>
            · intro data h
              rw [hsucc] at h
              exact absurd h (by
                simp [arenaStep, hgraph, rightContinueTarget])
        · refine ⟨?_, ?_⟩ <;>
            · intro data h
              rw [hsucc] at h
              exact absurd h (by
                simp [arenaStep, hgraph, rightCloseTarget])
      · exact absurd hpos (ihRL (chain, control, ent, st, mn))
      · exact absurd hpos (ihRR (chain, control, ent, st, mn))

/-! ### The tiered game path

The fold collapses the committed tier; the game path restores it: at a
boundary the path visits the boundary position and then the committed
position before the round resolves.  A round counter tracks how many
environment rounds have been consumed.
-/

/-- Resolve a committed boundary by an environment round. -/
def committedResolve
    (plan : BoundaryPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
      (Out₂ := Out₂) A C_L C_R C_V)
    (state : A.State)
    (envRound : EnvironmentRound In₁ In₂) :
    BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V :=
  match envRound.graph with
  | Graph.both =>
      A.boundaryBothTarget plan state
        (envRound.inputOne, envRound.inputTwo)
  | Graph.left =>
      A.boundaryOpenLeftTarget plan state
        (envRound.inputOne, envRound.inputTwo)
  | Graph.right =>
      A.boundaryOpenRightTarget plan state
        (envRound.inputTwo, envRound.inputOne)

theorem arenaStep_bnd
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (state minState : A.State)
    (envRound : EnvironmentRound In₁ In₂) :
    arenaStep plans (Sum.inl (state, minState)) envRound =
      committedResolve (plans (state, minState)) state envRound := by
  cases hgraph : envRound.graph <;>
    simp [arenaStep, committedResolve, hgraph]

/-- The game path with its round counter. -/
def gameAux (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) :
    Nat -> BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V × Nat
  | 0 => (Sum.inl (A.initial, A.initial), 0)
  | k + 1 =>
      match gameAux plans env k with
      | (Sum.inl (state, minState), t) =>
          (Sum.inr (Sum.inl ((state, state), plans (state, minState))), t)
      | (Sum.inr (Sum.inl ((state, _), plan)), t) =>
          (committedResolve plan state (env t), t + 1)
      | (position, t) => (arenaStep plans position (env t), t + 1)

/-- The tiered game path. -/
def gamePath (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) (k : Nat) :
    BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V :=
  (gameAux plans env k).1

/-- The number of environment rounds consumed by the game path. -/
def gameClock (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) (k : Nat) : Nat :=
  (gameAux plans env k).2

theorem gameAux_pair
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) (k : Nat) :
    gameAux plans env k = (gamePath plans env k, gameClock plans env k) :=
  rfl

/--
The game path shadows the fold: away from the committed tier it is the
fold at its clock, and at the committed tier it stores the boundary
state twice together with the plan the family commits there.
-/
theorem gameAux_shadow
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) :
    ∀ k : Nat,
      ((∀ committed,
          gamePath plans env k ≠ Sum.inr (Sum.inl committed)) ->
        gamePath plans env k =
          arenaFoldSeq plans env (gameClock plans env k)) ∧
      (∀ pair plan,
        gamePath plans env k = Sum.inr (Sum.inl (pair, plan)) ->
          pair.2 = pair.1 ∧
            ∃ minState,
              arenaFoldSeq plans env (gameClock plans env k) =
                  Sum.inl (pair.1, minState) ∧
                plan = plans (pair.1, minState)) := by
  intro k
  induction k with
  | zero =>
      constructor
      · intro _
        rfl
      · intro pair plan h
        exact absurd h (by simp [gamePath, gameAux])
  | succ k ih =>
      obtain ⟨ihShadow, ihCommitted⟩ := ih
      rcases hpos : gamePath plans env k with
        ⟨state, minState⟩ | ⟨pair, plan⟩ | inBlockL | inBlockR |
        inRevL | inRevR
      · have hfold :
            arenaFoldSeq plans env (gameClock plans env k) =
              Sum.inl (state, minState) := by
          rw [←
            ihShadow (by
              intro committed hc
              rw [hpos] at hc
              simp at hc)]
          exact hpos
        have hstep :
            gameAux plans env (k + 1) =
              (Sum.inr (Sum.inl ((state, state), plans (state, minState))),
                gameClock plans env k) := by
          have hpair :
              gameAux plans env k =
                (Sum.inl (state, minState), gameClock plans env k) := by
            rw [gameAux_pair, hpos]
          simp [gameAux, hpair]
        constructor
        · intro hnot
          exfalso
          refine hnot ((state, state), plans (state, minState)) ?_
          rw [show gamePath plans env (k + 1) =
              (gameAux plans env (k + 1)).1 from rfl, hstep]
        · intro pair' plan' h
          rw [show gamePath plans env (k + 1) =
              (gameAux plans env (k + 1)).1 from rfl, hstep] at h
          simp only [Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq] at h
          obtain ⟨hpaireq, hplaneq⟩ := h
          refine ⟨?_, minState, ?_, ?_⟩
          · rw [← hpaireq]
          · rw [show gameClock plans env (k + 1) =
                (gameAux plans env (k + 1)).2 from rfl, hstep, ← hpaireq]
            exact hfold
          · rw [← hplaneq, ← hpaireq]
      · obtain ⟨hdiag, minState, hfold, hplan⟩ :=
          ihCommitted pair plan hpos
        rcases pair with ⟨state, state'⟩
        cases hdiag
        have hpair :
            gameAux plans env k =
              (Sum.inr (Sum.inl ((state, state), plan)),
                gameClock plans env k) := by
          rw [gameAux_pair, hpos]
        have hstep :
            gameAux plans env (k + 1) =
              (committedResolve plan state (env (gameClock plans env k)),
                gameClock plans env k + 1) := by
          simp [gameAux, hpair]
        have hresolve :
            committedResolve plan state (env (gameClock plans env k)) =
              arenaFoldSeq plans env (gameClock plans env k + 1) := by
          rw [show arenaFoldSeq plans env (gameClock plans env k + 1) =
              arenaStep plans
                (arenaFoldSeq plans env (gameClock plans env k))
                (env (gameClock plans env k)) from rfl,
            hfold, arenaStep_bnd, hplan]
        constructor
        · intro _
          rw [show gamePath plans env (k + 1) =
              (gameAux plans env (k + 1)).1 from rfl, hstep,
            show gameClock plans env (k + 1) =
              (gameAux plans env (k + 1)).2 from rfl, hstep]
          exact hresolve
        · intro pair' plan' h
          rw [show gamePath plans env (k + 1) =
              (gameAux plans env (k + 1)).1 from rfl, hstep, hresolve]
            at h
          exact
            absurd h
              (arenaFoldSeq_ne_committed plans env
                (gameClock plans env k + 1) (pair', plan'))
      · have hfold :
            arenaFoldSeq plans env (gameClock plans env k) =
              Sum.inr (Sum.inr (Sum.inl inBlockL)) := by
          rw [←
            ihShadow (by
              intro committed hc
              rw [hpos] at hc
              simp at hc)]
          exact hpos
        have hpair :
            gameAux plans env k =
              (Sum.inr (Sum.inr (Sum.inl inBlockL)),
                gameClock plans env k) := by
          rw [gameAux_pair, hpos]
        have hstep :
            gameAux plans env (k + 1) =
              (arenaStep plans (Sum.inr (Sum.inr (Sum.inl inBlockL)))
                  (env (gameClock plans env k)),
                gameClock plans env k + 1) := by
          simp [gameAux, hpair]
        have hnext :
            (gameAux plans env (k + 1)).1 =
              arenaFoldSeq plans env (gameClock plans env k + 1) := by
          rw [hstep,
            show arenaFoldSeq plans env (gameClock plans env k + 1) =
              arenaStep plans
                (arenaFoldSeq plans env (gameClock plans env k))
                (env (gameClock plans env k)) from rfl,
            hfold]
        constructor
        · intro _
          rw [show gamePath plans env (k + 1) =
              (gameAux plans env (k + 1)).1 from rfl, hnext,
            show gameClock plans env (k + 1) =
              (gameAux plans env (k + 1)).2 from rfl, hstep]
        · intro pair' plan' h
          rw [show gamePath plans env (k + 1) =
              (gameAux plans env (k + 1)).1 from rfl, hnext] at h
          exact
            absurd h
              (arenaFoldSeq_ne_committed plans env
                (gameClock plans env k + 1) (pair', plan'))
      · have hfold :
            arenaFoldSeq plans env (gameClock plans env k) =
              Sum.inr (Sum.inr (Sum.inr (Sum.inl inBlockR))) := by
          rw [←
            ihShadow (by
              intro committed hc
              rw [hpos] at hc
              simp at hc)]
          exact hpos
        have hpair :
            gameAux plans env k =
              (Sum.inr (Sum.inr (Sum.inr (Sum.inl inBlockR))),
                gameClock plans env k) := by
          rw [gameAux_pair, hpos]
        have hstep :
            gameAux plans env (k + 1) =
              (arenaStep plans (Sum.inr (Sum.inr (Sum.inr (Sum.inl inBlockR))))
                  (env (gameClock plans env k)),
                gameClock plans env k + 1) := by
          simp [gameAux, hpair]
        have hnext :
            (gameAux plans env (k + 1)).1 =
              arenaFoldSeq plans env (gameClock plans env k + 1) := by
          rw [hstep,
            show arenaFoldSeq plans env (gameClock plans env k + 1) =
              arenaStep plans
                (arenaFoldSeq plans env (gameClock plans env k))
                (env (gameClock plans env k)) from rfl,
            hfold]
        constructor
        · intro _
          rw [show gamePath plans env (k + 1) =
              (gameAux plans env (k + 1)).1 from rfl, hnext,
            show gameClock plans env (k + 1) =
              (gameAux plans env (k + 1)).2 from rfl, hstep]
        · intro pair' plan' h
          rw [show gamePath plans env (k + 1) =
              (gameAux plans env (k + 1)).1 from rfl, hnext] at h
          exact
            absurd h
              (arenaFoldSeq_ne_committed plans env
                (gameClock plans env k + 1) (pair', plan'))

      · have hfold :
            arenaFoldSeq plans env (gameClock plans env k) =
              Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl inRevL)))) := by
          rw [←
            ihShadow (by
              intro committed hc
              rw [hpos] at hc
              simp at hc)]
          exact hpos
        have hpair :
            gameAux plans env k =
              (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl inRevL)))),
                gameClock plans env k) := by
          rw [gameAux_pair, hpos]
        have hstep :
            gameAux plans env (k + 1) =
              (arenaStep plans (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl inRevL)))))
                  (env (gameClock plans env k)),
                gameClock plans env k + 1) := by
          simp [gameAux, hpair]
        have hnext :
            (gameAux plans env (k + 1)).1 =
              arenaFoldSeq plans env (gameClock plans env k + 1) := by
          rw [hstep,
            show arenaFoldSeq plans env (gameClock plans env k + 1) =
              arenaStep plans
                (arenaFoldSeq plans env (gameClock plans env k))
                (env (gameClock plans env k)) from rfl,
            hfold]
        constructor
        · intro _
          rw [show gamePath plans env (k + 1) =
              (gameAux plans env (k + 1)).1 from rfl, hnext,
            show gameClock plans env (k + 1) =
              (gameAux plans env (k + 1)).2 from rfl, hstep]
        · intro pair' plan' h
          rw [show gamePath plans env (k + 1) =
              (gameAux plans env (k + 1)).1 from rfl, hnext] at h
          exact
            absurd h
              (arenaFoldSeq_ne_committed plans env
                (gameClock plans env k + 1) (pair', plan'))
      · have hfold :
            arenaFoldSeq plans env (gameClock plans env k) =
              Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr inRevR)))) := by
          rw [←
            ihShadow (by
              intro committed hc
              rw [hpos] at hc
              simp at hc)]
          exact hpos
        have hpair :
            gameAux plans env k =
              (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr inRevR)))),
                gameClock plans env k) := by
          rw [gameAux_pair, hpos]
        have hstep :
            gameAux plans env (k + 1) =
              (arenaStep plans (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr inRevR)))))
                  (env (gameClock plans env k)),
                gameClock plans env k + 1) := by
          simp [gameAux, hpair]
        have hnext :
            (gameAux plans env (k + 1)).1 =
              arenaFoldSeq plans env (gameClock plans env k + 1) := by
          rw [hstep,
            show arenaFoldSeq plans env (gameClock plans env k + 1) =
              arenaStep plans
                (arenaFoldSeq plans env (gameClock plans env k))
                (env (gameClock plans env k)) from rfl,
            hfold]
        constructor
        · intro _
          rw [show gamePath plans env (k + 1) =
              (gameAux plans env (k + 1)).1 from rfl, hnext,
            show gameClock plans env (k + 1) =
              (gameAux plans env (k + 1)).2 from rfl, hstep]
        · intro pair' plan' h
          rw [show gamePath plans env (k + 1) =
              (gameAux plans env (k + 1)).1 from rfl, hnext] at h
          exact
            absurd h
              (arenaFoldSeq_ne_committed plans env
                (gameClock plans env k + 1) (pair', plan'))

theorem gamePath_succ_bnd
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂)
    {k : Nat} {state minState : A.State}
    (hpos : gamePath plans env k = Sum.inl (state, minState)) :
    gamePath plans env (k + 1) =
        Sum.inr (Sum.inl ((state, state), plans (state, minState))) ∧
      gameClock plans env (k + 1) = gameClock plans env k := by
  have hpair :
      gameAux plans env k =
        (Sum.inl (state, minState), gameClock plans env k) := by
    rw [gameAux_pair, hpos]
  constructor
  · show (gameAux plans env (k + 1)).1 = _
    simp [gameAux, hpair]
  · show (gameAux plans env (k + 1)).2 = _
    simp [gameAux, hpair]

theorem gamePath_succ_committed
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂)
    {k : Nat} {state state' : A.State}
    {plan :
      BoundaryPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
        (Out₂ := Out₂) A C_L C_R C_V}
    (hpos :
      gamePath plans env k = Sum.inr (Sum.inl ((state, state'), plan))) :
    gamePath plans env (k + 1) =
        committedResolve plan state (env (gameClock plans env k)) ∧
      gameClock plans env (k + 1) = gameClock plans env k + 1 := by
  have hpair :
      gameAux plans env k =
        (Sum.inr (Sum.inl ((state, state'), plan)),
          gameClock plans env k) := by
    rw [gameAux_pair, hpos]
  constructor
  · show (gameAux plans env (k + 1)).1 = _
    simp [gameAux, hpair]
  · show (gameAux plans env (k + 1)).2 = _
    simp [gameAux, hpair]

theorem gamePath_succ_inBlockL
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂)
    {k : Nat}
    {data :
      LeftBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
          (Out₂ := Out₂) A C_L ×
        ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
            (Out₂ := Out₂) A C_L C_R C_V ×
        C_L × A.State × A.State}
    (hpos :
      gamePath plans env k = Sum.inr (Sum.inr (Sum.inl data))) :
    gamePath plans env (k + 1) =
        arenaStep plans (Sum.inr (Sum.inr (Sum.inl data)))
          (env (gameClock plans env k)) ∧
      gameClock plans env (k + 1) = gameClock plans env k + 1 := by
  have hpair :
      gameAux plans env k =
        (Sum.inr (Sum.inr (Sum.inl data)), gameClock plans env k) := by
    rw [gameAux_pair, hpos]
  constructor
  · show (gameAux plans env (k + 1)).1 = _
    simp [gameAux, hpair]
  · show (gameAux plans env (k + 1)).2 = _
    simp [gameAux, hpair]

theorem gamePath_succ_inBlockR
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂)
    {k : Nat}
    {data :
      RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
          (Out₂ := Out₂) A C_R ×
        ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
            (Out₂ := Out₂) A C_L C_R C_V ×
        C_R × A.State × A.State}
    (hpos :
      gamePath plans env k =
        Sum.inr (Sum.inr (Sum.inr (Sum.inl data)))) :
    gamePath plans env (k + 1) =
        arenaStep plans (Sum.inr (Sum.inr (Sum.inr (Sum.inl data))))
          (env (gameClock plans env k)) ∧
      gameClock plans env (k + 1) = gameClock plans env k + 1 := by
  have hpair :
      gameAux plans env k =
        (Sum.inr (Sum.inr (Sum.inr (Sum.inl data))),
          gameClock plans env k) := by
    rw [gameAux_pair, hpos]
  constructor
  · show (gameAux plans env (k + 1)).1 = _
    simp [gameAux, hpair]
  · show (gameAux plans env (k + 1)).2 = _
    simp [gameAux, hpair]

theorem gamePath_succ_inRevL
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂)
    {k : Nat}
    {data :
      ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
          (Out₂ := Out₂) A C_L C_R C_V ×
        C_V × (A.State × A.State) × A.State × A.State}
    (hpos :
      gamePath plans env k =
        Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl data))))) :
    gamePath plans env (k + 1) =
        arenaStep plans
          (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl data)))))
          (env (gameClock plans env k)) ∧
      gameClock plans env (k + 1) = gameClock plans env k + 1 := by
  have hpair :
      gameAux plans env k =
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl data)))),
          gameClock plans env k) := by
    rw [gameAux_pair, hpos]
  constructor
  · show (gameAux plans env (k + 1)).1 = _
    simp [gameAux, hpair]
  · show (gameAux plans env (k + 1)).2 = _
    simp [gameAux, hpair]

theorem gamePath_succ_inRevR
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂)
    {k : Nat}
    {data :
      ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
          (Out₂ := Out₂) A C_L C_R C_V ×
        C_V × (A.State × A.State) × A.State × A.State}
    (hpos :
      gamePath plans env k =
        Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr data))))) :
    gamePath plans env (k + 1) =
        arenaStep plans
          (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr data)))))
          (env (gameClock plans env k)) ∧
      gameClock plans env (k + 1) = gameClock plans env k + 1 := by
  have hpair :
      gameAux plans env k =
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr data)))),
          gameClock plans env k) := by
    rw [gameAux_pair, hpos]
  constructor
  · show (gameAux plans env (k + 1)).1 = _
    simp [gameAux, hpair]
  · show (gameAux plans env (k + 1)).2 = _
    simp [gameAux, hpair]

section GamePathLegality

variable
  [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
  [DecidableEq In₁] [DecidableEq In₂] [DecidableEq A.State]
  [Fintype C_L] [DecidableEq C_L] [Fintype C_R] [DecidableEq C_R]
  [Fintype C_V] [DecidableEq C_V]
  [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
  [Inhabited C_L] [Inhabited C_R] [Inhabited C_V]

/-- The game path is a play of the boundary game from the initial
boundary. -/
theorem gamePath_playFrom
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) :
    (DetParityAutomaton.boundaryGame A C_L C_R C_V).PlayFrom
      (Sum.inl (A.initial, A.initial)) (gamePath plans env) := by
  constructor
  · rfl
  · intro k
    obtain ⟨ihShadow, ihCommitted⟩ := gameAux_shadow plans env k
    rcases hpos : gamePath plans env k with
      ⟨state, minState⟩ | ⟨pair, plan⟩ | inBlockL | inBlockR |
      inRevL | inRevR
    · obtain ⟨hstep, _⟩ := gamePath_succ_bnd plans env hpos
      rw [hstep]
      exact ⟨plans (state, minState), rfl⟩
    · obtain ⟨hdiag, minState, hfold, hplan⟩ :=
        ihCommitted pair plan hpos
      rcases pair with ⟨state, state'⟩
      cases hdiag
      obtain ⟨hstep, _⟩ := gamePath_succ_committed plans env hpos
      rw [hstep]
      cases hgraph : (env (gameClock plans env k)).graph
      · exact
          Or.inr (Or.inl
            ⟨((env (gameClock plans env k)).inputOne,
                (env (gameClock plans env k)).inputTwo),
              by simp [committedResolve, hgraph]⟩)
      · exact
          Or.inr (Or.inr
            ⟨((env (gameClock plans env k)).inputTwo,
                (env (gameClock plans env k)).inputOne),
              by simp [committedResolve, hgraph]⟩)
      · exact
          Or.inl
            ⟨((env (gameClock plans env k)).inputOne,
                (env (gameClock plans env k)).inputTwo),
              by simp [committedResolve, hgraph]⟩
    · obtain ⟨hstep, _⟩ := gamePath_succ_inBlockL plans env hpos
      obtain ⟨plan, chain, control, state, minState⟩ := inBlockL
      rw [hstep]
      cases hgraph : (env (gameClock plans env k)).graph
      · exact
          Or.inl
            ⟨((env (gameClock plans env k)).inputOne,
                (env (gameClock plans env k)).inputTwo),
              by simp [arenaStep, hgraph]⟩
      · exact
          Or.inr (Or.inr
            ⟨((env (gameClock plans env k)).inputOne,
                (env (gameClock plans env k)).inputTwo),
              by simp [arenaStep, hgraph]⟩)
      · exact
          Or.inr (Or.inl
            ⟨((env (gameClock plans env k)).inputOne,
                (env (gameClock plans env k)).inputTwo),
              by simp [arenaStep, hgraph]⟩)
    · obtain ⟨hstep, _⟩ := gamePath_succ_inBlockR plans env hpos
      obtain ⟨plan, chain, control, state, minState⟩ := inBlockR
      rw [hstep]
      cases hgraph : (env (gameClock plans env k)).graph
      · exact
          Or.inr (Or.inr
            ⟨((env (gameClock plans env k)).inputTwo,
                (env (gameClock plans env k)).inputOne),
              by simp [arenaStep, hgraph]⟩)
      · exact
          Or.inl
            ⟨((env (gameClock plans env k)).inputTwo,
                (env (gameClock plans env k)).inputOne),
              by simp [arenaStep, hgraph]⟩
      · exact
          Or.inr (Or.inl
            ⟨((env (gameClock plans env k)).inputTwo,
                (env (gameClock plans env k)).inputOne),
              by simp [arenaStep, hgraph]⟩)
    · obtain ⟨hstep, _⟩ := gamePath_succ_inRevL plans env hpos
      obtain ⟨chain, control, entry, state, minState⟩ := inRevL
      rw [hstep]
      cases hgraph : (env (gameClock plans env k)).graph
      · exact
          Or.inl
            ⟨((env (gameClock plans env k)).inputOne,
                (env (gameClock plans env k)).inputTwo),
              by simp [arenaStep, hgraph]⟩
      · exact
          Or.inr (Or.inr
            ⟨((env (gameClock plans env k)).inputOne,
                (env (gameClock plans env k)).inputTwo),
              by simp [arenaStep, hgraph]⟩)
      · exact
          Or.inr (Or.inl
            ⟨((env (gameClock plans env k)).inputOne,
                (env (gameClock plans env k)).inputTwo),
              by simp [arenaStep, hgraph]⟩)
    · obtain ⟨hstep, _⟩ := gamePath_succ_inRevR plans env hpos
      obtain ⟨chain, control, entry, state, minState⟩ := inRevR
      rw [hstep]
      cases hgraph : (env (gameClock plans env k)).graph
      · exact
          Or.inr (Or.inr
            ⟨((env (gameClock plans env k)).inputOne,
                (env (gameClock plans env k)).inputTwo),
              by simp [arenaStep, hgraph]⟩)
      · exact
          Or.inl
            ⟨((env (gameClock plans env k)).inputOne,
                (env (gameClock plans env k)).inputTwo),
              by simp [arenaStep, hgraph]⟩
      · exact
          Or.inr (Or.inl
            ⟨((env (gameClock plans env k)).inputOne,
                (env (gameClock plans env k)).inputTwo),
              by simp [arenaStep, hgraph]⟩)

/-- A positional Even strategy commits a plan at every boundary. -/
theorem exists_plan_of_positionalStrategy
    (τ :
      (DetParityAutomaton.boundaryGame A C_L C_R C_V).PositionalStrategy
        ParityPlayer.even)
    (atom : A.State × A.State) :
    ∃ plan :
        BoundaryPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
          (Out₂ := Out₂) A C_L C_R C_V,
      τ.move (Sum.inl atom) =
        Sum.inr (Sum.inl ((atom.1, atom.1), plan)) := by
  have h := τ.legal (Sum.inl atom) rfl
  rcases atom with ⟨state, minState⟩
  exact h

/-- The plan family committed by a positional Even strategy. -/
noncomputable def plansOf
    (τ :
      (DetParityAutomaton.boundaryGame A C_L C_R C_V).PositionalStrategy
        ParityPlayer.even) :
    PlanFamily (In₁ := In₁) A C_L C_R C_V :=
  fun atom => (exists_plan_of_positionalStrategy τ atom).choose

/-- The positional Even strategy that commits a prescribed plan family `Q`: at
every boundary atom it plays the block-plan move carrying `Q atom`; elsewhere
(Odd-owned positions) its move is irrelevant.  This is a right inverse of
`plansOf` (`plansOf_committingStrategy`), so every plan family is realized by
some positional strategy -- in particular a folded, `ReversalMeasurable` family. -/
def committingStrategy (Q : PlanFamily (In₁ := In₁) A C_L C_R C_V) :
    (DetParityAutomaton.boundaryGame A C_L C_R C_V).PositionalStrategy
      ParityPlayer.even where
  move
    | Sum.inl atom => Sum.inr (Sum.inl ((atom.1, atom.1), Q atom))
    | other => other
  legal := by
    intro pos howner
    rcases pos with atom | other
    · obtain ⟨state, minState⟩ := atom
      exact ⟨Q (state, minState), rfl⟩
    · exact absurd howner
        (by simp [DetParityAutomaton.boundaryGame, boundaryOwner])

/-- `plansOf` is a retraction: `committingStrategy Q` commits exactly `Q`.  Hence
`plansOf` is surjective -- every plan family, including a θ̄-folded one, arises
from a positional strategy. -/
theorem plansOf_committingStrategy
    (Q : PlanFamily (In₁ := In₁) A C_L C_R C_V) :
    plansOf (committingStrategy Q) = Q := by
  funext atom
  have hspec :=
    (exists_plan_of_positionalStrategy (committingStrategy Q) atom).choose_spec
  have hmove :
      (committingStrategy (In₁ := In₁) Q).move (Sum.inl atom) =
        Sum.inr (Sum.inl ((atom.1, atom.1), Q atom)) := rfl
  have heq := hmove.symm.trans hspec
  exact (congrArg Prod.snd (Sum.inl.inj (Sum.inr.inj heq))).symm

/-- The game path of the committed plan family is consistent with the
positional strategy. -/
theorem gamePath_consistent
    (τ :
      (DetParityAutomaton.boundaryGame A C_L C_R C_V).PositionalStrategy
        ParityPlayer.even)
    (env : EnvironmentSequence In₁ In₂) :
    CountableParityGame.PositionalStrategy.Consistent
      (G := DetParityAutomaton.boundaryGame A C_L C_R C_V) τ
      (gamePath (plansOf τ) env) := by
  intro k howner
  rcases hpos : gamePath (plansOf τ) env k with
    ⟨state, minState⟩ | ⟨pair, plan⟩ | inBlockL | inBlockR
  · obtain ⟨hstep, _⟩ := gamePath_succ_bnd (plansOf τ) env hpos
    rw [hstep]
    exact
      ((exists_plan_of_positionalStrategy τ (state, minState)).choose_spec).symm
  · rw [hpos] at howner
    exact absurd howner (by simp [DetParityAutomaton.boundaryGame,
      boundaryOwner])
  · rw [hpos] at howner
    exact absurd howner (by simp [DetParityAutomaton.boundaryGame,
      boundaryOwner])
  · rw [hpos] at howner
    exact absurd howner (by simp [DetParityAutomaton.boundaryGame,
      boundaryOwner])

/--
A winning positional Even strategy of the boundary game wins along the
game path of every real no-direct play: the path's minimal recurring
game priority is even.
-/
theorem gamePath_minPriorityEven
    (τ :
      (DetParityAutomaton.boundaryGame A C_L C_R C_V).PositionalStrategy
        ParityPlayer.even)
    (hwin :
      CountableParityGame.PositionalStrategy.WinningFrom
        (G := DetParityAutomaton.boundaryGame A C_L C_R C_V) τ
        (Sum.inl (A.initial, A.initial)))
    (env : EnvironmentSequence In₁ In₂) :
    (DetParityAutomaton.boundaryGame A C_L C_R C_V).MinPriorityEven
      (gamePath (plansOf τ) env) :=
  hwin (gamePath (plansOf τ) env)
    (gamePath_playFrom (plansOf τ) env)
    (gamePath_consistent τ env)

end GamePathLegality

/-! ### Clock growth, reach, and priority emission -/

theorem gameClock_le_succ
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) (k : Nat) :
    gameClock plans env k ≤ gameClock plans env (k + 1) := by
  rcases hpos : gamePath plans env k with
    ⟨state, minState⟩ | ⟨⟨state, state'⟩, plan⟩ | inBlockL | inBlockR |
    inRevL | inRevR
  · rw [(gamePath_succ_bnd plans env hpos).2]
  · rw [(gamePath_succ_committed plans env hpos).2]
    exact Nat.le_succ _
  · rw [(gamePath_succ_inBlockL plans env hpos).2]
    exact Nat.le_succ _
  · rw [(gamePath_succ_inBlockR plans env hpos).2]
    exact Nat.le_succ _
  · rw [(gamePath_succ_inRevL plans env hpos).2]
    exact Nat.le_succ _
  · rw [(gamePath_succ_inRevR plans env hpos).2]
    exact Nat.le_succ _

theorem gameClock_mono
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) :
    Monotone (gameClock plans env) :=
  monotone_nat_of_le_succ (gameClock_le_succ plans env)

theorem gameClock_le
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) :
    ∀ k : Nat, gameClock plans env k ≤ k := by
  intro k
  induction k with
  | zero => exact Nat.le_refl 0
  | succ k ih =>
      rcases hpos : gamePath plans env k with
        ⟨state, minState⟩ | ⟨⟨state, state'⟩, plan⟩ | inBlockL | inBlockR |
        inRevL | inRevR
      · rw [(gamePath_succ_bnd plans env hpos).2]
        exact Nat.le_succ_of_le ih
      · rw [(gamePath_succ_committed plans env hpos).2]
        omega
      · rw [(gamePath_succ_inBlockL plans env hpos).2]
        omega
      · rw [(gamePath_succ_inBlockR plans env hpos).2]
        omega
      · rw [(gamePath_succ_inRevL plans env hpos).2]
        omega
      · rw [(gamePath_succ_inRevR plans env hpos).2]
        omega

theorem gameClock_two_step
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) (k : Nat) :
    gameClock plans env k + 1 ≤ gameClock plans env (k + 2) := by
  have hcast :
      gameClock plans env (k + 1 + 1) = gameClock plans env (k + 2) :=
    rfl
  rcases hpos : gamePath plans env k with
    ⟨state, minState⟩ | ⟨⟨state, state'⟩, plan⟩ | inBlockL | inBlockR |
    inRevL | inRevR
  · obtain ⟨hnext, hclock⟩ := gamePath_succ_bnd plans env hpos
    have hclock2 :=
      (gamePath_succ_committed plans env (k := k + 1) hnext).2
    omega
  · have hclock := (gamePath_succ_committed plans env hpos).2
    have hmono := gameClock_le_succ plans env (k + 1)
    omega
  · have hclock := (gamePath_succ_inBlockL plans env hpos).2
    have hmono := gameClock_le_succ plans env (k + 1)
    omega
  · have hclock := (gamePath_succ_inBlockR plans env hpos).2
    have hmono := gameClock_le_succ plans env (k + 1)
    omega
  · have hclock := (gamePath_succ_inRevL plans env hpos).2
    have hmono := gameClock_le_succ plans env (k + 1)
    omega
  · have hclock := (gamePath_succ_inRevR plans env hpos).2
    have hmono := gameClock_le_succ plans env (k + 1)
    omega

theorem le_gameClock_two_mul
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) :
    ∀ n : Nat, n ≤ gameClock plans env (2 * n) := by
  intro n
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
      have hstep := gameClock_two_step plans env (2 * n)
      have hrw : 2 * (n + 1) = 2 * n + 2 := by omega
      rw [hrw]
      omega

/-- Every round is reached by the game path with the fold's position. -/
theorem exists_gamePath_reach
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) :
    ∀ t : Nat,
      ∃ k : Nat,
        gameClock plans env k = t ∧
          gamePath plans env k = arenaFoldSeq plans env t := by
  intro t
  induction t with
  | zero => exact ⟨0, rfl, rfl⟩
  | succ t ih =>
      obtain ⟨k, hclock, hpath⟩ := ih
      rcases hfold : arenaFoldSeq plans env t with
        ⟨state, minState⟩ | committed | inBlockL | inBlockR |
        inRevL | inRevR
      · rw [hfold] at hpath
        obtain ⟨hnext, hclock1⟩ := gamePath_succ_bnd plans env hpath
        obtain ⟨hnext2, hclock2⟩ :=
          gamePath_succ_committed plans env (k := k + 1) hnext
        refine ⟨k + 1 + 1, by omega, ?_⟩
        rw [hnext2, hclock1, hclock,
          show arenaFoldSeq plans env (t + 1) =
            arenaStep plans (arenaFoldSeq plans env t) (env t) from rfl,
          hfold, arenaStep_bnd]
      · exact
          absurd hfold (arenaFoldSeq_ne_committed plans env t committed)
      · rw [hfold] at hpath
        obtain ⟨hnext, hclock1⟩ :=
          gamePath_succ_inBlockL plans env hpath
        refine ⟨k + 1, by omega, ?_⟩
        rw [hnext, hclock,
          show arenaFoldSeq plans env (t + 1) =
            arenaStep plans (arenaFoldSeq plans env t) (env t) from rfl,
          hfold]
      · rw [hfold] at hpath
        obtain ⟨hnext, hclock1⟩ :=
          gamePath_succ_inBlockR plans env hpath
        refine ⟨k + 1, by omega, ?_⟩
        rw [hnext, hclock,
          show arenaFoldSeq plans env (t + 1) =
            arenaStep plans (arenaFoldSeq plans env t) (env t) from rfl,
          hfold]
      · rw [hfold] at hpath
        obtain ⟨hnext, hclock1⟩ :=
          gamePath_succ_inRevL plans env hpath
        refine ⟨k + 1, by omega, ?_⟩
        rw [hnext, hclock,
          show arenaFoldSeq plans env (t + 1) =
            arenaStep plans (arenaFoldSeq plans env t) (env t) from rfl,
          hfold]
      · rw [hfold] at hpath
        obtain ⟨hnext, hclock1⟩ :=
          gamePath_succ_inRevR plans env hpath
        refine ⟨k + 1, by omega, ?_⟩
        rw [hnext, hclock,
          show arenaFoldSeq plans env (t + 1) =
            arenaStep plans (arenaFoldSeq plans env t) (env t) from rfl,
          hfold]

/--
Every run priority of the emitted word is emitted by the game path at
an index at least its round: block positions emit interior run
priorities, and the committed tier emits the boundary state's priority.
-/
theorem exists_gamePriority_emission
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂)
    (t : Nat) :
    ∃ k : Nat,
      t ≤ k ∧
        boundaryPriority A C_L C_R C_V (gamePath plans env k) =
          A.priority (A.run (arenaWord plans env) t) := by
  obtain ⟨k, hclock, hpath⟩ := exists_gamePath_reach plans env t
  have hstate := positionState_arenaFoldSeq plans env t
  have htk : t ≤ k := by
    have := gameClock_le plans env k
    omega
  rcases hfold : arenaFoldSeq plans env t with
    ⟨state, minState⟩ | committed | inBlockL | inBlockR |
    inRevL | inRevR
  · rw [hfold] at hpath hstate
    obtain ⟨hnext, _⟩ := gamePath_succ_bnd plans env hpath
    refine ⟨k + 1, by omega, ?_⟩
    rw [hnext]
    show A.priority state = _
    rw [← hstate]
    rfl
  · exact
      absurd hfold (arenaFoldSeq_ne_committed plans env t committed)
  · rw [hfold] at hpath hstate
    obtain ⟨plan, chain, control, state, minState⟩ := inBlockL
    refine ⟨k, htk, ?_⟩
    rw [hpath]
    show A.priority state = _
    rw [← hstate]
    rfl
  · rw [hfold] at hpath hstate
    obtain ⟨plan, chain, control, state, minState⟩ := inBlockR
    refine ⟨k, htk, ?_⟩
    rw [hpath]
    show A.priority state = _
    rw [← hstate]
    rfl
  · rw [hfold] at hpath hstate
    obtain ⟨chain, control, entry, state, minState⟩ := inRevL
    refine ⟨k, htk, ?_⟩
    rw [hpath]
    show A.priority state = _
    rw [← hstate]
    rfl
  · rw [hfold] at hpath hstate
    obtain ⟨chain, control, entry, state, minState⟩ := inRevR
    refine ⟨k, htk, ?_⟩
    rw [hpath]
    show A.priority state = _
    rw [← hstate]
    rfl

/-- The tracked state equals one of its two arguments. -/
theorem minPriorityState_eq_or
    {A :
      DetParityAutomaton.{max u v x y, s}
        (RoundRecord In₁ In₂ Graph Out₁ Out₂)}
    (incumbent next : A.State) :
    A.minPriorityState incumbent next = next ∨
      A.minPriorityState incumbent next = incumbent := by
  unfold minPriorityState
  split
  · exact Or.inl rfl
  · exact Or.inr rfl


/--
Attainment of the tracked minimum: the minimal-priority state stored in
a fold position is a run state of the current block, at an index
dominating every earlier boundary time of the fold.
-/
theorem arenaFold_min_attained
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) :
    ∀ t : Nat,
      (∀ state minState,
        arenaFoldSeq plans env t = Sum.inl (state, minState) ->
          t = 0 ∨
            ∃ j : Nat,
              j < t ∧
                minState = A.run (arenaWord plans env) j ∧
                ∀ b : Nat, b < t ->
                  (∃ pair, arenaFoldSeq plans env b = Sum.inl pair) ->
                    b ≤ j) ∧
      (∀ data :
          LeftBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
              (Out₂ := Out₂) A C_L ×
            ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
                (Out₂ := Out₂) A C_L C_R C_V ×
            C_L × A.State × A.State,
        arenaFoldSeq plans env t = Sum.inr (Sum.inr (Sum.inl data)) ->
          ∃ j : Nat,
            j ≤ t ∧
              data.2.2.2.2 = A.run (arenaWord plans env) j ∧
              ∀ b : Nat, b ≤ t ->
                (∃ pair, arenaFoldSeq plans env b = Sum.inl pair) ->
                  b ≤ j) ∧
      (∀ data :
          RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
              (Out₂ := Out₂) A C_R ×
            ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
                (Out₂ := Out₂) A C_L C_R C_V ×
            C_R × A.State × A.State,
        arenaFoldSeq plans env t = Sum.inr (Sum.inr (Sum.inr (Sum.inl data))) ->
          ∃ j : Nat,
            j ≤ t ∧
              data.2.2.2.2 = A.run (arenaWord plans env) j ∧
              ∀ b : Nat, b ≤ t ->
                (∃ pair, arenaFoldSeq plans env b = Sum.inl pair) ->
                  b ≤ j) ∧
      (∀ data :
          ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
                (Out₂ := Out₂) A C_L C_R C_V ×
            C_V × (A.State × A.State) × A.State × A.State,
        arenaFoldSeq plans env t = Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl data)))) ->
          ∃ j : Nat,
            j ≤ t ∧
              data.2.2.2.2 = A.run (arenaWord plans env) j ∧
              ∀ b : Nat, b ≤ t ->
                (∃ pair, arenaFoldSeq plans env b = Sum.inl pair) ->
                  b ≤ j) ∧
      (∀ data :
          ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
                (Out₂ := Out₂) A C_L C_R C_V ×
            C_V × (A.State × A.State) × A.State × A.State,
        arenaFoldSeq plans env t = Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr data)))) ->
          ∃ j : Nat,
            j ≤ t ∧
              data.2.2.2.2 = A.run (arenaWord plans env) j ∧
              ∀ b : Nat, b ≤ t ->
                (∃ pair, arenaFoldSeq plans env b = Sum.inl pair) ->
                  b ≤ j) := by
  intro t
  induction t with
  | zero =>
      refine ⟨fun state minState _ => Or.inl rfl, ?_, ?_, ?_, ?_⟩ <;>
        · intro data h
          exact absurd h (by simp [arenaFoldSeq])
  | succ t ih =>
      obtain ⟨ihBnd, ihL, ihR, ihRL, ihRR⟩ := ih
      have hrunT := positionState_arenaFoldSeq plans env t
      have hrunT1 := positionState_arenaFoldSeq plans env (t + 1)
      have hsucc :
          arenaFoldSeq plans env (t + 1) =
            arenaStep plans (arenaFoldSeq plans env t) (env t) := rfl
      rw [hsucc] at hrunT1
      rcases hfold : arenaFoldSeq plans env t with
        ⟨state, mn⟩ | committed | ⟨plan, chain, control, st, mn⟩ |
        ⟨plan, chain, control, st, mn⟩ |
        ⟨chain, control, ent, st, mn⟩ | ⟨chain, control, ent, st, mn⟩
      · rw [hfold] at hsucc hrunT
        rw [hfold] at hrunT1
        have hq : state = A.run (arenaWord plans env) t := hrunT
        cases hgraph : (env t).graph
        · -- left opening
          simp only [arenaStep, hgraph, boundaryOpenLeftTarget,
            positionState] at hrunT1
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · intro state' minState' h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, boundaryOpenLeftTarget])
          · rintro ⟨dplan, dchain, dctl, dst, dmn⟩ h
            rw [hsucc] at h
            simp only [arenaStep, hgraph, boundaryOpenLeftTarget,
              Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq] at h
            obtain ⟨-, -, -, -, hdmn⟩ := h
            rw [hrunT1] at hdmn
            rcases minPriorityState_eq_or (A := A) state
                (A.run (arenaWord plans env) (t + 1)) with heq | heq
            · refine ⟨t + 1, Nat.le_refl _, ?_, fun b hb _ => hb⟩
              show dmn = _
              rw [← hdmn, heq]
            · refine ⟨t, Nat.le_succ t, ?_, ?_⟩
              · show dmn = _
                rw [← hdmn, heq, hq]
              · intro b hb hpair
                by_cases hbe : b = t + 1
                · subst hbe
                  obtain ⟨pair, hpairb⟩ := hpair
                  rw [hsucc] at hpairb
                  simp [arenaStep, hgraph, boundaryOpenLeftTarget] at hpairb
                · omega
          · intro data h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, boundaryOpenLeftTarget])
          · intro data h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, boundaryOpenLeftTarget])
          · intro data h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, boundaryOpenLeftTarget])
        · -- right opening
          simp only [arenaStep, hgraph, boundaryOpenRightTarget,
            positionState] at hrunT1
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · intro state' minState' h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, boundaryOpenRightTarget])
          · intro data h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, boundaryOpenRightTarget])
          · rintro ⟨dplan, dchain, dctl, dst, dmn⟩ h
            rw [hsucc] at h
            simp only [arenaStep, hgraph, boundaryOpenRightTarget,
              Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq] at h
            obtain ⟨-, -, -, -, hdmn⟩ := h
            rw [hrunT1] at hdmn
            rcases minPriorityState_eq_or (A := A) state
                (A.run (arenaWord plans env) (t + 1)) with heq | heq
            · refine ⟨t + 1, Nat.le_refl _, ?_, fun b hb _ => hb⟩
              show dmn = _
              rw [← hdmn, heq]
            · refine ⟨t, Nat.le_succ t, ?_, ?_⟩
              · show dmn = _
                rw [← hdmn, heq, hq]
              · intro b hb hpair
                by_cases hbe : b = t + 1
                · subst hbe
                  obtain ⟨pair, hpairb⟩ := hpair
                  rw [hsucc] at hpairb
                  simp [arenaStep, hgraph, boundaryOpenRightTarget] at hpairb
                · omega
          · intro data h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, boundaryOpenRightTarget])
          · intro data h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, boundaryOpenRightTarget])
        · -- synchronizing round
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · intro state' minState' h
            rw [hsucc] at h
            simp only [arenaStep, hgraph, boundaryBothTarget,
              Sum.inl.injEq, Prod.mk.injEq] at h
            obtain ⟨-, hmn⟩ := h
            refine Or.inr ⟨t, Nat.lt_succ_self t, ?_, ?_⟩
            · rw [← hmn, hq]
            · intro b hb hpair
              omega
          · intro data h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, boundaryBothTarget])
          · intro data h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, boundaryBothTarget])
          · intro data h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, boundaryBothTarget])
          · intro data h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, boundaryBothTarget])
      · exact
          absurd hfold (arenaFoldSeq_ne_committed plans env t committed)
      · rw [hfold] at hsucc hrunT
        rw [hfold] at hrunT1
        obtain ⟨j, hjle, hjeq, hjbound⟩ :=
          ihL (plan, chain, control, st, mn) hfold
        have hjeq' : mn = A.run (arenaWord plans env) j := hjeq
        cases hgraph : (env t).graph
        · -- continuation
          simp only [arenaStep, hgraph, leftContinueTarget,
            positionState] at hrunT1
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · intro state' minState' h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, leftContinueTarget])
          · rintro ⟨dplan, dchain, dctl, dst, dmn⟩ h
            rw [hsucc] at h
            simp only [arenaStep, hgraph, leftContinueTarget,
              Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq] at h
            obtain ⟨-, -, -, -, hdmn⟩ := h
            rw [hrunT1] at hdmn
            rcases minPriorityState_eq_or (A := A) mn
                (A.run (arenaWord plans env) (t + 1)) with heq | heq
            · refine ⟨t + 1, Nat.le_refl _, ?_, fun b hb _ => hb⟩
              show dmn = _
              rw [← hdmn, heq]
            · refine ⟨j, Nat.le_succ_of_le hjle, ?_, ?_⟩
              · show dmn = _
                rw [← hdmn, heq, hjeq']
              · intro b hb hpair
                by_cases hbe : b = t + 1
                · subst hbe
                  obtain ⟨pair, hpairb⟩ := hpair
                  rw [hsucc] at hpairb
                  simp [arenaStep, hgraph, leftContinueTarget] at hpairb
                · exact hjbound b (by omega) hpair
          · intro data h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, leftContinueTarget])
          · intro data h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, leftContinueTarget])
          · intro data h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, leftContinueTarget])
        · -- direct reversal
          simp only [arenaStep, hgraph, leftReverseTarget,
            positionState] at hrunT1
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · intro state' minState' h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, leftReverseTarget])
          · intro data h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, leftReverseTarget])
          · intro data h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, leftReverseTarget])
          · intro data h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, leftReverseTarget])
          · rintro ⟨dchain, dctl, dent, dst, dmn⟩ h
            rw [hsucc] at h
            simp only [arenaStep, hgraph, leftReverseTarget,
              Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq] at h
            obtain ⟨-, -, -, -, hdmn⟩ := h
            rw [hrunT1] at hdmn
            rcases minPriorityState_eq_or (A := A) mn
                (A.run (arenaWord plans env) (t + 1)) with heq | heq
            · refine ⟨t + 1, Nat.le_refl _, ?_, fun b hb _ => hb⟩
              show dmn = _
              rw [← hdmn, heq]
            · refine ⟨j, Nat.le_succ_of_le hjle, ?_, ?_⟩
              · show dmn = _
                rw [← hdmn, heq, hjeq']
              · intro b hb hpair
                by_cases hbe : b = t + 1
                · subst hbe
                  obtain ⟨pair, hpairb⟩ := hpair
                  rw [hsucc] at hpairb
                  simp [arenaStep, hgraph, leftReverseTarget] at hpairb
                · exact hjbound b (by omega) hpair
        · -- close
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · intro state' minState' h
            rw [hsucc] at h
            simp only [arenaStep, hgraph, leftCloseTarget,
              Sum.inl.injEq, Prod.mk.injEq] at h
            obtain ⟨-, hmn⟩ := h
            refine Or.inr ⟨j, Nat.lt_succ_of_le hjle, ?_, ?_⟩
            · rw [← hmn, hjeq']
            · intro b hb hpair
              exact hjbound b (by omega) hpair
          · intro data h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, leftCloseTarget])
          · intro data h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, leftCloseTarget])
          · intro data h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, leftCloseTarget])
          · intro data h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, leftCloseTarget])
      · rw [hfold] at hsucc hrunT
        rw [hfold] at hrunT1
        obtain ⟨j, hjle, hjeq, hjbound⟩ :=
          ihR (plan, chain, control, st, mn) hfold
        have hjeq' : mn = A.run (arenaWord plans env) j := hjeq
        cases hgraph : (env t).graph
        · -- direct reversal
          simp only [arenaStep, hgraph, rightReverseTarget,
            positionState] at hrunT1
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · intro state' minState' h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, rightReverseTarget])
          · intro data h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, rightReverseTarget])
          · intro data h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, rightReverseTarget])
          · rintro ⟨dchain, dctl, dent, dst, dmn⟩ h
            rw [hsucc] at h
            simp only [arenaStep, hgraph, rightReverseTarget,
              Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq] at h
            obtain ⟨-, -, -, -, hdmn⟩ := h
            rw [hrunT1] at hdmn
            rcases minPriorityState_eq_or (A := A) mn
                (A.run (arenaWord plans env) (t + 1)) with heq | heq
            · refine ⟨t + 1, Nat.le_refl _, ?_, fun b hb _ => hb⟩
              show dmn = _
              rw [← hdmn, heq]
            · refine ⟨j, Nat.le_succ_of_le hjle, ?_, ?_⟩
              · show dmn = _
                rw [← hdmn, heq, hjeq']
              · intro b hb hpair
                by_cases hbe : b = t + 1
                · subst hbe
                  obtain ⟨pair, hpairb⟩ := hpair
                  rw [hsucc] at hpairb
                  simp [arenaStep, hgraph, rightReverseTarget] at hpairb
                · exact hjbound b (by omega) hpair
          · intro data h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, rightReverseTarget])
        · -- continuation
          simp only [arenaStep, hgraph, rightContinueTarget,
            positionState] at hrunT1
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · intro state' minState' h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, rightContinueTarget])
          · intro data h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, rightContinueTarget])
          · rintro ⟨dplan, dchain, dctl, dst, dmn⟩ h
            rw [hsucc] at h
            simp only [arenaStep, hgraph, rightContinueTarget,
              Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq] at h
            obtain ⟨-, -, -, -, hdmn⟩ := h
            rw [hrunT1] at hdmn
            rcases minPriorityState_eq_or (A := A) mn
                (A.run (arenaWord plans env) (t + 1)) with heq | heq
            · refine ⟨t + 1, Nat.le_refl _, ?_, fun b hb _ => hb⟩
              show dmn = _
              rw [← hdmn, heq]
            · refine ⟨j, Nat.le_succ_of_le hjle, ?_, ?_⟩
              · show dmn = _
                rw [← hdmn, heq, hjeq']
              · intro b hb hpair
                by_cases hbe : b = t + 1
                · subst hbe
                  obtain ⟨pair, hpairb⟩ := hpair
                  rw [hsucc] at hpairb
                  simp [arenaStep, hgraph, rightContinueTarget] at hpairb
                · exact hjbound b (by omega) hpair
          · intro data h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, rightContinueTarget])
          · intro data h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, rightContinueTarget])
        · -- close
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · intro state' minState' h
            rw [hsucc] at h
            simp only [arenaStep, hgraph, rightCloseTarget,
              Sum.inl.injEq, Prod.mk.injEq] at h
            obtain ⟨-, hmn⟩ := h
            refine Or.inr ⟨j, Nat.lt_succ_of_le hjle, ?_, ?_⟩
            · rw [← hmn, hjeq']
            · intro b hb hpair
              exact hjbound b (by omega) hpair
          · intro data h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, rightCloseTarget])
          · intro data h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, rightCloseTarget])
          · intro data h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, rightCloseTarget])
          · intro data h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, rightCloseTarget])
      · rw [hfold] at hsucc hrunT
        rw [hfold] at hrunT1
        obtain ⟨j, hjle, hjeq, hjbound⟩ :=
          ihRL (chain, control, ent, st, mn) hfold
        have hjeq' : mn = A.run (arenaWord plans env) j := hjeq
        cases hgraph : (env t).graph
        · -- continuation
          simp only [arenaStep, hgraph, revLeftContinueTarget,
            positionState] at hrunT1
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · intro state' minState' h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, revLeftContinueTarget])
          · intro data h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, revLeftContinueTarget])
          · intro data h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, revLeftContinueTarget])
          · rintro ⟨dchain, dctl, dent, dst, dmn⟩ h
            rw [hsucc] at h
            simp only [arenaStep, hgraph, revLeftContinueTarget,
              Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq] at h
            obtain ⟨-, -, -, -, hdmn⟩ := h
            rw [hrunT1] at hdmn
            rcases minPriorityState_eq_or (A := A) mn
                (A.run (arenaWord plans env) (t + 1)) with heq | heq
            · refine ⟨t + 1, Nat.le_refl _, ?_, fun b hb _ => hb⟩
              show dmn = _
              rw [← hdmn, heq]
            · refine ⟨j, Nat.le_succ_of_le hjle, ?_, ?_⟩
              · show dmn = _
                rw [← hdmn, heq, hjeq']
              · intro b hb hpair
                by_cases hbe : b = t + 1
                · subst hbe
                  obtain ⟨pair, hpairb⟩ := hpair
                  rw [hsucc] at hpairb
                  simp [arenaStep, hgraph, revLeftContinueTarget] at hpairb
                · exact hjbound b (by omega) hpair
          · intro data h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, revLeftContinueTarget])
        · -- re-reversal
          simp only [arenaStep, hgraph, revLeftReverseTarget,
            positionState] at hrunT1
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · intro state' minState' h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, revLeftReverseTarget])
          · intro data h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, revLeftReverseTarget])
          · intro data h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, revLeftReverseTarget])
          · intro data h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, revLeftReverseTarget])
          · rintro ⟨dchain, dctl, dent, dst, dmn⟩ h
            rw [hsucc] at h
            simp only [arenaStep, hgraph, revLeftReverseTarget,
              Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq] at h
            obtain ⟨-, -, -, -, hdmn⟩ := h
            rw [hrunT1] at hdmn
            rcases minPriorityState_eq_or (A := A) mn
                (A.run (arenaWord plans env) (t + 1)) with heq | heq
            · refine ⟨t + 1, Nat.le_refl _, ?_, fun b hb _ => hb⟩
              show dmn = _
              rw [← hdmn, heq]
            · refine ⟨j, Nat.le_succ_of_le hjle, ?_, ?_⟩
              · show dmn = _
                rw [← hdmn, heq, hjeq']
              · intro b hb hpair
                by_cases hbe : b = t + 1
                · subst hbe
                  obtain ⟨pair, hpairb⟩ := hpair
                  rw [hsucc] at hpairb
                  simp [arenaStep, hgraph, revLeftReverseTarget] at hpairb
                · exact hjbound b (by omega) hpair
        · -- close
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · intro state' minState' h
            rw [hsucc] at h
            simp only [arenaStep, hgraph, revLeftCloseTarget,
              Sum.inl.injEq, Prod.mk.injEq] at h
            obtain ⟨-, hmn⟩ := h
            refine Or.inr ⟨j, Nat.lt_succ_of_le hjle, ?_, ?_⟩
            · rw [← hmn, hjeq']
            · intro b hb hpair
              exact hjbound b (by omega) hpair
          · intro data h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, revLeftCloseTarget])
          · intro data h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, revLeftCloseTarget])
          · intro data h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, revLeftCloseTarget])
          · intro data h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, revLeftCloseTarget])
      · rw [hfold] at hsucc hrunT
        rw [hfold] at hrunT1
        obtain ⟨j, hjle, hjeq, hjbound⟩ :=
          ihRR (chain, control, ent, st, mn) hfold
        have hjeq' : mn = A.run (arenaWord plans env) j := hjeq
        cases hgraph : (env t).graph
        · -- re-reversal
          simp only [arenaStep, hgraph, revRightReverseTarget,
            positionState] at hrunT1
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · intro state' minState' h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, revRightReverseTarget])
          · intro data h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, revRightReverseTarget])
          · intro data h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, revRightReverseTarget])
          · rintro ⟨dchain, dctl, dent, dst, dmn⟩ h
            rw [hsucc] at h
            simp only [arenaStep, hgraph, revRightReverseTarget,
              Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq] at h
            obtain ⟨-, -, -, -, hdmn⟩ := h
            rw [hrunT1] at hdmn
            rcases minPriorityState_eq_or (A := A) mn
                (A.run (arenaWord plans env) (t + 1)) with heq | heq
            · refine ⟨t + 1, Nat.le_refl _, ?_, fun b hb _ => hb⟩
              show dmn = _
              rw [← hdmn, heq]
            · refine ⟨j, Nat.le_succ_of_le hjle, ?_, ?_⟩
              · show dmn = _
                rw [← hdmn, heq, hjeq']
              · intro b hb hpair
                by_cases hbe : b = t + 1
                · subst hbe
                  obtain ⟨pair, hpairb⟩ := hpair
                  rw [hsucc] at hpairb
                  simp [arenaStep, hgraph, revRightReverseTarget] at hpairb
                · exact hjbound b (by omega) hpair
          · intro data h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, revRightReverseTarget])
        · -- continuation
          simp only [arenaStep, hgraph, revRightContinueTarget,
            positionState] at hrunT1
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · intro state' minState' h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, revRightContinueTarget])
          · intro data h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, revRightContinueTarget])
          · intro data h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, revRightContinueTarget])
          · intro data h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, revRightContinueTarget])
          · rintro ⟨dchain, dctl, dent, dst, dmn⟩ h
            rw [hsucc] at h
            simp only [arenaStep, hgraph, revRightContinueTarget,
              Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq] at h
            obtain ⟨-, -, -, -, hdmn⟩ := h
            rw [hrunT1] at hdmn
            rcases minPriorityState_eq_or (A := A) mn
                (A.run (arenaWord plans env) (t + 1)) with heq | heq
            · refine ⟨t + 1, Nat.le_refl _, ?_, fun b hb _ => hb⟩
              show dmn = _
              rw [← hdmn, heq]
            · refine ⟨j, Nat.le_succ_of_le hjle, ?_, ?_⟩
              · show dmn = _
                rw [← hdmn, heq, hjeq']
              · intro b hb hpair
                by_cases hbe : b = t + 1
                · subst hbe
                  obtain ⟨pair, hpairb⟩ := hpair
                  rw [hsucc] at hpairb
                  simp [arenaStep, hgraph, revRightContinueTarget] at hpairb
                · exact hjbound b (by omega) hpair
        · -- close
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · intro state' minState' h
            rw [hsucc] at h
            simp only [arenaStep, hgraph, revRightCloseTarget,
              Sum.inl.injEq, Prod.mk.injEq] at h
            obtain ⟨-, hmn⟩ := h
            refine Or.inr ⟨j, Nat.lt_succ_of_le hjle, ?_, ?_⟩
            · rw [← hmn, hjeq']
            · intro b hb hpair
              exact hjbound b (by omega) hpair
          · intro data h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, revRightCloseTarget])
          · intro data h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, revRightCloseTarget])
          · intro data h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, revRightCloseTarget])
          · intro data h
            rw [hsucc] at h
            exact absurd h (by simp [arenaStep, hgraph, revRightCloseTarget])

/--
Away from boundary positions, the game path's priority is the run
priority of its round.
-/
theorem gamePriority_eq_run_of_not_bnd
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂)
    (k : Nat)
    (hnot : ∀ pair, gamePath plans env k ≠ Sum.inl pair) :
    boundaryPriority A C_L C_R C_V (gamePath plans env k) =
      A.priority
        (A.run (arenaWord plans env) (gameClock plans env k)) := by
  obtain ⟨hshadow, hcommitted⟩ := gameAux_shadow plans env k
  have hps :=
    positionState_arenaFoldSeq plans env (gameClock plans env k)
  rcases hpos : gamePath plans env k with
    pair | ⟨⟨q, q'⟩, plan⟩ | ⟨pl, ch, c, stt, mnn⟩ |
    ⟨pl, ch, c, stt, mnn⟩ | ⟨ch, c, ent, stt, mnn⟩ |
    ⟨ch, c, ent, stt, mnn⟩
  · exact absurd hpos (hnot pair)
  · obtain ⟨hdiag, mnn, hfold, _⟩ := hcommitted (q, q') plan hpos
    have hd : q' = q := hdiag
    rw [hfold] at hps
    have hq : q = A.run (arenaWord plans env) (gameClock plans env k) :=
      hps
    show A.priority q' = _
    rw [hd, hq]
  · have hfold :
        arenaFoldSeq plans env (gameClock plans env k) =
          Sum.inr (Sum.inr (Sum.inl (pl, ch, c, stt, mnn))) := by
      rw [←
        hshadow (by
          intro committed hc
          rw [hpos] at hc
          simp at hc)]
      exact hpos
    rw [hfold] at hps
    have hstt : stt = A.run (arenaWord plans env) (gameClock plans env k) :=
      hps
    show A.priority stt = _
    rw [hstt]
  · have hfold :
        arenaFoldSeq plans env (gameClock plans env k) =
          Sum.inr (Sum.inr (Sum.inr (Sum.inl (pl, ch, c, stt, mnn)))) := by
      rw [←
        hshadow (by
          intro committed hc
          rw [hpos] at hc
          simp at hc)]
      exact hpos
    rw [hfold] at hps
    have hstt : stt = A.run (arenaWord plans env) (gameClock plans env k) :=
      hps
    show A.priority stt = _
    rw [hstt]
  · have hfold :
        arenaFoldSeq plans env (gameClock plans env k) =
          Sum.inr (Sum.inr (Sum.inr (Sum.inr
            (Sum.inl (ch, c, ent, stt, mnn))))) := by
      rw [←
        hshadow (by
          intro committed hc
          rw [hpos] at hc
          simp at hc)]
      exact hpos
    rw [hfold] at hps
    have hstt : stt = A.run (arenaWord plans env) (gameClock plans env k) :=
      hps
    show A.priority stt = _
    rw [hstt]
  · have hfold :
        arenaFoldSeq plans env (gameClock plans env k) =
          Sum.inr (Sum.inr (Sum.inr (Sum.inr
            (Sum.inr (ch, c, ent, stt, mnn))))) := by
      rw [←
        hshadow (by
          intro committed hc
          rw [hpos] at hc
          simp at hc)]
      exact hpos
    rw [hfold] at hps
    have hstt : stt = A.run (arenaWord plans env) (gameClock plans env k) :=
      hps
    show A.priority stt = _
    rw [hstt]

/--
Upward recurrence transfer: every priority recurring along the game
path recurs among the run priorities of the emitted word.  Non-boundary
occurrences transfer at their round; boundary occurrences transfer
through the attained block minimum, whose index dominates the earlier
boundary supplied by a second occurrence.
-/
theorem seenInfinitelyOften_run_of_gamePath
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂)
    {w : Nat}
    (hw :
      NatSeqSeenInfinitelyOften
        (fun k => boundaryPriority A C_L C_R C_V (gamePath plans env k)) w) :
    NatSeqSeenInfinitelyOften
      (fun t => A.priority (A.run (arenaWord plans env) t)) w := by
  intro n
  obtain ⟨k₁, hk₁, hp₁⟩ := hw (2 * (n + 1))
  have hp₁beta :
      boundaryPriority A C_L C_R C_V (gamePath plans env k₁) = w := hp₁
  have ht₁ : n + 1 ≤ gameClock plans env k₁ :=
    Nat.le_trans (le_gameClock_two_mul plans env (n + 1))
      (gameClock_mono plans env hk₁)
  by_cases hbnd₁ : ∀ pair, gamePath plans env k₁ ≠ Sum.inl pair
  · refine ⟨gameClock plans env k₁, by omega, ?_⟩
    show
      A.priority (A.run (arenaWord plans env) (gameClock plans env k₁)) =
        w
    rw [← gamePriority_eq_run_of_not_bnd plans env k₁ hbnd₁]
    exact hp₁beta
  · push Not at hbnd₁
    obtain ⟨⟨q₁, mn₁⟩, hpos₁⟩ := hbnd₁
    have hfold₁ :
        arenaFoldSeq plans env (gameClock plans env k₁) =
          Sum.inl (q₁, mn₁) := by
      rw [←
        (gameAux_shadow plans env k₁).1 (by
          intro committed hc
          rw [hpos₁] at hc
          simp at hc)]
      exact hpos₁
    obtain ⟨k₂, hk₂, hp₂⟩ := hw (2 * (gameClock plans env k₁ + 1))
    have hp₂beta :
        boundaryPriority A C_L C_R C_V (gamePath plans env k₂) = w := hp₂
    have ht₂ :
        gameClock plans env k₁ + 1 ≤ gameClock plans env k₂ :=
      Nat.le_trans
        (le_gameClock_two_mul plans env (gameClock plans env k₁ + 1))
        (gameClock_mono plans env hk₂)
    by_cases hbnd₂ : ∀ pair, gamePath plans env k₂ ≠ Sum.inl pair
    · refine ⟨gameClock plans env k₂, by omega, ?_⟩
      show
        A.priority
            (A.run (arenaWord plans env) (gameClock plans env k₂)) =
          w
      rw [← gamePriority_eq_run_of_not_bnd plans env k₂ hbnd₂]
      exact hp₂beta
    · push Not at hbnd₂
      obtain ⟨⟨q₂, mn₂⟩, hpos₂⟩ := hbnd₂
      have hfold₂ :
          arenaFoldSeq plans env (gameClock plans env k₂) =
            Sum.inl (q₂, mn₂) := by
        rw [←
          (gameAux_shadow plans env k₂).1 (by
            intro committed hc
            rw [hpos₂] at hc
            simp at hc)]
        exact hpos₂
      rcases
          (arenaFold_min_attained plans env
              (gameClock plans env k₂)).1 q₂ mn₂ hfold₂ with
        hzero | ⟨j, hj, hjeq, hjbound⟩
      · omega
      · have hjt₁ :
            gameClock plans env k₁ ≤ j :=
          hjbound (gameClock plans env k₁) (by omega)
            ⟨(q₁, mn₁), hfold₁⟩
        refine ⟨j, by omega, ?_⟩
        show A.priority (A.run (arenaWord plans env) j) = w
        rw [← hjeq]
        rw [hpos₂] at hp₂beta
        exact hp₂beta

section H4bEndpoint

variable
  [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
  [DecidableEq In₁] [DecidableEq In₂] [DecidableEq A.State]
  [Fintype C_L] [DecidableEq C_L] [Fintype C_R] [DecidableEq C_R]
  [Fintype C_V] [DecidableEq C_V]
  [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
  [Inhabited C_L] [Inhabited C_R] [Inhabited C_V]

/--
The H4b endpoint: a winning positional Even strategy of the boundary
game makes the emitted word of every no-direct play accepted by the
objective automaton.
-/
theorem accepts_arenaWord_of_winning
    (τ :
      (DetParityAutomaton.boundaryGame A C_L C_R C_V).PositionalStrategy
        ParityPlayer.even)
    (hwin :
      CountableParityGame.PositionalStrategy.WinningFrom
        (G := DetParityAutomaton.boundaryGame A C_L C_R C_V) τ
        (Sum.inl (A.initial, A.initial)))
    (env : EnvironmentSequence In₁ In₂) :
    A.Accepts (arenaWord (plansOf τ) env) := by
  have hpath := gamePath_minPriorityEven τ hwin env
  have hgame :
      NatSeqMinEvenParity
        (fun k =>
          boundaryPriority A C_L C_R C_V (gamePath (plansOf τ) env k)) :=
    hpath
  rw [DetParityAutomaton.accepts_iff_natSeqMinEvenParity]
  refine
    (natSeqMinEvenParity_iff_of_recurring_transfer
        (fun k =>
          boundaryPriority A C_L C_R C_V (gamePath (plansOf τ) env k))
        (fun t => A.priority (A.run (arenaWord (plansOf τ) env) t))
        ?_ ?_).mp hgame
  · intro w hw
    exact seenInfinitelyOften_run_of_gamePath (plansOf τ) env hw
  · intro v hv n
    obtain ⟨t, htn, hvt⟩ := hv n
    have hvtbeta :
        A.priority (A.run (arenaWord (plansOf τ) env) t) = v := hvt
    obtain ⟨k, hkt, hkp⟩ :=
      exists_gamePriority_emission (plansOf τ) env t
    refine ⟨k, by omega, ?_⟩
    show
      boundaryPriority A C_L C_R C_V (gamePath (plansOf τ) env k) ≤ v
    exact Nat.le_of_eq (by rw [hkp, hvtbeta])

end H4bEndpoint

end DetParityAutomaton

end DistributedSynthesis
