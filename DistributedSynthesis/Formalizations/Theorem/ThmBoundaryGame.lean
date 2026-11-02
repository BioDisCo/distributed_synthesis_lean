/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmJournalBlockMonitors
import DistributedSynthesis.Formalizations.Theorem.ThmZielonkaCountableParity

/-!
# The boundary game

This file defines the finite boundary parity game of the journal
construction: the perfect-information game whose Even player is the
coalition committing, at every synchronization boundary, a complete
plan for the next block, and whose Odd player is the environment
choosing inputs, the block orientation, the closing time, and direct
orientation reversals.

The information discipline of the two-process model is enforced by the
arena shape rather than by side conditions:

* Even moves only at boundary positions, committing a
  `BoundaryPlan`: one narrowed block plan per orientation together
  with a chain plan for directly reversed blocks.  All within-block
  positions belong to Odd, so a positional Even strategy never reads
  within-block data that the sender cannot observe; the sender
  component of a plan evolves on sender inputs alone.
* A `both` round at a boundary plays the two plans' opening responses:
  the receiver's view after an opening one-sided round and after a
  `both` round are identical (`thm:onebitfringe`), so its output table
  must be shared, and it is, structurally.
* Within a block, the receiver table of the current narrowed label is
  used both to continue and to close, because the receiver cannot see
  the close; the sender's closing response is a separate full-knowledge
  table since the sender receives in the closing round, and its staged
  no-receive value (the `rev` table) serves the directly reversing
  round the sender cannot distinguish from the close.
* Within a directly reversed block no output can be baked (the block
  has no committed boundary), so the chain plan stages both processes'
  four table values per round and the environment resolves the round
  three ways: continue, close to a genuine boundary, or reverse again.
  The chain control enters from the block control through the plan's
  handoff maps and steps on the mixed sender directions.

Positions carry the objective automaton state together with a state of
minimal priority seen since the last boundary, matching the tracking of
`ThmJournalBlockMonitors.lean`; a close hands that minimal state to the
boundary position, whose priority is the closed block's minimum, and
the sampled minimum continues across direct reversals.  Block positions
carry the current state's priority, so plays trapped forever in blocks
are decided by the tail parity.  By the pasting theorems of
`ThmParityBlockPasting.lean` and `ThmBoundaryDecomposition.lean`, the
interleaved parity value of the game agrees with acceptance of the
corresponding real play in both regimes.
-/

namespace DistributedSynthesis

universe u v x y s

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

namespace DetParityAutomaton

variable
  (A :
    DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))

/-- The state of smaller priority, preferring the incumbent on ties. -/
def minPriorityState (incumbent next : A.State) : A.State :=
  if A.priority next < A.priority incumbent then next else incumbent

/--
A committed plan for a left block: finite control over sender inputs,
a narrowed label per control state, a sender closing table, and the
receiver's staged no-receive table for a directly reversing close.
The label's receiver table is indexed by the block monitor state,
which the receiver computes privately.
-/
structure LeftBlockPlan (C : Type max u v x y s) where
  init : C
  step : C -> In₂ -> C
  label :
    C -> NarrowedBlockLabel In₁ In₂ Out₁ Out₂ (A.State × A.State)
  close : C -> A.State × A.State -> In₁ × In₂ -> Out₂
  rev : C -> A.State × A.State -> In₁ -> Out₁

/-- A committed plan for a right block: the orientation mirror. -/
structure RightBlockPlan (C : Type max u v x y s) where
  init : C
  step : C -> In₁ -> C
  label :
    C -> NarrowedBlockLabel In₂ In₁ Out₂ Out₁ (A.State × A.State)
  close : C -> A.State × A.State -> In₂ × In₁ -> Out₁
  rev : C -> A.State × A.State -> In₂ -> Out₂

/--
A committed plan for directly reversed blocks: chain control entered
from a block control through the handoff maps, stepping on the mixed
sender directions, with the four-value staged tables of the two
reversed orientations (process one's receive and no-receive values,
process two's no-receive and receive values, in this order).
-/
structure ChainPlan (C_L C_R C_V : Type max u v x y s) where
  enterL : C_L -> C_V
  enterR : C_R -> C_V
  step : C_V -> In₂ ⊕ In₁ -> C_V
  labelL :
    C_V ->
      ((A.State × A.State) × A.State × A.State ->
          In₁ × In₂ -> Out₁) ×
        ((A.State × A.State) × A.State × A.State -> In₁ -> Out₁) ×
        (A.State × A.State -> In₂ -> Out₂) ×
        ((A.State × A.State) × A.State × A.State ->
          In₁ × In₂ -> Out₂)
  labelR :
    C_V ->
      ((A.State × A.State) × A.State × A.State ->
          In₁ × In₂ -> Out₁) ×
        (A.State × A.State -> In₁ -> Out₁) ×
        ((A.State × A.State) × A.State × A.State -> In₂ -> Out₂) ×
        ((A.State × A.State) × A.State × A.State ->
          In₁ × In₂ -> Out₂)

section Instances

variable {A}
variable {C C_L C_R C_V : Type max u v x y s}
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂] [DecidableEq A.State]

instance [Fintype C] [DecidableEq C] :
    Fintype (LeftBlockPlan (In₁ := In₁) A C) :=
  letI : Fintype (C -> In₂ -> C) := inferInstance
  letI :
      Fintype
        (C -> NarrowedBlockLabel In₁ In₂ Out₁ Out₂ (A.State × A.State)) :=
    inferInstance
  letI :
      Fintype (C -> A.State × A.State -> In₁ × In₂ -> Out₂) :=
    inferInstance
  letI :
      Fintype (C -> A.State × A.State -> In₁ -> Out₁) :=
    inferInstance
  Fintype.ofEquiv
    (C × (C -> In₂ -> C) ×
      (C -> NarrowedBlockLabel In₁ In₂ Out₁ Out₂ (A.State × A.State)) ×
      (C -> A.State × A.State -> In₁ × In₂ -> Out₂) ×
      (C -> A.State × A.State -> In₁ -> Out₁))
    {
      toFun := fun data =>
        ⟨data.1, data.2.1, data.2.2.1, data.2.2.2.1, data.2.2.2.2⟩
      invFun := fun plan =>
        (plan.init, plan.step, plan.label, plan.close, plan.rev)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
    }

instance [Fintype C] [DecidableEq C] :
    Fintype (RightBlockPlan (In₂ := In₂) A C) :=
  letI : Fintype (C -> In₁ -> C) := inferInstance
  letI :
      Fintype
        (C -> NarrowedBlockLabel In₂ In₁ Out₂ Out₁ (A.State × A.State)) :=
    inferInstance
  letI :
      Fintype (C -> A.State × A.State -> In₂ × In₁ -> Out₁) :=
    inferInstance
  letI :
      Fintype (C -> A.State × A.State -> In₂ -> Out₂) :=
    inferInstance
  Fintype.ofEquiv
    (C × (C -> In₁ -> C) ×
      (C -> NarrowedBlockLabel In₂ In₁ Out₂ Out₁ (A.State × A.State)) ×
      (C -> A.State × A.State -> In₂ × In₁ -> Out₁) ×
      (C -> A.State × A.State -> In₂ -> Out₂))
    {
      toFun := fun data =>
        ⟨data.1, data.2.1, data.2.2.1, data.2.2.2.1, data.2.2.2.2⟩
      invFun := fun plan =>
        (plan.init, plan.step, plan.label, plan.close, plan.rev)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
    }

instance [Fintype C_L] [DecidableEq C_L] [Fintype C_R] [DecidableEq C_R]
    [Fintype C_V] [DecidableEq C_V] :
    Fintype (ChainPlan (In₁ := In₁) A C_L C_R C_V) :=
  letI : Fintype (C_L -> C_V) := inferInstance
  letI : Fintype (C_R -> C_V) := inferInstance
  letI : Fintype (C_V -> In₂ ⊕ In₁ -> C_V) := inferInstance
  letI :
      Fintype
        ((A.State × A.State) × A.State × A.State ->
          In₁ × In₂ -> Out₁) :=
    inferInstance
  letI :
      Fintype
        ((A.State × A.State) × A.State × A.State -> In₁ -> Out₁) :=
    inferInstance
  letI :
      Fintype
        ((A.State × A.State) × A.State × A.State -> In₂ -> Out₂) :=
    inferInstance
  letI :
      Fintype
        ((A.State × A.State) × A.State × A.State ->
          In₁ × In₂ -> Out₂) :=
    inferInstance
  letI : Fintype (A.State × A.State -> In₁ -> Out₁) := inferInstance
  letI : Fintype (A.State × A.State -> In₂ -> Out₂) := inferInstance
  letI :
      Fintype
        (C_V ->
          ((A.State × A.State) × A.State × A.State ->
              In₁ × In₂ -> Out₁) ×
            ((A.State × A.State) × A.State × A.State -> In₁ -> Out₁) ×
            (A.State × A.State -> In₂ -> Out₂) ×
            ((A.State × A.State) × A.State × A.State ->
              In₁ × In₂ -> Out₂)) :=
    inferInstance
  letI :
      Fintype
        (C_V ->
          ((A.State × A.State) × A.State × A.State ->
              In₁ × In₂ -> Out₁) ×
            (A.State × A.State -> In₁ -> Out₁) ×
            ((A.State × A.State) × A.State × A.State -> In₂ -> Out₂) ×
            ((A.State × A.State) × A.State × A.State ->
              In₁ × In₂ -> Out₂)) :=
    inferInstance
  Fintype.ofEquiv
    ((C_L -> C_V) × (C_R -> C_V) × (C_V -> In₂ ⊕ In₁ -> C_V) ×
      (C_V ->
        ((A.State × A.State) × A.State × A.State ->
            In₁ × In₂ -> Out₁) ×
          ((A.State × A.State) × A.State × A.State -> In₁ -> Out₁) ×
          (A.State × A.State -> In₂ -> Out₂) ×
          ((A.State × A.State) × A.State × A.State ->
            In₁ × In₂ -> Out₂)) ×
      (C_V ->
        ((A.State × A.State) × A.State × A.State ->
            In₁ × In₂ -> Out₁) ×
          (A.State × A.State -> In₁ -> Out₁) ×
          ((A.State × A.State) × A.State × A.State -> In₂ -> Out₂) ×
          ((A.State × A.State) × A.State × A.State ->
            In₁ × In₂ -> Out₂)))
    {
      toFun := fun data =>
        ⟨data.1, data.2.1, data.2.2.1, data.2.2.2.1, data.2.2.2.2⟩
      invFun := fun plan =>
        (plan.enterL, plan.enterR, plan.step, plan.labelL, plan.labelR)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
    }

end Instances

section Inhabited

variable {A}
variable {C C_L C_R C_V : Type max u v x y s}

instance [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Inhabited C] :
    Inhabited (LeftBlockPlan (In₁ := In₁) A C) :=
  ⟨{
      init := default
      step := fun control _ => control
      label := fun _ => (fun _ => default, fun _ _ => default)
      close := fun _ _ _ => default
      rev := fun _ _ _ => default
    }⟩

instance [Inhabited In₁] [Inhabited Out₁] [Inhabited Out₂] [Inhabited C] :
    Inhabited (RightBlockPlan (In₂ := In₂) A C) :=
  ⟨{
      init := default
      step := fun control _ => control
      label := fun _ => (fun _ => default, fun _ _ => default)
      close := fun _ _ _ => default
      rev := fun _ _ _ => default
    }⟩

instance [Inhabited Out₁] [Inhabited Out₂] [Inhabited C_V] :
    Inhabited (ChainPlan (In₁ := In₁) (In₂ := In₂) A C_L C_R C_V) :=
  ⟨{
      enterL := fun _ => default
      enterR := fun _ => default
      step := fun control _ => control
      labelL := fun _ =>
        (fun _ _ => default, fun _ _ => default, fun _ _ => default,
          fun _ _ => default)
      labelR := fun _ =>
        (fun _ _ => default, fun _ _ => default, fun _ _ => default,
          fun _ _ => default)
    }⟩

end Inhabited

/-- A boundary move: one committed plan per block orientation and one
chain plan for directly reversed blocks. -/
abbrev BoundaryPlan (C_L C_R C_V : Type max u v x y s) :=
  LeftBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
    A C_L ×
    RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
      A C_R ×
    ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
      A C_L C_R C_V

/--
Positions of the boundary game.  The first summand is a boundary (Even
to commit a plan; the second component is the minimal-priority state of
the closed block, carrying its emitted priority).  The second summand
is a committed boundary (Odd to choose the round).  The third and
fourth are within-block positions (Odd to continue, close, or directly
reverse), carrying the block plan, the chain plan, the plan control,
the automaton state, and the minimal-priority state since the boundary.
The fifth and sixth are the directly reversed positions of the two
orientations, carrying the chain plan and its control.
-/
abbrev BoundaryGamePosition (C_L C_R C_V : Type max u v x y s) :=
  (A.State × A.State) ⊕
    ((A.State × A.State) × BoundaryPlan (In₁ := In₁) A C_L C_R C_V) ⊕
    ((LeftBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
        (Out₂ := Out₂) A C_L) ×
      (ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
        (Out₂ := Out₂) A C_L C_R C_V) ×
      C_L × A.State × A.State) ⊕
    ((RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
        (Out₂ := Out₂) A C_R) ×
      (ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
        (Out₂ := Out₂) A C_L C_R C_V) ×
      C_R × A.State × A.State) ⊕
    ((ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
        (Out₂ := Out₂) A C_L C_R C_V) ×
      C_V × (A.State × A.State) × A.State × A.State) ⊕
    ((ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
        (Out₂ := Out₂) A C_L C_R C_V) ×
      C_V × (A.State × A.State) × A.State × A.State)

variable {C_L C_R C_V : Type max u v x y s}

/-- The round record of a left block round. -/
def leftRoundRecord (move : In₁ × In₂) (outOne : Out₁) (outTwo : Out₂) :
    RoundRecord In₁ In₂ Graph Out₁ Out₂ :=
  ⟨move.1, move.2, Graph.left, outOne, outTwo⟩

/-- The round record of a right block round, receiver-first move. -/
def rightRoundRecord (move : In₂ × In₁) (outOne : Out₁) (outTwo : Out₂) :
    RoundRecord In₁ In₂ Graph Out₁ Out₂ :=
  ⟨move.2, move.1, Graph.right, outOne, outTwo⟩

/-- The round record of a synchronizing round. -/
def bothRoundRecord (move : In₁ × In₂) (outOne : Out₁) (outTwo : Out₂) :
    RoundRecord In₁ In₂ Graph Out₁ Out₂ :=
  ⟨move.1, move.2, Graph.both, outOne, outTwo⟩

section Arena

variable (C_L C_R C_V)

/-- Boundary positions are Even's; all others are Odd's. -/
def boundaryOwner :
    BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V -> ParityPlayer
  | Sum.inl _ => ParityPlayer.even
  | _ => ParityPlayer.odd

/--
Boundary tiers carry the closed block's minimum priority; block and
reversed positions carry the current state's priority.
-/
def boundaryPriority :
    BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V -> Nat
  | Sum.inl (_, minState) => A.priority minState
  | Sum.inr (Sum.inl ((_, minState), _)) => A.priority minState
  | Sum.inr (Sum.inr (Sum.inl (_, _, _, state, _))) => A.priority state
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl (_, _, _, state, _)))) =>
      A.priority state
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (_, _, _, state, _))))) =>
      A.priority state
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (_, _, _, state, _))))) =>
      A.priority state

variable {C_L C_R C_V}

/-- The opening receiver response of the committed left plan. -/
def planOpenOne
    (plan : BoundaryPlan (In₁ := In₁) A C_L C_R C_V)
    (state : A.State) (move : In₁ × In₂) : Out₁ :=
  (plan.1.label plan.1.init).2 (state, state) move

/-- The opening receiver response of the committed right plan. -/
def planOpenTwo
    (plan : BoundaryPlan (In₁ := In₁) A C_L C_R C_V)
    (state : A.State) (move : In₁ × In₂) : Out₂ :=
  (plan.2.1.label plan.2.1.init).2 (state, state) (move.2, move.1)

/-- The target of a synchronizing round at a committed boundary. -/
def boundaryBothTarget
    (plan : BoundaryPlan (In₁ := In₁) A C_L C_R C_V)
    (state : A.State) (move : In₁ × In₂) :
    BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V :=
  Sum.inl
    (A.step state
        (bothRoundRecord move (A.planOpenOne plan state move)
          (A.planOpenTwo plan state move)),
      state)

/-- The target of a left block opening at a committed boundary. -/
def boundaryOpenLeftTarget
    (plan : BoundaryPlan (In₁ := In₁) A C_L C_R C_V)
    (state : A.State) (move : In₁ × In₂) :
    BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V :=
  let next :=
    A.step state
      (leftRoundRecord move (A.planOpenOne plan state move)
        ((plan.1.label plan.1.init).1 move.2))
  Sum.inr (Sum.inr (Sum.inl
    (plan.1, plan.2.2, plan.1.step plan.1.init move.2, next,
      A.minPriorityState state next)))

/-- The target of a right block opening at a committed boundary. -/
def boundaryOpenRightTarget
    (plan : BoundaryPlan (In₁ := In₁) A C_L C_R C_V)
    (state : A.State) (move : In₂ × In₁) :
    BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V :=
  let next :=
    A.step state
      (rightRoundRecord move
        ((plan.2.1.label plan.2.1.init).1 move.2)
        (A.planOpenTwo plan state (move.2, move.1)))
  Sum.inr (Sum.inr (Sum.inr (Sum.inl
    (plan.2.1, plan.2.2, plan.2.1.step plan.2.1.init move.2, next,
      A.minPriorityState state next))))

/-- The target of a continuation round inside a left block. -/
def leftContinueTarget
    (plan :
      LeftBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
        (Out₂ := Out₂) A C_L)
    (chain :
      ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
        (Out₂ := Out₂) A C_L C_R C_V)
    (control : C_L) (state minState : A.State) (move : In₁ × In₂) :
    BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V :=
  let next :=
    A.step state
      (leftRoundRecord move
        ((plan.label control).2 (state, minState) move)
        ((plan.label control).1 move.2))
  Sum.inr (Sum.inr (Sum.inl
    (plan, chain, plan.step control move.2, next,
      A.minPriorityState minState next)))

/-- The target of a closing round inside a left block: the receiver
plays its continuation table, the sender its closing table. -/
def leftCloseTarget
    (plan :
      LeftBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
        (Out₂ := Out₂) A C_L)
    (control : C_L) (state minState : A.State) (move : In₁ × In₂) :
    BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V :=
  Sum.inl
    (A.step state
        (bothRoundRecord move
          ((plan.label control).2 (state, minState) move)
          (plan.close control (state, minState) move)),
      minState)

/-- The target of a directly reversing round inside a left block: the
receiver's staged no-receive value meets the sender's closing table in
a right round, and the play enters the reversed chain through the
handoff map; the sampled minimum continues across the handoff. -/
def leftReverseTarget
    (plan :
      LeftBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
        (Out₂ := Out₂) A C_L)
    (chain :
      ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
        (Out₂ := Out₂) A C_L C_R C_V)
    (control : C_L) (state minState : A.State) (move : In₁ × In₂) :
    BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V :=
  let next :=
    A.step state
      (rightRoundRecord (move.2, move.1)
        (plan.rev control (state, minState) move.1)
        (plan.close control (state, minState) move))
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
    (chain, chain.step (chain.enterL control) (Sum.inr move.1),
      (next, A.minPriorityState minState next), next,
      A.minPriorityState minState next)))))

/-- The target of a continuation round inside a right block. -/
def rightContinueTarget
    (plan :
      RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
        (Out₂ := Out₂) A C_R)
    (chain :
      ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
        (Out₂ := Out₂) A C_L C_R C_V)
    (control : C_R) (state minState : A.State) (move : In₂ × In₁) :
    BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V :=
  let next :=
    A.step state
      (rightRoundRecord move
        ((plan.label control).1 move.2)
        ((plan.label control).2 (state, minState) move))
  Sum.inr (Sum.inr (Sum.inr (Sum.inl
    (plan, chain, plan.step control move.2, next,
      A.minPriorityState minState next))))

/-- The target of a closing round inside a right block. -/
def rightCloseTarget
    (plan :
      RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
        (Out₂ := Out₂) A C_R)
    (control : C_R) (state minState : A.State) (move : In₂ × In₁) :
    BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V :=
  Sum.inl
    (A.step state
        (bothRoundRecord (move.2, move.1)
          (plan.close control (state, minState) move)
          ((plan.label control).2 (state, minState) move)),
      minState)

/-- The target of a directly reversing round inside a right block:
the orientation mirror of `leftReverseTarget`. -/
def rightReverseTarget
    (plan :
      RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
        (Out₂ := Out₂) A C_R)
    (chain :
      ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
        (Out₂ := Out₂) A C_L C_R C_V)
    (control : C_R) (state minState : A.State) (move : In₂ × In₁) :
    BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V :=
  let next :=
    A.step state
      (leftRoundRecord (move.2, move.1)
        (plan.close control (state, minState) move)
        (plan.rev control (state, minState) move.1))
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl
    (chain, chain.step (chain.enterR control) (Sum.inl move.1),
      (next, A.minPriorityState minState next), next,
      A.minPriorityState minState next)))))

/-- The target of a continuation round inside a reversed left block:
process one's receive value meets process two's no-receive value in a
left round. -/
def revLeftContinueTarget
    (chain :
      ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
        (Out₂ := Out₂) A C_L C_R C_V)
    (control : C_V) (entry : A.State × A.State)
    (state minState : A.State) (move : In₁ × In₂) :
    BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V :=
  let staged := chain.labelL control
  let next :=
    A.step state
      (leftRoundRecord move (staged.1 (entry, state, minState) move)
        (staged.2.2.1 entry move.2))
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl
    (chain, chain.step control (Sum.inl move.2), entry, next,
      A.minPriorityState minState next)))))

/-- The target of a closing round inside a reversed left block: both
receive values synchronize and the block minimum is emitted at the
reached boundary. -/
def revLeftCloseTarget
    (chain :
      ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
        (Out₂ := Out₂) A C_L C_R C_V)
    (control : C_V) (entry : A.State × A.State)
    (state minState : A.State) (move : In₁ × In₂) :
    BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V :=
  let staged := chain.labelL control
  Sum.inl
    (A.step state
        (bothRoundRecord move
          (staged.1 (entry, state, minState) move)
          (staged.2.2.2 (entry, state, minState) move)),
      minState)

/-- The target of a re-reversing round inside a reversed left block:
process one's no-receive value meets process two's receive value in a
right round. -/
def revLeftReverseTarget
    (chain :
      ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
        (Out₂ := Out₂) A C_L C_R C_V)
    (control : C_V) (entry : A.State × A.State)
    (state minState : A.State) (move : In₁ × In₂) :
    BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V :=
  let staged := chain.labelL control
  let next :=
    A.step state
      (rightRoundRecord (move.2, move.1)
        (staged.2.1 (entry, state, minState) move.1)
        (staged.2.2.2 (entry, state, minState) move))
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
    (chain, chain.step control (Sum.inr move.1),
      (next, A.minPriorityState minState next), next,
      A.minPriorityState minState next)))))

/-- The target of a continuation round inside a reversed right
block. -/
def revRightContinueTarget
    (chain :
      ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
        (Out₂ := Out₂) A C_L C_R C_V)
    (control : C_V) (entry : A.State × A.State)
    (state minState : A.State) (move : In₁ × In₂) :
    BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V :=
  let staged := chain.labelR control
  let next :=
    A.step state
      (rightRoundRecord (move.2, move.1) (staged.2.1 entry move.1)
        (staged.2.2.2 (entry, state, minState) move))
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
    (chain, chain.step control (Sum.inr move.1), entry, next,
      A.minPriorityState minState next)))))

/-- The target of a closing round inside a reversed right block. -/
def revRightCloseTarget
    (chain :
      ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
        (Out₂ := Out₂) A C_L C_R C_V)
    (control : C_V) (entry : A.State × A.State)
    (state minState : A.State) (move : In₁ × In₂) :
    BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V :=
  let staged := chain.labelR control
  Sum.inl
    (A.step state
        (bothRoundRecord move
          (staged.1 (entry, state, minState) move)
          (staged.2.2.2 (entry, state, minState) move)),
      minState)

/-- The target of a re-reversing round inside a reversed right
block. -/
def revRightReverseTarget
    (chain :
      ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
        (Out₂ := Out₂) A C_L C_R C_V)
    (control : C_V) (entry : A.State × A.State)
    (state minState : A.State) (move : In₁ × In₂) :
    BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V :=
  let staged := chain.labelR control
  let next :=
    A.step state
      (leftRoundRecord move (staged.1 (entry, state, minState) move)
        (staged.2.2.1 (entry, state, minState) move.2))
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl
    (chain, chain.step control (Sum.inl move.2),
      (next, A.minPriorityState minState next), next,
      A.minPriorityState minState next)))))

variable (C_L C_R C_V)

/-- The edges of the boundary game. -/
def boundaryStep :
    BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V ->
      BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V -> Prop
  | Sum.inl (state, _), target =>
      ∃ plan : BoundaryPlan (In₁ := In₁) A C_L C_R C_V,
        target = Sum.inr (Sum.inl ((state, state), plan))
  | Sum.inr (Sum.inl ((state, _), plan)), target =>
      (∃ move : In₁ × In₂,
        target = A.boundaryBothTarget plan state move) ∨
      (∃ move : In₁ × In₂,
        target = A.boundaryOpenLeftTarget plan state move) ∨
      (∃ move : In₂ × In₁,
        target = A.boundaryOpenRightTarget plan state move)
  | Sum.inr (Sum.inr (Sum.inl (plan, chain, control, state, minState))),
      target =>
      (∃ move : In₁ × In₂,
        target =
          A.leftContinueTarget plan chain control state minState
            move) ∨
      (∃ move : In₁ × In₂,
        target =
          A.leftCloseTarget (C_R := C_R) (C_V := C_V) plan control
            state minState move) ∨
      (∃ move : In₁ × In₂,
        target =
          A.leftReverseTarget plan chain control state minState move)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl
      (plan, chain, control, state, minState)))), target =>
      (∃ move : In₂ × In₁,
        target =
          A.rightContinueTarget plan chain control state minState
            move) ∨
      (∃ move : In₂ × In₁,
        target =
          A.rightCloseTarget (C_L := C_L) (C_V := C_V) plan control
            state minState move) ∨
      (∃ move : In₂ × In₁,
        target =
          A.rightReverseTarget plan chain control state minState move)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl
      (chain, control, entry, state, minState))))), target =>
      (∃ move : In₁ × In₂,
        target =
          A.revLeftContinueTarget chain control entry state minState
            move) ∨
      (∃ move : In₁ × In₂,
        target =
          A.revLeftCloseTarget chain control entry state minState
            move) ∨
      (∃ move : In₁ × In₂,
        target =
          A.revLeftReverseTarget chain control entry state minState
            move)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
      (chain, control, entry, state, minState))))), target =>
      (∃ move : In₁ × In₂,
        target =
          A.revRightContinueTarget chain control entry state minState
            move) ∨
      (∃ move : In₁ × In₂,
        target =
          A.revRightCloseTarget chain control entry state minState
            move) ∨
      (∃ move : In₁ × In₂,
        target =
          A.revRightReverseTarget chain control entry state minState
            move)

variable
  [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
  [Inhabited C_L] [Inhabited C_R] [Inhabited C_V]

theorem boundaryStep_total
    (position : BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V) :
    ∃ target : BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V,
      boundaryStep A C_L C_R C_V position target := by
  rcases position with ⟨state, minState⟩ | ⟨⟨⟨state, minState⟩, plan⟩ |
    ⟨plan, chain, control, state, minState⟩ |
    ⟨plan, chain, control, state, minState⟩ |
    ⟨chain, control, entry, state, minState⟩ |
    ⟨chain, control, entry, state, minState⟩⟩
  · exact ⟨_, default, rfl⟩
  · exact ⟨_, Or.inl ⟨default, rfl⟩⟩
  · exact ⟨_, Or.inl ⟨default, rfl⟩⟩
  · exact ⟨_, Or.inl ⟨default, rfl⟩⟩
  · exact ⟨_, Or.inl ⟨default, rfl⟩⟩
  · exact ⟨_, Or.inl ⟨default, rfl⟩⟩

/--
The boundary game: the finite perfect-information parity game whose
Even player commits block plans at boundaries and whose parity value,
through the pasting theorems, is acceptance of the corresponding real
play.
-/
def boundaryGame [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂]
    [DecidableEq A.State] [Fintype C_L] [DecidableEq C_L] [Fintype C_R]
    [DecidableEq C_R] [Fintype C_V] [DecidableEq C_V] :
    CountableParityGame.{max u v x y s} where
  Position := BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V
  positionCountable := by
    letI :
        Fintype
          (ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
            (Out₂ := Out₂) A C_L C_R C_V) :=
      inferInstance
    exact Finite.to_countable
  owner := boundaryOwner A C_L C_R C_V
  step := boundaryStep A C_L C_R C_V
  step_total := boundaryStep_total A C_L C_R C_V
  priority := boundaryPriority A C_L C_R C_V
  priority_finite := by
    have hsub :
        Set.range (boundaryPriority A C_L C_R C_V) ⊆
          Set.range A.priority := by
      rintro p ⟨position, rfl⟩
      rcases position with ⟨_, minState⟩ | ⟨⟨⟨_, minState⟩, _⟩ |
        ⟨_, _, _, state, _⟩ | ⟨_, _, _, state, _⟩ |
        ⟨_, _, _, state, _⟩ | ⟨_, _, _, state, _⟩⟩
      · exact ⟨minState, rfl⟩
      · exact ⟨minState, rfl⟩
      · exact ⟨state, rfl⟩
      · exact ⟨state, rfl⟩
      · exact ⟨state, rfl⟩
      · exact ⟨state, rfl⟩
    exact Set.Finite.subset (Set.finite_range A.priority) hsub

end Arena

end DetParityAutomaton

end DistributedSynthesis
