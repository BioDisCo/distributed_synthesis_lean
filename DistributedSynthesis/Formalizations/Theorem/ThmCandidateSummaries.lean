/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmArenaFold
import DistributedSynthesis.Formalizations.Theorem.ThmLocalSummaryAutomaton
import DistributedSynthesis.Formalizations.Theorem.ThmReversedBlockThreads

/-!
# Candidate summaries for the boundary game plans

This file builds the local summary automaton of a committed plan
family: the finite per-process knowledge with which the two processes
play the arena word of `ThmArenaFold.lean` from their own views alone
(step H4c of the readback-upgrade plan).

Each summary carries the process's last emitted output (the readback
tables are the output projections) together with a core knowledge of
the arena position, in one of three shapes: after a receive round the
position is known up to the one-bit fringe, as a pair of candidates
(the own-block continuation and the boundary reached by a close);
at a resolved boundary it is known exactly; inside a block of the
opposite orientation the process tracks only the committed plan and
its own control, which its own inputs drive.

The pending bit resolves one round late, and always: at a receive
round the partner's previous summary shape reveals whether the partner
received in the previous round, which distinguishes the one-sided
round from the synchronizing one; at a `noRecv` round the no-direct
discipline itself resolves the previous bit, because continuing the
other orientation immediately would be a direct reversal.  At a close
the newly informed sender reads the block state off the partner's
candidate, which is exactly what the plan's closing table consumes.
-/

namespace DistributedSynthesis

universe u v x y s

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

namespace DetParityAutomaton

variable
  (A :
    DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))
  (C_L C_R C_V : Type max u v x y s)

/-- Within-block knowledge of the dominant side of a left block. -/
abbrev LeftBlockData :=
  LeftBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
      A C_L ×
    ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_L C_R C_V ×
    C_L × A.State × A.State

/-- Within-block knowledge of the dominant side of a right block. -/
abbrev RightBlockData :=
  RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
      A C_R ×
    ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_L C_R C_V ×
    C_R × A.State × A.State

/--
Within-block knowledge of the *informed* (receiving) side of a directly
reversed block: the committed chain plan, its control, and the composed
chain thread (`entry`, `current`).  The reversed-block label is
`plan.labelL control` (a left-oriented reversed block) or
`plan.labelR control` (a right-oriented one); both are exactly the
narrowed reversed-block labels of `ThmReversedBlockThreads.lean`, so the
step maps delegate to the thread maps there verbatim.
-/
abbrev RevInformedData :=
  ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
      A C_L C_R C_V ×
    C_V × ChainThread A

/--
Within-block knowledge of the *blind* (non-receiving) side of a directly
reversed block: the committed chain plan, its control, and the frozen
entry thread alone.  The blind side's outputs are indexed by this entry
(the one-bit fringe), never by the current thread it cannot observe.
-/
abbrev RevBlindData :=
  ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
      A C_L C_R C_V ×
    C_V × (A.State × A.State)

/--
The ambiguous entry-indexed tier of process one: the summary state right after a
`Sum.inl`+`noRecv` transition, which process one cannot resolve into a no-direct
right-block opening or a direct reversal (the frozen fringe bit `b_old`).  It
carries both readings -- the C-side subordinate data of the right block and the
E-side blind reversed-right data -- and steps them in lockstep; θ̄-measurability
of the committed plan makes the single emitted output agree with both.
-/
abbrev OneTier :=
  (RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
      A C_R ×
    C_R) ×
    RevBlindData (In₁ := In₁) A C_L C_R C_V

/-- The ambiguous entry-indexed tier of process two: the orientation mirror,
with a left-block subordinate C-side and a blind reversed-left E-side. -/
abbrev TwoTier :=
  (LeftBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
      A C_L ×
    C_L) ×
    RevBlindData (In₁ := In₁) A C_L C_R C_V

/--
Core knowledge of process one: a candidate pair after a receive round
(the left-block continuation and the boundary reached by a close), an
exactly known boundary, or the sender data inside a right block.  The
last two summands carry directly reversed blocks: as the informed side
of a reversed *left* block (a candidate pair, the reversed continuation
and the boundary reached by a close), and as the blind side of a
reversed *right* block (the frozen entry alone).
-/
abbrev OneCore :=
  (LeftBlockData (In₁ := In₁) A C_L C_R C_V × (A.State × A.State)) ⊕
    (A.State × A.State) ⊕
    (RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
        (Out₂ := Out₂) A C_R ×
      C_R) ⊕
    (RevInformedData (In₁ := In₁) A C_L C_R C_V × (A.State × A.State)) ⊕
    RevBlindData (In₁ := In₁) A C_L C_R C_V ⊕
    OneTier (In₁ := In₁) A C_L C_R C_V

/-- Core knowledge of process two: the orientation mirror.  The last three
summands are the informed side of a reversed *right* block, the blind side of a
reversed *left* block, and the ambiguous entry-indexed tier. -/
abbrev TwoCore :=
  (RightBlockData (In₁ := In₁) A C_L C_R C_V × (A.State × A.State)) ⊕
    (A.State × A.State) ⊕
    (LeftBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
        (Out₂ := Out₂) A C_L ×
      C_L) ⊕
    (RevInformedData (In₁ := In₁) A C_L C_R C_V × (A.State × A.State)) ⊕
    RevBlindData (In₁ := In₁) A C_L C_R C_V ⊕
    TwoTier (In₁ := In₁) A C_L C_R C_V

/--
The base position of process one after resolving the pending bit: a
boundary or a left-block interior.
-/
abbrev OneBase :=
  (A.State × A.State) ⊕ LeftBlockData (In₁ := In₁) A C_L C_R C_V

/-- The mirror base for process two. -/
abbrev TwoBase :=
  (A.State × A.State) ⊕ RightBlockData (In₁ := In₁) A C_L C_R C_V

variable {A C_L C_R C_V}

/-- Process one is currently the subordinate side of a left block: the resolved
subordinate or the ambiguous entry-indexed tier (both blind on the sender
side). -/
def TwoCore.isSubordinate :
    TwoCore (In₁ := In₁) A C_L C_R C_V -> Bool
  | Sum.inr (Sum.inr (Sum.inl _)) => true
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr _)))) => true
  | _ => false

/-- Process two is currently the subordinate side of a right block: the resolved
subordinate or the ambiguous entry-indexed tier. -/
def OneCore.isSubordinate :
    OneCore (In₁ := In₁) A C_L C_R C_V -> Bool
  | Sum.inr (Sum.inr (Sum.inl _)) => true
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr _)))) => true
  | _ => false

section Steps

variable (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Inhabited C_L] [Inhabited C_R]

/-- Process one's output at a receive round from a resolved base. -/
def oneRecvOutput (base : OneBase (In₁ := In₁) A C_L C_R C_V)
    (move : In₁ × In₂) : Out₁ :=
  match base with
  | Sum.inl boundary =>
      A.planOpenOne (plans boundary) boundary.1 move
  | Sum.inr (plan, chain, control, state, minState) =>
      (plan.label control).2 (state, minState) move

/-- Process two's output at a receive round from a resolved base. -/
def twoRecvOutput (base : TwoBase (In₁ := In₁) A C_L C_R C_V)
    (move : In₁ × In₂) : Out₂ :=
  match base with
  | Sum.inl boundary =>
      A.planOpenTwo (plans boundary) boundary.1 move
  | Sum.inr (plan, chain, control, state, minState) =>
      (plan.label control).2 (state, minState) (move.2, move.1)

/--
The left-block candidate successor of process one's base on a receive
round: opening from a boundary, continuing inside a left block.  The
subordinate output is the plan's sender component.
-/
def oneLeftSuccessor (base : OneBase (In₁ := In₁) A C_L C_R C_V)
    (move : In₁ × In₂) : LeftBlockData (In₁ := In₁) A C_L C_R C_V :=
  match base with
  | Sum.inl boundary =>
      let plan := (plans boundary).1
      let next :=
        A.step boundary.1
          (leftRoundRecord move
            (A.planOpenOne (plans boundary) boundary.1 move)
            ((plan.label plan.init).1 move.2))
      (plan, (plans boundary).2.2, plan.step plan.init move.2, next,
        A.minPriorityState boundary.1 next)
  | Sum.inr (plan, chain, control, state, minState) =>
      let next :=
        A.step state
          (leftRoundRecord move
            ((plan.label control).2 (state, minState) move)
            ((plan.label control).1 move.2))
      (plan, chain, plan.step control move.2, next,
        A.minPriorityState minState next)

/-- The boundary candidate successor of process one's base on a
receive round: a synchronizing round from a boundary or a close. -/
def oneBothSuccessor (base : OneBase (In₁ := In₁) A C_L C_R C_V)
    (move : In₁ × In₂) : A.State × A.State :=
  match base with
  | Sum.inl boundary =>
      (A.step boundary.1
          (bothRoundRecord move
            (A.planOpenOne (plans boundary) boundary.1 move)
            (A.planOpenTwo (plans boundary) boundary.1 move)),
        boundary.1)
  | Sum.inr (plan, chain, control, state, minState) =>
      (A.step state
          (bothRoundRecord move
            ((plan.label control).2 (state, minState) move)
            (plan.close control (state, minState) move)),
        minState)

/-- The right-block candidate successor of process two's base. -/
def twoRightSuccessor (base : TwoBase (In₁ := In₁) A C_L C_R C_V)
    (move : In₁ × In₂) : RightBlockData (In₁ := In₁) A C_L C_R C_V :=
  match base with
  | Sum.inl boundary =>
      let plan := (plans boundary).2.1
      let next :=
        A.step boundary.1
          (rightRoundRecord (move.2, move.1)
            ((plan.label plan.init).1 move.1)
            (A.planOpenTwo (plans boundary) boundary.1 move))
      (plan, (plans boundary).2.2, plan.step plan.init move.1, next,
        A.minPriorityState boundary.1 next)
  | Sum.inr (plan, chain, control, state, minState) =>
      let next :=
        A.step state
          (rightRoundRecord (move.2, move.1)
            ((plan.label control).1 move.1)
            ((plan.label control).2 (state, minState) (move.2, move.1)))
      (plan, chain, plan.step control move.1, next,
        A.minPriorityState minState next)

/-- The boundary candidate successor of process two's base. -/
def twoBothSuccessor (base : TwoBase (In₁ := In₁) A C_L C_R C_V)
    (move : In₁ × In₂) : A.State × A.State :=
  match base with
  | Sum.inl boundary =>
      (A.step boundary.1
          (bothRoundRecord move
            (A.planOpenOne (plans boundary) boundary.1 move)
            (A.planOpenTwo (plans boundary) boundary.1 move)),
        boundary.1)
  | Sum.inr (plan, chain, control, state, minState) =>
      (A.step state
          (bothRoundRecord move
            (plan.close control (state, minState) (move.2, move.1))
            ((plan.label control).2 (state, minState) (move.2, move.1))),
        minState)

/--
Process one's step at a receive round.  The partner's previous core
resolves the pending bit: a subordinate partner means the previous
round was one-sided.  From the sender state the round is a close, and
the partner's within-block candidate supplies the block state.
-/
def oneRecvStep
    (core : OneCore (In₁ := In₁) A C_L C_R C_V)
    (move : In₁ × In₂)
    (other : TwoCore (In₁ := In₁) A C_L C_R C_V) :
    Out₁ × OneCore (In₁ := In₁) A C_L C_R C_V :=
  match core with
  | Sum.inl (candLeft, candBoundary) =>
      let base : OneBase (In₁ := In₁) A C_L C_R C_V :=
        if TwoCore.isSubordinate other then Sum.inr candLeft
        else Sum.inl candBoundary
      (oneRecvOutput (A := A) plans base move,
        Sum.inl
          (oneLeftSuccessor (A := A) plans base move,
            oneBothSuccessor (A := A) plans base move))
  | Sum.inr (Sum.inl boundary) =>
      let base : OneBase (In₁ := In₁) A C_L C_R C_V := Sum.inl boundary
      (oneRecvOutput (A := A) plans base move,
        Sum.inl
          (oneLeftSuccessor (A := A) plans base move,
            oneBothSuccessor (A := A) plans base move))
  | Sum.inr (Sum.inr (Sum.inl (plan, control))) =>
      match other with
      | Sum.inl ((planTwo, chainTwo, controlTwo, state, minState), _) =>
          let outOne :=
            plan.close control (state, minState) (move.2, move.1)
          let outTwo :=
            (planTwo.label controlTwo).2 (state, minState)
              (move.2, move.1)
          let revNext :=
            A.step state
              (leftRoundRecord move
                (planTwo.close controlTwo (state, minState) (move.2, move.1))
                (planTwo.rev controlTwo (state, minState) move.2))
          let revMin := A.minPriorityState minState revNext
          (outOne,
            Sum.inr (Sum.inr (Sum.inr (Sum.inl
              ((chainTwo,
                  chainTwo.step (chainTwo.enterR controlTwo) (Sum.inl move.2),
                  ((revNext, revMin), revNext, revMin)),
                A.step state (bothRoundRecord move outOne outTwo),
                minState)))))
      | _ => (default, Sum.inr (Sum.inl (A.initial, A.initial)))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl ((plan, control, th), boundary)))) =>
      if TwoCore.isSubordinate other then
        let lab := plan.labelL control
        (lab.1 th move,
          Sum.inr (Sum.inr (Sum.inr (Sum.inl
            ((plan, plan.step control (Sum.inl move.2),
                revLeftThreadStep A th lab move.1 move.2),
              revLeftThreadClose A th lab move.1 move.2)))))
      else
        let base : OneBase (In₁ := In₁) A C_L C_R C_V := Sum.inl boundary
        (oneRecvOutput (A := A) plans base move,
          Sum.inl
            (oneLeftSuccessor (A := A) plans base move,
              oneBothSuccessor (A := A) plans base move))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (_, _, _))))) =>
      match other with
      | Sum.inr (Sum.inr (Sum.inr (Sum.inl ((planTwo, controlTwo, th), _)))) =>
          let lab := planTwo.labelR controlTwo
          (lab.1 th move,
            Sum.inr (Sum.inl (revRightThreadClose A th lab move.1 move.2)))
      | _ => (default, Sum.inr (Sum.inl (A.initial, A.initial)))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ((rplan, rc), (chainE, cVE, _))))) ) =>
      match other with
      | Sum.inl ((planTwo, chainTwo, controlTwo, state, minState), _) =>
          let outOne :=
            rplan.close rc (state, minState) (move.2, move.1)
          let outTwo :=
            (planTwo.label controlTwo).2 (state, minState) (move.2, move.1)
          let revNext :=
            A.step state
              (leftRoundRecord move
                (planTwo.close controlTwo (state, minState) (move.2, move.1))
                (planTwo.rev controlTwo (state, minState) move.2))
          let revMin := A.minPriorityState minState revNext
          (outOne,
            Sum.inr (Sum.inr (Sum.inr (Sum.inl
              ((chainTwo,
                  chainTwo.step (chainTwo.enterR controlTwo) (Sum.inl move.2),
                  ((revNext, revMin), revNext, revMin)),
                A.step state (bothRoundRecord move outOne outTwo),
                minState)))))
      | Sum.inr (Sum.inr (Sum.inr (Sum.inl ((_, _, thD), _)))) =>
          let lab := chainE.labelR cVE
          (lab.1 thD move,
            Sum.inr (Sum.inr (Sum.inr (Sum.inl
              ((chainE, chainE.step cVE (Sum.inl move.2),
                  revRightThreadReverse A thD lab move.1 move.2),
                revRightThreadClose A thD lab move.1 move.2)))))
      | _ => (default, Sum.inr (Sum.inl (A.initial, A.initial)))

/--
Process one's step at a `noRecv` round.  A pending bit resolves to the
boundary candidate: continuing a left block with a right round would be
a direct reversal.  Inside a reversed block a `noRecv` round is a
re-reversal (the informed side becomes blind, freezing the current
thread as the new entry) or a blind continuation.
-/
def oneNoRecvStep
    (core : OneCore (In₁ := In₁) A C_L C_R C_V)
    (inputOne : In₁) :
    Out₁ × OneCore (In₁ := In₁) A C_L C_R C_V :=
  match core with
  | Sum.inl (candLeft, candBoundary) =>
      let rplan := (plans candBoundary).2.1
      let chain := candLeft.2.1
      ((rplan.label rplan.init).1 inputOne,
        Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
          ((rplan, rplan.step rplan.init inputOne),
            (chain, chain.step (chain.enterL candLeft.2.2.1) (Sum.inr inputOne),
              (candLeft.2.2.2.1, candLeft.2.2.2.2))))))))
  | Sum.inr (Sum.inl boundary) =>
      let plan := (plans boundary).2.1
      ((plan.label plan.init).1 inputOne,
        Sum.inr (Sum.inr (Sum.inl (plan, plan.step plan.init inputOne))))
  | Sum.inr (Sum.inr (Sum.inl (plan, control))) =>
      ((plan.label control).1 inputOne,
        Sum.inr (Sum.inr (Sum.inl (plan, plan.step control inputOne))))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl ((chainD, cVD, thD), boundary)))) =>
      let rplan := (plans boundary).2.1
      ((rplan.label rplan.init).1 inputOne,
        Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
          ((rplan, rplan.step rplan.init inputOne),
            (chainD, chainD.step cVD (Sum.inr inputOne),
              thD.2)))))))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (plan, control, entry))))) =>
      let lab := plan.labelR control
      (lab.2.1 entry inputOne,
        Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl
          (plan, plan.step control (Sum.inr inputOne), entry))))))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ((rplan, rc), (chain, cV, entry)))))) =>
      ((rplan.label rc).1 inputOne,
        Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
          ((rplan, rplan.step rc inputOne),
            (chain, chain.step cV (Sum.inr inputOne), entry)))))))

/-- Process two's step at a receive round: the orientation mirror. -/
def twoRecvStep
    (core : TwoCore (In₁ := In₁) A C_L C_R C_V)
    (move : In₁ × In₂)
    (other : OneCore (In₁ := In₁) A C_L C_R C_V) :
    Out₂ × TwoCore (In₁ := In₁) A C_L C_R C_V :=
  match core with
  | Sum.inl (candRight, candBoundary) =>
      let base : TwoBase (In₁ := In₁) A C_L C_R C_V :=
        if OneCore.isSubordinate other then Sum.inr candRight
        else Sum.inl candBoundary
      (twoRecvOutput (A := A) plans base move,
        Sum.inl
          (twoRightSuccessor (A := A) plans base move,
            twoBothSuccessor (A := A) plans base move))
  | Sum.inr (Sum.inl boundary) =>
      let base : TwoBase (In₁ := In₁) A C_L C_R C_V := Sum.inl boundary
      (twoRecvOutput (A := A) plans base move,
        Sum.inl
          (twoRightSuccessor (A := A) plans base move,
            twoBothSuccessor (A := A) plans base move))
  | Sum.inr (Sum.inr (Sum.inl (plan, control))) =>
      match other with
      | Sum.inl ((planOne, chainOne, controlOne, state, minState), _) =>
          let outTwo := plan.close control (state, minState) move
          let outOne :=
            (planOne.label controlOne).2 (state, minState) move
          let revNext :=
            A.step state
              (rightRoundRecord (move.2, move.1)
                (planOne.rev controlOne (state, minState) move.1)
                (planOne.close controlOne (state, minState) move))
          let revMin := A.minPriorityState minState revNext
          (outTwo,
            Sum.inr (Sum.inr (Sum.inr (Sum.inl
              ((chainOne,
                  chainOne.step (chainOne.enterL controlOne) (Sum.inr move.1),
                  ((revNext, revMin), revNext, revMin)),
                A.step state (bothRoundRecord move outOne outTwo),
                minState)))))
      | _ => (default, Sum.inr (Sum.inl (A.initial, A.initial)))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl ((plan, control, th), boundary)))) =>
      if OneCore.isSubordinate other then
        let lab := plan.labelR control
        (lab.2.2.2 th move,
          Sum.inr (Sum.inr (Sum.inr (Sum.inl
            ((plan, plan.step control (Sum.inr move.1),
                revRightThreadStep A th lab move.1 move.2),
              revRightThreadClose A th lab move.1 move.2)))))
      else
        let base : TwoBase (In₁ := In₁) A C_L C_R C_V := Sum.inl boundary
        (twoRecvOutput (A := A) plans base move,
          Sum.inl
            (twoRightSuccessor (A := A) plans base move,
              twoBothSuccessor (A := A) plans base move))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (_, _, _))))) =>
      match other with
      | Sum.inr (Sum.inr (Sum.inr (Sum.inl ((planOne, controlOne, th), _)))) =>
          let lab := planOne.labelL controlOne
          (lab.2.2.2 th move,
            Sum.inr (Sum.inl (revLeftThreadClose A th lab move.1 move.2)))
      | _ => (default, Sum.inr (Sum.inl (A.initial, A.initial)))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ((lplan, lc), (chainE, cVE, _))))) ) =>
      match other with
      | Sum.inl ((planOne, chainOne, controlOne, state, minState), _) =>
          let outTwo := lplan.close lc (state, minState) move
          let outOne :=
            (planOne.label controlOne).2 (state, minState) move
          let revNext :=
            A.step state
              (rightRoundRecord (move.2, move.1)
                (planOne.rev controlOne (state, minState) move.1)
                (planOne.close controlOne (state, minState) move))
          let revMin := A.minPriorityState minState revNext
          (outTwo,
            Sum.inr (Sum.inr (Sum.inr (Sum.inl
              ((chainOne,
                  chainOne.step (chainOne.enterL controlOne) (Sum.inr move.1),
                  ((revNext, revMin), revNext, revMin)),
                A.step state (bothRoundRecord move outOne outTwo),
                minState)))))
      | Sum.inr (Sum.inr (Sum.inr (Sum.inl ((_, _, thD), _)))) =>
          let lab := chainE.labelL cVE
          (lab.2.2.2 thD move,
            Sum.inr (Sum.inr (Sum.inr (Sum.inl
              ((chainE, chainE.step cVE (Sum.inr move.1),
                  revLeftThreadReverse A thD lab move.1 move.2),
                revLeftThreadClose A thD lab move.1 move.2)))))
      | _ => (default, Sum.inr (Sum.inl (A.initial, A.initial)))

/-- Process two's step at a `noRecv` round. -/
def twoNoRecvStep
    (core : TwoCore (In₁ := In₁) A C_L C_R C_V)
    (inputTwo : In₂) :
    Out₂ × TwoCore (In₁ := In₁) A C_L C_R C_V :=
  match core with
  | Sum.inl (candRight, candBoundary) =>
      let lplan := (plans candBoundary).1
      let chain := candRight.2.1
      ((lplan.label lplan.init).1 inputTwo,
        Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
          ((lplan, lplan.step lplan.init inputTwo),
            (chain, chain.step (chain.enterR candRight.2.2.1) (Sum.inl inputTwo),
              (candRight.2.2.2.1, candRight.2.2.2.2))))))))
  | Sum.inr (Sum.inl boundary) =>
      let plan := (plans boundary).1
      ((plan.label plan.init).1 inputTwo,
        Sum.inr (Sum.inr (Sum.inl (plan, plan.step plan.init inputTwo))))
  | Sum.inr (Sum.inr (Sum.inl (plan, control))) =>
      ((plan.label control).1 inputTwo,
        Sum.inr (Sum.inr (Sum.inl (plan, plan.step control inputTwo))))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl ((chainD, cVD, thD), boundary)))) =>
      let lplan := (plans boundary).1
      ((lplan.label lplan.init).1 inputTwo,
        Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
          ((lplan, lplan.step lplan.init inputTwo),
            (chainD, chainD.step cVD (Sum.inl inputTwo),
              thD.2)))))))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (plan, control, entry))))) =>
      let lab := plan.labelL control
      (lab.2.2.1 entry inputTwo,
        Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl
          (plan, plan.step control (Sum.inl inputTwo), entry))))))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ((lplan, lc), (chain, cV, entry)))))) =>
      ((lplan.label lc).1 inputTwo,
        Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
          ((lplan, lplan.step lc inputTwo),
            (chain, chain.step cV (Sum.inl inputTwo), entry)))))))

end Steps

section Automaton

variable (A) (C_L C_R C_V)

/-- The summary state spaces of the two processes. -/
def journalSummaryType : Proc -> Type max u v x y s
  | Proc.one =>
      Out₁ ×
        OneCore (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂) A C_L C_R C_V
  | Proc.two =>
      Out₂ ×
        TwoCore (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) A C_L C_R C_V

variable {A C_L C_R C_V}

/-- The first input carried by a view increment. -/
def inputOneOf [Inhabited In₁] : PSum In₁ In₂ -> In₁
  | PSum.inl inputOne => inputOne
  | PSum.inr _ => default

/-- The second input carried by a view increment. -/
def inputTwoOf [Inhabited In₂] : PSum In₁ In₂ -> In₂
  | PSum.inr inputTwo => inputTwo
  | PSum.inl _ => default

variable
  [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
  [DecidableEq In₁] [DecidableEq In₂] [DecidableEq A.State]
  [Fintype C_L] [DecidableEq C_L] [Fintype C_R] [DecidableEq C_R]
  [Fintype C_V] [DecidableEq C_V]
  [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
  [Inhabited C_L] [Inhabited C_R] [Inhabited C_V]

instance : Fintype (OneTier (In₁ := In₁) A C_L C_R C_V) := inferInstance

instance : Fintype (TwoTier (In₁ := In₁) A C_L C_R C_V) := inferInstance

instance : ∀ d : Proc,
    Fintype (journalSummaryType (In₁ := In₁) A C_L C_R C_V d)
  | Proc.one => inferInstanceAs (Fintype (Out₁ × _))
  | Proc.two => inferInstanceAs (Fintype (Out₂ × _))

/--
The local summary automaton of a committed plan family: the finite
per-process knowledge with which the two processes play the arena word
from their own views.  The readback tables are the output projections.
-/
def journalSummaries (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V) :
    LocalSummaryAutomaton.{u, v, max u v x y s} In₁ In₂ where
  Summary := journalSummaryType (In₁ := In₁) A C_L C_R C_V
  finite := inferInstance
  initial := fun d =>
    match d with
    | Proc.one => (default, Sum.inr (Sum.inl (A.initial, A.initial)))
    | Proc.two => (default, Sum.inr (Sum.inl (A.initial, A.initial)))
  stepNoRecv := fun d =>
    match d with
    | Proc.one => fun summary input =>
        oneNoRecvStep (A := A) plans summary.2 (inputOneOf input)
    | Proc.two => fun summary input =>
        twoNoRecvStep (A := A) plans summary.2 (inputTwoOf input)
  stepRecv := fun d =>
    match d with
    | Proc.one => fun summary inputSelf other inputOther =>
        oneRecvStep (A := A) plans summary.2
          (inputOneOf inputSelf, inputTwoOf inputOther) other.2
    | Proc.two => fun summary inputSelf other inputOther =>
        twoRecvStep (A := A) plans summary.2
          (inputOneOf inputOther, inputTwoOf inputSelf) other.2

/--
The pasted strategy of a committed plan family: each process folds its
view through the candidate summaries and emits the stored output.
-/
def journalStrategy (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V) :
    StrategyPair In₁ In₂ Out₁ Out₂ :=
  (journalSummaries (In₁ := In₁) plans).readbackStrategy
    Prod.fst Prod.fst

end Automaton

end DetParityAutomaton

end DistributedSynthesis
