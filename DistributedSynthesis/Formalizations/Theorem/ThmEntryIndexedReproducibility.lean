/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmCandidateSummaries
import DistributedSynthesis.Formalizations.Theorem.ThmPlanFolding

/-!
# Entry-indexed reproducibility of the blind reversal output

This file formalizes `prop:entrysound` from `real_model/paper.tex` at the
boundary-game level: the soundness (reproducibility) half of the entry-indexed
handoff commitment for direct reversals.

At a summary position `Sum.inl (candLeft, candBoundary)` process one, on a
`noRecv` (right) round, cannot tell whether it is opening a fresh right block at
the boundary `candBoundary` (the no-direct case, arena target
`boundaryOpenRightTarget`) or directly reversing the left block `candLeft` (a
direct reversal, arena target `leftReverseTarget`).  The two histories differ
only by the frozen own-fringe bit `b_old` of `lem:noorientationconsensus`, which
process one never observes; by `thm:onebitfringe` it is its only pending
ambiguity.  A legal blind strategy must therefore emit the same output on the
two candidates -- this is **θ̄-measurability** (`OneBlindMeasurable`) -- and once
it does, its reversal output is **reproducible** from process one's own view: it
equals the right-block opening output, which reads only process one's own input
and not the reversed-block state it cannot observe.

The two blind outputs the summary must reconcile are, verbatim from
`ThmArenaFold.arenaRecord`:

* the **reversal** output `LeftBlockPlan.rev control (state, minState) inputOne`
  (the `leftReverseTarget` round record), which reads the block state; and
* the **right-open** output `(RightBlockPlan.label init).1 inputOne` (the
  `boundaryOpenRightTarget` round record), which reads only `inputOne`.

θ̄-measurability equates them; reproducibility is then that the former is a
function of `inputOne` alone.  The statements for process two are the orientation
mirror.  This is the sound half that `prop:starsound` needs; it makes no
finiteness or completeness claim (those are `prop:reversedblockmonitor` and
`prop:starcomplete`).
-/

namespace DistributedSynthesis

universe u v x y s

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

namespace DetParityAutomaton

variable
  {A :
    DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂)}
  {C_L C_R C_V : Type max u v x y s}

/--
Process one's blind output on a directly reversing right round out of a left
block: the left plan's staged reversing value, reading the block state and its
own input.  This is the `outOne` of `leftReverseTarget`'s round record.
-/
def blindLeftReversalOutput
    (ldata : LeftBlockData (In₁ := In₁) A C_L C_R C_V) (inputOne : In₁) : Out₁ :=
  ldata.1.rev ldata.2.2.1 (ldata.2.2.2.1, ldata.2.2.2.2) inputOne

/--
Process one's blind output on a right round opening a fresh right block at a
boundary: the committed right plan's opening sender value, reading only its own
input.  This is the `outOne` of `boundaryOpenRightTarget`'s round record and is
manifestly a function of `(boundary, inputOne)` alone.
-/
def blindRightOpenOutput
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (boundary : A.State × A.State) (inputOne : In₁) : Out₁ :=
  ((plans boundary).2.1.label (plans boundary).2.1.init).1 inputOne

/--
θ̄-measurability of process one's blind side at a `Sum.inl` candidate pair: the
direct-reversal output of the left-block candidate agrees with the right-opening
output of the boundary candidate, for every own input.  A legal blind strategy
satisfies this because it cannot observe the fringe bit `b_old` that distinguishes
the two candidates (`lem:noorientationconsensus`).
-/
def OneBlindMeasurable
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (ldata : LeftBlockData (In₁ := In₁) A C_L C_R C_V)
    (boundary : A.State × A.State) : Prop :=
  ∀ inputOne : In₁,
    blindLeftReversalOutput (A := A) ldata inputOne =
      blindRightOpenOutput (A := A) plans boundary inputOne

/--
Reproducibility of the blind reversal output (`prop:entrysound`, process one).
Under θ̄-measurability the reversal output, a priori a function of the whole
within-block datum `ldata` (its committed left plan, control, and the block
state `(state, minState)` it holds), equals the right-opening output, which is a
function of `(boundary, inputOne)` alone.  Hence process one reproduces its
reversal output from data it possesses -- the boundary candidate `boundary` (the
reduced entry thread it determines from its own view) and its own input -- without
consulting the reversed-block state it cannot observe.
-/
theorem blindLeftReversal_reproducible
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (ldata : LeftBlockData (In₁ := In₁) A C_L C_R C_V)
    (boundary : A.State × A.State)
    (h : OneBlindMeasurable plans ldata boundary) (inputOne : In₁) :
    blindLeftReversalOutput (A := A) ldata inputOne =
      ((plans boundary).2.1.label (plans boundary).2.1.init).1 inputOne :=
  h inputOne

/--
Process two's blind output on a directly reversing left round out of a right
block: the right plan's staged reversing value, reading the block state and its
own input.  This is the `outTwo` of `rightReverseTarget`'s round record.
-/
def blindRightReversalOutput
    (rdata : RightBlockData (In₁ := In₁) A C_L C_R C_V) (inputTwo : In₂) : Out₂ :=
  rdata.1.rev rdata.2.2.1 (rdata.2.2.2.1, rdata.2.2.2.2) inputTwo

/--
Process two's blind output on a left round opening a fresh left block at a
boundary: the committed left plan's opening sender value, reading only its own
input.  This is the `outTwo` of `boundaryOpenLeftTarget`'s round record and is
manifestly a function of `(boundary, inputTwo)` alone.
-/
def blindLeftOpenOutput
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (boundary : A.State × A.State) (inputTwo : In₂) : Out₂ :=
  ((plans boundary).1.label (plans boundary).1.init).1 inputTwo

/--
θ̄-measurability of process two's blind side at a `Sum.inl` candidate pair: the
orientation mirror of `OneBlindMeasurable`.
-/
def TwoBlindMeasurable
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (rdata : RightBlockData (In₁ := In₁) A C_L C_R C_V)
    (boundary : A.State × A.State) : Prop :=
  ∀ inputTwo : In₂,
    blindRightReversalOutput (A := A) rdata inputTwo =
      blindLeftOpenOutput (A := A) plans boundary inputTwo

/--
Reproducibility of the blind reversal output (`prop:entrysound`, process two):
the orientation mirror of `blindLeftReversal_reproducible`.
-/
theorem blindRightReversal_reproducible
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (rdata : RightBlockData (In₁ := In₁) A C_L C_R C_V)
    (boundary : A.State × A.State)
    (h : TwoBlindMeasurable plans rdata boundary) (inputTwo : In₂) :
    blindRightReversalOutput (A := A) rdata inputTwo =
      ((plans boundary).1.label (plans boundary).1.init).1 inputTwo :=
  h inputTwo

/-! ### Agreement with the arena outputs

The two abstract blind values are exactly the process-one output the arena emits
at the two positions a `Sum.inl` core cannot tell apart on a right round: the
boundary (no direct reversal, `Sum.inl`) and the within-left block (direct
reversal, `Sum.inr (Sum.inr (Sum.inl _))`).  These lemmas pin the accessors to
`arenaRecord` and derive the arena-level agreement under θ̄-measurability, which
is the fact the reversed-tier tracking consumes. -/

/-- The arena's process-one output when a right round opens a right block at a
boundary is `blindRightOpenOutput`. -/
theorem arenaRecord_boundary_right_outputOne
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (state minState : A.State) (envRound : EnvironmentRound In₁ In₂)
    (hgraph : envRound.graph = Graph.right) :
    (arenaRecord plans (Sum.inl (state, minState)) envRound).outputOne =
      blindRightOpenOutput (A := A) plans (state, minState) envRound.inputOne := by
  simp [arenaRecord, hgraph, blindRightOpenOutput, rightRoundRecord]

/-- The arena's process-one output on a directly reversing right round out of a
left block is `blindLeftReversalOutput`. -/
theorem arenaRecord_inLeft_right_outputOne
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (ldata : LeftBlockData (In₁ := In₁) A C_L C_R C_V)
    (envRound : EnvironmentRound In₁ In₂)
    (hgraph : envRound.graph = Graph.right) :
    (arenaRecord plans (Sum.inr (Sum.inr (Sum.inl ldata))) envRound).outputOne =
      blindLeftReversalOutput (A := A) ldata envRound.inputOne := by
  obtain ⟨plan, chain, control, state, minState⟩ := ldata
  simp [arenaRecord, hgraph, blindLeftReversalOutput, rightRoundRecord]

/--
Arena-level θ̄-measurability of process one's blind side: on a right round the
arena emits the same process-one output at the within-left block (a direct
reversal) as at the boundary (no reversal), whenever the plan is θ̄-measurable
at the candidate pair.  Process one, unable to tell the two positions apart,
emits this common value from its own view.
-/
theorem arenaRecord_one_blind_agree
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (ldata : LeftBlockData (In₁ := In₁) A C_L C_R C_V)
    (boundary : A.State × A.State) (envRound : EnvironmentRound In₁ In₂)
    (hgraph : envRound.graph = Graph.right)
    (h : OneBlindMeasurable plans ldata boundary) :
    (arenaRecord plans (Sum.inr (Sum.inr (Sum.inl ldata))) envRound).outputOne =
      (arenaRecord plans (Sum.inl boundary) envRound).outputOne := by
  obtain ⟨bstate, bminState⟩ := boundary
  rw [arenaRecord_inLeft_right_outputOne plans ldata envRound hgraph,
    arenaRecord_boundary_right_outputOne plans bstate bminState envRound hgraph]
  exact h envRound.inputOne

/-- The arena's process-two output when a left round opens a left block at a
boundary is `blindLeftOpenOutput`. -/
theorem arenaRecord_boundary_left_outputTwo
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (state minState : A.State) (envRound : EnvironmentRound In₁ In₂)
    (hgraph : envRound.graph = Graph.left) :
    (arenaRecord plans (Sum.inl (state, minState)) envRound).outputTwo =
      blindLeftOpenOutput (A := A) plans (state, minState) envRound.inputTwo := by
  simp [arenaRecord, hgraph, blindLeftOpenOutput, leftRoundRecord]

/-- The arena's process-two output on a directly reversing left round out of a
right block is `blindRightReversalOutput`. -/
theorem arenaRecord_inRight_left_outputTwo
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (rdata : RightBlockData (In₁ := In₁) A C_L C_R C_V)
    (envRound : EnvironmentRound In₁ In₂)
    (hgraph : envRound.graph = Graph.left) :
    (arenaRecord plans (Sum.inr (Sum.inr (Sum.inr (Sum.inl rdata)))) envRound).outputTwo =
      blindRightReversalOutput (A := A) rdata envRound.inputTwo := by
  obtain ⟨plan, chain, control, state, minState⟩ := rdata
  simp [arenaRecord, hgraph, blindRightReversalOutput, leftRoundRecord]

/-- Arena-level θ̄-measurability of process two's blind side: the orientation
mirror of `arenaRecord_one_blind_agree`. -/
theorem arenaRecord_two_blind_agree
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (rdata : RightBlockData (In₁ := In₁) A C_L C_R C_V)
    (boundary : A.State × A.State) (envRound : EnvironmentRound In₁ In₂)
    (hgraph : envRound.graph = Graph.left)
    (h : TwoBlindMeasurable plans rdata boundary) :
    (arenaRecord plans (Sum.inr (Sum.inr (Sum.inr (Sum.inl rdata)))) envRound).outputTwo =
      (arenaRecord plans (Sum.inl boundary) envRound).outputTwo := by
  obtain ⟨bstate, bminState⟩ := boundary
  rw [arenaRecord_inRight_left_outputTwo plans rdata envRound hgraph,
    arenaRecord_boundary_left_outputTwo plans bstate bminState envRound hgraph]
  exact h envRound.inputTwo

/-! ### The plan-family θ̄-measurability hypothesis

A committed plan family is *blind-measurable* when every process's blind
reversal output agrees with its no-direct opening output at the corresponding
candidate pair (uniform form, over all pairs; the reachable-only form is
implied).  This is the boundary-game statement of `def:entrythread`'s
entry-indexed commitment: a legal blind strategy, unable to observe the fringe
bit `b_old`, commits plans on which the two indistinguishable outputs coincide.
It is the single hypothesis the dropped-`hnodirect` journal readback consumes on
the blind side; the informed side needs none (it resolves `b_old` at the reversal
round, `lem:reversaltwobits`). -/

/-- Both processes' blind sides are θ̄-measurable at every candidate pair.  The
within-block datum is one *committed* at some boundary atom (`ChainCommittedAt`),
so the reversal output quantified over is the strategy's own committed reversal
output, not an arbitrary function; this is what makes the hypothesis a genuine
θ̄-factoring claim (paper `prop:entrysound`/`prop:starcomplete`) rather than a
vacuous demand on unreachable data. -/
def PlanBlindMeasurable (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V) : Prop :=
  (∀ (atom : A.State × A.State)
      (chain :
        ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
          A C_L C_R C_V)
      (control : C_L) (state minState : A.State) (boundary : A.State × A.State),
      OneBlindMeasurable plans
        ((plans atom).1, chain, control, state, minState) boundary) ∧
    (∀ (atom : A.State × A.State)
        (chain :
          ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
            A C_L C_R C_V)
        (control : C_R) (state minState : A.State) (boundary : A.State × A.State),
        TwoBlindMeasurable plans
          ((plans atom).2.1, chain, control, state, minState) boundary)

/-! ### Per-round (continuation) θ̄-measurability

The reversal-entry agreement is not enough: a reversed block of two or more
rounds emits a blind value on each interior round, and the summary state after a
`Sum.inl`+noRecv transition is the same whether the arena continued into a
no-direct right block (interior output `(RightBlockPlan.label control).1 inputOne`,
process one the subordinate sender) or a reversed-right block (interior output
`(ChainPlan.labelR control).2.1 entry inputOne`, process one the blind sender).
For one summary to reproduce both, the two must agree on every interior round.
These lemmas pin the interior blind values to `arenaRecord` and state the interior
agreement, the companion of `arenaRecord_one_blind_agree` for continuation rounds.
The full plan condition (a lockstep bisimulation of the two control trajectories
maintaining this agreement) composes these round conditions along the block. -/

/-- Process one's blind interior output inside a no-direct right block (the
subordinate sender's continuation value), reading only its own input. -/
def blindRightSubordinateOutput
    (rdata : RightBlockData (In₁ := In₁) A C_L C_R C_V) (inputOne : In₁) : Out₁ :=
  (rdata.1.label rdata.2.2.1).1 inputOne

/-- Process one's blind interior output inside a reversed-right block (the blind
sender's `oneSend` value), reading the frozen entry and its own input. -/
def blindRevRightSendOutput
    (chain :
      ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_L C_R C_V)
    (control : C_V) (entry : A.State × A.State) (inputOne : In₁) : Out₁ :=
  (chain.labelR control).2.1 entry inputOne

/-- The arena's process-one output on an interior right round inside a right
block is `blindRightSubordinateOutput`. -/
theorem arenaRecord_inRight_right_outputOne
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (rdata : RightBlockData (In₁ := In₁) A C_L C_R C_V)
    (envRound : EnvironmentRound In₁ In₂)
    (hgraph : envRound.graph = Graph.right) :
    (arenaRecord plans (Sum.inr (Sum.inr (Sum.inr (Sum.inl rdata)))) envRound).outputOne =
      blindRightSubordinateOutput (A := A) rdata envRound.inputOne := by
  obtain ⟨plan, chain, control, state, minState⟩ := rdata
  simp [arenaRecord, hgraph, blindRightSubordinateOutput, rightRoundRecord]

/-- The arena's process-one output on an interior right round inside a
reversed-right block is `blindRevRightSendOutput`. -/
theorem arenaRecord_revRight_right_outputOne
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (chain :
      ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_L C_R C_V)
    (control : C_V) (entry : A.State × A.State) (state minState : A.State)
    (envRound : EnvironmentRound In₁ In₂)
    (hgraph : envRound.graph = Graph.right) :
    (arenaRecord plans
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
          (chain, control, entry, state, minState)))))) envRound).outputOne =
      blindRevRightSendOutput (A := A) chain control entry envRound.inputOne := by
  simp [arenaRecord, hgraph, blindRevRightSendOutput, rightRoundRecord]

/--
Interior θ̄-measurability of process one's blind side: the hypothesis that, at a
matched pair of a no-direct right-block interior and a reversed-right-block
interior, the subordinate continuation value agrees with the blind `oneSend`
value on every own input.  This is the per-round condition the block-long
lockstep bisimulation maintains.
-/
def OneBlindContinueMeasurable
    (rdata : RightBlockData (In₁ := In₁) A C_L C_R C_V)
    (chain :
      ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_L C_R C_V)
    (control : C_V) (entry : A.State × A.State) : Prop :=
  ∀ inputOne : In₁,
    blindRightSubordinateOutput (A := A) rdata inputOne =
      blindRevRightSendOutput (A := A) chain control entry inputOne

/-- Interior arena agreement: on a right round the arena emits the same
process-one output at a reversed-right interior as at the matched right-block
interior, whenever the interior is θ̄-measurable. -/
theorem arenaRecord_one_blind_continue_agree
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (rdata : RightBlockData (In₁ := In₁) A C_L C_R C_V)
    (chain :
      ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_L C_R C_V)
    (control : C_V) (entry : A.State × A.State) (state minState : A.State)
    (envRound : EnvironmentRound In₁ In₂)
    (hgraph : envRound.graph = Graph.right)
    (h : OneBlindContinueMeasurable (A := A) rdata chain control entry) :
    (arenaRecord plans
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
          (chain, control, entry, state, minState)))))) envRound).outputOne =
      (arenaRecord plans (Sum.inr (Sum.inr (Sum.inr (Sum.inl rdata)))) envRound).outputOne := by
  rw [arenaRecord_revRight_right_outputOne plans chain control entry state minState
        envRound hgraph,
    arenaRecord_inRight_right_outputOne plans rdata envRound hgraph]
  exact (h envRound.inputOne).symm

/-! ### The block-long lockstep bisimulation

A process's blind output inside a block depends only on its own control and
input, and its control advances only on its own input: process one's subordinate
control advances by `RightBlockPlan.step c inputOne` and its reversed control by
`ChainPlan.step c (Sum.inr inputOne)`, both on `inputOne` alone.  So the no-direct
and reversed control trajectories run in lockstep on the process's own input
word.  Trace-measurability is the invariant that their blind outputs agree along
every such word; it yields the immediate interior agreement (`head`) and is
preserved by one interior round (`step`), which is exactly the induction
`journal_step` needs across a reversed block.  The mirror on process two relates a
left-block subordinate to a reversed-left blind sender. -/

/-- Process one's subordinate control after a word of its own inputs. -/
def rightSubordinateControlAfter
    (rightplan :
      RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_R) :
    C_R -> List In₁ -> C_R
  | c, [] => c
  | c, i :: w => rightSubordinateControlAfter rightplan (rightplan.step c i) w

/-- Process one's reversed (blind sender) control after a word of its own
inputs. -/
def chainSendControlAfter
    (chain :
      ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_L C_R C_V) :
    C_V -> List In₁ -> C_V
  | c, [] => c
  | c, i :: w => chainSendControlAfter chain (chain.step c (Sum.inr i)) w

/--
Block-long θ̄-measurability of process one's blind side: along every word of its
own inputs, the subordinate continuation value agrees with the reversed blind
`oneSend` value.  This is trace-equivalence of the two lockstep control
trajectories; it composes the per-round condition
`OneBlindContinueMeasurable` over the whole block.
-/
def OneBlindTraceMeasurable
    (rightplan :
      RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_R)
    (c_R : C_R)
    (chain :
      ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_L C_R C_V)
    (c_V : C_V) (entry : A.State × A.State) : Prop :=
  ∀ (w : List In₁) (i : In₁),
    (rightplan.label (rightSubordinateControlAfter rightplan c_R w)).1 i =
      (chain.labelR (chainSendControlAfter chain c_V w)).2.1 entry i

/-- The immediate interior agreement extracted from the block-long invariant. -/
theorem OneBlindTraceMeasurable.head
    {rightplan :
      RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_R}
    {c_R : C_R}
    {chain :
      ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_L C_R C_V}
    {c_V : C_V} {entry : A.State × A.State}
    (h : OneBlindTraceMeasurable (A := A) rightplan c_R chain c_V entry)
    (i : In₁) :
    (rightplan.label c_R).1 i = (chain.labelR c_V).2.1 entry i :=
  h [] i

/-- Bridge: the block-long invariant gives the per-round interior measurability
`OneBlindContinueMeasurable` at the current controls, for any within-block datum
built from the subordinate plan and control.  This links the trace invariant to
the arena agreement `arenaRecord_one_blind_continue_agree`. -/
theorem OneBlindTraceMeasurable.continueMeasurable
    {rightplan :
      RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_R}
    {c_R : C_R}
    {chain :
      ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_L C_R C_V}
    {c_V : C_V} {entry : A.State × A.State}
    (h : OneBlindTraceMeasurable (A := A) rightplan c_R chain c_V entry)
    (chain' :
      ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_L C_R C_V)
    (state minState : A.State) :
    OneBlindContinueMeasurable (A := A) (rightplan, chain', c_R, state, minState)
      chain c_V entry :=
  fun i => h.head i

/-- The block-long invariant is preserved by one interior round: the two
controls advance on the process's own input. -/
theorem OneBlindTraceMeasurable.step
    {rightplan :
      RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_R}
    {c_R : C_R}
    {chain :
      ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_L C_R C_V}
    {c_V : C_V} {entry : A.State × A.State}
    (h : OneBlindTraceMeasurable (A := A) rightplan c_R chain c_V entry)
    (i : In₁) :
    OneBlindTraceMeasurable (A := A) rightplan (rightplan.step c_R i) chain
      (chain.step c_V (Sum.inr i)) entry :=
  fun w j => h (i :: w) j

/-- Process two's subordinate control after a word of its own inputs. -/
def leftSubordinateControlAfter
    (leftplan :
      LeftBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_L) :
    C_L -> List In₂ -> C_L
  | c, [] => c
  | c, i :: w => leftSubordinateControlAfter leftplan (leftplan.step c i) w

/-- Process two's reversed (blind sender) control after a word of its own
inputs. -/
def chainSendControlAfterTwo
    (chain :
      ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_L C_R C_V) :
    C_V -> List In₂ -> C_V
  | c, [] => c
  | c, i :: w => chainSendControlAfterTwo chain (chain.step c (Sum.inl i)) w

/-- Block-long θ̄-measurability of process two's blind side: the orientation
mirror of `OneBlindTraceMeasurable`. -/
def TwoBlindTraceMeasurable
    (leftplan :
      LeftBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_L)
    (c_L : C_L)
    (chain :
      ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_L C_R C_V)
    (c_V : C_V) (entry : A.State × A.State) : Prop :=
  ∀ (w : List In₂) (i : In₂),
    (leftplan.label (leftSubordinateControlAfter leftplan c_L w)).1 i =
      (chain.labelL (chainSendControlAfterTwo chain c_V w)).2.2.1 entry i

/-- The immediate interior agreement for process two. -/
theorem TwoBlindTraceMeasurable.head
    {leftplan :
      LeftBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_L}
    {c_L : C_L}
    {chain :
      ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_L C_R C_V}
    {c_V : C_V} {entry : A.State × A.State}
    (h : TwoBlindTraceMeasurable (A := A) leftplan c_L chain c_V entry)
    (i : In₂) :
    (leftplan.label c_L).1 i = (chain.labelL c_V).2.2.1 entry i :=
  h [] i

/-! ### θ̄-indexing of the blind slot (entry measurability)

At the reversal round the blind process cannot compute the arena's post-round
entry (it does not receive, so it never sees the partner output that the entry's
automaton step consumes); it freezes the pre-round entry it does know.  For its
`oneSend` value to match the arena's -- which uses the post-round entry -- the
blind slot must agree on the two entries, which differ exactly by the frozen
own-fringe bit `b_old`.  This is `def:entrythread`'s requirement that the
entry-indexed table factor through `θ̄ = θ mod b_old`. -/

/-- Process one's reversed `oneSend` value agrees on two entries the blind side
cannot tell apart (the frozen pre-reversal entry and the true post-reversal
entry). -/
def OneBlindEntryMeasurable
    (chain :
      ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_L C_R C_V)
    (control : C_V) (entry entry' : A.State × A.State) : Prop :=
  ∀ inputOne : In₁,
    (chain.labelR control).2.1 entry inputOne =
      (chain.labelR control).2.1 entry' inputOne

/-- Under entry measurability the arena's process-one output at a reversed-right
interior is unchanged when the entry is replaced by an indistinguishable one. -/
theorem arenaRecord_revRight_entry_swap
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (chain :
      ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_L C_R C_V)
    (control : C_V) (entry entry' : A.State × A.State)
    (state minState state' minState' : A.State)
    (envRound : EnvironmentRound In₁ In₂)
    (hgraph : envRound.graph = Graph.right)
    (h : OneBlindEntryMeasurable (A := A) chain control entry entry') :
    (arenaRecord plans
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
          (chain, control, entry, state, minState)))))) envRound).outputOne =
      (arenaRecord plans
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
          (chain, control, entry', state', minState')))))) envRound).outputOne := by
  rw [arenaRecord_revRight_right_outputOne plans chain control entry state minState
        envRound hgraph,
    arenaRecord_revRight_right_outputOne plans chain control entry' state' minState'
        envRound hgraph]
  exact h envRound.inputOne

/-- Process two's reversed `twoSend` value agrees on two indistinguishable
entries: the orientation mirror of `OneBlindEntryMeasurable`. -/
def TwoBlindEntryMeasurable
    (chain :
      ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_L C_R C_V)
    (control : C_V) (entry entry' : A.State × A.State) : Prop :=
  ∀ inputTwo : In₂,
    (chain.labelL control).2.2.1 entry inputTwo =
      (chain.labelL control).2.2.1 entry' inputTwo

/-- The block-long invariant is preserved by one interior round, for process
two. -/
theorem TwoBlindTraceMeasurable.step
    {leftplan :
      LeftBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_L}
    {c_L : C_L}
    {chain :
      ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_L C_R C_V}
    {c_V : C_V} {entry : A.State × A.State}
    (h : TwoBlindTraceMeasurable (A := A) leftplan c_L chain c_V entry)
    (i : In₂) :
    TwoBlindTraceMeasurable (A := A) leftplan (leftplan.step c_L i) chain
      (chain.step c_V (Sum.inl i)) entry :=
  fun w j => h (i :: w) j

/-! ### Block-long blind agreement of the folded chain, by construction

`foldChain` (paper `lem:blindonetransducer`) builds the reversed-block chain by
replaying the committed block plans, tying the chain control `C_L ⊕ C_R` to the
block control.  The two lemmas below are the payoff for the single-reversal
direction: at a reversed-right block the chain's blind `oneSend` slot is *by
construction* the right plan's subordinate label, and its control advances in
lockstep with the block's, so `OneBlindTraceMeasurable` holds with no hypothesis
on the underlying strategy (mirror for process two at a reversed-left block).
This turns the `leftTrace`/`rightTrace` demands of `ReversalMeasurable` from
assumptions into consequences of the fold, whenever the certificate is read at
the committed folded chain.  The blind slot ignores the entry thread, so the
agreement is uniform in `entry`, as `def:entrythread`'s θ̄-factoring requires. -/

/-- Under `foldChain`, process one's reversed send-control after a word of its
own inputs is exactly the right plan's subordinate control, tagged `Sum.inr`. -/
theorem chainSendControlAfter_foldChain_inr
    (leftPlan :
      LeftBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_L)
    (rightPlan :
      RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_R)
    (c_R : C_R) (w : List In₁) :
    chainSendControlAfter (foldChain leftPlan rightPlan) (Sum.inr c_R) w =
      Sum.inr (rightSubordinateControlAfter rightPlan c_R w) := by
  induction w generalizing c_R with
  | nil => rfl
  | cons i w ih => exact ih (rightPlan.step c_R i)

/-- Under `foldChain`, process two's reversed send-control after a word of its
own inputs is exactly the left plan's subordinate control, tagged `Sum.inl`. -/
theorem chainSendControlAfterTwo_foldChain_inl
    (leftPlan :
      LeftBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_L)
    (rightPlan :
      RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_R)
    (c_L : C_L) (w : List In₂) :
    chainSendControlAfterTwo (foldChain leftPlan rightPlan) (Sum.inl c_L) w =
      Sum.inl (leftSubordinateControlAfter leftPlan c_L w) := by
  induction w generalizing c_L with
  | nil => rfl
  | cons i w ih => exact ih (leftPlan.step c_L i)

/-- Process one's block-long blind agreement holds by construction at the folded
chain: the reversed-right send slot is the right plan's subordinate label at the
matched control, for every entry thread. -/
theorem foldChain_oneBlindTraceMeasurable
    (leftPlan :
      LeftBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_L)
    (rightPlan :
      RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_R)
    (c_R : C_R) (entry : A.State × A.State) :
    OneBlindTraceMeasurable (A := A) rightPlan c_R
      (foldChain leftPlan rightPlan) (Sum.inr c_R) entry := by
  intro w i
  rw [chainSendControlAfter_foldChain_inr]
  rfl

/-- Process two's block-long blind agreement holds by construction at the folded
chain: the mirror of `foldChain_oneBlindTraceMeasurable`. -/
theorem foldChain_twoBlindTraceMeasurable
    (leftPlan :
      LeftBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_L)
    (rightPlan :
      RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_R)
    (c_L : C_L) (entry : A.State × A.State) :
    TwoBlindTraceMeasurable (A := A) leftPlan c_L
      (foldChain leftPlan rightPlan) (Sum.inl c_L) entry := by
  intro w i
  rw [chainSendControlAfterTwo_foldChain_inl]
  rfl

/-! ### Cross-boundary blind agreement for the global fold

The single-reversal lemmas above pair a block plan with the fold of *that same*
plan.  The global fold instead pairs the *successor* boundary's block plan
(`rpCand`) with the *opening* boundary's chain (`foldChain leftPlan rpOpen`),
two distinct atoms (paper `cor:blindcrossreading`).

The general engine is `_agree`: block-long agreement holds exactly when the two
plans emit the same blind output *at every own-input word* -- the word-indexed
form the entry-indexed table `t_{\bar\theta}` needs (`def:entrythread`; the blind
output depends on the own-input word, not merely a constant).  This is the
view-summary shape: two plans driven by the one `\bar\theta`-monitor from a common
entry produce equal outputs word-by-word.  The constant-table lemmas `_shared`
(used by the degenerate `globalFold`) are the special case where the common output
is a fixed table `t`, independent of the control the word reaches. -/

/-- Process one's block-long blind agreement across two boundaries whose right
plans emit the same blind output at every own-input word (the general,
word-indexed form). -/
theorem foldChain_oneBlindTraceMeasurable_agree
    (leftPlan :
      LeftBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_L)
    (rpCand rpOpen :
      RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_R)
    (c_R c_R' : C_R) (entry : A.State × A.State)
    (hagree :
      ∀ w : List In₁,
        (rpCand.label (rightSubordinateControlAfter rpCand c_R w)).1 =
          (rpOpen.label (rightSubordinateControlAfter rpOpen c_R' w)).1) :
    OneBlindTraceMeasurable (A := A) rpCand c_R
      (foldChain leftPlan rpOpen) (Sum.inr c_R') entry := by
  intro w i
  rw [chainSendControlAfter_foldChain_inr]
  exact congrFun (hagree w) i

/-- Process two's block-long blind agreement in the word-indexed form: the mirror
of `foldChain_oneBlindTraceMeasurable_agree`. -/
theorem foldChain_twoBlindTraceMeasurable_agree
    (lpCand lpOpen :
      LeftBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_L)
    (rightPlan :
      RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_R)
    (c_L c_L' : C_L) (entry : A.State × A.State)
    (hagree :
      ∀ w : List In₂,
        (lpCand.label (leftSubordinateControlAfter lpCand c_L w)).1 =
          (lpOpen.label (leftSubordinateControlAfter lpOpen c_L' w)).1) :
    TwoBlindTraceMeasurable (A := A) lpCand c_L
      (foldChain lpOpen rightPlan) (Sum.inl c_L') entry := by
  intro w i
  rw [chainSendControlAfterTwo_foldChain_inl]
  exact congrFun (hagree w) i

/-- Process one's block-long blind agreement across two boundaries whose right
plans share the blind table `t`: the constant-table special case of
`foldChain_oneBlindTraceMeasurable_agree`. -/
theorem foldChain_oneBlindTraceMeasurable_shared
    (leftPlan :
      LeftBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_L)
    (rpCand rpOpen :
      RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_R)
    (t : In₁ -> Out₁)
    (hcand : ∀ c, (rpCand.label c).1 = t)
    (hopen : ∀ c, (rpOpen.label c).1 = t)
    (c_R c_R' : C_R) (entry : A.State × A.State) :
    OneBlindTraceMeasurable (A := A) rpCand c_R
      (foldChain leftPlan rpOpen) (Sum.inr c_R') entry :=
  foldChain_oneBlindTraceMeasurable_agree leftPlan rpCand rpOpen c_R c_R' entry
    (fun w => by rw [hcand, hopen])

/-- Process two's block-long blind agreement across two boundaries whose left
plans share the blind table `t`: the constant-table special case of
`foldChain_twoBlindTraceMeasurable_agree`. -/
theorem foldChain_twoBlindTraceMeasurable_shared
    (lpCand lpOpen :
      LeftBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_L)
    (rightPlan :
      RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_R)
    (t : In₂ -> Out₂)
    (hcand : ∀ c, (lpCand.label c).1 = t)
    (hopen : ∀ c, (lpOpen.label c).1 = t)
    (c_L c_L' : C_L) (entry : A.State × A.State) :
    TwoBlindTraceMeasurable (A := A) lpCand c_L
      (foldChain lpOpen rightPlan) (Sum.inl c_L') entry :=
  foldChain_twoBlindTraceMeasurable_agree lpCand lpOpen rightPlan c_L c_L' entry
    (fun w => by rw [hcand, hopen])

end DetParityAutomaton

end DistributedSynthesis
