/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmCandidateSummaries
import DistributedSynthesis.Formalizations.Theorem.ThmEntryIndexedReproducibility
import DistributedSynthesis.Formalizations.Theorem.ThmPlanFolding

/-!
# The play correspondence of the candidate summaries

This file proves that the pasted strategy of a committed plan family
plays exactly the arena word: on the no-direct fragment,
`execution (journalStrategy plans) env = arenaWord plans env`
(step H4c of the readback-upgrade plan).

The proof is a joint induction maintaining that each process's summary
core tracks the arena fold position (`OneCoreTracks`, `TwoCoreTracks`):
at a boundary the core is the exact boundary or an ambiguous candidate
pair whose boundary candidate is true; inside the own-orientation block
the ambiguous pair's block candidate is true; inside the opposite block
the core is the committed plan with its own-input-driven control.  The
one-bit fringe resolves soundly by shape correlation: the partner's
core is subordinate exactly when the fold is inside the block the
partner sends into, so at receive rounds the partner's shape selects
the true candidate, and at `noRecv` rounds the no-direct discipline
does.  The candidate successors of `ThmCandidateSummaries.lean` mirror
the arena target payloads verbatim, so every step preserves tracking
definitionally.

Combining with the boundary-game soundness endpoint
`accepts_arenaWord_of_winning` yields step H4d, the fragment soundness
of the journal readback: a winning positional Even strategy of the
boundary game pastes to a distributed strategy, the readback of the
candidate summary automaton of its committed plans, all of whose
no-direct executions are accepted
(`accepts_execution_journalStrategy_of_winning`).
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
Process one's core tracks the arena position: at a boundary it is the
exact boundary or an ambiguous pair whose boundary candidate is true;
inside a left block the ambiguous pair's block candidate is true;
inside a right block it is the committed plan with its control.
-/
def OneCoreTracks
    (core : OneCore (In₁ := In₁) A C_L C_R C_V)
    (position : BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V) :
    Prop :=
  match position with
  | Sum.inl boundary =>
      core = Sum.inr (Sum.inl boundary) ∨
        (∃ ldata, core = Sum.inl (ldata, boundary)) ∨
        (∃ revData, core =
          Sum.inr (Sum.inr (Sum.inr (Sum.inl (revData, boundary)))))
  | Sum.inr (Sum.inl _) => False
  | Sum.inr (Sum.inr (Sum.inl ldata)) =>
      ∃ boundary, core = Sum.inl (ldata, boundary)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl rdata))) =>
      core = Sum.inr (Sum.inr (Sum.inl (rdata.1, rdata.2.2.1))) ∨
        ∃ eside, core =
          Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
            ((rdata.1, rdata.2.2.1), eside)))))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (chain, control, entry, state, minState))))) =>
      ∃ boundary, core =
        Sum.inr (Sum.inr (Sum.inr (Sum.inl
          ((chain, control, (entry, state, minState)), boundary))))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (chain, control, entry, _, _))))) =>
      ∃ rplan rc frozen,
        core =
          Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
            ((rplan, rc), (chain, control, frozen))))) ) ∧
          OneBlindTraceMeasurable rplan rc chain control entry

/-- Process two's core tracks the arena position: the mirror. -/
def TwoCoreTracks
    (core : TwoCore (In₁ := In₁) A C_L C_R C_V)
    (position : BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V) :
    Prop :=
  match position with
  | Sum.inl boundary =>
      core = Sum.inr (Sum.inl boundary) ∨
        (∃ rdata, core = Sum.inl (rdata, boundary)) ∨
        (∃ revData, core =
          Sum.inr (Sum.inr (Sum.inr (Sum.inl (revData, boundary)))))
  | Sum.inr (Sum.inl _) => False
  | Sum.inr (Sum.inr (Sum.inl ldata)) =>
      core = Sum.inr (Sum.inr (Sum.inl (ldata.1, ldata.2.2.1))) ∨
        ∃ eside, core =
          Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
            ((ldata.1, ldata.2.2.1), eside)))))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl rdata))) =>
      ∃ boundary, core = Sum.inl (rdata, boundary)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (chain, control, entry, _, _))))) =>
      ∃ lplan lc frozen,
        core =
          Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
            ((lplan, lc), (chain, control, frozen))))) ) ∧
          TwoBlindTraceMeasurable lplan lc chain control entry
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (chain, control, entry, state, minState))))) =>
      ∃ boundary, core =
        Sum.inr (Sum.inr (Sum.inr (Sum.inl
          ((chain, control, (entry, state, minState)), boundary))))

section Correspondence

variable
  [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
  [DecidableEq In₁] [DecidableEq In₂] [DecidableEq A.State]
  [Fintype C_L] [DecidableEq C_L] [Fintype C_R] [DecidableEq C_R]
  [Fintype C_V] [DecidableEq C_V]
  [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

/-- The summary of process one after `n` rounds of the readback play. -/
def oneSummaryAt (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    Out₁ × OneCore (In₁ := In₁) A C_L C_R C_V :=
  (journalSummaries (In₁ := In₁) plans).read
    (currentView Proc.one (executionPrefix (journalStrategy plans) env n))

/-- The summary of process two after `n` rounds of the readback play. -/
def twoSummaryAt (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    Out₂ × TwoCore (In₁ := In₁) A C_L C_R C_V :=
  (journalSummaries (In₁ := In₁) plans).read
    (currentView Proc.two (executionPrefix (journalStrategy plans) env n))

/--
The emitted round of the readback play: the round's outputs are the
stored outputs of the freshly advanced summaries.
-/
theorem execution_journal_apply
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    execution (journalStrategy plans) env n =
      { inputOne := (env n).inputOne
        inputTwo := (env n).inputTwo
        graph := (env n).graph
        outputOne := (oneSummaryAt plans env (n + 1)).1
        outputTwo := (twoSummaryAt plans env (n + 1)).1 } := by
  rw [execution_apply]
  unfold oneSummaryAt twoSummaryAt
  simp only [currentView_executionPrefix_succ]
  rfl

theorem oneSummaryAt_succ_left
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hgraph : (env n).graph = Graph.left) :
    oneSummaryAt plans env (n + 1) =
      oneRecvStep (A := A) plans (oneSummaryAt plans env n).2
        ((env n).inputOne, (env n).inputTwo)
        (twoSummaryAt plans env n).2 := by
  have hview :
      currentView Proc.one
          (executionPrefix (journalStrategy plans) env (n + 1)) =
        View.recv
          (currentView Proc.one
            (executionPrefix (journalStrategy plans) env n))
          (PSum.inl (env n).inputOne)
          (currentView Proc.two
            (executionPrefix (journalStrategy plans) env n))
          (PSum.inr (env n).inputTwo) := by
    rw [currentView_executionPrefix_succ]
    simp [nextView, advanceViewsWithEnvironment, hgraph, currentView]
  unfold oneSummaryAt twoSummaryAt
  rw [hview]
  rfl

theorem oneSummaryAt_succ_both
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hgraph : (env n).graph = Graph.both) :
    oneSummaryAt plans env (n + 1) =
      oneRecvStep (A := A) plans (oneSummaryAt plans env n).2
        ((env n).inputOne, (env n).inputTwo)
        (twoSummaryAt plans env n).2 := by
  have hview :
      currentView Proc.one
          (executionPrefix (journalStrategy plans) env (n + 1)) =
        View.recv
          (currentView Proc.one
            (executionPrefix (journalStrategy plans) env n))
          (PSum.inl (env n).inputOne)
          (currentView Proc.two
            (executionPrefix (journalStrategy plans) env n))
          (PSum.inr (env n).inputTwo) := by
    rw [currentView_executionPrefix_succ]
    simp [nextView, advanceViewsWithEnvironment, hgraph, currentView]
  unfold oneSummaryAt twoSummaryAt
  rw [hview]
  rfl

theorem oneSummaryAt_succ_right
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hgraph : (env n).graph = Graph.right) :
    oneSummaryAt plans env (n + 1) =
      oneNoRecvStep (A := A) plans (oneSummaryAt plans env n).2
        (env n).inputOne := by
  have hview :
      currentView Proc.one
          (executionPrefix (journalStrategy plans) env (n + 1)) =
        View.noRecv
          (currentView Proc.one
            (executionPrefix (journalStrategy plans) env n))
          (PSum.inl (env n).inputOne) := by
    rw [currentView_executionPrefix_succ]
    simp [nextView, advanceViewsWithEnvironment, hgraph, currentView]
  unfold oneSummaryAt
  rw [hview]
  rfl

theorem twoSummaryAt_succ_left
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hgraph : (env n).graph = Graph.left) :
    twoSummaryAt plans env (n + 1) =
      twoNoRecvStep (A := A) plans (twoSummaryAt plans env n).2
        (env n).inputTwo := by
  have hview :
      currentView Proc.two
          (executionPrefix (journalStrategy plans) env (n + 1)) =
        View.noRecv
          (currentView Proc.two
            (executionPrefix (journalStrategy plans) env n))
          (PSum.inr (env n).inputTwo) := by
    rw [currentView_executionPrefix_succ]
    simp [nextView, advanceViewsWithEnvironment, hgraph, currentView]
  unfold twoSummaryAt
  rw [hview]
  rfl

theorem twoSummaryAt_succ_both
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hgraph : (env n).graph = Graph.both) :
    twoSummaryAt plans env (n + 1) =
      twoRecvStep (A := A) plans (twoSummaryAt plans env n).2
        ((env n).inputOne, (env n).inputTwo)
        (oneSummaryAt plans env n).2 := by
  have hview :
      currentView Proc.two
          (executionPrefix (journalStrategy plans) env (n + 1)) =
        View.recv
          (currentView Proc.two
            (executionPrefix (journalStrategy plans) env n))
          (PSum.inr (env n).inputTwo)
          (currentView Proc.one
            (executionPrefix (journalStrategy plans) env n))
          (PSum.inl (env n).inputOne) := by
    rw [currentView_executionPrefix_succ]
    simp [nextView, advanceViewsWithEnvironment, hgraph, currentView]
  unfold twoSummaryAt oneSummaryAt
  rw [hview]
  rfl

theorem twoSummaryAt_succ_right
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hgraph : (env n).graph = Graph.right) :
    twoSummaryAt plans env (n + 1) =
      twoRecvStep (A := A) plans (twoSummaryAt plans env n).2
        ((env n).inputOne, (env n).inputTwo)
        (oneSummaryAt plans env n).2 := by
  have hview :
      currentView Proc.two
          (executionPrefix (journalStrategy plans) env (n + 1)) =
        View.recv
          (currentView Proc.two
            (executionPrefix (journalStrategy plans) env n))
          (PSum.inr (env n).inputTwo)
          (currentView Proc.one
            (executionPrefix (journalStrategy plans) env n))
          (PSum.inl (env n).inputOne) := by
    rw [currentView_executionPrefix_succ]
    simp [nextView, advanceViewsWithEnvironment, hgraph, currentView]
  unfold twoSummaryAt oneSummaryAt
  rw [hview]
  rfl

/-- The arena post-reversal entry thread when a within-left block reverses on a
right round: the `(next, minState')` component of `leftReverseTarget`. -/
def leftReverseEntry
    (plan :
      LeftBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) A C_L)
    (control : C_L) (state minState : A.State) (move : In₁ × In₂) :
    A.State × A.State :=
  let next :=
    A.step state
      (rightRoundRecord (move.2, move.1)
        (plan.rev control (state, minState) move.1)
        (plan.close control (state, minState) move))
  (next, A.minPriorityState minState next)

/-- The arena post-reversal entry thread when a within-right block reverses on a
left round: the `(next, minState')` component of `rightReverseTarget`. -/
def rightReverseEntry
    (plan :
      RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) A C_R)
    (control : C_R) (state minState : A.State) (move : In₂ × In₁) :
    A.State × A.State :=
  let next :=
    A.step state
      (leftRoundRecord (move.2, move.1)
        (plan.close control (state, minState) move)
        (plan.rev control (state, minState) move.1))
  (next, A.minPriorityState minState next)

/-- The arena post-re-reversal entry thread when a reversed-right block reverses
again on a left round: the `(next, minState')` component of
`revRightReverseTarget`. -/
def revRightReverseEntry
    (chain :
      ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_L C_R C_V)
    (control : C_V) (entry : A.State × A.State) (state minState : A.State)
    (move : In₁ × In₂) : A.State × A.State :=
  let staged := chain.labelR control
  let next :=
    A.step state
      (leftRoundRecord move (staged.1 (entry, state, minState) move)
        (staged.2.2.1 (entry, state, minState) move.2))
  (next, A.minPriorityState minState next)

/-- The arena post-re-reversal entry thread when a reversed-left block reverses
again on a right round: the `(next, minState')` component of
`revLeftReverseTarget`. -/
def revLeftReverseEntry
    (chain :
      ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_L C_R C_V)
    (control : C_V) (entry : A.State × A.State) (state minState : A.State)
    (move : In₁ × In₂) : A.State × A.State :=
  let staged := chain.labelL control
  let next :=
    A.step state
      (rightRoundRecord (move.2, move.1)
        (staged.2.1 (entry, state, minState) move.1)
        (staged.2.2.2 (entry, state, minState) move))
  (next, A.minPriorityState minState next)

/-- A chain control is a **right-reset control** when it is the result of a
process-one (`Sum.inr`) chain step.  Every reversed-*right* boundary-game position
carries such a control (all three producers -- `leftReverseTarget`,
`revLeftReverseTarget`, `revRightContinueTarget` -- set it to
`chain.step _ (Sum.inr _)`), and for the folded chain a subsequent re-reversal
step on a `Sum.inl` round then deterministically restarts the opposite-orientation
block from its initial control (paper `cor:folddischarge`: "restarting the other
block plan from its initial control").  This is the abstract, chain-only expression
of the reset-parity a re-reversal always enjoys. -/
def RightResetControl
    (chain :
      ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) A C_L C_R C_V)
    (control : C_V) : Prop :=
  ∃ (pre : C_V) (priorMove : In₁), control = chain.step pre (Sum.inr priorMove)

/-- A chain control is a **left-reset control** when it is the result of a
process-two (`Sum.inl`) chain step: the orientation mirror of `RightResetControl`,
carried by every reversed-*left* position. -/
def LeftResetControl
    (chain :
      ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) A C_L C_R C_V)
    (control : C_V) : Prop :=
  ∃ (pre : C_V) (priorMove : In₂), control = chain.step pre (Sum.inl priorMove)

/--
The entry-indexed measurability certificate that replaces `hnodirect` in the
full-model journal readback.  It is the boundary-game statement of
`def:entrythread`'s entry-indexed commitment: the blind side, unable to observe
the fringe bit `b_old`, commits plans on which the two outputs it cannot
distinguish coincide.  `blind` is the reversal-entry agreement
(`prop:entrysound`); `leftTrace`/`rightTrace` are the block-long trace
agreements at the tier's post-reversal controls and the arena's post-reversal
entry, the invariant the reversed-tier tracking carries and `.step` preserves.
The reversed-block chain is not free: it is the one committed at the block's
*opening* boundary (`(plans openBoundary).2.2`), whereas the block plan whose
blind output it must reproduce is committed at the *successor* boundary
(`candBoundary`).  This cross-boundary pairing (paper `cor:blindcrossreading`)
is what forces the folded commitment to be one global blind table
(`rem:globalblindtable`); the opening boundary is recovered at each consumption
site from `ChainCommittedAt`.  The informed side needs no hypothesis
(`lem:reversaltwobits`).
-/
structure ReversalMeasurable
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V) : Prop where
  blind : PlanBlindMeasurable plans
  leftTrace :
    ∀ (plan :
        LeftBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
          A C_L)
      (control : C_L) (state minState : A.State)
      (candBoundary openBoundary : A.State × A.State) (move : In₁ × In₂),
      OneBlindTraceMeasurable ((plans candBoundary).2.1)
        (((plans candBoundary).2.1).step ((plans candBoundary).2.1).init move.1)
        ((plans openBoundary).2.2)
        (((plans openBoundary).2.2).step
          (((plans openBoundary).2.2).enterL control) (Sum.inr move.1))
        (leftReverseEntry plan control state minState move)
  rightTrace :
    ∀ (plan :
        RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
          A C_R)
      (control : C_R) (state minState : A.State)
      (candBoundary openBoundary : A.State × A.State) (move : In₂ × In₁),
      TwoBlindTraceMeasurable ((plans candBoundary).1)
        (((plans candBoundary).1).step ((plans candBoundary).1).init move.1)
        ((plans openBoundary).2.2)
        (((plans openBoundary).2.2).step
          (((plans openBoundary).2.2).enterR control) (Sum.inl move.1))
        (rightReverseEntry plan control state minState move)
  rightReReverseBlind :
    ∀ (control : C_V) (entry : A.State × A.State) (state minState : A.State)
      (boundary openBoundary : A.State × A.State) (i : In₂),
      (((plans boundary).1).label ((plans boundary).1).init).1 i =
        (((plans openBoundary).2.2).labelR control).2.2.1 (entry, state, minState) i
  rightReReverseTrace :
    ∀ (control : C_V) (entry : A.State × A.State) (state minState : A.State)
      (boundary openBoundary : A.State × A.State) (move : In₁ × In₂),
      RightResetControl ((plans openBoundary).2.2) control →
      TwoBlindTraceMeasurable ((plans boundary).1)
        (((plans boundary).1).step ((plans boundary).1).init move.2)
        ((plans openBoundary).2.2)
        (((plans openBoundary).2.2).step control (Sum.inl move.2))
        (revRightReverseEntry ((plans openBoundary).2.2) control entry state
          minState move)
  leftReReverseBlind :
    ∀ (control : C_V) (entry : A.State × A.State) (state minState : A.State)
      (boundary openBoundary : A.State × A.State) (i : In₁),
      (((plans boundary).2.1).label ((plans boundary).2.1).init).1 i =
        (((plans openBoundary).2.2).labelL control).2.1 (entry, state, minState) i
  leftReReverseTrace :
    ∀ (control : C_V) (entry : A.State × A.State) (state minState : A.State)
      (boundary openBoundary : A.State × A.State) (move : In₁ × In₂),
      LeftResetControl ((plans openBoundary).2.2) control →
      OneBlindTraceMeasurable ((plans boundary).2.1)
        (((plans boundary).2.1).step ((plans boundary).2.1).init move.1)
        ((plans openBoundary).2.2)
        (((plans openBoundary).2.2).step control (Sum.inr move.1))
        (revLeftReverseEntry ((plans openBoundary).2.2) control entry state
          minState move)

/-! ### The global fold discharges the trace obligations by construction

Read at the global fold `globalFold t_L t_R P`, the restated `leftTrace` and
`rightTrace` are consequences of the shared blind tables, with no hypothesis on
`P`.  The successor boundary's block plan and the opening boundary's committed
chain both emit the one table (`t_R` on process one, `t_L` on process two) along
every own-input word, so the block-long agreement of paper
`cor:blindcrossreading` holds definitionally.  These two lemmas are Part 1 of the
discharge of `EntryIndexedCertificate`; realization of a winning `(t_L, t_R)` is
Part 2 (`prop:starcomplete`). -/

omit [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁]
    [DecidableEq In₂] [DecidableEq A.State] [Fintype C_L] [DecidableEq C_L] [Fintype C_R]
    [DecidableEq C_R] [Fintype C_V] [DecidableEq C_V] [Inhabited In₁] [Inhabited In₂]
    [Inhabited Out₁] [Inhabited Out₂] in
/-- The global fold satisfies the restated `leftTrace`: the successor boundary's
right plan and the opening boundary's folded chain both read `t_R`. -/
theorem globalFold_leftTrace
    (t_L : In₂ -> Out₂) (t_R : In₁ -> Out₁)
    (P : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (plan :
      LeftBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_L)
    (control : C_L) (state minState : A.State)
    (candBoundary openBoundary : A.State × A.State) (move : In₁ × In₂) :
    OneBlindTraceMeasurable ((globalFold t_L t_R P candBoundary).2.1)
      (((globalFold t_L t_R P candBoundary).2.1).step
        ((globalFold t_L t_R P candBoundary).2.1).init move.1)
      ((globalFold t_L t_R P openBoundary).2.2)
      (((globalFold t_L t_R P openBoundary).2.2).step
        (((globalFold t_L t_R P openBoundary).2.2).enterL control) (Sum.inr move.1))
      (leftReverseEntry plan control state minState move) :=
  foldChain_oneBlindTraceMeasurable_shared
    (overwriteLeftBlind t_L t_R (P openBoundary).1)
    (overwriteRightBlind t_R t_L (P candBoundary).2.1)
    (overwriteRightBlind t_R t_L (P openBoundary).2.1) t_R (fun _ => rfl) (fun _ => rfl)
    ((overwriteRightBlind t_R t_L (P candBoundary).2.1).step
      (overwriteRightBlind t_R t_L (P candBoundary).2.1).init move.1)
    ((overwriteRightBlind t_R t_L (P openBoundary).2.1).step
      (overwriteRightBlind t_R t_L (P openBoundary).2.1).init move.1)
    (leftReverseEntry plan control state minState move)

omit [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁]
    [DecidableEq In₂] [DecidableEq A.State] [Fintype C_L] [DecidableEq C_L] [Fintype C_R]
    [DecidableEq C_R] [Fintype C_V] [DecidableEq C_V] [Inhabited In₁] [Inhabited In₂]
    [Inhabited Out₁] [Inhabited Out₂] in
/-- The global fold satisfies the restated `rightTrace`: the mirror of
`globalFold_leftTrace`. -/
theorem globalFold_rightTrace
    (t_L : In₂ -> Out₂) (t_R : In₁ -> Out₁)
    (P : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (plan :
      RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_R)
    (control : C_R) (state minState : A.State)
    (candBoundary openBoundary : A.State × A.State) (move : In₂ × In₁) :
    TwoBlindTraceMeasurable ((globalFold t_L t_R P candBoundary).1)
      (((globalFold t_L t_R P candBoundary).1).step
        ((globalFold t_L t_R P candBoundary).1).init move.1)
      ((globalFold t_L t_R P openBoundary).2.2)
      (((globalFold t_L t_R P openBoundary).2.2).step
        (((globalFold t_L t_R P openBoundary).2.2).enterR control) (Sum.inl move.1))
      (rightReverseEntry plan control state minState move) :=
  foldChain_twoBlindTraceMeasurable_shared
    (overwriteLeftBlind t_L t_R (P candBoundary).1)
    (overwriteLeftBlind t_L t_R (P openBoundary).1)
    (overwriteRightBlind t_R t_L (P openBoundary).2.1) t_L (fun _ => rfl) (fun _ => rfl)
    ((overwriteLeftBlind t_L t_R (P candBoundary).1).step
      (overwriteLeftBlind t_L t_R (P candBoundary).1).init move.1)
    ((overwriteLeftBlind t_L t_R (P openBoundary).1).step
      (overwriteLeftBlind t_L t_R (P openBoundary).1).init move.1)
    (rightReverseEntry plan control state minState move)

/-! ### The global fold discharges the re-reversal obligations by construction

At a re-reversal the folded chain switches orientation, restarting the other
plan from `init`.  Its blind slot still reads the shared table, so the block-long
agreement holds for *either* prior control (paper `cor:blindcrossreading`); the
proofs case on the chain control and reduce to the shared engines (trace) or
to `rfl` (the immediate blind agreement). -/

section
omit [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁]
    [DecidableEq In₂] [DecidableEq A.State] [Fintype C_L] [DecidableEq C_L] [Fintype C_R]
    [DecidableEq C_R] [Fintype C_V] [DecidableEq C_V] [Inhabited In₁] [Inhabited In₂]
    [Inhabited Out₁] [Inhabited Out₂]

/-- The global fold satisfies `rightReReverseBlind`: the left plan's blind init
value and the folded chain's re-reversed left slot are both `t_L`. -/
theorem globalFold_rightReReverseBlind
    (t_L : In₂ -> Out₂) (t_R : In₁ -> Out₁)
    (P : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (control : C_L ⊕ C_R) (entry : A.State × A.State) (state minState : A.State)
    (boundary openBoundary : A.State × A.State) (i : In₂) :
    (((globalFold t_L t_R P boundary).1).label
        ((globalFold t_L t_R P boundary).1).init).1 i =
      (((globalFold t_L t_R P openBoundary).2.2).labelR control).2.2.1
        (entry, state, minState) i := by
  cases control <;> rfl

/-- The global fold satisfies `leftReReverseBlind`: the mirror of
`globalFold_rightReReverseBlind`. -/
theorem globalFold_leftReReverseBlind
    (t_L : In₂ -> Out₂) (t_R : In₁ -> Out₁)
    (P : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (control : C_L ⊕ C_R) (entry : A.State × A.State) (state minState : A.State)
    (boundary openBoundary : A.State × A.State) (i : In₁) :
    (((globalFold t_L t_R P boundary).2.1).label
        ((globalFold t_L t_R P boundary).2.1).init).1 i =
      (((globalFold t_L t_R P openBoundary).2.2).labelL control).2.1
        (entry, state, minState) i := by
  cases control <;> rfl

/-- The global fold satisfies `rightReReverseTrace`: the re-reversed left slot of
the folded chain reads `t_L` for either prior control. -/
theorem globalFold_rightReReverseTrace
    (t_L : In₂ -> Out₂) (t_R : In₁ -> Out₁)
    (P : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (control : C_L ⊕ C_R) (entry : A.State × A.State) (state minState : A.State)
    (boundary openBoundary : A.State × A.State) (move : In₁ × In₂)
    (_hreset :
      RightResetControl ((globalFold t_L t_R P openBoundary).2.2) control) :
    TwoBlindTraceMeasurable ((globalFold t_L t_R P boundary).1)
      (((globalFold t_L t_R P boundary).1).step
        ((globalFold t_L t_R P boundary).1).init move.2)
      ((globalFold t_L t_R P openBoundary).2.2)
      (((globalFold t_L t_R P openBoundary).2.2).step control (Sum.inl move.2))
      (revRightReverseEntry ((globalFold t_L t_R P openBoundary).2.2) control
        entry state minState move) := by
  cases control <;>
    exact foldChain_twoBlindTraceMeasurable_shared
      (overwriteLeftBlind t_L t_R (P boundary).1)
      (overwriteLeftBlind t_L t_R (P openBoundary).1)
      (overwriteRightBlind t_R t_L (P openBoundary).2.1) t_L (fun _ => rfl)
      (fun _ => rfl) _ _ _

/-- The global fold satisfies `leftReReverseTrace`: the mirror of
`globalFold_rightReReverseTrace`. -/
theorem globalFold_leftReReverseTrace
    (t_L : In₂ -> Out₂) (t_R : In₁ -> Out₁)
    (P : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (control : C_L ⊕ C_R) (entry : A.State × A.State) (state minState : A.State)
    (boundary openBoundary : A.State × A.State) (move : In₁ × In₂)
    (_hreset :
      LeftResetControl ((globalFold t_L t_R P openBoundary).2.2) control) :
    OneBlindTraceMeasurable ((globalFold t_L t_R P boundary).2.1)
      (((globalFold t_L t_R P boundary).2.1).step
        ((globalFold t_L t_R P boundary).2.1).init move.1)
      ((globalFold t_L t_R P openBoundary).2.2)
      (((globalFold t_L t_R P openBoundary).2.2).step control (Sum.inr move.1))
      (revLeftReverseEntry ((globalFold t_L t_R P openBoundary).2.2) control
        entry state minState move) := by
  cases control <;>
    exact foldChain_oneBlindTraceMeasurable_shared
      (overwriteLeftBlind t_L t_R (P openBoundary).1)
      (overwriteRightBlind t_R t_L (P boundary).2.1)
      (overwriteRightBlind t_R t_L (P openBoundary).2.1) t_R (fun _ => rfl)
      (fun _ => rfl) _ _ _

/-- The global fold satisfies the blind commitment by construction: since the fold
overwrites the reversal slot `.rev` and the boundary-opening slot `label .1` by the
same table (`t_R` on process one, `t_L` on process two), the reversal output equals
the boundary-opening output at every candidate pair.  This is the
reversal-opening commitment of `cor:folddischarge`, here made an identity by the
fold; the substantive content it displaces is realization
(`prop:starcomplete`): whether such a folded pair `(t_L, t_R)` is played by a
winning strategy. -/
theorem globalFold_blind
    (t_L : In₂ -> Out₂) (t_R : In₁ -> Out₁)
    (P : PlanFamily (In₁ := In₁) A C_L C_R C_V) :
    PlanBlindMeasurable (globalFold t_L t_R P) :=
  ⟨fun _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => rfl⟩

/-- **The global fold is reversal-measurable, unconditionally.** All six
trace/re-reversal obligations hold by construction (the shared subordinate tables),
and the blind commitment holds by construction too (the shared reversal tables,
`globalFold_blind`).  The entry-indexed measurability certificate is thus satisfied
by an explicit family for *every* choice of blind tables `(t_L, t_R)`; what is *not*
supplied here is realization -- that some `(t_L, t_R)` is played by a winning
strategy -- which is the separate content of `prop:starcomplete`. -/
theorem globalFold_reversalMeasurable
    (t_L : In₂ -> Out₂) (t_R : In₁ -> Out₁)
    (P : PlanFamily (In₁ := In₁) A C_L C_R C_V) :
    ReversalMeasurable (globalFold t_L t_R P) where
  blind := globalFold_blind t_L t_R P
  leftTrace := globalFold_leftTrace t_L t_R P
  rightTrace := globalFold_rightTrace t_L t_R P
  rightReReverseBlind := globalFold_rightReReverseBlind t_L t_R P
  rightReReverseTrace := globalFold_rightReReverseTrace t_L t_R P
  leftReReverseBlind := globalFold_leftReReverseBlind t_L t_R P
  leftReReverseTrace := globalFold_leftReReverseTrace t_L t_R P

end

/-! ### The control-dependent fold `foldθ` discharges `leftTrace` from word-agreement

Unlike `globalFold`, the realizing `foldθ` reads a control-dependent blind function
`bRr`, so cross-boundary agreement is not `rfl`; it is the word-indexed agreement of
`foldChain_oneBlindTraceMeasurable_agree`.  The hypothesis `hagree` is the exact Lean
form of paper `cor:blindcrossreading`: the successor boundary's right plan and the
opening boundary's right plan emit the same blind value at every own-input word,
because both are the shared `\bar\theta`-monitor `bRr` run from a common entry.  This
lemma isolates that residual; the `\bar\theta`-monitor construction discharging it is
the next step. -/

omit [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁]
    [DecidableEq In₂] [DecidableEq A.State] [Fintype C_L] [DecidableEq C_L] [Fintype C_R]
    [DecidableEq C_R] [Fintype C_V] [DecidableEq C_V] [Inhabited In₁] [Inhabited In₂]
    [Inhabited Out₁] [Inhabited Out₂] in
/-- The control-dependent fold satisfies the restated `leftTrace` from the
word-indexed agreement `hagree` of the shared blind function `bRr` across the
successor and opening boundaries (paper `cor:blindcrossreading`). -/
theorem foldθ_leftTrace
    (bLl : C_L -> In₂ -> Out₂) (bRl : C_L -> In₁ -> Out₁)
    (bRr : C_R -> In₁ -> Out₁) (bLr : C_R -> In₂ -> Out₂)
    (P : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (plan :
      LeftBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_L)
    (control : C_L) (state minState : A.State)
    (candBoundary openBoundary : A.State × A.State) (move : In₁ × In₂)
    (hagree :
      ∀ w : List In₁,
        bRr (rightSubordinateControlAfter
          (overwriteRightBlindF bRr bLr (P candBoundary).2.1)
          ((overwriteRightBlindF bRr bLr (P candBoundary).2.1).step
            (overwriteRightBlindF bRr bLr (P candBoundary).2.1).init move.1) w) =
          bRr (rightSubordinateControlAfter
            (overwriteRightBlindF bRr bLr (P openBoundary).2.1)
            ((overwriteRightBlindF bRr bLr (P openBoundary).2.1).step
              (overwriteRightBlindF bRr bLr (P openBoundary).2.1).init move.1) w)) :
    OneBlindTraceMeasurable ((foldθ bLl bRl bRr bLr P candBoundary).2.1)
      (((foldθ bLl bRl bRr bLr P candBoundary).2.1).step
        ((foldθ bLl bRl bRr bLr P candBoundary).2.1).init move.1)
      ((foldθ bLl bRl bRr bLr P openBoundary).2.2)
      (((foldθ bLl bRl bRr bLr P openBoundary).2.2).step
        (((foldθ bLl bRl bRr bLr P openBoundary).2.2).enterL control) (Sum.inr move.1))
      (leftReverseEntry plan control state minState move) :=
  foldChain_oneBlindTraceMeasurable_agree
    (overwriteLeftBlindF bLl bRl (P openBoundary).1)
    (overwriteRightBlindF bRr bLr (P candBoundary).2.1)
    (overwriteRightBlindF bRr bLr (P openBoundary).2.1)
    ((overwriteRightBlindF bRr bLr (P candBoundary).2.1).step
      (overwriteRightBlindF bRr bLr (P candBoundary).2.1).init move.1)
    ((overwriteRightBlindF bRr bLr (P openBoundary).2.1).step
      (overwriteRightBlindF bRr bLr (P openBoundary).2.1).init move.1)
    (leftReverseEntry plan control state minState move) hagree

omit [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁]
    [DecidableEq In₂] [DecidableEq A.State] [Fintype C_L] [DecidableEq C_L] [Fintype C_R]
    [DecidableEq C_R] [Fintype C_V] [DecidableEq C_V] [Inhabited In₁] [Inhabited In₂]
    [Inhabited Out₁] [Inhabited Out₂] in
/-- The control-dependent fold satisfies the restated `rightTrace` from the
word-indexed agreement `hagree` of the shared blind function `bLl` across the
successor and opening boundaries: the mirror of `foldθ_leftTrace`. -/
theorem foldθ_rightTrace
    (bLl : C_L -> In₂ -> Out₂) (bRl : C_L -> In₁ -> Out₁)
    (bRr : C_R -> In₁ -> Out₁) (bLr : C_R -> In₂ -> Out₂)
    (P : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (plan :
      RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_R)
    (control : C_R) (state minState : A.State)
    (candBoundary openBoundary : A.State × A.State) (move : In₂ × In₁)
    (hagree :
      ∀ w : List In₂,
        bLl (leftSubordinateControlAfter
          (overwriteLeftBlindF bLl bRl (P candBoundary).1)
          ((overwriteLeftBlindF bLl bRl (P candBoundary).1).step
            (overwriteLeftBlindF bLl bRl (P candBoundary).1).init move.1) w) =
          bLl (leftSubordinateControlAfter
            (overwriteLeftBlindF bLl bRl (P openBoundary).1)
            ((overwriteLeftBlindF bLl bRl (P openBoundary).1).step
              (overwriteLeftBlindF bLl bRl (P openBoundary).1).init move.1) w)) :
    TwoBlindTraceMeasurable ((foldθ bLl bRl bRr bLr P candBoundary).1)
      (((foldθ bLl bRl bRr bLr P candBoundary).1).step
        ((foldθ bLl bRl bRr bLr P candBoundary).1).init move.1)
      ((foldθ bLl bRl bRr bLr P openBoundary).2.2)
      (((foldθ bLl bRl bRr bLr P openBoundary).2.2).step
        (((foldθ bLl bRl bRr bLr P openBoundary).2.2).enterR control) (Sum.inl move.1))
      (rightReverseEntry plan control state minState move) :=
  foldChain_twoBlindTraceMeasurable_agree
    (overwriteLeftBlindF bLl bRl (P candBoundary).1)
    (overwriteLeftBlindF bLl bRl (P openBoundary).1)
    (overwriteRightBlindF bRr bLr (P openBoundary).2.1)
    ((overwriteLeftBlindF bLl bRl (P candBoundary).1).step
      (overwriteLeftBlindF bLl bRl (P candBoundary).1).init move.1)
    ((overwriteLeftBlindF bLl bRl (P openBoundary).1).step
      (overwriteLeftBlindF bLl bRl (P openBoundary).1).init move.1)
    (rightReverseEntry plan control state minState move) hagree

/-! ### The control-dependent fold discharges the re-reversal obligations

The re-reversal fields for `foldθ` mirror the trace fields but at a re-reversal:
the chain switches orientation, restarting the opposite plan.  The blind fields
reduce (by the `overwrite*BlindF` identities) to a single value agreement between
the boundary's plan-init blind and the folded chain's re-reversed slot; the trace
fields to the word-indexed `_agree`, cased on the prior chain control (each branch
reaches a different opening control, so the agreement is stated over the reached
control).  Every hypothesis is a `cor:blindcrossreading` instance the shared
`\bar\theta`-monitor discharges. -/

section
omit [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁]
    [DecidableEq In₂] [DecidableEq A.State] [Fintype C_L] [DecidableEq C_L] [Fintype C_R]
    [DecidableEq C_R] [Fintype C_V] [DecidableEq C_V] [Inhabited In₁] [Inhabited In₂]
    [Inhabited Out₁] [Inhabited Out₂]

/-- The control-dependent fold satisfies `rightReReverseBlind` from the value
agreement of `bLl` between the boundary's left-plan init and the folded chain's
re-reversed left slot. -/
theorem foldθ_rightReReverseBlind
    (bLl : C_L -> In₂ -> Out₂) (bRl : C_L -> In₁ -> Out₁)
    (bRr : C_R -> In₁ -> Out₁) (bLr : C_R -> In₂ -> Out₂)
    (P : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (control : C_L ⊕ C_R) (entry : A.State × A.State) (state minState : A.State)
    (boundary openBoundary : A.State × A.State) (i : In₂)
    (hagree :
      bLl ((P boundary).1.init) i =
        (((foldθ bLl bRl bRr bLr P openBoundary).2.2).labelR control).2.2.1
          (entry, state, minState) i) :
    (((foldθ bLl bRl bRr bLr P boundary).1).label
        ((foldθ bLl bRl bRr bLr P boundary).1).init).1 i =
      (((foldθ bLl bRl bRr bLr P openBoundary).2.2).labelR control).2.2.1
        (entry, state, minState) i :=
  hagree

/-- The control-dependent fold satisfies `leftReReverseBlind`: the mirror, on
`bRr`. -/
theorem foldθ_leftReReverseBlind
    (bLl : C_L -> In₂ -> Out₂) (bRl : C_L -> In₁ -> Out₁)
    (bRr : C_R -> In₁ -> Out₁) (bLr : C_R -> In₂ -> Out₂)
    (P : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (control : C_L ⊕ C_R) (entry : A.State × A.State) (state minState : A.State)
    (boundary openBoundary : A.State × A.State) (i : In₁)
    (hagree :
      bRr ((P boundary).2.1.init) i =
        (((foldθ bLl bRl bRr bLr P openBoundary).2.2).labelL control).2.1
          (entry, state, minState) i) :
    (((foldθ bLl bRl bRr bLr P boundary).2.1).label
        ((foldθ bLl bRl bRr bLr P boundary).2.1).init).1 i =
      (((foldθ bLl bRl bRr bLr P openBoundary).2.2).labelL control).2.1
        (entry, state, minState) i :=
  hagree

/-- The control-dependent fold satisfies `rightReReverseTrace` from the word-indexed
agreement of `bLl` over the reached opening control (cased on the prior control). -/
theorem foldθ_rightReReverseTrace
    (bLl : C_L -> In₂ -> Out₂) (bRl : C_L -> In₁ -> Out₁)
    (bRr : C_R -> In₁ -> Out₁) (bLr : C_R -> In₂ -> Out₂)
    (P : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (control : C_L ⊕ C_R) (entry : A.State × A.State) (state minState : A.State)
    (boundary openBoundary : A.State × A.State) (move : In₁ × In₂)
    (hagree :
      ∀ w : List In₂,
        bLl (leftSubordinateControlAfter
          (overwriteLeftBlindF bLl bRl (P boundary).1)
          ((overwriteLeftBlindF bLl bRl (P boundary).1).step
            (overwriteLeftBlindF bLl bRl (P boundary).1).init move.2) w) =
          bLl (leftSubordinateControlAfter
            (overwriteLeftBlindF bLl bRl (P openBoundary).1)
            (match control with
              | Sum.inl c =>
                (overwriteLeftBlindF bLl bRl (P openBoundary).1).step c move.2
              | Sum.inr _ =>
                (overwriteLeftBlindF bLl bRl (P openBoundary).1).step
                  (overwriteLeftBlindF bLl bRl (P openBoundary).1).init move.2) w))
    (_hreset :
      RightResetControl ((foldθ bLl bRl bRr bLr P openBoundary).2.2) control) :
    TwoBlindTraceMeasurable ((foldθ bLl bRl bRr bLr P boundary).1)
      (((foldθ bLl bRl bRr bLr P boundary).1).step
        ((foldθ bLl bRl bRr bLr P boundary).1).init move.2)
      ((foldθ bLl bRl bRr bLr P openBoundary).2.2)
      (((foldθ bLl bRl bRr bLr P openBoundary).2.2).step control (Sum.inl move.2))
      (revRightReverseEntry ((foldθ bLl bRl bRr bLr P openBoundary).2.2) control
        entry state minState move) := by
  cases control <;>
    exact foldChain_twoBlindTraceMeasurable_agree
      (overwriteLeftBlindF bLl bRl (P boundary).1)
      (overwriteLeftBlindF bLl bRl (P openBoundary).1)
      (overwriteRightBlindF bRr bLr (P openBoundary).2.1) _ _ _ hagree

/-- The control-dependent fold satisfies `leftReReverseTrace`: the mirror, on
`bRr`, over the reached opening control. -/
theorem foldθ_leftReReverseTrace
    (bLl : C_L -> In₂ -> Out₂) (bRl : C_L -> In₁ -> Out₁)
    (bRr : C_R -> In₁ -> Out₁) (bLr : C_R -> In₂ -> Out₂)
    (P : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (control : C_L ⊕ C_R) (entry : A.State × A.State) (state minState : A.State)
    (boundary openBoundary : A.State × A.State) (move : In₁ × In₂)
    (hagree :
      ∀ w : List In₁,
        bRr (rightSubordinateControlAfter
          (overwriteRightBlindF bRr bLr (P boundary).2.1)
          ((overwriteRightBlindF bRr bLr (P boundary).2.1).step
            (overwriteRightBlindF bRr bLr (P boundary).2.1).init move.1) w) =
          bRr (rightSubordinateControlAfter
            (overwriteRightBlindF bRr bLr (P openBoundary).2.1)
            (match control with
              | Sum.inr c =>
                (overwriteRightBlindF bRr bLr (P openBoundary).2.1).step c move.1
              | Sum.inl _ =>
                (overwriteRightBlindF bRr bLr (P openBoundary).2.1).step
                  (overwriteRightBlindF bRr bLr (P openBoundary).2.1).init move.1) w))
    (_hreset :
      LeftResetControl ((foldθ bLl bRl bRr bLr P openBoundary).2.2) control) :
    OneBlindTraceMeasurable ((foldθ bLl bRl bRr bLr P boundary).2.1)
      (((foldθ bLl bRl bRr bLr P boundary).2.1).step
        ((foldθ bLl bRl bRr bLr P boundary).2.1).init move.1)
      ((foldθ bLl bRl bRr bLr P openBoundary).2.2)
      (((foldθ bLl bRl bRr bLr P openBoundary).2.2).step control (Sum.inr move.1))
      (revLeftReverseEntry ((foldθ bLl bRl bRr bLr P openBoundary).2.2) control
        entry state minState move) := by
  cases control <;>
    exact foldChain_oneBlindTraceMeasurable_agree
      (overwriteLeftBlindF bLl bRl (P openBoundary).1)
      (overwriteRightBlindF bRr bLr (P boundary).2.1)
      (overwriteRightBlindF bRr bLr (P openBoundary).2.1) _ _ _ hagree

/-- The control-dependent fold satisfies the blind commitment `PlanBlindMeasurable`
from the reversal-opening agreements: process one's reversal output `bRl` equals the
right-plan opening table `bRr`, and the mirror on `bLr`/`bLl`.  These are the
reversal-opening commitment of `cor:folddischarge` (paper `prop:entrysound`), which
the `\bar\theta`-monitor makes an identity by driving `.rev` and `label .1` from the
one table at the block's entry. -/
theorem foldθ_blind
    (bLl : C_L -> In₂ -> Out₂) (bRl : C_L -> In₁ -> Out₁)
    (bRr : C_R -> In₁ -> Out₁) (bLr : C_R -> In₂ -> Out₂)
    (P : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (h1 :
      ∀ (control : C_L) (boundary : A.State × A.State) (i : In₁),
        bRl control i = bRr ((P boundary).2.1.init) i)
    (h2 :
      ∀ (control : C_R) (boundary : A.State × A.State) (i : In₂),
        bLr control i = bLl ((P boundary).1.init) i) :
    PlanBlindMeasurable (foldθ bLl bRl bRr bLr P) :=
  ⟨fun _ _ control _ _ boundary i => h1 control boundary i,
    fun _ _ control _ _ boundary i => h2 control boundary i⟩

/-- **The realizing fold `foldθ` is reversal-measurable, reduced to the
`cor:blindcrossreading` agreements.**  Unlike `globalFold` (constant tables, all
obligations by `rfl`), `foldθ` reads control-dependent blind functions, so its
seven `ReversalMeasurable` obligations hold exactly when the shared `θ̄`-monitors
`bRr`, `bLl` agree across the successor and opening boundaries -- the word-indexed
form of paper `cor:blindcrossreading`, whose *view* side is proved
(`ThmThetaBar.blindTable_crossReading_procOne`/`_procTwo`).  This is the capstone
of the measurability half (`hmeas`) for the *realizing* fold: with these
agreements it discharges `reversalMeasurable_winner_of_fold`'s `hmeas` slot at
`fold := foldθ …`, leaving `hwin` (winning-preservation, `prop:starcomplete`) as
the sole residual.  The `θ̄`-monitor construction that makes the agreements true
by construction is the next step. -/
theorem foldθ_reversalMeasurable
    (bLl : C_L -> In₂ -> Out₂) (bRl : C_L -> In₁ -> Out₁)
    (bRr : C_R -> In₁ -> Out₁) (bLr : C_R -> In₂ -> Out₂)
    (P : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (h1 :
      ∀ (control : C_L) (boundary : A.State × A.State) (i : In₁),
        bRl control i = bRr ((P boundary).2.1.init) i)
    (h2 :
      ∀ (control : C_R) (boundary : A.State × A.State) (i : In₂),
        bLr control i = bLl ((P boundary).1.init) i)
    (hLeftTrace :
      ∀ (candBoundary openBoundary : A.State × A.State) (move : In₁ × In₂),
        ∀ w : List In₁,
          bRr (rightSubordinateControlAfter
            (overwriteRightBlindF bRr bLr (P candBoundary).2.1)
            ((overwriteRightBlindF bRr bLr (P candBoundary).2.1).step
              (overwriteRightBlindF bRr bLr (P candBoundary).2.1).init move.1) w) =
            bRr (rightSubordinateControlAfter
              (overwriteRightBlindF bRr bLr (P openBoundary).2.1)
              ((overwriteRightBlindF bRr bLr (P openBoundary).2.1).step
                (overwriteRightBlindF bRr bLr (P openBoundary).2.1).init move.1) w))
    (hRightTrace :
      ∀ (candBoundary openBoundary : A.State × A.State) (move : In₂ × In₁),
        ∀ w : List In₂,
          bLl (leftSubordinateControlAfter
            (overwriteLeftBlindF bLl bRl (P candBoundary).1)
            ((overwriteLeftBlindF bLl bRl (P candBoundary).1).step
              (overwriteLeftBlindF bLl bRl (P candBoundary).1).init move.1) w) =
            bLl (leftSubordinateControlAfter
              (overwriteLeftBlindF bLl bRl (P openBoundary).1)
              ((overwriteLeftBlindF bLl bRl (P openBoundary).1).step
                (overwriteLeftBlindF bLl bRl (P openBoundary).1).init move.1) w))
    (hRightReReverseBlind :
      ∀ (control : C_L ⊕ C_R) (entry : A.State × A.State) (state minState : A.State)
        (boundary openBoundary : A.State × A.State) (i : In₂),
        bLl ((P boundary).1.init) i =
          (((foldθ bLl bRl bRr bLr P openBoundary).2.2).labelR control).2.2.1
            (entry, state, minState) i)
    (hRightReReverseTrace :
      ∀ (control : C_L ⊕ C_R) (entry : A.State × A.State) (state minState : A.State)
        (boundary openBoundary : A.State × A.State) (move : In₁ × In₂),
        ∀ w : List In₂,
          bLl (leftSubordinateControlAfter
            (overwriteLeftBlindF bLl bRl (P boundary).1)
            ((overwriteLeftBlindF bLl bRl (P boundary).1).step
              (overwriteLeftBlindF bLl bRl (P boundary).1).init move.2) w) =
            bLl (leftSubordinateControlAfter
              (overwriteLeftBlindF bLl bRl (P openBoundary).1)
              (match control with
                | Sum.inl c =>
                  (overwriteLeftBlindF bLl bRl (P openBoundary).1).step c move.2
                | Sum.inr _ =>
                  (overwriteLeftBlindF bLl bRl (P openBoundary).1).step
                    (overwriteLeftBlindF bLl bRl (P openBoundary).1).init move.2) w))
    (hLeftReReverseBlind :
      ∀ (control : C_L ⊕ C_R) (entry : A.State × A.State) (state minState : A.State)
        (boundary openBoundary : A.State × A.State) (i : In₁),
        bRr ((P boundary).2.1.init) i =
          (((foldθ bLl bRl bRr bLr P openBoundary).2.2).labelL control).2.1
            (entry, state, minState) i)
    (hLeftReReverseTrace :
      ∀ (control : C_L ⊕ C_R) (entry : A.State × A.State) (state minState : A.State)
        (boundary openBoundary : A.State × A.State) (move : In₁ × In₂),
        ∀ w : List In₁,
          bRr (rightSubordinateControlAfter
            (overwriteRightBlindF bRr bLr (P boundary).2.1)
            ((overwriteRightBlindF bRr bLr (P boundary).2.1).step
              (overwriteRightBlindF bRr bLr (P boundary).2.1).init move.1) w) =
            bRr (rightSubordinateControlAfter
              (overwriteRightBlindF bRr bLr (P openBoundary).2.1)
              (match control with
                | Sum.inr c =>
                  (overwriteRightBlindF bRr bLr (P openBoundary).2.1).step c move.1
                | Sum.inl _ =>
                  (overwriteRightBlindF bRr bLr (P openBoundary).2.1).step
                    (overwriteRightBlindF bRr bLr (P openBoundary).2.1).init move.1) w)) :
    ReversalMeasurable (foldθ bLl bRl bRr bLr P) where
  blind := foldθ_blind bLl bRl bRr bLr P h1 h2
  leftTrace := fun plan control state minState candBoundary openBoundary move =>
    foldθ_leftTrace bLl bRl bRr bLr P plan control state minState candBoundary
      openBoundary move (hLeftTrace candBoundary openBoundary move)
  rightTrace := fun plan control state minState candBoundary openBoundary move =>
    foldθ_rightTrace bLl bRl bRr bLr P plan control state minState candBoundary
      openBoundary move (hRightTrace candBoundary openBoundary move)
  rightReReverseBlind := fun control entry state minState boundary openBoundary i =>
    foldθ_rightReReverseBlind bLl bRl bRr bLr P control entry state minState
      boundary openBoundary i
      (hRightReReverseBlind control entry state minState boundary openBoundary i)
  rightReReverseTrace := fun control entry state minState boundary openBoundary move =>
    foldθ_rightReReverseTrace bLl bRl bRr bLr P control entry state minState
      boundary openBoundary move
      (hRightReReverseTrace control entry state minState boundary openBoundary move)
  leftReReverseBlind := fun control entry state minState boundary openBoundary i =>
    foldθ_leftReReverseBlind bLl bRl bRr bLr P control entry state minState
      boundary openBoundary i
      (hLeftReReverseBlind control entry state minState boundary openBoundary i)
  leftReReverseTrace := fun control entry state minState boundary openBoundary move =>
    foldθ_leftReReverseTrace bLl bRl bRr bLr P control entry state minState
      boundary openBoundary move
      (hLeftReReverseTrace control entry state minState boundary openBoundary move)

/-- **Reset-parity reachability.**  Every reversed-*left* boundary-game position
reached by the fold carries a `LeftResetControl`, and every reversed-*right*
position a `RightResetControl`: the control was set, one step earlier, by the
producing target (`leftReverseTarget`/`rightReverseTarget` on the original
reversal, or the `revLeft*`/`revRight*` targets on a re-reversal or interior
continuation), each of which steps the chain on a round of the position's own
orientation.  This is the invariant that lets the entry-indexed certificate
restrict its two re-reversal *trace* obligations to reset-parity controls, since
those obligations are consumed only at such positions. -/
theorem arenaFoldSeq_reset
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) :
    ∀ n : Nat,
      (∀ chain control entry state minState,
        arenaFoldSeq plans env n =
            Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl
              (chain, control, entry, state, minState))))) →
          LeftResetControl chain control) ∧
      (∀ chain control entry state minState,
        arenaFoldSeq plans env n =
            Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
              (chain, control, entry, state, minState))))) →
          RightResetControl chain control) := by
  intro n
  cases n with
  | zero =>
      constructor <;>
        · intro chain control entry state minState h
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
        cases hgraph : (env n).graph <;>
          constructor <;>
          · intro c ctrl e s m h
            rw [hsucc] at h
            exact absurd h (by
              simp [arenaStep, hgraph, boundaryOpenLeftTarget,
                boundaryOpenRightTarget, boundaryBothTarget])
      · exact absurd hpos (arenaFoldSeq_ne_committed plans env n committed)
      · rw [hpos] at hsucc
        cases hgraph : (env n).graph
        · constructor <;>
            · intro c ctrl e s m h
              rw [hsucc] at h
              exact absurd h (by simp [arenaStep, hgraph, leftContinueTarget])
        · refine ⟨fun c ctrl e s m h => absurd h (by
              rw [hsucc]; simp [arenaStep, hgraph, leftReverseTarget]), ?_⟩
          intro c ctrl e s m h
          rw [hsucc] at h
          simp only [arenaStep, hgraph, leftReverseTarget, Sum.inr.injEq,
            Prod.mk.injEq] at h
          obtain ⟨hc, hctrl, -⟩ := h
          subst hc
          exact ⟨_, _, hctrl.symm⟩
        · constructor <;>
            · intro c ctrl e s m h
              rw [hsucc] at h
              exact absurd h (by simp [arenaStep, hgraph, leftCloseTarget])
      · rw [hpos] at hsucc
        cases hgraph : (env n).graph
        · refine ⟨?_, fun c ctrl e s m h => absurd h (by
              rw [hsucc]; simp [arenaStep, hgraph, rightReverseTarget])⟩
          intro c ctrl e s m h
          rw [hsucc] at h
          simp only [arenaStep, hgraph, rightReverseTarget, Sum.inr.injEq,
            Sum.inl.injEq, Prod.mk.injEq] at h
          obtain ⟨hc, hctrl, -⟩ := h
          subst hc
          exact ⟨_, _, hctrl.symm⟩
        · constructor <;>
            · intro c ctrl e s m h
              rw [hsucc] at h
              exact absurd h (by simp [arenaStep, hgraph, rightContinueTarget])
        · constructor <;>
            · intro c ctrl e s m h
              rw [hsucc] at h
              exact absurd h (by simp [arenaStep, hgraph, rightCloseTarget])
      · rw [hpos] at hsucc
        cases hgraph : (env n).graph
        · refine ⟨?_, fun c ctrl e s m h => absurd h (by
              rw [hsucc]; simp [arenaStep, hgraph, revLeftContinueTarget])⟩
          intro c ctrl e s m h
          rw [hsucc] at h
          simp only [arenaStep, hgraph, revLeftContinueTarget, Sum.inr.injEq,
            Sum.inl.injEq, Prod.mk.injEq] at h
          obtain ⟨hc, hctrl, -⟩ := h
          subst hc
          exact ⟨_, _, hctrl.symm⟩
        · refine ⟨fun c ctrl e s m h => absurd h (by
              rw [hsucc]; simp [arenaStep, hgraph, revLeftReverseTarget]), ?_⟩
          intro c ctrl e s m h
          rw [hsucc] at h
          simp only [arenaStep, hgraph, revLeftReverseTarget, Sum.inr.injEq,
            Prod.mk.injEq] at h
          obtain ⟨hc, hctrl, -⟩ := h
          subst hc
          exact ⟨_, _, hctrl.symm⟩
        · constructor <;>
            · intro c ctrl e s m h
              rw [hsucc] at h
              exact absurd h (by simp [arenaStep, hgraph, revLeftCloseTarget])
      · rw [hpos] at hsucc
        cases hgraph : (env n).graph
        · refine ⟨?_, fun c ctrl e s m h => absurd h (by
              rw [hsucc]; simp [arenaStep, hgraph, revRightReverseTarget])⟩
          intro c ctrl e s m h
          rw [hsucc] at h
          simp only [arenaStep, hgraph, revRightReverseTarget, Sum.inr.injEq,
            Sum.inl.injEq, Prod.mk.injEq] at h
          obtain ⟨hc, hctrl, -⟩ := h
          subst hc
          exact ⟨_, _, hctrl.symm⟩
        · refine ⟨fun c ctrl e s m h => absurd h (by
              rw [hsucc]; simp [arenaStep, hgraph, revRightContinueTarget]), ?_⟩
          intro c ctrl e s m h
          rw [hsucc] at h
          simp only [arenaStep, hgraph, revRightContinueTarget, Sum.inr.injEq,
            Prod.mk.injEq] at h
          obtain ⟨hc, hctrl, -⟩ := h
          subst hc
          exact ⟨_, _, hctrl.symm⟩
        · constructor <;>
            · intro c ctrl e s m h
              rw [hsucc] at h
              exact absurd h (by simp [arenaStep, hgraph, revRightCloseTarget])

end

/--
One round of the correspondence: if both cores track the fold position,
the emitted round is the arena record and the advanced cores track the
advanced position.
-/
theorem journal_step
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂)
    (hnodirect : NoDirectReversalSequence env) (n : Nat)
    (h1 :
      OneCoreTracks (oneSummaryAt plans env n).2 (arenaFoldSeq plans env n))
    (h2 :
      TwoCoreTracks (twoSummaryAt plans env n).2
        (arenaFoldSeq plans env n)) :
    execution (journalStrategy plans) env n = arenaWord plans env n ∧
      OneCoreTracks (oneSummaryAt plans env (n + 1)).2
        (arenaFoldSeq plans env (n + 1)) ∧
      TwoCoreTracks (twoSummaryAt plans env (n + 1)).2
        (arenaFoldSeq plans env (n + 1)) := by
  have hfold :
      arenaFoldSeq plans env (n + 1) =
        arenaStep plans (arenaFoldSeq plans env n) (env n) := rfl
  have hexec := execution_journal_apply plans env n
  rcases hpos : arenaFoldSeq plans env n with
    ⟨state, minState⟩ | committed |
      ⟨plan, chain, control, state, minState⟩ |
      ⟨plan, chain, control, state, minState⟩ | inRevL | inRevR
  · rw [hpos] at h1 h2 hfold
    simp only [OneCoreTracks] at h1
    simp only [TwoCoreTracks] at h2
    have harena :
        arenaWord plans env n =
          arenaRecord plans (Sum.inl (state, minState)) (env n) := by
      show arenaRecord plans (arenaFoldSeq plans env n) (env n) = _
      rw [hpos]
    have hsub2 :
        TwoCore.isSubordinate ((twoSummaryAt plans env n).2) = false := by
      rcases h2 with h2 | ⟨rdata, h2⟩ | ⟨revData, h2⟩ <;> rw [h2] <;> rfl
    have hsub1 :
        OneCore.isSubordinate ((oneSummaryAt plans env n).2) = false := by
      rcases h1 with h1 | ⟨ldata, h1⟩ | ⟨revData, h1⟩ <;> rw [h1] <;> rfl
    have honeStep :
        ∀ move : In₁ × In₂,
          oneRecvStep (A := A) plans (oneSummaryAt plans env n).2 move
              (twoSummaryAt plans env n).2 =
            (oneRecvOutput (A := A) plans (Sum.inl (state, minState)) move,
              Sum.inl
                (oneLeftSuccessor (A := A) plans
                    (Sum.inl (state, minState)) move,
                  oneBothSuccessor (A := A) plans
                    (Sum.inl (state, minState)) move)) := by
      intro move
      rcases h1 with h1 | ⟨ldata, h1⟩ | ⟨revData, h1⟩ <;> rw [h1] <;>
        simp [oneRecvStep, hsub2]
    have htwoStep :
        ∀ move : In₁ × In₂,
          twoRecvStep (A := A) plans (twoSummaryAt plans env n).2 move
              (oneSummaryAt plans env n).2 =
            (twoRecvOutput (A := A) plans (Sum.inl (state, minState)) move,
              Sum.inl
                (twoRightSuccessor (A := A) plans
                    (Sum.inl (state, minState)) move,
                  twoBothSuccessor (A := A) plans
                    (Sum.inl (state, minState)) move)) := by
      intro move
      rcases h2 with h2 | ⟨rdata, h2⟩ | ⟨revData, h2⟩ <;> rw [h2] <;>
        simp [twoRecvStep, hsub1]
    cases hgraph : (env n).graph
    · refine ⟨?_, ?_, ?_⟩
      · rw [hexec, harena, oneSummaryAt_succ_left plans env n hgraph,
          twoSummaryAt_succ_left plans env n hgraph, honeStep]
        rcases h2 with h2 | ⟨rdata, h2⟩ | ⟨revData, h2⟩ <;> rw [h2] <;>
          simp [arenaRecord, hgraph, twoNoRecvStep, oneRecvOutput,
            planOpenOne, leftRoundRecord]
      · rw [hfold, oneSummaryAt_succ_left plans env n hgraph, honeStep]
        simp only [arenaStep, hgraph]
        exact ⟨_, rfl⟩
      · rw [hfold, twoSummaryAt_succ_left plans env n hgraph]
        simp only [arenaStep, hgraph]
        rcases h2 with h2 | ⟨rdata, h2⟩ | ⟨revData, h2⟩
        · rw [h2]; exact Or.inl rfl
        · rw [h2]; exact Or.inr ⟨_, rfl⟩
        · rw [h2]; exact Or.inr ⟨_, rfl⟩
    · refine ⟨?_, ?_, ?_⟩
      · rw [hexec, harena, oneSummaryAt_succ_right plans env n hgraph,
          twoSummaryAt_succ_right plans env n hgraph, htwoStep]
        rcases h1 with h1 | ⟨ldata, h1⟩ | ⟨revData, h1⟩ <;> rw [h1] <;>
          simp [arenaRecord, hgraph, oneNoRecvStep, twoRecvOutput,
            planOpenTwo, rightRoundRecord]
      · rw [hfold, oneSummaryAt_succ_right plans env n hgraph]
        simp only [arenaStep, hgraph]
        rcases h1 with h1 | ⟨ldata, h1⟩ | ⟨revData, h1⟩
        · rw [h1]; exact Or.inl rfl
        · rw [h1]; exact Or.inr ⟨_, rfl⟩
        · rw [h1]; exact Or.inr ⟨_, rfl⟩
      · rw [hfold, twoSummaryAt_succ_right plans env n hgraph, htwoStep]
        simp only [arenaStep, hgraph]
        exact ⟨_, rfl⟩
    · refine ⟨?_, ?_, ?_⟩
      · rw [hexec, harena, oneSummaryAt_succ_both plans env n hgraph,
          twoSummaryAt_succ_both plans env n hgraph, honeStep, htwoStep]
        simp [arenaRecord, hgraph, oneRecvOutput, twoRecvOutput,
          planOpenOne, planOpenTwo, bothRoundRecord]
      · rw [hfold, oneSummaryAt_succ_both plans env n hgraph, honeStep]
        simp only [arenaStep, hgraph]
        exact Or.inr (Or.inl ⟨_, rfl⟩)
      · rw [hfold, twoSummaryAt_succ_both plans env n hgraph, htwoStep]
        simp only [arenaStep, hgraph]
        exact Or.inr (Or.inl ⟨_, rfl⟩)
  · exact
      absurd hpos (arenaFoldSeq_ne_committed plans env n committed)
  · rw [hpos] at h1 h2 hfold
    simp only [OneCoreTracks] at h1
    simp only [TwoCoreTracks] at h2
    obtain ⟨bcand, hcore1⟩ := h1
    have harena :
        arenaWord plans env n =
          arenaRecord plans
            (Sum.inr (Sum.inr (Sum.inl (plan, chain, control, state, minState))))
            (env n) := by
      show arenaRecord plans (arenaFoldSeq plans env n) (env n) = _
      rw [hpos]
    have hsub2 :
        TwoCore.isSubordinate ((twoSummaryAt plans env n).2) = true := by
      rcases h2 with h2 | ⟨eside, h2⟩ <;> rw [h2] <;> rfl
    have honeStep :
        ∀ move : In₁ × In₂,
          oneRecvStep (A := A) plans (oneSummaryAt plans env n).2 move
              (twoSummaryAt plans env n).2 =
            (oneRecvOutput (A := A) plans
                (Sum.inr (plan, chain, control, state, minState)) move,
              Sum.inl
                (oneLeftSuccessor (A := A) plans
                    (Sum.inr (plan, chain, control, state, minState)) move,
                  oneBothSuccessor (A := A) plans
                    (Sum.inr (plan, chain, control, state, minState)) move)) := by
      intro move
      rw [hcore1]
      simp [oneRecvStep, hsub2]
    obtain ⟨m, hm, hmLeft⟩ :=
      (arenaFoldSeq_shape plans env n).1
        (plan, chain, control, state, minState) hpos
    cases hgraph : (env n).graph
    · refine ⟨?_, ?_, ?_⟩
      · rcases h2 with h2 | ⟨eside, h2⟩ <;>
          rw [hexec, harena, oneSummaryAt_succ_left plans env n hgraph,
            twoSummaryAt_succ_left plans env n hgraph, honeStep, h2] <;>
          simp [arenaRecord, hgraph, twoNoRecvStep, oneRecvOutput,
            leftRoundRecord]
      · rw [hfold, oneSummaryAt_succ_left plans env n hgraph, honeStep]
        simp only [arenaStep, hgraph]
        exact ⟨_, rfl⟩
      · rcases h2 with h2 | ⟨eside, h2⟩
        · rw [hfold, twoSummaryAt_succ_left plans env n hgraph, h2]
          simp only [arenaStep, hgraph]
          exact Or.inl rfl
        · rw [hfold, twoSummaryAt_succ_left plans env n hgraph, h2]
          simp only [arenaStep, hgraph]
          exact Or.inr ⟨_, rfl⟩
    · subst hm
      exact absurd hgraph ((hnodirect m).1 hmLeft)
    · refine ⟨?_, ?_, ?_⟩
      · rw [hexec, harena, oneSummaryAt_succ_both plans env n hgraph,
          twoSummaryAt_succ_both plans env n hgraph, honeStep]
        rcases h2 with h2 | ⟨eside, h2⟩ <;> rw [h2, hcore1] <;>
          simp [twoRecvStep, arenaRecord, hgraph, oneRecvOutput,
            bothRoundRecord]
      · rw [hfold, oneSummaryAt_succ_both plans env n hgraph, honeStep]
        simp only [arenaStep, hgraph]
        exact Or.inr (Or.inl ⟨_, rfl⟩)
      · rw [hfold, twoSummaryAt_succ_both plans env n hgraph]
        simp only [arenaStep, hgraph]
        rcases h2 with h2 | ⟨eside, h2⟩
        · rw [h2, hcore1]; exact Or.inr (Or.inr ⟨_, rfl⟩)
        · rw [h2, hcore1]; exact Or.inr (Or.inr ⟨_, rfl⟩)
  · rw [hpos] at h1 h2 hfold
    simp only [OneCoreTracks] at h1
    simp only [TwoCoreTracks] at h2
    obtain ⟨bcand, hcore2⟩ := h2
    have harena :
        arenaWord plans env n =
          arenaRecord plans
            (Sum.inr (Sum.inr (Sum.inr (Sum.inl
              (plan, chain, control, state, minState)))))
            (env n) := by
      show arenaRecord plans (arenaFoldSeq plans env n) (env n) = _
      rw [hpos]
    have hsub1 :
        OneCore.isSubordinate ((oneSummaryAt plans env n).2) = true := by
      rcases h1 with h1 | ⟨eside, h1⟩ <;> rw [h1] <;> rfl
    have htwoStep :
        ∀ move : In₁ × In₂,
          twoRecvStep (A := A) plans (twoSummaryAt plans env n).2 move
              (oneSummaryAt plans env n).2 =
            (twoRecvOutput (A := A) plans
                (Sum.inr (plan, chain, control, state, minState)) move,
              Sum.inl
                (twoRightSuccessor (A := A) plans
                    (Sum.inr (plan, chain, control, state, minState)) move,
                  twoBothSuccessor (A := A) plans
                    (Sum.inr (plan, chain, control, state, minState)) move)) := by
      intro move
      rw [hcore2]
      simp [twoRecvStep, hsub1]
    obtain ⟨m, hm, hmRight⟩ :=
      (arenaFoldSeq_shape plans env n).2.1
        (plan, chain, control, state, minState) hpos
    cases hgraph : (env n).graph
    · subst hm
      exact absurd hgraph ((hnodirect m).2 hmRight)
    · refine ⟨?_, ?_, ?_⟩
      · rcases h1 with h1 | ⟨eside, h1⟩ <;>
          rw [hexec, harena, oneSummaryAt_succ_right plans env n hgraph,
            twoSummaryAt_succ_right plans env n hgraph, htwoStep, h1] <;>
          simp [arenaRecord, hgraph, oneNoRecvStep, twoRecvOutput,
            rightRoundRecord]
      · rcases h1 with h1 | ⟨eside, h1⟩
        · rw [hfold, oneSummaryAt_succ_right plans env n hgraph, h1]
          simp only [arenaStep, hgraph]
          exact Or.inl rfl
        · rw [hfold, oneSummaryAt_succ_right plans env n hgraph, h1]
          simp only [arenaStep, hgraph]
          exact Or.inr ⟨_, rfl⟩
      · rw [hfold, twoSummaryAt_succ_right plans env n hgraph, htwoStep]
        simp only [arenaStep, hgraph]
        exact ⟨_, rfl⟩
    · refine ⟨?_, ?_, ?_⟩
      · rw [hexec, harena, oneSummaryAt_succ_both plans env n hgraph,
          twoSummaryAt_succ_both plans env n hgraph, htwoStep]
        rcases h1 with h1 | ⟨eside, h1⟩ <;> rw [h1, hcore2] <;>
          simp [oneRecvStep, arenaRecord, hgraph, twoRecvOutput,
            bothRoundRecord]
      · rw [hfold, oneSummaryAt_succ_both plans env n hgraph]
        simp only [arenaStep, hgraph]
        rcases h1 with h1 | ⟨eside, h1⟩
        · rw [h1, hcore2]; exact Or.inr (Or.inr ⟨_, rfl⟩)
        · rw [h1, hcore2]; exact Or.inr (Or.inr ⟨_, rfl⟩)
      · rw [hfold, twoSummaryAt_succ_both plans env n hgraph, htwoStep]
        simp only [arenaStep, hgraph]
        exact Or.inr (Or.inl ⟨_, rfl⟩)
  · exact
      absurd hpos
        ((arenaFoldSeq_reversed_unreachable_of_noDirect plans env hnodirect
            n).1 inRevL)
  · exact
      absurd hpos
        ((arenaFoldSeq_reversed_unreachable_of_noDirect plans env hnodirect
            n).2 inRevR)

/--
Full-model round correspondence (drops `hnodirect`, adds the certificate `hcert`).
Unconditional in the environment: no `NoDirectReversalSequence` hypothesis.
The reversed-block interior (S5/S6, all of continue/close/re-reverse) is proved
from the entry-indexed measurability certificate `hcert`.
-/
theorem journal_step_full
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂)
    (hcert : ReversalMeasurable plans) (n : Nat)
    (h1 :
      OneCoreTracks (oneSummaryAt plans env n).2 (arenaFoldSeq plans env n))
    (h2 :
      TwoCoreTracks (twoSummaryAt plans env n).2
        (arenaFoldSeq plans env n)) :
    execution (journalStrategy plans) env n = arenaWord plans env n ∧
      OneCoreTracks (oneSummaryAt plans env (n + 1)).2
        (arenaFoldSeq plans env (n + 1)) ∧
      TwoCoreTracks (twoSummaryAt plans env (n + 1)).2
        (arenaFoldSeq plans env (n + 1)) := by
  have hfold :
      arenaFoldSeq plans env (n + 1) =
        arenaStep plans (arenaFoldSeq plans env n) (env n) := rfl
  have hexec := execution_journal_apply plans env n
  rcases hpos : arenaFoldSeq plans env n with
    ⟨state, minState⟩ | committed |
      ⟨plan, chain, control, state, minState⟩ |
      ⟨plan, chain, control, state, minState⟩ | inRevL | inRevR
  · rw [hpos] at h1 h2 hfold
    simp only [OneCoreTracks] at h1
    simp only [TwoCoreTracks] at h2
    have harena :
        arenaWord plans env n =
          arenaRecord plans (Sum.inl (state, minState)) (env n) := by
      show arenaRecord plans (arenaFoldSeq plans env n) (env n) = _
      rw [hpos]
    have hsub2 :
        TwoCore.isSubordinate ((twoSummaryAt plans env n).2) = false := by
      rcases h2 with h2 | ⟨rdata, h2⟩ | ⟨revData, h2⟩ <;> rw [h2] <;> rfl
    have hsub1 :
        OneCore.isSubordinate ((oneSummaryAt plans env n).2) = false := by
      rcases h1 with h1 | ⟨ldata, h1⟩ | ⟨revData, h1⟩ <;> rw [h1] <;> rfl
    have honeStep :
        ∀ move : In₁ × In₂,
          oneRecvStep (A := A) plans (oneSummaryAt plans env n).2 move
              (twoSummaryAt plans env n).2 =
            (oneRecvOutput (A := A) plans (Sum.inl (state, minState)) move,
              Sum.inl
                (oneLeftSuccessor (A := A) plans
                    (Sum.inl (state, minState)) move,
                  oneBothSuccessor (A := A) plans
                    (Sum.inl (state, minState)) move)) := by
      intro move
      rcases h1 with h1 | ⟨ldata, h1⟩ | ⟨revData, h1⟩ <;> rw [h1] <;>
        simp [oneRecvStep, hsub2]
    have htwoStep :
        ∀ move : In₁ × In₂,
          twoRecvStep (A := A) plans (twoSummaryAt plans env n).2 move
              (oneSummaryAt plans env n).2 =
            (twoRecvOutput (A := A) plans (Sum.inl (state, minState)) move,
              Sum.inl
                (twoRightSuccessor (A := A) plans
                    (Sum.inl (state, minState)) move,
                  twoBothSuccessor (A := A) plans
                    (Sum.inl (state, minState)) move)) := by
      intro move
      rcases h2 with h2 | ⟨rdata, h2⟩ | ⟨revData, h2⟩ <;> rw [h2] <;>
        simp [twoRecvStep, hsub1]
    cases hgraph : (env n).graph
    · refine ⟨?_, ?_, ?_⟩
      · rw [hexec, harena, oneSummaryAt_succ_left plans env n hgraph,
          twoSummaryAt_succ_left plans env n hgraph, honeStep]
        rcases h2 with h2 | ⟨rdata, h2⟩ | ⟨revData, h2⟩ <;> rw [h2] <;>
          simp [arenaRecord, hgraph, twoNoRecvStep, oneRecvOutput,
            planOpenOne, leftRoundRecord]
      · rw [hfold, oneSummaryAt_succ_left plans env n hgraph, honeStep]
        simp only [arenaStep, hgraph]
        exact ⟨_, rfl⟩
      · rw [hfold, twoSummaryAt_succ_left plans env n hgraph]
        simp only [arenaStep, hgraph]
        rcases h2 with h2 | ⟨rdata, h2⟩ | ⟨revData, h2⟩
        · rw [h2]; exact Or.inl rfl
        · rw [h2]; exact Or.inr ⟨_, rfl⟩
        · rw [h2]; exact Or.inr ⟨_, rfl⟩
    · refine ⟨?_, ?_, ?_⟩
      · rw [hexec, harena, oneSummaryAt_succ_right plans env n hgraph,
          twoSummaryAt_succ_right plans env n hgraph, htwoStep]
        rcases h1 with h1 | ⟨ldata, h1⟩ | ⟨revData, h1⟩ <;> rw [h1] <;>
          simp [arenaRecord, hgraph, oneNoRecvStep, twoRecvOutput,
            planOpenTwo, rightRoundRecord]
      · rw [hfold, oneSummaryAt_succ_right plans env n hgraph]
        simp only [arenaStep, hgraph]
        rcases h1 with h1 | ⟨ldata, h1⟩ | ⟨revData, h1⟩
        · rw [h1]; exact Or.inl rfl
        · rw [h1]; exact Or.inr ⟨_, rfl⟩
        · rw [h1]; exact Or.inr ⟨_, rfl⟩
      · rw [hfold, twoSummaryAt_succ_right plans env n hgraph, htwoStep]
        simp only [arenaStep, hgraph]
        exact ⟨_, rfl⟩
    · refine ⟨?_, ?_, ?_⟩
      · rw [hexec, harena, oneSummaryAt_succ_both plans env n hgraph,
          twoSummaryAt_succ_both plans env n hgraph, honeStep, htwoStep]
        simp [arenaRecord, hgraph, oneRecvOutput, twoRecvOutput,
          planOpenOne, planOpenTwo, bothRoundRecord]
      · rw [hfold, oneSummaryAt_succ_both plans env n hgraph, honeStep]
        simp only [arenaStep, hgraph]
        exact Or.inr (Or.inl ⟨_, rfl⟩)
      · rw [hfold, twoSummaryAt_succ_both plans env n hgraph, htwoStep]
        simp only [arenaStep, hgraph]
        exact Or.inr (Or.inl ⟨_, rfl⟩)
  · exact
      absurd hpos (arenaFoldSeq_ne_committed plans env n committed)
  · rw [hpos] at h1 h2 hfold
    simp only [OneCoreTracks] at h1
    simp only [TwoCoreTracks] at h2
    obtain ⟨bcand, hcore1⟩ := h1
    have harena :
        arenaWord plans env n =
          arenaRecord plans
            (Sum.inr (Sum.inr (Sum.inl (plan, chain, control, state, minState))))
            (env n) := by
      show arenaRecord plans (arenaFoldSeq plans env n) (env n) = _
      rw [hpos]
    have hsub2 :
        TwoCore.isSubordinate ((twoSummaryAt plans env n).2) = true := by
      rcases h2 with h2 | ⟨eside, h2⟩ <;> rw [h2] <;> rfl
    have honeStep :
        ∀ move : In₁ × In₂,
          oneRecvStep (A := A) plans (oneSummaryAt plans env n).2 move
              (twoSummaryAt plans env n).2 =
            (oneRecvOutput (A := A) plans
                (Sum.inr (plan, chain, control, state, minState)) move,
              Sum.inl
                (oneLeftSuccessor (A := A) plans
                    (Sum.inr (plan, chain, control, state, minState)) move,
                  oneBothSuccessor (A := A) plans
                    (Sum.inr (plan, chain, control, state, minState)) move)) := by
      intro move
      rw [hcore1]
      simp [oneRecvStep, hsub2]
    obtain ⟨m, hm, hmLeft⟩ :=
      (arenaFoldSeq_shape plans env n).1
        (plan, chain, control, state, minState) hpos
    cases hgraph : (env n).graph
    · refine ⟨?_, ?_, ?_⟩
      · rcases h2 with h2 | ⟨eside, h2⟩ <;>
          rw [hexec, harena, oneSummaryAt_succ_left plans env n hgraph,
            twoSummaryAt_succ_left plans env n hgraph, honeStep, h2] <;>
          simp [arenaRecord, hgraph, twoNoRecvStep, oneRecvOutput,
            leftRoundRecord]
      · rw [hfold, oneSummaryAt_succ_left plans env n hgraph, honeStep]
        simp only [arenaStep, hgraph]
        exact ⟨_, rfl⟩
      · rcases h2 with h2 | ⟨eside, h2⟩
        · rw [hfold, twoSummaryAt_succ_left plans env n hgraph, h2]
          simp only [arenaStep, hgraph]
          exact Or.inl rfl
        · rw [hfold, twoSummaryAt_succ_left plans env n hgraph, h2]
          simp only [arenaStep, hgraph]
          exact Or.inr ⟨_, rfl⟩
    · clear hm hmLeft
      have hcommit :
          ChainCommittedAt plans
            (Sum.inr (Sum.inr (Sum.inl (plan, chain, control, state, minState)))) := by
        rw [← hpos]; exact chainCommittedAt_arenaFoldSeq plans env n
      simp only [ChainCommittedAt] at hcommit
      obtain ⟨atom, hplan, hchain⟩ := hcommit
      rcases h2 with h2 | ⟨eside, h2⟩ <;>
        refine ⟨?_, ?_, ?_⟩
      · rw [hexec, harena, oneSummaryAt_succ_right plans env n hgraph,
          twoSummaryAt_succ_right plans env n hgraph, hcore1, h2]
        simp only [oneNoRecvStep, twoRecvStep, arenaRecord, hgraph,
          rightRoundRecord, RoundRecord.mk.injEq, and_true, true_and]
        rw [hplan]
        exact (hcert.blind.1 atom chain control state minState bcand
          (env n).inputOne).symm
      · rw [hfold, oneSummaryAt_succ_right plans env n hgraph, hcore1]
        simp only [arenaStep, hgraph, oneNoRecvStep, leftReverseTarget,
          OneCoreTracks, leftReverseEntry]
        rw [hchain]
        exact ⟨_, _, _, rfl,
          hcert.leftTrace plan control state minState bcand atom
            ((env n).inputOne, (env n).inputTwo)⟩
      · rw [hfold, twoSummaryAt_succ_right plans env n hgraph, h2, hcore1]
        simp only [arenaStep, hgraph, twoRecvStep, leftReverseTarget,
          TwoCoreTracks]
        exact ⟨_, rfl⟩
      · rw [hexec, harena, oneSummaryAt_succ_right plans env n hgraph,
          twoSummaryAt_succ_right plans env n hgraph, hcore1, h2]
        simp only [oneNoRecvStep, twoRecvStep, arenaRecord, hgraph,
          rightRoundRecord, RoundRecord.mk.injEq, and_true, true_and]
        rw [hplan]
        exact (hcert.blind.1 atom chain control state minState bcand
          (env n).inputOne).symm
      · rw [hfold, oneSummaryAt_succ_right plans env n hgraph, hcore1]
        simp only [arenaStep, hgraph, oneNoRecvStep, leftReverseTarget,
          OneCoreTracks, leftReverseEntry]
        rw [hchain]
        exact ⟨_, _, _, rfl,
          hcert.leftTrace plan control state minState bcand atom
            ((env n).inputOne, (env n).inputTwo)⟩
      · rw [hfold, twoSummaryAt_succ_right plans env n hgraph, h2, hcore1]
        simp only [arenaStep, hgraph, twoRecvStep, leftReverseTarget,
          TwoCoreTracks]
        exact ⟨_, rfl⟩
    · refine ⟨?_, ?_, ?_⟩
      · rw [hexec, harena, oneSummaryAt_succ_both plans env n hgraph,
          twoSummaryAt_succ_both plans env n hgraph, honeStep]
        rcases h2 with h2 | ⟨eside, h2⟩ <;> rw [h2, hcore1] <;>
          simp [twoRecvStep, arenaRecord, hgraph, oneRecvOutput,
            bothRoundRecord]
      · rw [hfold, oneSummaryAt_succ_both plans env n hgraph, honeStep]
        simp only [arenaStep, hgraph]
        exact Or.inr (Or.inl ⟨_, rfl⟩)
      · rw [hfold, twoSummaryAt_succ_both plans env n hgraph]
        simp only [arenaStep, hgraph]
        rcases h2 with h2 | ⟨eside, h2⟩
        · rw [h2, hcore1]; exact Or.inr (Or.inr ⟨_, rfl⟩)
        · rw [h2, hcore1]; exact Or.inr (Or.inr ⟨_, rfl⟩)
  · rw [hpos] at h1 h2 hfold
    simp only [OneCoreTracks] at h1
    simp only [TwoCoreTracks] at h2
    obtain ⟨bcand, hcore2⟩ := h2
    have harena :
        arenaWord plans env n =
          arenaRecord plans
            (Sum.inr (Sum.inr (Sum.inr (Sum.inl
              (plan, chain, control, state, minState)))))
            (env n) := by
      show arenaRecord plans (arenaFoldSeq plans env n) (env n) = _
      rw [hpos]
    have hsub1 :
        OneCore.isSubordinate ((oneSummaryAt plans env n).2) = true := by
      rcases h1 with h1 | ⟨eside, h1⟩ <;> rw [h1] <;> rfl
    have htwoStep :
        ∀ move : In₁ × In₂,
          twoRecvStep (A := A) plans (twoSummaryAt plans env n).2 move
              (oneSummaryAt plans env n).2 =
            (twoRecvOutput (A := A) plans
                (Sum.inr (plan, chain, control, state, minState)) move,
              Sum.inl
                (twoRightSuccessor (A := A) plans
                    (Sum.inr (plan, chain, control, state, minState)) move,
                  twoBothSuccessor (A := A) plans
                    (Sum.inr (plan, chain, control, state, minState)) move)) := by
      intro move
      rw [hcore2]
      simp [twoRecvStep, hsub1]
    obtain ⟨m, hm, hmRight⟩ :=
      (arenaFoldSeq_shape plans env n).2.1
        (plan, chain, control, state, minState) hpos
    cases hgraph : (env n).graph
    · clear hm hmRight
      have hcommit :
          ChainCommittedAt plans
            (Sum.inr (Sum.inr (Sum.inr (Sum.inl
              (plan, chain, control, state, minState))))) := by
        rw [← hpos]; exact chainCommittedAt_arenaFoldSeq plans env n
      simp only [ChainCommittedAt] at hcommit
      obtain ⟨atom, hplan, hchain⟩ := hcommit
      rcases h1 with h1 | ⟨eside, h1⟩ <;>
        refine ⟨?_, ?_, ?_⟩
      · rw [hexec, harena, oneSummaryAt_succ_left plans env n hgraph,
          twoSummaryAt_succ_left plans env n hgraph, hcore2, h1]
        simp only [twoNoRecvStep, oneRecvStep, arenaRecord, hgraph,
          leftRoundRecord, RoundRecord.mk.injEq, and_true, true_and]
        rw [hplan]
        exact (hcert.blind.2 atom chain control state minState bcand
          (env n).inputTwo).symm
      · rw [hfold, oneSummaryAt_succ_left plans env n hgraph, h1, hcore2]
        simp only [arenaStep, hgraph, oneRecvStep, rightReverseTarget,
          OneCoreTracks]
        exact ⟨_, rfl⟩
      · rw [hfold, twoSummaryAt_succ_left plans env n hgraph, hcore2]
        simp only [arenaStep, hgraph, twoNoRecvStep, rightReverseTarget,
          TwoCoreTracks, rightReverseEntry]
        rw [hchain]
        exact ⟨_, _, _, rfl,
          hcert.rightTrace plan control state minState bcand atom
            ((env n).inputTwo, (env n).inputOne)⟩
      · rw [hexec, harena, oneSummaryAt_succ_left plans env n hgraph,
          twoSummaryAt_succ_left plans env n hgraph, hcore2, h1]
        simp only [twoNoRecvStep, oneRecvStep, arenaRecord, hgraph,
          leftRoundRecord, RoundRecord.mk.injEq, and_true, true_and]
        rw [hplan]
        exact (hcert.blind.2 atom chain control state minState bcand
          (env n).inputTwo).symm
      · rw [hfold, oneSummaryAt_succ_left plans env n hgraph, h1, hcore2]
        simp only [arenaStep, hgraph, oneRecvStep, rightReverseTarget,
          OneCoreTracks]
        exact ⟨_, rfl⟩
      · rw [hfold, twoSummaryAt_succ_left plans env n hgraph, hcore2]
        simp only [arenaStep, hgraph, twoNoRecvStep, rightReverseTarget,
          TwoCoreTracks, rightReverseEntry]
        rw [hchain]
        exact ⟨_, _, _, rfl,
          hcert.rightTrace plan control state minState bcand atom
            ((env n).inputTwo, (env n).inputOne)⟩
    · refine ⟨?_, ?_, ?_⟩
      · rcases h1 with h1 | ⟨eside, h1⟩ <;>
          rw [hexec, harena, oneSummaryAt_succ_right plans env n hgraph,
            twoSummaryAt_succ_right plans env n hgraph, htwoStep, h1] <;>
          simp [arenaRecord, hgraph, oneNoRecvStep, twoRecvOutput,
            rightRoundRecord]
      · rcases h1 with h1 | ⟨eside, h1⟩
        · rw [hfold, oneSummaryAt_succ_right plans env n hgraph, h1]
          simp only [arenaStep, hgraph]
          exact Or.inl rfl
        · rw [hfold, oneSummaryAt_succ_right plans env n hgraph, h1]
          simp only [arenaStep, hgraph]
          exact Or.inr ⟨_, rfl⟩
      · rw [hfold, twoSummaryAt_succ_right plans env n hgraph, htwoStep]
        simp only [arenaStep, hgraph]
        exact ⟨_, rfl⟩
    · refine ⟨?_, ?_, ?_⟩
      · rw [hexec, harena, oneSummaryAt_succ_both plans env n hgraph,
          twoSummaryAt_succ_both plans env n hgraph, htwoStep]
        rcases h1 with h1 | ⟨eside, h1⟩ <;> rw [h1, hcore2] <;>
          simp [oneRecvStep, arenaRecord, hgraph, twoRecvOutput,
            bothRoundRecord]
      · rw [hfold, oneSummaryAt_succ_both plans env n hgraph]
        simp only [arenaStep, hgraph]
        rcases h1 with h1 | ⟨eside, h1⟩
        · rw [h1, hcore2]; exact Or.inr (Or.inr ⟨_, rfl⟩)
        · rw [h1, hcore2]; exact Or.inr (Or.inr ⟨_, rfl⟩)
      · rw [hfold, twoSummaryAt_succ_both plans env n hgraph, htwoStep]
        simp only [arenaStep, hgraph]
        exact Or.inr (Or.inl ⟨_, rfl⟩)
  · obtain ⟨chain, control, entry, state, minState⟩ := inRevL
    rw [hpos] at h1 h2 hfold
    simp only [OneCoreTracks] at h1
    simp only [TwoCoreTracks] at h2
    obtain ⟨bnd, hcore1⟩ := h1
    obtain ⟨lplan, lc, frozen, hcore2, htrace⟩ := h2
    have hcommit :
        ChainCommittedAt plans
          (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl
            (chain, control, entry, state, minState)))))) := by
      rw [← hpos]; exact chainCommittedAt_arenaFoldSeq plans env n
    simp only [ChainCommittedAt] at hcommit
    obtain ⟨atom, hchain⟩ := hcommit
    have harena :
        arenaWord plans env n =
          arenaRecord plans
            (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl
              (chain, control, entry, state, minState))))))
            (env n) := by
      show arenaRecord plans (arenaFoldSeq plans env n) (env n) = _
      rw [hpos]
    cases hgraph : (env n).graph
    · refine ⟨?_, ?_, ?_⟩
      · rw [hexec, harena, oneSummaryAt_succ_left plans env n hgraph,
          twoSummaryAt_succ_left plans env n hgraph, hcore1, hcore2]
        simp only [oneRecvStep, twoNoRecvStep, arenaRecord, hgraph,
          TwoCore.isSubordinate, if_true, leftRoundRecord, RoundRecord.mk.injEq,
          and_true, true_and]
        exact htrace.head (env n).inputTwo
      · rw [hfold, oneSummaryAt_succ_left plans env n hgraph, hcore1, hcore2]
        simp only [arenaStep, hgraph, oneRecvStep, TwoCore.isSubordinate, if_true,
          revLeftContinueTarget, OneCoreTracks]
        exact ⟨_, rfl⟩
      · rw [hfold, twoSummaryAt_succ_left plans env n hgraph, hcore2]
        simp only [arenaStep, hgraph, twoNoRecvStep, revLeftContinueTarget,
          TwoCoreTracks]
        exact ⟨_, _, _, rfl, htrace.step (env n).inputTwo⟩
    · refine ⟨?_, ?_, ?_⟩
      · rw [hexec, harena, oneSummaryAt_succ_right plans env n hgraph,
          twoSummaryAt_succ_right plans env n hgraph, hcore1, hcore2]
        simp only [oneNoRecvStep, twoRecvStep, arenaRecord, hgraph,
          rightRoundRecord, RoundRecord.mk.injEq, and_true, true_and]
        rw [hchain]
        exact hcert.leftReReverseBlind control entry state minState bnd atom
          (env n).inputOne
      · rw [hfold, oneSummaryAt_succ_right plans env n hgraph, hcore1]
        simp only [arenaStep, hgraph, oneNoRecvStep, revLeftReverseTarget,
          OneCoreTracks, revLeftReverseEntry]
        rw [hchain]
        exact ⟨_, _, _, rfl,
          hcert.leftReReverseTrace control entry state minState bnd atom
            ((env n).inputOne, (env n).inputTwo)
            (hchain ▸ (arenaFoldSeq_reset plans env n).1 chain control entry state
              minState hpos)⟩
      · rw [hfold, twoSummaryAt_succ_right plans env n hgraph, hcore2, hcore1]
        simp only [arenaStep, hgraph, twoRecvStep, revLeftReverseTarget,
          TwoCoreTracks]
        exact ⟨_, rfl⟩
    · refine ⟨?_, ?_, ?_⟩
      · rw [hexec, harena, oneSummaryAt_succ_both plans env n hgraph,
          twoSummaryAt_succ_both plans env n hgraph, hcore1, hcore2]
        simp only [oneRecvStep, twoRecvStep, arenaRecord, hgraph,
          TwoCore.isSubordinate, if_true, bothRoundRecord, RoundRecord.mk.injEq,
          and_true, true_and]
      · rw [hfold, oneSummaryAt_succ_both plans env n hgraph, hcore1, hcore2]
        simp only [arenaStep, hgraph, oneRecvStep, TwoCore.isSubordinate, if_true,
          revLeftCloseTarget, OneCoreTracks]
        exact Or.inr (Or.inr ⟨_, rfl⟩)
      · rw [hfold, twoSummaryAt_succ_both plans env n hgraph, hcore2, hcore1]
        simp only [arenaStep, hgraph, twoRecvStep, revLeftCloseTarget,
          TwoCoreTracks]
        exact Or.inr (Or.inr ⟨_, rfl⟩)
  · obtain ⟨chain, control, entry, state, minState⟩ := inRevR
    rw [hpos] at h1 h2 hfold
    simp only [OneCoreTracks] at h1
    simp only [TwoCoreTracks] at h2
    obtain ⟨rplan, rc, frozen, hcore1, htrace⟩ := h1
    obtain ⟨bnd, hcore2⟩ := h2
    have hcommit :
        ChainCommittedAt plans
          (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
            (chain, control, entry, state, minState)))))) := by
      rw [← hpos]; exact chainCommittedAt_arenaFoldSeq plans env n
    simp only [ChainCommittedAt] at hcommit
    obtain ⟨atom, hchain⟩ := hcommit
    have harena :
        arenaWord plans env n =
          arenaRecord plans
            (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
              (chain, control, entry, state, minState))))))
            (env n) := by
      show arenaRecord plans (arenaFoldSeq plans env n) (env n) = _
      rw [hpos]
    cases hgraph : (env n).graph
    · refine ⟨?_, ?_, ?_⟩
      · rw [hexec, harena, oneSummaryAt_succ_left plans env n hgraph,
          twoSummaryAt_succ_left plans env n hgraph, hcore1, hcore2]
        simp only [oneRecvStep, twoNoRecvStep, arenaRecord, hgraph,
          leftRoundRecord, RoundRecord.mk.injEq, and_true, true_and]
        rw [hchain]
        exact hcert.rightReReverseBlind control entry state minState bnd atom
          (env n).inputTwo
      · rw [hfold, oneSummaryAt_succ_left plans env n hgraph, hcore1, hcore2]
        simp only [arenaStep, hgraph, oneRecvStep, revRightReverseTarget,
          OneCoreTracks]
        exact ⟨_, rfl⟩
      · rw [hfold, twoSummaryAt_succ_left plans env n hgraph, hcore2]
        simp only [arenaStep, hgraph, twoNoRecvStep, revRightReverseTarget,
          TwoCoreTracks, revRightReverseEntry]
        rw [hchain]
        exact ⟨_, _, _, rfl,
          hcert.rightReReverseTrace control entry state minState bnd atom
            ((env n).inputOne, (env n).inputTwo)
            (hchain ▸ (arenaFoldSeq_reset plans env n).2 chain control entry state
              minState hpos)⟩
    · refine ⟨?_, ?_, ?_⟩
      · rw [hexec, harena, oneSummaryAt_succ_right plans env n hgraph,
          twoSummaryAt_succ_right plans env n hgraph, hcore1, hcore2]
        simp only [oneNoRecvStep, twoRecvStep, arenaRecord, hgraph,
          OneCore.isSubordinate, if_true, rightRoundRecord, RoundRecord.mk.injEq,
          and_true, true_and]
        exact htrace.head (env n).inputOne
      · rw [hfold, oneSummaryAt_succ_right plans env n hgraph, hcore1]
        simp only [arenaStep, hgraph, oneNoRecvStep, revRightContinueTarget,
          OneCoreTracks]
        exact ⟨_, _, _, rfl, htrace.step (env n).inputOne⟩
      · rw [hfold, twoSummaryAt_succ_right plans env n hgraph, hcore2, hcore1]
        simp only [arenaStep, hgraph, twoRecvStep, OneCore.isSubordinate,
          revRightContinueTarget, TwoCoreTracks]
        exact ⟨_, rfl⟩
    · refine ⟨?_, ?_, ?_⟩
      · rw [hexec, harena, oneSummaryAt_succ_both plans env n hgraph,
          twoSummaryAt_succ_both plans env n hgraph, hcore1, hcore2]
        simp only [oneRecvStep, twoRecvStep, arenaRecord, hgraph,
          OneCore.isSubordinate, if_true, bothRoundRecord, RoundRecord.mk.injEq,
          and_true, true_and]
      · rw [hfold, oneSummaryAt_succ_both plans env n hgraph, hcore1, hcore2]
        simp only [arenaStep, hgraph, oneRecvStep, revRightCloseTarget,
          OneCoreTracks]
        exact Or.inr (Or.inr ⟨_, rfl⟩)
      · rw [hfold, twoSummaryAt_succ_both plans env n hgraph, hcore2, hcore1]
        simp only [arenaStep, hgraph, twoRecvStep, OneCore.isSubordinate,
          revRightCloseTarget, TwoCoreTracks]
        exact Or.inr (Or.inr ⟨_, rfl⟩)

/-- Both cores track the fold position at every round. -/
theorem journal_tracks
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂)
    (hnodirect : NoDirectReversalSequence env) (n : Nat) :
    OneCoreTracks (oneSummaryAt plans env n).2 (arenaFoldSeq plans env n) ∧
      TwoCoreTracks (twoSummaryAt plans env n).2
        (arenaFoldSeq plans env n) := by
  induction n with
  | zero => exact ⟨Or.inl rfl, Or.inl rfl⟩
  | succ n ih =>
      obtain ⟨h1, h2⟩ := ih
      exact ⟨(journal_step plans env hnodirect n h1 h2).2.1,
        (journal_step plans env hnodirect n h1 h2).2.2⟩

/--
The play correspondence (step H4c): on the no-direct fragment the
pasted strategy of a committed plan family plays exactly the arena
word.
-/
theorem execution_journalStrategy_eq_arenaWord
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂)
    (hnodirect : NoDirectReversalSequence env) :
    execution (journalStrategy plans) env = arenaWord plans env := by
  funext n
  obtain ⟨h1, h2⟩ := journal_tracks plans env hnodirect n
  exact (journal_step plans env hnodirect n h1 h2).1

/--
Full-model version of `journal_tracks`: both cores track the fold position at
every round, on every environment, from the entry-indexed certificate `hcert`
(no `NoDirectReversalSequence`).
-/
theorem journal_tracks_full
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂)
    (hcert : ReversalMeasurable plans) (n : Nat) :
    OneCoreTracks (oneSummaryAt plans env n).2 (arenaFoldSeq plans env n) ∧
      TwoCoreTracks (twoSummaryAt plans env n).2
        (arenaFoldSeq plans env n) := by
  induction n with
  | zero => exact ⟨Or.inl rfl, Or.inl rfl⟩
  | succ n ih =>
      obtain ⟨h1, h2⟩ := ih
      exact ⟨(journal_step_full plans env hcert n h1 h2).2.1,
        (journal_step_full plans env hcert n h1 h2).2.2⟩

/--
Full-model play correspondence: the pasted strategy of a committed plan family
plays exactly the arena word on every environment (no `NoDirectReversalSequence`),
given the entry-indexed certificate `hcert`.
-/
theorem execution_journalStrategy_eq_arenaWord_full
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂)
    (hcert : ReversalMeasurable plans) :
    execution (journalStrategy plans) env = arenaWord plans env := by
  funext n
  obtain ⟨h1, h2⟩ := journal_tracks_full plans env hcert n
  exact (journal_step_full plans env hcert n h1 h2).1

variable [Inhabited C_L] [Inhabited C_R] [Inhabited C_V]

/--
Fragment soundness of the journal readback (step H4d): a winning
positional Even strategy of the boundary game pastes, through the
candidate summaries of its committed plan family, to a distributed
strategy all of whose no-direct executions are accepted.  The pasted
strategy is by definition the readback of the local summary automaton
`journalSummaries (plansOf τ)` under the output-projection tables.
-/
theorem accepts_execution_journalStrategy_of_winning
    (τ :
      (DetParityAutomaton.boundaryGame A C_L C_R C_V).PositionalStrategy
        ParityPlayer.even)
    (hwin :
      CountableParityGame.PositionalStrategy.WinningFrom
        (G := DetParityAutomaton.boundaryGame A C_L C_R C_V) τ
        (Sum.inl (A.initial, A.initial)))
    (env : EnvironmentSequence In₁ In₂)
    (hnodirect : NoDirectReversalSequence env) :
    A.Accepts (execution (journalStrategy (plansOf τ)) env) := by
  rw [execution_journalStrategy_eq_arenaWord (plansOf τ) env hnodirect]
  exact accepts_arenaWord_of_winning τ hwin env

/--
Full-model soundness of the journal readback: a winning positional Even strategy
of the boundary game pastes to a distributed strategy all of whose executions —
on *every* environment, including direct reversals — are accepted, given the
entry-indexed measurability certificate for its plan family `plansOf τ`.
-/
theorem accepts_execution_journalStrategy_of_winning_full
    (τ :
      (DetParityAutomaton.boundaryGame A C_L C_R C_V).PositionalStrategy
        ParityPlayer.even)
    (hwin :
      CountableParityGame.PositionalStrategy.WinningFrom
        (G := DetParityAutomaton.boundaryGame A C_L C_R C_V) τ
        (Sum.inl (A.initial, A.initial)))
    (env : EnvironmentSequence In₁ In₂)
    (hcert : ReversalMeasurable (plansOf τ)) :
    A.Accepts (execution (journalStrategy (plansOf τ)) env) := by
  rw [execution_journalStrategy_eq_arenaWord_full (plansOf τ) env hcert]
  exact accepts_arenaWord_of_winning τ hwin env

end Correspondence

end DetParityAutomaton

end DistributedSynthesis
