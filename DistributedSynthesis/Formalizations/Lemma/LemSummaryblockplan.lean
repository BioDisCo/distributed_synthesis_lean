/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmSummaryFold

/-!
# Summary-controlled block plans

The realizing θ̄-fold (paper `prop:starcomplete`/`prop:starsound`) needs a plan family whose
block control **is** a summary state, so that its blind slot is a summary-indexed table shared
with the reversed-block chain -- unlike a generic plan, whose per-boundary controls differ and
force a constant (non-realizing) blind table (`globalFold`).  No such construction existed
(`journalSummaries` runs the other way, plan family -> automaton).

This file builds the missing primitive.  We parameterize by the summary *type* `S` with its own
`init`/`step`/output tables rather than by a `LocalSummaryAutomaton` directly -- this keeps the
*structural* `hmeas` (block-long agreement, which needs only a **shared** step/blind, not the
automaton's semantics) cleanly separated from `hsound` (which instantiates `S := M.Summary d`,
`step := M.stepNoRecv d`, and uses cross-reading), and it sidesteps a universe-`max`
polymorphism issue.  The two facts the shared-summary trace lemma needs -- that the plan's
`step` is the block step and its blind label is the given output -- hold by `rfl`.
-/

namespace DistributedSynthesis

universe u v x y s

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

namespace DetParityAutomaton

variable
  {A :
    DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂)}

/-- The summary-controlled **right** block plan: process one is the subordinate sender, so the
control is a process-one summary type `S` stepped by `step` on its own input; the blind slot is
the summary-indexed table `blindR`, and the informed slot / close / reversal outputs are
supplied. -/
def summaryRightBlockPlan
    (S : Type max u v x y s) (init : S) (step : S -> In₁ -> S)
    (blindR : S -> In₁ -> Out₁)
    (informedR : S -> (A.State × A.State) -> In₂ × In₁ -> Out₂)
    (closeR : S -> (A.State × A.State) -> In₂ × In₁ -> Out₁)
    (revR : S -> (A.State × A.State) -> In₂ -> Out₂) :
    RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) A S where
  init := init
  step := step
  label := fun s => (blindR s, informedR s)
  close := closeR
  rev := revR

/-- The summary-controlled **left** block plan: the orientation mirror, process two the
subordinate sender, control a process-two summary type `S`. -/
def summaryLeftBlockPlan
    (S : Type max u v x y s) (init : S) (step : S -> In₂ -> S)
    (blindL : S -> In₂ -> Out₂)
    (informedL : S -> (A.State × A.State) -> In₁ × In₂ -> Out₁)
    (closeL : S -> (A.State × A.State) -> In₁ × In₂ -> Out₂)
    (revL : S -> (A.State × A.State) -> In₁ -> Out₁) :
    LeftBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) A S where
  init := init
  step := step
  label := fun s => (blindL s, informedL s)
  close := closeL
  rev := revL

/-- The **summary chain**: `foldChain`, but its two re-reversal blind slots (`labelR.2.2.1`,
`labelL.2.1`) are overridden to the *constant fresh-opening* outputs `(L.label L.init).1`,
`(R.label R.init).1`.  A re-reversal is the reversing process's first send, so its output is the
block-opening output -- the same derived-output insight as `revL`/`revR`, now for the chain.
This makes the re-reversal blind obligations (`rightReReverseBlind`, `leftReReverseBlind`) hold
by `rfl`, while the trace slots (`labelR.2.1`, `labelL.2.2.1`) and the step/enter maps are kept
from `foldChain`, so the block-long trace agreements are unaffected. -/
def summaryChain {S₁ S₂ : Type max u v x y s}
    (L : LeftBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) A S₂)
    (R : RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) A S₁) :
    ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) A S₂ S₁ (S₂ ⊕ S₁) :=
  { foldChain L R with
    labelR := fun cv =>
      (((foldChain L R).labelR cv).1,
        ((foldChain L R).labelR cv).2.1,
        (fun _ i => (L.label L.init).1 i),
        ((foldChain L R).labelR cv).2.2.2)
    labelL := fun cv =>
      (((foldChain L R).labelL cv).1,
        (fun _ i => (R.label R.init).1 i),
        ((foldChain L R).labelL cv).2.2.1,
        ((foldChain L R).labelL cv).2.2.2) }

/-- The **summary-controlled plan family**: at every boundary atom, commit the fixed
summary-driven block plans and their `summaryChain`.  It is atom-independent -- the summary reads
the play's state from the view, so no per-atom commitment is needed -- which is exactly what
makes it `b_old`-invariant.  Control types are `(S₂, S₁, S₂ ⊕ S₁)`. -/
def summaryPlanFamily
    (S₁ S₂ : Type max u v x y s)
    (init₁ : S₁) (step₁ : S₁ -> In₁ -> S₁)
    (blindR : S₁ -> In₁ -> Out₁)
    (informedR : S₁ -> (A.State × A.State) -> In₂ × In₁ -> Out₂)
    (closeR : S₁ -> (A.State × A.State) -> In₂ × In₁ -> Out₁)
    (init₂ : S₂) (step₂ : S₂ -> In₂ -> S₂)
    (blindL : S₂ -> In₂ -> Out₂)
    (informedL : S₂ -> (A.State × A.State) -> In₁ × In₂ -> Out₁)
    (closeL : S₂ -> (A.State × A.State) -> In₁ × In₂ -> Out₂) :
    PlanFamily (In₁ := In₁) A S₂ S₁ (S₂ ⊕ S₁) :=
  -- The reversal outputs are **derived**, not free: a reversal round is the reversing process's
  -- *first* send (its send-summary is fresh `init`), so its output is the block-opening output.
  -- This builds `b_old`-invariance in and makes `PlanBlindMeasurable` hold by `rfl`.
  let revL : S₂ -> (A.State × A.State) -> In₁ -> Out₁ := fun _ _ i => blindR init₁ i
  let revR : S₁ -> (A.State × A.State) -> In₂ -> Out₂ := fun _ _ i => blindL init₂ i
  fun _ =>
    (summaryLeftBlockPlan (A := A) S₂ init₂ step₂ blindL informedL closeL revL,
      summaryRightBlockPlan (A := A) S₁ init₁ step₁ blindR informedR closeR revR,
      summaryChain (summaryLeftBlockPlan (A := A) S₂ init₂ step₂ blindL informedL closeL revL)
        (summaryRightBlockPlan (A := A) S₁ init₁ step₁ blindR informedR closeR revR))

/-- The chain control projects onto process one's summary: on the right (process-one) branch it
is the carried summary; on the left branch it defaults to the block init (the branch sends no
process-one round, so the value is unobserved -- and matches `foldChain.enterL = Sum.inr init`). -/
def summaryChainProjOne {S₁ S₂ : Type max u v x y s} (init₁ : S₁) :
    (S₂ ⊕ S₁) -> S₁
  | Sum.inl _ => init₁
  | Sum.inr s => s

/-- The chain control projects onto process two's summary: the orientation mirror. -/
def summaryChainProjTwo {S₁ S₂ : Type max u v x y s} (init₂ : S₂) :
    (S₂ ⊕ S₁) -> S₂
  | Sum.inl s => s
  | Sum.inr _ => init₂

end DetParityAutomaton

end DistributedSynthesis
