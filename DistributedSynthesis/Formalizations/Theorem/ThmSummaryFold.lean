/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmEntryIndexedReproducibility

/-!
# Blind trace-measurability by construction from a shared summary control

The block-long blind agreement `OneBlindTraceMeasurable`/`TwoBlindTraceMeasurable`
compares a subordinate block plan's blind slot, run along the process's own-input
word, against a reversed-block chain's blind slot run along the *same* word.  For
a blind table indexed on the abstract plan control the two control trajectories
`rightSubordinateControlAfter`/`chainSendControlAfter` diverge (they are folded by
different `step` maps), so the agreement is a genuine hypothesis -- the impasse of
`foldθ_leftTrace`, met only by a control-blind (constant) table (`globalFold`).

The resolution of the summary route is to give both the block plan and the chain
the **same** control dynamics -- a single summary step `stepS` -- and the **same**
summary-indexed blind table `b` (the chain slot ignoring the frozen entry, which
is what makes it entry-measurable at once).  Then the two trajectories are the
identical fold of the input word from a common control, so they coincide by an
elementary induction, and the two blind slots agree by `rfl`.  This is the
mechanism that turns block-long agreement from a hypothesis into a theorem, in
pure form: it is independent of how the plans are assembled and of the summary
automaton, requiring only the four defining equations below.  Instantiating
`stepS`/`b` with a `LocalSummaryAutomaton`'s `stepNoRecv`/output table -- so that
the shared control *is* the process's own view-summary -- is what makes the
committed family reversal-measurable while remaining realizing (the blind output
depends on the whole own-input word through the summary, not merely on the current
input as `globalFold` forces).  Paper `cor:blindcrossreading`/`prop:starcomplete`.
-/

namespace DistributedSynthesis

universe u v x y s c

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

namespace DetParityAutomaton

variable
  {A :
    DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂)}
  {C_L C_R : Type max u v x y s}

/--
Process one's block-long blind agreement holds by construction whenever the
subordinate right plan and the reversed-block chain compute the *same*
summary-indexed blind output.  The chain may carry a richer control `C_V` (e.g.
the joint summary pair, so one chain serves both orientations); it is linked to
the block plan's summary control `S` by a projection `π` compatible with the two
steps (`hstepV`) and starting aligned (`hπ`).  The chain slot ignores the frozen
entry (`hlabelV` has no `entry` dependence), so entry-measurability is automatic
and the block-long agreement is `rfl` after the two control trajectories are shown
to project onto one another.  With `C_V := S` and `π := id` this is the plain
"shared control" form.
-/
theorem oneBlindTraceMeasurable_of_sharedSummary
    {S C_V : Type max u v x y s}
    (rightplan :
      RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) A S)
    (chain :
      ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_L S C_V)
    (stepS : S -> In₁ -> S) (b : S -> In₁ -> Out₁) (π : C_V -> S)
    (hstepR : ∀ (cc : S) (i : In₁), rightplan.step cc i = stepS cc i)
    (hlabelR : ∀ cc : S, (rightplan.label cc).1 = b cc)
    (hstepV : ∀ (cc : C_V) (i : In₁), π (chain.step cc (Sum.inr i)) = stepS (π cc) i)
    (hlabelV :
      ∀ (cc : C_V) (entry : A.State × A.State), (chain.labelR cc).2.1 entry = b (π cc))
    (c : S) (cv : C_V) (hπ : π cv = c) (entry : A.State × A.State) :
    OneBlindTraceMeasurable (A := A) rightplan c chain cv entry := by
  have hctrl :
      ∀ (w : List In₁) (cc : C_V),
        rightSubordinateControlAfter rightplan (π cc) w =
          π (chainSendControlAfter chain cc w) := by
    intro w
    induction w with
    | nil => intro cc; rfl
    | cons j rest ih =>
        intro cc
        simp only [rightSubordinateControlAfter, chainSendControlAfter]
        rw [hstepR, ← hstepV]
        exact ih (chain.step cc (Sum.inr j))
  intro w i
  rw [hlabelR, hlabelV, ← hπ, hctrl]

/--
Process two's block-long blind agreement holds by construction: the orientation
mirror of `oneBlindTraceMeasurable_of_sharedSummary`, with a summary control
stepping on process two's own input and the chain's left slot ignoring the entry.
-/
theorem twoBlindTraceMeasurable_of_sharedSummary
    {S C_V : Type max u v x y s}
    (leftplan :
      LeftBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) A S)
    (chain :
      ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A S C_R C_V)
    (stepS : S -> In₂ -> S) (b : S -> In₂ -> Out₂) (π : C_V -> S)
    (hstepL : ∀ (cc : S) (i : In₂), leftplan.step cc i = stepS cc i)
    (hlabelL : ∀ cc : S, (leftplan.label cc).1 = b cc)
    (hstepV : ∀ (cc : C_V) (i : In₂), π (chain.step cc (Sum.inl i)) = stepS (π cc) i)
    (hlabelV :
      ∀ (cc : C_V) (entry : A.State × A.State),
        (chain.labelL cc).2.2.1 entry = b (π cc))
    (c : S) (cv : C_V) (hπ : π cv = c) (entry : A.State × A.State) :
    TwoBlindTraceMeasurable (A := A) leftplan c chain cv entry := by
  have hctrl :
      ∀ (w : List In₂) (cc : C_V),
        leftSubordinateControlAfter leftplan (π cc) w =
          π (chainSendControlAfterTwo chain cc w) := by
    intro w
    induction w with
    | nil => intro cc; rfl
    | cons j rest ih =>
        intro cc
        simp only [leftSubordinateControlAfter, chainSendControlAfterTwo]
        rw [hstepL, ← hstepV]
        exact ih (chain.step cc (Sum.inl j))
  intro w i
  rw [hlabelL, hlabelV, ← hπ, hctrl]

end DetParityAutomaton

end DistributedSynthesis
