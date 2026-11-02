/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFringeelim

/-!
# The delayed-hierarchy winning game (`delayed_dynamic.tex`, `thm:main` + `lem:fringe`)

This file combines the two standalone results of the delayed-dynamic development into
the intended winning-game theorem:

* `lem:delayonehierarchy` (`LemDelayonehierarchy.lean`): the two processes' information
  about the *settled* past is totally ordered by refinement -- the informed side's
  current observation determines the blind side's prefix, with delay one.  The
  mechanism is the receive semantics of `def:views`: a receive stores the sender's
  **entire** prior view, so the current observation embeds the whole settled history.

* `lem:fringeelim` (`LemFringeelim.lean`): over traces on which the older fringe values
  are **recoverable** from the history, a winning fringe-dependent strategy pair exists
  iff a winning fringe-*free* (contingent) pair exists -- one committed continuation per
  current fringe value (`fringeElim_winning_iff`).

The bridge is that the delay-one hierarchy *discharges* the recoverability hypothesis
of fringe elimination.  We model the delay-one property structurally: an observation is
a pair `(o, past)` whose second component is the settled past-fringe list the informed
view already exposes (paper: the nested `View.recv` payload).  The recoverer
`recoverEmbedded` reads that list off the current observation; then
`RecoveredBy`/`PairRecoveredBy` hold by `List.getLast?_concat`, with no side condition
beyond the trace being *self-embedding* -- exactly what a delay-one-hierarchical play is.

The payoff, `delayedHierarchyWinningGame`, is the winning-game form: for a
delay-one-hierarchical game (observations embedding the settled past), realizability by a
fringe-dependent strategy is equivalent to realizability by a finite-fringe-measurable
one.  The blind side's committed action is thereby a contingent action over the current
fringe alone -- the fringe-free (strict-hierarchical) game the decision procedure needs.
-/

namespace DistributedSynthesis

universe u₁ u₂ v₁ v₂ w₁ w₂

/-- A **delay-one observation** for a process: the settled increment `o` together with the
list `past` of already-resolved fringe values the informed view exposes (the nested
`View.recv` payload of `def:views`).  This is the structural content of the delay-one
hierarchy: the current observation carries the whole settled past. -/
abbrev DelayOneObs (O : Type u₁) (R : Type v₁) := O × List R

/-- Read the settled past-fringe list off the **current** (last) observation.  This is the
recoverer the delay-one hierarchy supplies: the informed side's current view already
exposes every resolved past fringe, so no reconstruction beyond reading the last
observation is needed. -/
def recoverEmbedded {O : Type u₁} {R : Type v₁}
    (history : List (DelayOneObs O R)) : List R :=
  match history.getLast? with
  | none => []
  | some obs => obs.2

@[simp]
theorem recoverEmbedded_concat {O : Type u₁} {R : Type v₁}
    (history : List (DelayOneObs O R)) (obs : DelayOneObs O R) :
    recoverEmbedded (history ++ [obs]) = obs.2 := by
  simp [recoverEmbedded, List.getLast?_concat]

/-- A play is **delay-one-hierarchical** when each round's observation embeds exactly the
fringe values already played -- i.e. the informed view exposes the whole settled past
(the nested `View.recv` payload of `def:views`; `lem:delayonehierarchy`).  This is the
structural content the delay-one hierarchy supplies to fringe elimination. -/
def SelfEmbedding
    {O₁ : Type u₁} {O₂ : Type u₂} {R₁ : Type v₁} {R₂ : Type v₂}
    (pastOne : List R₁) (pastTwo : List R₂)
    (trace :
      List (FringeObservationStep (DelayOneObs O₁ R₁) (DelayOneObs O₂ R₂) R₁ R₂)) :
    Prop :=
  match trace with
  | [] => True
  | step :: rest =>
      step.historyOne.2 = pastOne ∧ step.historyTwo.2 = pastTwo ∧
        SelfEmbedding (pastOne ++ [step.fringeOne]) (pastTwo ++ [step.fringeTwo]) rest

/-- **The delay-one hierarchy discharges fringe-recoverability.**  For the delay-one
recoverer `recoverEmbedded`, `PairRecoveredBy` holds along a trace exactly when the trace
is delay-one-hierarchical (`SelfEmbedding`): reading the settled past off the current
observation is faithful precisely when the observation embeds it.  The `histOne`/`histTwo`
prefixes are irrelevant -- `recoverEmbedded` reads only the current observation
(`recoverEmbedded_concat`), the concrete meaning of "delay one". -/
theorem pairRecoveredBy_recoverEmbedded_iff
    {O₁ : Type u₁} {O₂ : Type u₂} {R₁ : Type v₁} {R₂ : Type v₂}
    (histOne : List (DelayOneObs O₁ R₁)) (histTwo : List (DelayOneObs O₂ R₂))
    (pastOne : List R₁) (pastTwo : List R₂)
    (trace :
      List (FringeObservationStep (DelayOneObs O₁ R₁) (DelayOneObs O₂ R₂) R₁ R₂)) :
    PairRecoveredBy recoverEmbedded recoverEmbedded
        histOne histTwo pastOne pastTwo trace ↔
      SelfEmbedding pastOne pastTwo trace := by
  induction trace generalizing histOne histTwo pastOne pastTwo with
  | nil => exact Iff.rfl
  | cons step rest ih =>
      unfold PairRecoveredBy SelfEmbedding
      rw [recoverEmbedded_concat, recoverEmbedded_concat, ih]

section WinningGame

variable {O₁ : Type u₁} {O₂ : Type u₂} {R₁ : Type v₁} {R₂ : Type v₂}
  {Out₁ : Type w₁} {Out₂ : Type w₂}

/-- A **fringe-dependent** strategy pair *wins the delay-one-hierarchical game*: it meets
the finite-trace spec on every delay-one-hierarchical play (`SelfEmbedding`).  The blind
side may consult the whole history, including older fringe values. -/
def DelayOneWins
    (spec : OutputTraceSpec Out₁ Out₂)
    (σ : FringeStrategyPair (DelayOneObs O₁ R₁) (DelayOneObs O₂ R₂) R₁ R₂ Out₁ Out₂) :
    Prop :=
  ∀ trace :
      List (FringeObservationStep (DelayOneObs O₁ R₁) (DelayOneObs O₂ R₂) R₁ R₂),
    SelfEmbedding [] [] trace ->
      spec (originalPairOutputsFrom σ [] [] [] [] trace)

/-- A **fringe-free** (contingent) strategy pair wins the delay-one-hierarchical game: its
action is one committed continuation per *current* fringe value, with no dependence on the
older fringe values -- the strict-hierarchical strategy the decision procedure produces. -/
def DelayOneWinsContingent
    (spec : OutputTraceSpec Out₁ Out₂)
    (σ :
      ContingentStrategyPair (DelayOneObs O₁ R₁) (DelayOneObs O₂ R₂) R₁ R₂ Out₁ Out₂) :
    Prop :=
  ∀ trace :
      List (FringeObservationStep (DelayOneObs O₁ R₁) (DelayOneObs O₂ R₂) R₁ R₂),
    SelfEmbedding [] [] trace ->
      spec (contingentPairOutputsFrom σ [] [] trace)

theorem delayOneWins_iff_originalWinsRecoverable
    (spec : OutputTraceSpec Out₁ Out₂)
    (σ : FringeStrategyPair (DelayOneObs O₁ R₁) (DelayOneObs O₂ R₂) R₁ R₂ Out₁ Out₂) :
    DelayOneWins spec σ ↔
      OriginalWinsRecoverable recoverEmbedded recoverEmbedded spec σ := by
  unfold DelayOneWins OriginalWinsRecoverable
  exact forall_congr' fun trace =>
    imp_congr_left (pairRecoveredBy_recoverEmbedded_iff [] [] [] [] trace).symm

theorem delayOneWinsContingent_iff_contingentWinsRecoverable
    (spec : OutputTraceSpec Out₁ Out₂)
    (σ :
      ContingentStrategyPair (DelayOneObs O₁ R₁) (DelayOneObs O₂ R₂) R₁ R₂ Out₁ Out₂) :
    DelayOneWinsContingent spec σ ↔
      ContingentWinsRecoverable recoverEmbedded recoverEmbedded spec σ := by
  unfold DelayOneWinsContingent ContingentWinsRecoverable
  exact forall_congr' fun trace =>
    imp_congr_left (pairRecoveredBy_recoverEmbedded_iff [] [] [] [] trace).symm

/-- **The delayed-hierarchy winning game** (`delayed_dynamic.tex`, `thm:main`).  In a
delay-one-hierarchical game -- observations embedding the settled past, `lem:delayonehierarchy`
-- a *fringe-dependent* strategy pair wins iff a *fringe-free* (contingent) one does.  The
forward direction is the substantive one: the delay-one hierarchy makes the older fringe
values recoverable from the history (`recoverEmbedded`, `pairRecoveredBy_recoverEmbedded_iff`),
so `lem:fringeelim` (`fringeElim_winning_iff`) replaces each blind action by a finite
contingent action over the *current* fringe -- collapsing the game to the strict-hierarchical
one a decision procedure handles.  Direct reversals contribute exactly such a fringe (the
one-bit acknowledgement, `thm:onebitfringe`), so this is the paper mechanism by which the
`{←,→,↔}` model's blind commitment is made finite and leader-agnostic. -/
theorem delayedHierarchyWinningGame (spec : OutputTraceSpec Out₁ Out₂) :
    (∃ σ :
        FringeStrategyPair (DelayOneObs O₁ R₁) (DelayOneObs O₂ R₂) R₁ R₂ Out₁ Out₂,
      DelayOneWins spec σ) ↔
    (∃ σ :
        ContingentStrategyPair (DelayOneObs O₁ R₁) (DelayOneObs O₂ R₂) R₁ R₂ Out₁ Out₂,
      DelayOneWinsContingent spec σ) := by
  simp only [delayOneWins_iff_originalWinsRecoverable,
    delayOneWinsContingent_iff_contingentWinsRecoverable]
  exact fringeElim_winning_iff recoverEmbedded recoverEmbedded spec

end WinningGame

end DistributedSynthesis
