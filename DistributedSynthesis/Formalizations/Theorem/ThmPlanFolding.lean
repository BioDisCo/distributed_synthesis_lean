/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmArenaFold

/-!
# Folding a committed plan family onto the entry thread

The measurability certificate `ReversalMeasurable` demands an *internal*
consistency of each committed `BoundaryPlan`: the reversed-block `ChainPlan`'s
blind slots must reproduce the block plans' blind outputs at the entry thread.
An arbitrary committed plan (e.g. `plansOf τ`) need not satisfy this — the block
plans and the chain are independent fields.

The fold below replaces the committed chain by one that literally *replays* the
committed block plans (paper `prop:starcomplete`): the reversed-right block runs
the right block plan, the reversed-left block runs the left block plan, and a
re-reversal switches orientation by restarting the other plan.  With the chain
control tied to the block control (`C_V = C_L ⊕ C_R`), every blind slot equals a
block-plan blind output *by construction*, so `ReversalMeasurable` will hold
definitionally.  Realization-preservation of the fold is the separate
substantive step.
-/

namespace DistributedSynthesis

universe u v x y s

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

namespace DetParityAutomaton

variable
  {A :
    DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂)}
  {C_L C_R : Type max u v x y s}

/--
The folded chain plan on `C_V = C_L ⊕ C_R`: it replays the committed block
plans.  A reversed-right block (control `Sum.inr c_R`) runs `rightPlan`; a
reversed-left block (control `Sum.inl c_L`) runs `leftPlan`; a re-reversal
switches orientation, restarting the other plan from its `init`.  The blind
slots (`labelR .2.1`, `labelL .2.2.1`, entry-indexed by type) are exactly the
block plans' blind outputs, which makes the entry-indexed agreements hold by
`rfl`.
-/
def foldChain
    (leftPlan :
      LeftBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_L)
    (rightPlan :
      RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_R) :
    ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
      A C_L C_R (C_L ⊕ C_R) where
  enterL := fun _ => Sum.inr rightPlan.init
  enterR := fun _ => Sum.inl leftPlan.init
  step := fun cv d =>
    match cv, d with
    | Sum.inr c_R, Sum.inr i₁ => Sum.inr (rightPlan.step c_R i₁)
    | Sum.inr _, Sum.inl i₂ => Sum.inl (leftPlan.step leftPlan.init i₂)
    | Sum.inl c_L, Sum.inl i₂ => Sum.inl (leftPlan.step c_L i₂)
    | Sum.inl _, Sum.inr i₁ => Sum.inr (rightPlan.step rightPlan.init i₁)
  labelL := fun cv =>
    match cv with
    | Sum.inl c_L =>
        (fun q move => (leftPlan.label c_L).2 q.2 move,
          fun _ i => (rightPlan.label rightPlan.init).1 i,
          fun _ i => (leftPlan.label c_L).1 i,
          fun q move => leftPlan.close c_L q.2 move)
    | Sum.inr c_R =>
        (fun q move => leftPlan.rev leftPlan.init q.2 move.1,
          fun _ i => (rightPlan.label c_R).1 i,
          fun _ i => (leftPlan.label leftPlan.init).1 i,
          fun q move => (rightPlan.label c_R).2 q.2 (move.2, move.1))
  labelR := fun cv =>
    match cv with
    | Sum.inr c_R =>
        (fun q move => rightPlan.close c_R q.2 (move.2, move.1),
          fun _ i => (rightPlan.label c_R).1 i,
          fun _ i => (leftPlan.label leftPlan.init).1 i,
          fun q move => (rightPlan.label c_R).2 q.2 (move.2, move.1))
    | Sum.inl c_L =>
        (fun q move => leftPlan.rev c_L q.2 move.1,
          fun _ i => (rightPlan.label rightPlan.init).1 i,
          fun _ i => (leftPlan.label c_L).1 i,
          fun q move => leftPlan.close c_L q.2 move)

/-- Overwrite a right block plan's two blind slots by shared tables: the
subordinate slot (`label .1`, process one's own-input output when process one is
the right-block subordinate sender) by `t_R`, and the reversal slot (`rev`,
process two's output when the right block directly reverses) by `t_L`.  The
informed receiver table `label .2`, the control transition, and `close` are
untouched. -/
def overwriteRightBlind (t_R : In₁ -> Out₁) (t_L : In₂ -> Out₂)
    (rp :
      RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_R) :
    RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
      A C_R :=
  { rp with label := fun c => (t_R, (rp.label c).2), rev := fun _ _ i => t_L i }

/-- Overwrite a left block plan's two blind slots by shared tables: the
subordinate slot (`label .1`, process two's output as left-block subordinate
sender) by `t_L`, and the reversal slot (`rev`, process one's output when the
left block directly reverses) by `t_R`: the orientation mirror of
`overwriteRightBlind`. -/
def overwriteLeftBlind (t_L : In₂ -> Out₂) (t_R : In₁ -> Out₁)
    (lp :
      LeftBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_L) :
    LeftBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
      A C_L :=
  { lp with label := fun c => (t_L, (lp.label c).2), rev := fun _ _ i => t_R i }

@[simp] theorem overwriteRightBlind_blind (t_R : In₁ -> Out₁) (t_L : In₂ -> Out₂)
    (rp :
      RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_R)
    (c : C_R) : ((overwriteRightBlind t_R t_L rp).label c).1 = t_R := rfl

@[simp] theorem overwriteRightBlind_rev (t_R : In₁ -> Out₁) (t_L : In₂ -> Out₂)
    (rp :
      RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_R)
    (c : C_R) (q : A.State × A.State) :
    (overwriteRightBlind t_R t_L rp).rev c q = fun i => t_L i := rfl

@[simp] theorem overwriteLeftBlind_blind (t_L : In₂ -> Out₂) (t_R : In₁ -> Out₁)
    (lp :
      LeftBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_L)
    (c : C_L) : ((overwriteLeftBlind t_L t_R lp).label c).1 = t_L := rfl

@[simp] theorem overwriteLeftBlind_rev (t_L : In₂ -> Out₂) (t_R : In₁ -> Out₁)
    (lp :
      LeftBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_L)
    (c : C_L) (q : A.State × A.State) :
    (overwriteLeftBlind t_L t_R lp).rev c q = fun i => t_R i := rfl

variable
  {C_V : Type max u v x y s}

/--
The folded plan family: keep each atom's committed block plans, replace its
chain by `foldChain` of those block plans.  The control type becomes
`C_L ⊕ C_R`.
-/
def foldPlanFamily
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V) :
    PlanFamily (In₁ := In₁) A C_L C_R (C_L ⊕ C_R) :=
  fun atom =>
    ((plans atom).1, (plans atom).2.1,
      foldChain (plans atom).1 (plans atom).2.1)

/--
The **global** fold: overwrite every atom's block-plan blind slots by two shared
tables `t_L, t_R` and replay the overwritten plans through `foldChain`.  Unlike
`foldPlanFamily`, whose per-atom chain reproduces only *that atom's* blind
outputs, the global fold makes the successor boundary's block plan and the
opening boundary's chain read one and the same table, so the cross-boundary
agreement `cor:blindcrossreading` holds *by construction* (paper
`rem:globalblindtable`).  The tables are parameters; that a realizing pair
`(t_L, t_R)` exists is `prop:starcomplete`, proved separately.
-/
def globalFold (t_L : In₂ -> Out₂) (t_R : In₁ -> Out₁)
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V) :
    PlanFamily (In₁ := In₁) A C_L C_R (C_L ⊕ C_R) :=
  fun atom =>
    (overwriteLeftBlind t_L t_R (plans atom).1,
      overwriteRightBlind t_R t_L (plans atom).2.1,
      foldChain (overwriteLeftBlind t_L t_R (plans atom).1)
        (overwriteRightBlind t_R t_L (plans atom).2.1))

/-! ### The control-dependent (word-indexed) fold `foldθ`

`globalFold` folds the blind slots onto a *constant* table, which is measurable but
never realizing: a realizing blind side plays the entry-indexed table
`t_{\bar\theta}` (`def:entrythread`), whose output depends on the own-input *word*,
not merely a constant.  In the Mealy form of the plan, word-dependence is
control-dependence, so a realizing fold overwrites each blind slot by a function of
the plan's *control*.  The functions are the outputs of the shared
`\bar\theta`-monitor; here they are parameters.  Cross-boundary agreement is no
longer by `rfl` -- it is the word-indexed agreement of
`foldChain_oneBlindTraceMeasurable_agree`, discharged from the monitor's
determinism plus `cor:blindcrossreading` (both plans track one `\bar\theta` from a
common entry). -/

/-- Overwrite a right block plan's two blind slots by control-dependent functions:
`bR c` is the subordinate output at control `c`, `bL c` the reversal output. -/
def overwriteRightBlindF (bR : C_R -> In₁ -> Out₁) (bL : C_R -> In₂ -> Out₂)
    (rp :
      RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_R) :
    RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
      A C_R :=
  { rp with label := fun c => (bR c, (rp.label c).2), rev := fun c _ i => bL c i }

/-- Overwrite a left block plan's two blind slots by control-dependent functions:
the orientation mirror of `overwriteRightBlindF`. -/
def overwriteLeftBlindF (bL : C_L -> In₂ -> Out₂) (bR : C_L -> In₁ -> Out₁)
    (lp :
      LeftBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_L) :
    LeftBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
      A C_L :=
  { lp with label := fun c => (bL c, (lp.label c).2), rev := fun c _ i => bR c i }

@[simp] theorem overwriteRightBlindF_blind (bR : C_R -> In₁ -> Out₁)
    (bL : C_R -> In₂ -> Out₂)
    (rp :
      RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_R)
    (c : C_R) : ((overwriteRightBlindF bR bL rp).label c).1 = bR c := rfl

@[simp] theorem overwriteLeftBlindF_blind (bL : C_L -> In₂ -> Out₂)
    (bR : C_L -> In₁ -> Out₁)
    (lp :
      LeftBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_L)
    (c : C_L) : ((overwriteLeftBlindF bL bR lp).label c).1 = bL c := rfl

/-- The control-dependent fold: overwrite every atom's block-plan blind slots by
the shared control-indexed functions and replay through `foldChain`.  With
`bL`/`bR` constant this is `globalFold`; with them the outputs of the shared
`\bar\theta`-monitor it is the realizing fold, whose cross-boundary agreement is
`cor:blindcrossreading`. -/
def foldθ
    (bLl : C_L -> In₂ -> Out₂) (bRl : C_L -> In₁ -> Out₁)
    (bRr : C_R -> In₁ -> Out₁) (bLr : C_R -> In₂ -> Out₂)
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V) :
    PlanFamily (In₁ := In₁) A C_L C_R (C_L ⊕ C_R) :=
  fun atom =>
    (overwriteLeftBlindF bLl bRl (plans atom).1,
      overwriteRightBlindF bRr bLr (plans atom).2.1,
      foldChain (overwriteLeftBlindF bLl bRl (plans atom).1)
        (overwriteRightBlindF bRr bLr (plans atom).2.1))

/-! ### Chain provenance

Every block plan and chain appearing in an arena position of a plan family `plans`
is a component committed by `plans` at some boundary atom.  This is what lets the
measurability certificate reference `(plans atom).*` rather than the opaque chain
that `journal_step_full` carries: the chain is set once, at block opening, and
threaded unchanged through continue / reverse / re-reverse rounds. -/

/-- The position's block plan and chain are components of one committed
`BoundaryPlan` of `plans`. -/
def ChainCommittedAt
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V) :
    BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V -> Prop
  | Sum.inl _ => True
  | Sum.inr (Sum.inl _) => True
  | Sum.inr (Sum.inr (Sum.inl (plan, chain, _, _, _))) =>
      ∃ atom, plan = (plans atom).1 ∧ chain = (plans atom).2.2
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl (plan, chain, _, _, _)))) =>
      ∃ atom, plan = (plans atom).2.1 ∧ chain = (plans atom).2.2
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (chain, _, _, _, _))))) =>
      ∃ atom, chain = (plans atom).2.2
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (chain, _, _, _, _))))) =>
      ∃ atom, chain = (plans atom).2.2

/-- `arenaStep` preserves chain provenance: a boundary opens with a committed
plan, every within-block round keeps the same chain. -/
theorem chainCommittedAt_arenaStep
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (position : BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V)
    (envRound : EnvironmentRound In₁ In₂)
    (h : ChainCommittedAt plans position) :
    ChainCommittedAt plans (arenaStep plans position envRound) := by
  rcases position with
    ⟨state, minState⟩ | committed |
      ⟨plan, chain, control, state, minState⟩ |
      ⟨plan, chain, control, state, minState⟩ |
      ⟨chain, control, entry, state, minState⟩ |
      ⟨chain, control, entry, state, minState⟩
  · -- S1 boundary: opens a block (left/right) or a committed tier (both)
    simp only [arenaStep]
    cases envRound.graph <;>
      simp only [ChainCommittedAt, boundaryOpenLeftTarget, boundaryOpenRightTarget,
        boundaryBothTarget]
    · exact ⟨_, rfl, rfl⟩
    · exact ⟨_, rfl, rfl⟩
  · -- S2 committed tier: self-loop
    simp only [arenaStep, ChainCommittedAt]
  · -- S3 within-left: continue (keep) / reverse (keep chain) / close (boundary)
    obtain ⟨atom, hp, hc⟩ := h
    simp only [arenaStep]
    cases envRound.graph <;>
      simp only [ChainCommittedAt, leftContinueTarget, leftCloseTarget,
        leftReverseTarget]
    · exact ⟨atom, hp, hc⟩
    · exact ⟨atom, hc⟩
  · -- S4 within-right
    obtain ⟨atom, hp, hc⟩ := h
    simp only [arenaStep]
    cases envRound.graph <;>
      simp only [ChainCommittedAt, rightContinueTarget, rightCloseTarget,
        rightReverseTarget]
    · exact ⟨atom, hc⟩
    · exact ⟨atom, hp, hc⟩
  · -- S5 reversed-left
    obtain ⟨atom, hc⟩ := h
    simp only [arenaStep]
    cases envRound.graph <;>
      simp only [ChainCommittedAt, revLeftContinueTarget, revLeftCloseTarget,
        revLeftReverseTarget]
    · exact ⟨atom, hc⟩
    · exact ⟨atom, hc⟩
  · -- S6 reversed-right
    obtain ⟨atom, hc⟩ := h
    simp only [arenaStep]
    cases envRound.graph <;>
      simp only [ChainCommittedAt, revRightContinueTarget, revRightCloseTarget,
        revRightReverseTarget]
    · exact ⟨atom, hc⟩
    · exact ⟨atom, hc⟩

/-- Chain provenance holds along the whole arena fold. -/
theorem chainCommittedAt_arenaFoldSeq
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    ChainCommittedAt plans (arenaFoldSeq plans env n) := by
  induction n with
  | zero => exact trivial
  | succ n ih =>
      rw [arenaFoldSeq]
      exact chainCommittedAt_arenaStep plans _ (env n) ih

end DetParityAutomaton

end DistributedSynthesis
