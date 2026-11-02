/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemArenaSuffixTransport
import DistributedSynthesis.Formalizations.Lemma.LemSummaryreversalmeasurable

/-!
# The atom-indexed table family extracted from a committed plan family

the concrete
summary tables read literally from a plan family's finitely many committed
plans.  The summary state of the subordinate sender is a pair of the boundary
atom coordinate and the committed block-plan control at that atom
(`(A.State × A.State) × C_R` on the right, `(A.State × A.State) × C_L` on the
left), stepped by the sender's own input through the committed plan's own
`step`.  All six tables (`tableBlindR`/`tableInformedR`/`tableCloseR` and the
left mirrors) evaluate the plans of `G` -- for a boundary-game winner `τ` the
intended instance is `G := plansOf τ`, so **every table value comes from `τ`'s
finite committed plans**, never from a raw strategy.  This is the finiteness
quotient: the summary spaces are finite whenever `A.State` and the controls
are (the `Fintype` instances are inferred), and

* `tableFamily` is a `summaryPlanFamily`, so its `hmeas` is unconditional
  (`tableFamily_reversalMeasurable`, via
  `summaryPlanFamily_reversalMeasurable`);
* `RightTableSim`/`LeftTableSim` generalize the brick-8 replay simulations
  **across atoms**: at coordinate `a` the table family's in-block and
  reversed-block runs emit, round for round, the records of the *real*
  atom-dependent reference `G` in the block committed at `a`, with equal
  records on every non-reversal round, step preservation, agreement of the
  closing target atom, and suffix-word equality on a one-orientation
  environment.  The reference is `G` itself, not a constant representative:
  this is exactly the multi-block item (ii) left open by
  `LemArenaReplaySimulation`.

This module does not include the packaging of the
summary data as a `LocalSummaryAutomaton` feeding `summaryFold`.  The arena
route reads only the summary types, `init`, and the no-receive step, all
defined here; a genuine `stepRecv` (the θ̄ update at a receive) is readback
semantics that belongs to the `hsound` discharge, and a placeholder would be
dead code.  Likewise the alignment of the entry coordinate with the epoch's
entry atom is the per-epoch re-cut of `LemEpochRecut`, consuming
`LemEpochArenaCuts`; the simulations here keep the entry free.
-/

namespace DistributedSynthesis

universe u v x y s

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

namespace DetParityAutomaton

variable {A : DetParityAutomaton.{max u v x y, s} (RoundRecord In₁ In₂ Graph Out₁ Out₂)}
variable {C_L C_R C_V : Type max u v x y s}

/-- The initial process-one table summary: the initial boundary atom with the
right-plan control committed there. -/
def tableInitOne (G : PlanFamily (In₁ := In₁) A C_L C_R C_V) :
    (A.State × A.State) × C_R :=
  ((A.initial, A.initial), (G (A.initial, A.initial)).2.1.init)

/-- The process-one table summary steps by the sender's own input through the
committed right plan's step; the atom coordinate is carried unchanged. -/
def tableStepOne (G : PlanFamily (In₁ := In₁) A C_L C_R C_V) :
    (A.State × A.State) × C_R -> In₁ -> (A.State × A.State) × C_R :=
  fun s i => (s.1, (G s.1).2.1.step s.2 i)

/-- The blind right table: the committed right plan's blind label at the
carried atom and control. -/
def tableBlindR (G : PlanFamily (In₁ := In₁) A C_L C_R C_V) :
    (A.State × A.State) × C_R -> In₁ -> Out₁ :=
  fun s i => ((G s.1).2.1.label s.2).1 i

/-- The informed right table: the committed right plan's informed label. -/
def tableInformedR (G : PlanFamily (In₁ := In₁) A C_L C_R C_V) :
    (A.State × A.State) × C_R -> (A.State × A.State) -> In₂ × In₁ -> Out₂ :=
  fun s q m => ((G s.1).2.1.label s.2).2 q m

/-- The closing right table: the committed right plan's closing table. -/
def tableCloseR (G : PlanFamily (In₁ := In₁) A C_L C_R C_V) :
    (A.State × A.State) × C_R -> (A.State × A.State) -> In₂ × In₁ -> Out₁ :=
  fun s q m => (G s.1).2.1.close s.2 q m

/-- The initial process-two table summary: the orientation mirror of
`tableInitOne`. -/
def tableInitTwo (G : PlanFamily (In₁ := In₁) A C_L C_R C_V) :
    (A.State × A.State) × C_L :=
  ((A.initial, A.initial), (G (A.initial, A.initial)).1.init)

/-- The process-two table summary step: the orientation mirror of
`tableStepOne`. -/
def tableStepTwo (G : PlanFamily (In₁ := In₁) A C_L C_R C_V) :
    (A.State × A.State) × C_L -> In₂ -> (A.State × A.State) × C_L :=
  fun s i => (s.1, (G s.1).1.step s.2 i)

/-- The blind left table: the orientation mirror of `tableBlindR`. -/
def tableBlindL (G : PlanFamily (In₁ := In₁) A C_L C_R C_V) :
    (A.State × A.State) × C_L -> In₂ -> Out₂ :=
  fun s i => ((G s.1).1.label s.2).1 i

/-- The informed left table: the orientation mirror of `tableInformedR`. -/
def tableInformedL (G : PlanFamily (In₁ := In₁) A C_L C_R C_V) :
    (A.State × A.State) × C_L -> (A.State × A.State) -> In₁ × In₂ -> Out₁ :=
  fun s q m => ((G s.1).1.label s.2).2 q m

/-- The closing left table: the orientation mirror of `tableCloseR`. -/
def tableCloseL (G : PlanFamily (In₁ := In₁) A C_L C_R C_V) :
    (A.State × A.State) × C_L -> (A.State × A.State) -> In₁ × In₂ -> Out₂ :=
  fun s q m => (G s.1).1.close s.2 q m

/-- The table-controlled right block plan: `summaryRightBlockPlan` on the
atom-indexed summary, with the reversal slot derived as the left fresh-opening
output, as `summaryPlanFamily` prescribes. -/
def tableRightPlan (G : PlanFamily (In₁ := In₁) A C_L C_R C_V) :
    RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) A
      ((A.State × A.State) × C_R) :=
  summaryRightBlockPlan (A := A) ((A.State × A.State) × C_R) (tableInitOne G)
    (tableStepOne G) (tableBlindR G) (tableInformedR G) (tableCloseR G)
    (fun _ _ i => tableBlindL G (tableInitTwo G) i)

/-- The table-controlled left block plan: the orientation mirror of
`tableRightPlan`. -/
def tableLeftPlan (G : PlanFamily (In₁ := In₁) A C_L C_R C_V) :
    LeftBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) A
      ((A.State × A.State) × C_L) :=
  summaryLeftBlockPlan (A := A) ((A.State × A.State) × C_L) (tableInitTwo G)
    (tableStepTwo G) (tableBlindL G) (tableInformedL G) (tableCloseL G)
    (fun _ _ i => tableBlindR G (tableInitOne G) i)

/-- The table chain: the summary chain of the two table-controlled block
plans.  Its reversed branches replay the committed plans of the carried atom
coordinate -- the θ̄-indexed eternal replay. -/
def tableChain (G : PlanFamily (In₁ := In₁) A C_L C_R C_V) :
    ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) A
      ((A.State × A.State) × C_L) ((A.State × A.State) × C_R)
      (((A.State × A.State) × C_L) ⊕ ((A.State × A.State) × C_R)) :=
  summaryChain (tableLeftPlan G) (tableRightPlan G)

/-- The **atom-indexed table family**: the summary plan family whose tables
are extracted from `G`'s committed plans.  For `G := plansOf τ` every table
value comes from `τ`'s finite committed plans. -/
def tableFamily (G : PlanFamily (In₁ := In₁) A C_L C_R C_V) :
    PlanFamily (In₁ := In₁) A ((A.State × A.State) × C_L)
      ((A.State × A.State) × C_R)
      (((A.State × A.State) × C_L) ⊕ ((A.State × A.State) × C_R)) :=
  summaryPlanFamily (A := A) ((A.State × A.State) × C_R)
    ((A.State × A.State) × C_L)
    (tableInitOne G) (tableStepOne G) (tableBlindR G) (tableInformedR G)
    (tableCloseR G)
    (tableInitTwo G) (tableStepTwo G) (tableBlindL G) (tableInformedL G)
    (tableCloseL G)

@[simp]
theorem tableFamily_apply (G : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (atom : A.State × A.State) :
    tableFamily G atom = (tableLeftPlan G, tableRightPlan G, tableChain G) :=
  rfl

/-- **The table family's `hmeas` is unconditional**: it is a summary plan
family, so `summaryPlanFamily_reversalMeasurable` applies verbatim. -/
theorem tableFamily_reversalMeasurable
    (G : PlanFamily (In₁ := In₁) A C_L C_R C_V) :
    ReversalMeasurable (tableFamily G) :=
  summaryPlanFamily_reversalMeasurable (A := A) ((A.State × A.State) × C_R)
    ((A.State × A.State) × C_L)
    (tableInitOne G) (tableStepOne G) (tableBlindR G) (tableInformedR G)
    (tableCloseR G)
    (tableInitTwo G) (tableStepTwo G) (tableBlindL G) (tableInformedL G)
    (tableCloseL G)

/-- The right-orientation **table correspondence at atom `a`**: the table
family's in-block right position at summary `(a, c)`, and its reversed-right
position at chain control `Sum.inr (a, c)`, both correspond to the reference
`G`'s in-block right position at control `c` in the block committed at `a`.
Automaton state, minimum-priority state, and (in the reversed case) the
carried entry are free; aligning `a` with the epoch's entry atom is the β4
re-cut. -/
inductive RightTableSim (G : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (a : A.State × A.State) :
    BoundaryGamePosition (In₁ := In₁) A ((A.State × A.State) × C_L)
        ((A.State × A.State) × C_R)
        (((A.State × A.State) × C_L) ⊕ ((A.State × A.State) × C_R)) ->
      BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V -> Prop
  | inBlock (c : C_R) (state minState : A.State) :
      RightTableSim G a
        (Sum.inr (Sum.inr (Sum.inr (Sum.inl
          (tableRightPlan G, tableChain G, (a, c), state, minState)))))
        (Sum.inr (Sum.inr (Sum.inr (Sum.inl
          ((G a).2.1, (G a).2.2, c, state, minState)))))
  | reversed (c : C_R) (entry : A.State × A.State)
      (state minState : A.State) :
      RightTableSim G a
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
          (tableChain G, Sum.inr (a, c), entry, state, minState))))))
        (Sum.inr (Sum.inr (Sum.inr (Sum.inl
          ((G a).2.1, (G a).2.2, c, state, minState)))))

namespace RightTableSim

variable {G : PlanFamily (In₁ := In₁) A C_L C_R C_V} {a : A.State × A.State}
variable
  {p :
    BoundaryGamePosition (In₁ := In₁) A ((A.State × A.State) × C_L)
      ((A.State × A.State) × C_R)
      (((A.State × A.State) × C_L) ⊕ ((A.State × A.State) × C_R))}
variable {q : BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V}

/-- **Record agreement across atoms.**  Related positions emit equal round
records on every non-`left` round, against the atom-dependent reference `G`
itself: the tables at coordinate `a` *are* `(G a).2.1`'s labels. -/
theorem record_eq (h : RightTableSim G a p q)
    (round : EnvironmentRound In₁ In₂) (hg : round.graph ≠ Graph.left) :
    arenaRecord (tableFamily G) p round = arenaRecord G q round := by
  obtain ⟨i₁, i₂, g⟩ := round
  cases h <;> cases g
  · exact absurd rfl hg
  · rfl
  · rfl
  · exact absurd rfl hg
  · rfl
  · rfl

/-- **Step preservation across atoms.**  On an interior `right` round both
tiers continue with the control stepped by `(G a).2.1.step` on process one's
input; the atom coordinate is carried unchanged. -/
theorem step_right (h : RightTableSim G a p q)
    (round : EnvironmentRound In₁ In₂) (hg : round.graph = Graph.right) :
    RightTableSim G a (arenaStep (tableFamily G) p round)
      (arenaStep G q round) := by
  obtain ⟨i₁, i₂, g⟩ := round
  have hg' : g = Graph.right := hg
  subst hg'
  cases h with
  | inBlock c state minState => exact inBlock _ _ _
  | reversed c entry state minState => exact reversed _ _ _ _

/-- **Closing agreement across atoms.**  On a `both` round both folds leave
the block to the same boundary atom. -/
theorem close_target (h : RightTableSim G a p q)
    (round : EnvironmentRound In₁ In₂) (hg : round.graph = Graph.both) :
    ∃ atom : A.State × A.State,
      arenaStep (tableFamily G) p round = Sum.inl atom ∧
        arenaStep G q round = Sum.inl atom := by
  obtain ⟨i₁, i₂, g⟩ := round
  have hg' : g = Graph.both := hg
  subst hg'
  cases h with
  | inBlock c state minState => exact ⟨_, rfl, rfl⟩
  | reversed c entry state minState => exact ⟨_, rfl, rfl⟩

/-- The correspondence propagates along the fold while the environment plays
`right`. -/
theorem arenaFoldSeqFrom_sim (h : RightTableSim G a p q)
    (env : EnvironmentSequence In₁ In₂) :
    ∀ n : Nat, (∀ j : Nat, j < n -> (env j).graph = Graph.right) ->
      RightTableSim G a (arenaFoldSeqFrom (tableFamily G) p env n)
        (arenaFoldSeqFrom G q env n) := by
  intro n
  induction n with
  | zero => exact fun _ => h
  | succ n ih =>
      intro hright
      exact
        (ih fun j hj => hright j (Nat.lt_succ_of_lt hj)).step_right (env n)
          (hright n (Nat.lt_succ_self n))

/-- **Per-round word agreement**: while the environment stays `right` through
round `n`, the two suffix arena words agree at `n`. -/
theorem arenaWordFrom_agree (h : RightTableSim G a p q)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hright : ∀ j : Nat, j ≤ n -> (env j).graph = Graph.right) :
    arenaWordFrom (tableFamily G) p env n = arenaWordFrom G q env n :=
  (h.arenaFoldSeqFrom_sim env n fun j hj =>
      hright j (Nat.le_of_lt hj)).record_eq
    (env n)
    (fun hleft => by
      rw [hright n (Nat.le_refl n)] at hleft
      exact Graph.noConfusion hleft)

/-- **Suffix-word equality on an all-`right` environment**, against the
atom-dependent reference `G`. -/
theorem arenaWordFrom_eq (h : RightTableSim G a p q)
    (env : EnvironmentSequence In₁ In₂)
    (hright : ∀ j : Nat, (env j).graph = Graph.right) :
    arenaWordFrom (tableFamily G) p env = arenaWordFrom G q env :=
  funext fun n => h.arenaWordFrom_agree env n fun j _ => hright j

end RightTableSim

/-- The left-orientation **table correspondence at atom `a`**: the exact
orientation mirror of `RightTableSim`. -/
inductive LeftTableSim (G : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (a : A.State × A.State) :
    BoundaryGamePosition (In₁ := In₁) A ((A.State × A.State) × C_L)
        ((A.State × A.State) × C_R)
        (((A.State × A.State) × C_L) ⊕ ((A.State × A.State) × C_R)) ->
      BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V -> Prop
  | inBlock (c : C_L) (state minState : A.State) :
      LeftTableSim G a
        (Sum.inr (Sum.inr (Sum.inl
          (tableLeftPlan G, tableChain G, (a, c), state, minState))))
        (Sum.inr (Sum.inr (Sum.inl
          ((G a).1, (G a).2.2, c, state, minState))))
  | reversed (c : C_L) (entry : A.State × A.State)
      (state minState : A.State) :
      LeftTableSim G a
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl
          (tableChain G, Sum.inl (a, c), entry, state, minState))))))
        (Sum.inr (Sum.inr (Sum.inl
          ((G a).1, (G a).2.2, c, state, minState))))

namespace LeftTableSim

variable {G : PlanFamily (In₁ := In₁) A C_L C_R C_V} {a : A.State × A.State}
variable
  {p :
    BoundaryGamePosition (In₁ := In₁) A ((A.State × A.State) × C_L)
      ((A.State × A.State) × C_R)
      (((A.State × A.State) × C_L) ⊕ ((A.State × A.State) × C_R))}
variable {q : BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V}

/-- **Record agreement across atoms**, left orientation: equal round records
on every non-`right` round. -/
theorem record_eq (h : LeftTableSim G a p q)
    (round : EnvironmentRound In₁ In₂) (hg : round.graph ≠ Graph.right) :
    arenaRecord (tableFamily G) p round = arenaRecord G q round := by
  obtain ⟨i₁, i₂, g⟩ := round
  cases h <;> cases g
  · rfl
  · exact absurd rfl hg
  · rfl
  · rfl
  · exact absurd rfl hg
  · rfl

/-- **Step preservation across atoms**, left orientation. -/
theorem step_left (h : LeftTableSim G a p q)
    (round : EnvironmentRound In₁ In₂) (hg : round.graph = Graph.left) :
    LeftTableSim G a (arenaStep (tableFamily G) p round)
      (arenaStep G q round) := by
  obtain ⟨i₁, i₂, g⟩ := round
  have hg' : g = Graph.left := hg
  subst hg'
  cases h with
  | inBlock c state minState => exact inBlock _ _ _
  | reversed c entry state minState => exact reversed _ _ _ _

/-- **Closing agreement across atoms**, left orientation. -/
theorem close_target (h : LeftTableSim G a p q)
    (round : EnvironmentRound In₁ In₂) (hg : round.graph = Graph.both) :
    ∃ atom : A.State × A.State,
      arenaStep (tableFamily G) p round = Sum.inl atom ∧
        arenaStep G q round = Sum.inl atom := by
  obtain ⟨i₁, i₂, g⟩ := round
  have hg' : g = Graph.both := hg
  subst hg'
  cases h with
  | inBlock c state minState => exact ⟨_, rfl, rfl⟩
  | reversed c entry state minState => exact ⟨_, rfl, rfl⟩

/-- The correspondence propagates along the fold while the environment plays
`left`. -/
theorem arenaFoldSeqFrom_sim (h : LeftTableSim G a p q)
    (env : EnvironmentSequence In₁ In₂) :
    ∀ n : Nat, (∀ j : Nat, j < n -> (env j).graph = Graph.left) ->
      LeftTableSim G a (arenaFoldSeqFrom (tableFamily G) p env n)
        (arenaFoldSeqFrom G q env n) := by
  intro n
  induction n with
  | zero => exact fun _ => h
  | succ n ih =>
      intro hleft
      exact
        (ih fun j hj => hleft j (Nat.lt_succ_of_lt hj)).step_left (env n)
          (hleft n (Nat.lt_succ_self n))

/-- **Per-round word agreement**, left orientation. -/
theorem arenaWordFrom_agree (h : LeftTableSim G a p q)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hleft : ∀ j : Nat, j ≤ n -> (env j).graph = Graph.left) :
    arenaWordFrom (tableFamily G) p env n = arenaWordFrom G q env n :=
  (h.arenaFoldSeqFrom_sim env n fun j hj =>
      hleft j (Nat.le_of_lt hj)).record_eq
    (env n)
    (fun hright => by
      rw [hleft n (Nat.le_refl n)] at hright
      exact Graph.noConfusion hright)

/-- **Suffix-word equality on an all-`left` environment**, against the
atom-dependent reference `G`. -/
theorem arenaWordFrom_eq (h : LeftTableSim G a p q)
    (env : EnvironmentSequence In₁ In₂)
    (hleft : ∀ j : Nat, (env j).graph = Graph.left) :
    arenaWordFrom (tableFamily G) p env = arenaWordFrom G q env :=
  funext fun n => h.arenaWordFrom_agree env n fun j _ => hleft j

end LeftTableSim

end DetParityAutomaton

end DistributedSynthesis
