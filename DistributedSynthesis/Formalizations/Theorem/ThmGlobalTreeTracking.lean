/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmGlobalTreeStrategy

/-!
# Tracking boundary-game plays into the journal tree

Infrastructure for the winning proof of the tree strategy: every
consistent play of the boundary game walks a path of the global
journal tree, one direction per resolved round.  The directions are
read off consecutive position pairs, choosing a witnessing move where
the positions do not determine it; the choice is harmless because the
tracking invariant is stated against the positions' own components.
The canonical run of the global journal automaton is the fold of its
deterministic transition, and every accepting run agrees with it.

The tracking invariant `TreeTracks` records the alignment: at a
boundary the run sits at the atom and the freshly computed commitment
control is the control at the walked node; at a committed position
the plan is the tree plan of the walked node's control; within a
block the run is in block mode with the position's thread atom among
the realized threads, and the position's control is the walked node's
control.  The invariant implies in particular that the walked path
never reaches the sink.
-/

set_option linter.unusedSectionVars false

namespace DistributedSynthesis

universe u v x y s

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

namespace DetParityAutomaton

variable
  {A :
    DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂)}

section Run

variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂] [DecidableEq A.State]
variable (CL : LeftThreadChecker (In₁ := In₁) A)
variable (CR : RightThreadChecker (In₁ := In₁) A)
variable (CC : ChainThreadChecker (In₁ := In₁) (A := A))

/-- The deterministic run of the global journal automaton. -/
def globalRunIn :
    LabeledTree (GlobalJournalBranch (In₁ := In₁) A)
      (GlobalJournalLabel (In₁ := In₁) A) ->
      GlobalJournalState (In₁ := In₁) A CL CR CC ->
      TreeNode (GlobalJournalBranch (In₁ := In₁) A) ->
      GlobalJournalState (In₁ := In₁) A CL CR CC
  | _, state, [] => state
  | tree, state, branch :: rest =>
      globalRunIn (fun node => tree (branch :: node))
        (globalJournalStep A CL CR CC state (tree []) branch) rest

theorem globalRunIn_append
    (tree :
      LabeledTree (GlobalJournalBranch (In₁ := In₁) A)
        (GlobalJournalLabel (In₁ := In₁) A))
    (state : GlobalJournalState (In₁ := In₁) A CL CR CC) :
    ∀ (node : TreeNode (GlobalJournalBranch (In₁ := In₁) A))
      (branch : GlobalJournalBranch (In₁ := In₁) A),
      globalRunIn CL CR CC tree state (node ++ [branch]) =
        globalJournalStep A CL CR CC (globalRunIn CL CR CC tree state node)
          (tree node) branch := by
  intro node
  induction node generalizing tree state with
  | nil =>
      intro branch
      rfl
  | cons dir rest ih =>
      intro branch
      show
        globalRunIn CL CR CC (fun node => tree (dir :: node))
            (globalJournalStep A CL CR CC state (tree []) dir)
            (rest ++ [branch]) =
          _
      rw [ih]
      rfl

/-- Every accepting run of the automaton is the deterministic run. -/
theorem isRun_eq_globalRunIn
    (tree :
      LabeledTree (GlobalJournalBranch (In₁ := In₁) A)
        (GlobalJournalLabel (In₁ := In₁) A))
    (run :
      TreeNode (GlobalJournalBranch (In₁ := In₁) A) ->
        GlobalJournalState (In₁ := In₁) A CL CR CC)
    (hrun : (globalJournalAutomaton A CL CR CC).IsRun tree run) :
    ∀ node : TreeNode (GlobalJournalBranch (In₁ := In₁) A),
      run node =
        globalRunIn CL CR CC tree (Sum.inl (A.initial, A.initial)) node := by
  intro node
  induction node using List.reverseRecOn with
  | nil => exact hrun.1
  | append_singleton node branch ih =>
      rw [globalRunIn_append, ← ih]
      exact hrun.2 node branch

end Run

section Directions

variable
  (t :
    TransitionRationalTree.{max u v s, max u v x y s, s}
      (GlobalJournalBranch (In₁ := In₁) A)
      (GlobalJournalLabel (In₁ := In₁) A))

variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂] [DecidableEq A.State]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [DecidableEq t.Control] [Inhabited t.Control]

/-- The committed-to-left-block step carries an opening move. -/
theorem exists_openLeft_of_step
    {pair : A.State × A.State}
    {plan :
      BoundaryPlan (In₁ := In₁) A (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)}
    {data :
      LeftBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
          (Out₂ := Out₂) A (ULift.{max u v x y, s} t.Control) ×
        ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
            (Out₂ := Out₂) A (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control) ×
        ULift.{max u v x y, s} t.Control × A.State × A.State}
    (hstep :
      boundaryStep A (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)
        (Sum.inr (Sum.inl (pair, plan)))
        (Sum.inr (Sum.inr (Sum.inl data)))) :
    ∃ move : In₁ × In₂,
      (Sum.inr (Sum.inr (Sum.inl data)) :
          BoundaryGamePosition (In₁ := In₁) A
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)) =
        A.boundaryOpenLeftTarget plan pair.1 move := by
  rcases hstep with ⟨move, h⟩ | ⟨move, h⟩ | ⟨move, h⟩
  · exact absurd h (by simp [boundaryBothTarget])
  · exact ⟨move, h⟩
  · exact absurd h (by simp [boundaryOpenRightTarget])

/-- The committed-to-right-block step carries an opening move. -/
theorem exists_openRight_of_step
    {pair : A.State × A.State}
    {plan :
      BoundaryPlan (In₁ := In₁) A (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)}
    {data :
      RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
          (Out₂ := Out₂) A (ULift.{max u v x y, s} t.Control) ×
        ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
            (Out₂ := Out₂) A (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control) ×
        ULift.{max u v x y, s} t.Control × A.State × A.State}
    (hstep :
      boundaryStep A (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)
        (Sum.inr (Sum.inl (pair, plan)))
        (Sum.inr (Sum.inr (Sum.inr (Sum.inl data))))) :
    ∃ move : In₂ × In₁,
      (Sum.inr (Sum.inr (Sum.inr (Sum.inl data))) :
          BoundaryGamePosition (In₁ := In₁) A
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)) =
        A.boundaryOpenRightTarget plan pair.1 move := by
  rcases hstep with ⟨move, h⟩ | ⟨move, h⟩ | ⟨move, h⟩
  · exact absurd h (by simp [boundaryBothTarget])
  · exact absurd h (by simp [boundaryOpenLeftTarget])
  · exact ⟨move, h⟩

/-- The left-block continuation step carries a move. -/
theorem exists_continueL_of_step
    {source :
      LeftBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
          (Out₂ := Out₂) A (ULift.{max u v x y, s} t.Control) ×
        ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
            (Out₂ := Out₂) A (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control) ×
        ULift.{max u v x y, s} t.Control × A.State × A.State}
    {data :
      LeftBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
          (Out₂ := Out₂) A (ULift.{max u v x y, s} t.Control) ×
        ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
            (Out₂ := Out₂) A (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control) ×
        ULift.{max u v x y, s} t.Control × A.State × A.State}
    (hstep :
      boundaryStep A (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)
        (Sum.inr (Sum.inr (Sum.inl source)))
        (Sum.inr (Sum.inr (Sum.inl data)))) :
    ∃ move : In₁ × In₂,
      (Sum.inr (Sum.inr (Sum.inl data)) :
          BoundaryGamePosition (In₁ := In₁) A
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)) =
        A.leftContinueTarget source.1 source.2.1 source.2.2.1
          source.2.2.2.1 source.2.2.2.2 move := by
  obtain ⟨plan, chain, control, state, minState⟩ := source
  rcases hstep with ⟨move, h⟩ | ⟨move, h⟩ | ⟨move, h⟩
  · exact ⟨move, h⟩
  · exact absurd h (by simp [leftCloseTarget])
  · exact absurd h (by simp [leftReverseTarget])

/-- The right-block continuation step carries a move. -/
theorem exists_continueR_of_step
    {source :
      RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
          (Out₂ := Out₂) A (ULift.{max u v x y, s} t.Control) ×
        ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
            (Out₂ := Out₂) A (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control) ×
        ULift.{max u v x y, s} t.Control × A.State × A.State}
    {data :
      RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
          (Out₂ := Out₂) A (ULift.{max u v x y, s} t.Control) ×
        ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
            (Out₂ := Out₂) A (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control) ×
        ULift.{max u v x y, s} t.Control × A.State × A.State}
    (hstep :
      boundaryStep A (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)
        (Sum.inr (Sum.inr (Sum.inr (Sum.inl source))))
        (Sum.inr (Sum.inr (Sum.inr (Sum.inl data))))) :
    ∃ move : In₂ × In₁,
      (Sum.inr (Sum.inr (Sum.inr (Sum.inl data))) :
          BoundaryGamePosition (In₁ := In₁) A
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)) =
        A.rightContinueTarget source.1 source.2.1 source.2.2.1
          source.2.2.2.1 source.2.2.2.2 move := by
  obtain ⟨plan, chain, control, state, minState⟩ := source
  rcases hstep with ⟨move, h⟩ | ⟨move, h⟩ | ⟨move, h⟩
  · exact ⟨move, h⟩
  · exact absurd h (by simp [rightCloseTarget])
  · exact absurd h (by simp [rightReverseTarget])

/--
The tree directions consumed by one play step: an atom event at a
resolved boundary, the chosen sender input of a block round, and
nothing at a commitment.  The reader is proof-free: where the
positions do not determine the move, it decides the witnessing
existential classically, and legality makes the conditions hold.
-/
noncomputable def stepDirections
    (source target :
      BoundaryGamePosition (In₁ := In₁) A
        (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)) :
    List (GlobalJournalBranch (In₁ := In₁) A) :=
  match source, target with
  | Sum.inl _, _ => []
  | Sum.inr (Sum.inl _), Sum.inl atom => [Sum.inl atom]
  | Sum.inr (Sum.inl (pair, plan)), Sum.inr (Sum.inr (Sum.inl data)) =>
      letI :
          Decidable
            (∃ move : In₁ × In₂,
              (Sum.inr (Sum.inr (Sum.inl data)) :
                  BoundaryGamePosition (In₁ := In₁) A
                    (ULift.{max u v x y, s} t.Control)
                    (ULift.{max u v x y, s} t.Control)
                    (ULift.{max u v x y, s} t.Control)) =
                A.boundaryOpenLeftTarget plan pair.1 move) :=
        Classical.propDecidable _
      if h :
          ∃ move : In₁ × In₂,
            (Sum.inr (Sum.inr (Sum.inl data)) :
                BoundaryGamePosition (In₁ := In₁) A
                  (ULift.{max u v x y, s} t.Control)
                  (ULift.{max u v x y, s} t.Control)
                  (ULift.{max u v x y, s} t.Control)) =
              A.boundaryOpenLeftTarget plan pair.1 move then
        [Sum.inr (Sum.inl (Classical.choose h).2)]
      else []
  | Sum.inr (Sum.inl (pair, plan)),
      Sum.inr (Sum.inr (Sum.inr (Sum.inl data))) =>
      letI :
          Decidable
            (∃ move : In₂ × In₁,
              (Sum.inr (Sum.inr (Sum.inr (Sum.inl data))) :
                  BoundaryGamePosition (In₁ := In₁) A
                    (ULift.{max u v x y, s} t.Control)
                    (ULift.{max u v x y, s} t.Control)
                    (ULift.{max u v x y, s} t.Control)) =
                A.boundaryOpenRightTarget plan pair.1 move) :=
        Classical.propDecidable _
      if h :
          ∃ move : In₂ × In₁,
            (Sum.inr (Sum.inr (Sum.inr (Sum.inl data))) :
                BoundaryGamePosition (In₁ := In₁) A
                  (ULift.{max u v x y, s} t.Control)
                  (ULift.{max u v x y, s} t.Control)
                  (ULift.{max u v x y, s} t.Control)) =
              A.boundaryOpenRightTarget plan pair.1 move then
        [Sum.inr (Sum.inr (Classical.choose h).2)]
      else []
  | Sum.inr (Sum.inl _), Sum.inr (Sum.inl _) => []
  | Sum.inr (Sum.inl _), _ => []
  | Sum.inr (Sum.inr (Sum.inl source')), Sum.inr (Sum.inr (Sum.inl data)) =>
      letI :
          Decidable
            (∃ move : In₁ × In₂,
              (Sum.inr (Sum.inr (Sum.inl data)) :
                  BoundaryGamePosition (In₁ := In₁) A
                    (ULift.{max u v x y, s} t.Control)
                    (ULift.{max u v x y, s} t.Control)
                    (ULift.{max u v x y, s} t.Control)) =
                A.leftContinueTarget source'.1 source'.2.1 source'.2.2.1
                  source'.2.2.2.1 source'.2.2.2.2 move) :=
        Classical.propDecidable _
      if h :
          ∃ move : In₁ × In₂,
            (Sum.inr (Sum.inr (Sum.inl data)) :
                BoundaryGamePosition (In₁ := In₁) A
                  (ULift.{max u v x y, s} t.Control)
                  (ULift.{max u v x y, s} t.Control)
                  (ULift.{max u v x y, s} t.Control)) =
              A.leftContinueTarget source'.1 source'.2.1 source'.2.2.1
                source'.2.2.2.1 source'.2.2.2.2 move then
        [Sum.inr (Sum.inl (Classical.choose h).2)]
      else []
  | Sum.inr (Sum.inr (Sum.inl source')),
      Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr data)))) =>
      letI :
          Decidable
            (∃ move : In₁ × In₂,
              (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr data)))) :
                  BoundaryGamePosition (In₁ := In₁) A
                    (ULift.{max u v x y, s} t.Control)
                    (ULift.{max u v x y, s} t.Control)
                    (ULift.{max u v x y, s} t.Control)) =
                A.leftReverseTarget source'.1 source'.2.1 source'.2.2.1
                  source'.2.2.2.1 source'.2.2.2.2 move) :=
        Classical.propDecidable _
      if h :
          ∃ move : In₁ × In₂,
            (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr data)))) :
                BoundaryGamePosition (In₁ := In₁) A
                  (ULift.{max u v x y, s} t.Control)
                  (ULift.{max u v x y, s} t.Control)
                  (ULift.{max u v x y, s} t.Control)) =
              A.leftReverseTarget source'.1 source'.2.1 source'.2.2.1
                source'.2.2.2.1 source'.2.2.2.2 move then
        [Sum.inr (Sum.inr (Classical.choose h).1)]
      else []
  | Sum.inr (Sum.inr (Sum.inl _)), Sum.inl atom => [Sum.inl atom]
  | Sum.inr (Sum.inr (Sum.inl _)), _ => []
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl source'))),
      Sum.inr (Sum.inr (Sum.inr (Sum.inl data))) =>
      letI :
          Decidable
            (∃ move : In₂ × In₁,
              (Sum.inr (Sum.inr (Sum.inr (Sum.inl data))) :
                  BoundaryGamePosition (In₁ := In₁) A
                    (ULift.{max u v x y, s} t.Control)
                    (ULift.{max u v x y, s} t.Control)
                    (ULift.{max u v x y, s} t.Control)) =
                A.rightContinueTarget source'.1 source'.2.1 source'.2.2.1
                  source'.2.2.2.1 source'.2.2.2.2 move) :=
        Classical.propDecidable _
      if h :
          ∃ move : In₂ × In₁,
            (Sum.inr (Sum.inr (Sum.inr (Sum.inl data))) :
                BoundaryGamePosition (In₁ := In₁) A
                  (ULift.{max u v x y, s} t.Control)
                  (ULift.{max u v x y, s} t.Control)
                  (ULift.{max u v x y, s} t.Control)) =
              A.rightContinueTarget source'.1 source'.2.1 source'.2.2.1
                source'.2.2.2.1 source'.2.2.2.2 move then
        [Sum.inr (Sum.inr (Classical.choose h).2)]
      else []
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl source'))),
      Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl data)))) =>
      letI :
          Decidable
            (∃ move : In₂ × In₁,
              (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl data)))) :
                  BoundaryGamePosition (In₁ := In₁) A
                    (ULift.{max u v x y, s} t.Control)
                    (ULift.{max u v x y, s} t.Control)
                    (ULift.{max u v x y, s} t.Control)) =
                A.rightReverseTarget source'.1 source'.2.1 source'.2.2.1
                  source'.2.2.2.1 source'.2.2.2.2 move) :=
        Classical.propDecidable _
      if h :
          ∃ move : In₂ × In₁,
            (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl data)))) :
                BoundaryGamePosition (In₁ := In₁) A
                  (ULift.{max u v x y, s} t.Control)
                  (ULift.{max u v x y, s} t.Control)
                  (ULift.{max u v x y, s} t.Control)) =
              A.rightReverseTarget source'.1 source'.2.1 source'.2.2.1
                source'.2.2.2.1 source'.2.2.2.2 move then
        [Sum.inr (Sum.inl (Classical.choose h).1)]
      else []
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl _))), Sum.inl atom =>
      [Sum.inl atom]
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl _))), _ => []
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl source')))),
      Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl data)))) =>
      letI :
          Decidable
            (∃ move : In₁ × In₂,
              (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl data)))) :
                  BoundaryGamePosition (In₁ := In₁) A
                    (ULift.{max u v x y, s} t.Control)
                    (ULift.{max u v x y, s} t.Control)
                    (ULift.{max u v x y, s} t.Control)) =
                A.revLeftContinueTarget source'.1 source'.2.1
                  source'.2.2.1 source'.2.2.2.1 source'.2.2.2.2 move) :=
        Classical.propDecidable _
      if h :
          ∃ move : In₁ × In₂,
            (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl data)))) :
                BoundaryGamePosition (In₁ := In₁) A
                  (ULift.{max u v x y, s} t.Control)
                  (ULift.{max u v x y, s} t.Control)
                  (ULift.{max u v x y, s} t.Control)) =
              A.revLeftContinueTarget source'.1 source'.2.1
                source'.2.2.1 source'.2.2.2.1 source'.2.2.2.2 move then
        [Sum.inr (Sum.inl (Classical.choose h).2)]
      else []
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl source')))),
      Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr data)))) =>
      letI :
          Decidable
            (∃ move : In₁ × In₂,
              (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr data)))) :
                  BoundaryGamePosition (In₁ := In₁) A
                    (ULift.{max u v x y, s} t.Control)
                    (ULift.{max u v x y, s} t.Control)
                    (ULift.{max u v x y, s} t.Control)) =
                A.revLeftReverseTarget source'.1 source'.2.1
                  source'.2.2.1 source'.2.2.2.1 source'.2.2.2.2 move) :=
        Classical.propDecidable _
      if h :
          ∃ move : In₁ × In₂,
            (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr data)))) :
                BoundaryGamePosition (In₁ := In₁) A
                  (ULift.{max u v x y, s} t.Control)
                  (ULift.{max u v x y, s} t.Control)
                  (ULift.{max u v x y, s} t.Control)) =
              A.revLeftReverseTarget source'.1 source'.2.1
                source'.2.2.1 source'.2.2.2.1 source'.2.2.2.2 move then
        [Sum.inr (Sum.inr (Classical.choose h).1)]
      else []
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl _)))), Sum.inl atom =>
      [Sum.inl atom]
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl _)))), _ => []
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr source')))),
      Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr data)))) =>
      letI :
          Decidable
            (∃ move : In₁ × In₂,
              (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr data)))) :
                  BoundaryGamePosition (In₁ := In₁) A
                    (ULift.{max u v x y, s} t.Control)
                    (ULift.{max u v x y, s} t.Control)
                    (ULift.{max u v x y, s} t.Control)) =
                A.revRightContinueTarget source'.1 source'.2.1
                  source'.2.2.1 source'.2.2.2.1 source'.2.2.2.2 move) :=
        Classical.propDecidable _
      if h :
          ∃ move : In₁ × In₂,
            (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr data)))) :
                BoundaryGamePosition (In₁ := In₁) A
                  (ULift.{max u v x y, s} t.Control)
                  (ULift.{max u v x y, s} t.Control)
                  (ULift.{max u v x y, s} t.Control)) =
              A.revRightContinueTarget source'.1 source'.2.1
                source'.2.2.1 source'.2.2.2.1 source'.2.2.2.2 move then
        [Sum.inr (Sum.inr (Classical.choose h).1)]
      else []
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr source')))),
      Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl data)))) =>
      letI :
          Decidable
            (∃ move : In₁ × In₂,
              (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl data)))) :
                  BoundaryGamePosition (In₁ := In₁) A
                    (ULift.{max u v x y, s} t.Control)
                    (ULift.{max u v x y, s} t.Control)
                    (ULift.{max u v x y, s} t.Control)) =
                A.revRightReverseTarget source'.1 source'.2.1
                  source'.2.2.1 source'.2.2.2.1 source'.2.2.2.2 move) :=
        Classical.propDecidable _
      if h :
          ∃ move : In₁ × In₂,
            (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl data)))) :
                BoundaryGamePosition (In₁ := In₁) A
                  (ULift.{max u v x y, s} t.Control)
                  (ULift.{max u v x y, s} t.Control)
                  (ULift.{max u v x y, s} t.Control)) =
              A.revRightReverseTarget source'.1 source'.2.1
                source'.2.2.1 source'.2.2.2.1 source'.2.2.2.2 move then
        [Sum.inr (Sum.inl (Classical.choose h).2)]
      else []
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr _)))), Sum.inl atom =>
      [Sum.inl atom]
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr _)))), _ => []

/-- The tree node walked by a play after `n` steps. -/
noncomputable def playNodes
    (path :
      Nat ->
        BoundaryGamePosition (In₁ := In₁) A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)) :
    Nat -> TreeNode (GlobalJournalBranch (In₁ := In₁) A)
  | 0 => []
  | n + 1 =>
      playNodes path n ++ stepDirections t (path n) (path (n + 1))

/-- The predecessor position seen by the tree strategy. -/
def prevOpt
    (path :
      Nat ->
        BoundaryGamePosition (In₁ := In₁) A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control))
    (n : Nat) :
    Option
      (BoundaryGamePosition (In₁ := In₁) A
        (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)) :=
  if n = 0 then none else some (path (n - 1))

@[simp]
theorem prevOpt_zero
    (path :
      Nat ->
        BoundaryGamePosition (In₁ := In₁) A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)) :
    prevOpt t path 0 = none :=
  rfl

@[simp]
theorem prevOpt_succ
    (path :
      Nat ->
        BoundaryGamePosition (In₁ := In₁) A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control))
    (n : Nat) :
    prevOpt t path (n + 1) = some (path n) := by
  simp [prevOpt]

/-- The strategy's predecessor option is the tracking one. -/
theorem dite_prev_eq_prevOpt
    (path :
      Nat ->
        BoundaryGamePosition (In₁ := In₁) A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control))
    (n : Nat) :
    (if _h : n = 0 then none else some (path (n - 1))) =
      prevOpt t path n := by
  by_cases h : n = 0 <;> simp [prevOpt, h]

variable (CL : LeftThreadChecker (In₁ := In₁) A)
variable (CR : RightThreadChecker (In₁ := In₁) A)
variable (CC : ChainThreadChecker (In₁ := In₁) (A := A))

/--
The tracking invariant: the deterministic run at the walked node is
aligned with the play position, the position's controls are the
controls of the walked node, and within blocks the position's thread
atom is among the realized threads.
-/
def TreeTracks
    (path :
      Nat ->
        BoundaryGamePosition (In₁ := In₁) A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control))
    (node : TreeNode (GlobalJournalBranch (In₁ := In₁) A))
    (n : Nat) : Prop :=
  match path n with
  | Sum.inl atom =>
      globalRunIn CL CR CC t.labeledTree (Sum.inl (A.initial, A.initial))
          node =
        Sum.inl atom ∧
      controlAfter t (prevOpt t path n) atom = t.controlAt node
  | Sum.inr (Sum.inl (pair, plan)) =>
      (∃ atom : A.State × A.State,
        globalRunIn CL CR CC t.labeledTree (Sum.inl (A.initial, A.initial))
            node =
          Sum.inl atom ∧
        pair = (atom.1, atom.1)) ∧
      plan = treeBoundaryPlan t (t.controlAt node)
  | Sum.inr (Sum.inr (Sum.inl (plan, chain, control, state, minState))) =>
      (∃ checker threads,
        globalRunIn CL CR CC t.labeledTree (Sum.inl (A.initial, A.initial))
            node =
          Sum.inr (Sum.inl (checker, threads)) ∧
        (state, minState) ∈ threads) ∧
      control = ULift.up (t.controlAt node) ∧
      (∃ root : t.Control, plan = treeLeftPlan t root) ∧
      chain = treeChainPlan t
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl
      (plan, chain, control, state, minState)))) =>
      (∃ checker threads,
        globalRunIn CL CR CC t.labeledTree (Sum.inl (A.initial, A.initial))
            node =
          Sum.inr (Sum.inr (Sum.inl (checker, threads))) ∧
        (state, minState) ∈ threads) ∧
      control = ULift.up (t.controlAt node) ∧
      (∃ root : t.Control, plan = treeRightPlan t root) ∧
      chain = treeChainPlan t
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl
      (chain, control, state, minState))))) =>
      (∃ checker threads,
        globalRunIn CL CR CC t.labeledTree (Sum.inl (A.initial, A.initial))
            node =
          Sum.inr (Sum.inr (Sum.inr (Sum.inl (checker, threads)))) ∧
        (state, minState) ∈ threads) ∧
      control = ULift.up (t.controlAt node) ∧
      chain = treeChainPlan t
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
      (chain, control, state, minState))))) =>
      (∃ checker threads,
        globalRunIn CL CR CC t.labeledTree (Sum.inl (A.initial, A.initial))
            node =
          Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl
            (checker, threads))))) ∧
        (state, minState) ∈ threads) ∧
      control = ULift.up (t.controlAt node) ∧
      chain = treeChainPlan t

/-! ### Reduction lemmas for the direction reader -/

theorem controlAt_concat
    (node : TreeNode (GlobalJournalBranch (In₁ := In₁) A))
    (branch : GlobalJournalBranch (In₁ := In₁) A) :
    t.controlAt (node ++ [branch]) =
      t.step (t.controlAt node) branch := by
  rw [TransitionRationalTree.controlAt_append]
  rfl

@[simp]
theorem stepDirections_bnd (atom : A.State × A.State)
    (target :
      BoundaryGamePosition (In₁ := In₁) A
        (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)) :
    stepDirections t (Sum.inl atom) target = [] :=
  rfl

@[simp]
theorem stepDirections_committed_bnd
    (pair : A.State × A.State)
    (plan :
      BoundaryPlan (In₁ := In₁) A (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control))
    (atom' : A.State × A.State) :
    stepDirections t (Sum.inr (Sum.inl (pair, plan))) (Sum.inl atom') =
      [Sum.inl atom'] :=
  rfl

@[simp]
theorem stepDirections_blockL_bnd
    (data :
      LeftBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
          (Out₂ := Out₂) A (ULift.{max u v x y, s} t.Control) ×
        ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
            (Out₂ := Out₂) A (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control) ×
        ULift.{max u v x y, s} t.Control × A.State × A.State)
    (atom' : A.State × A.State) :
    stepDirections t (Sum.inr (Sum.inr (Sum.inl data))) (Sum.inl atom') =
      [Sum.inl atom'] :=
  rfl

@[simp]
theorem stepDirections_blockR_bnd
    (data :
      RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
          (Out₂ := Out₂) A (ULift.{max u v x y, s} t.Control) ×
        ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
            (Out₂ := Out₂) A (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control) ×
        ULift.{max u v x y, s} t.Control × A.State × A.State)
    (atom' : A.State × A.State) :
    stepDirections t (Sum.inr (Sum.inr (Sum.inr (Sum.inl data))))
        (Sum.inl atom') =
      [Sum.inl atom'] :=
  rfl

theorem stepDirections_committed_blockL
    (pair : A.State × A.State)
    (plan :
      BoundaryPlan (In₁ := In₁) A (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control))
    (data :
      LeftBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
          (Out₂ := Out₂) A (ULift.{max u v x y, s} t.Control) ×
        ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
            (Out₂ := Out₂) A (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control) ×
        ULift.{max u v x y, s} t.Control × A.State × A.State)
    (h :
      ∃ move : In₁ × In₂,
        (Sum.inr (Sum.inr (Sum.inl data)) :
            BoundaryGamePosition (In₁ := In₁) A
              (ULift.{max u v x y, s} t.Control)
              (ULift.{max u v x y, s} t.Control)
              (ULift.{max u v x y, s} t.Control)) =
          A.boundaryOpenLeftTarget plan pair.1 move) :
    stepDirections t (Sum.inr (Sum.inl (pair, plan)))
        (Sum.inr (Sum.inr (Sum.inl data))) =
      [Sum.inr (Sum.inl (Classical.choose h).2)] := by
  simp only [stepDirections]
  rw [dif_pos h]

theorem stepDirections_committed_blockR
    (pair : A.State × A.State)
    (plan :
      BoundaryPlan (In₁ := In₁) A (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control))
    (data :
      RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
          (Out₂ := Out₂) A (ULift.{max u v x y, s} t.Control) ×
        ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
            (Out₂ := Out₂) A (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control) ×
        ULift.{max u v x y, s} t.Control × A.State × A.State)
    (h :
      ∃ move : In₂ × In₁,
        (Sum.inr (Sum.inr (Sum.inr (Sum.inl data))) :
            BoundaryGamePosition (In₁ := In₁) A
              (ULift.{max u v x y, s} t.Control)
              (ULift.{max u v x y, s} t.Control)
              (ULift.{max u v x y, s} t.Control)) =
          A.boundaryOpenRightTarget plan pair.1 move) :
    stepDirections t (Sum.inr (Sum.inl (pair, plan)))
        (Sum.inr (Sum.inr (Sum.inr (Sum.inl data)))) =
      [Sum.inr (Sum.inr (Classical.choose h).2)] := by
  simp only [stepDirections]
  rw [dif_pos h]

theorem stepDirections_blockL_blockL
    (source' data :
      LeftBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
          (Out₂ := Out₂) A (ULift.{max u v x y, s} t.Control) ×
        ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
            (Out₂ := Out₂) A (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control) ×
        ULift.{max u v x y, s} t.Control × A.State × A.State)
    (h :
      ∃ move : In₁ × In₂,
        (Sum.inr (Sum.inr (Sum.inl data)) :
            BoundaryGamePosition (In₁ := In₁) A
              (ULift.{max u v x y, s} t.Control)
              (ULift.{max u v x y, s} t.Control)
              (ULift.{max u v x y, s} t.Control)) =
          A.leftContinueTarget source'.1 source'.2.1 source'.2.2.1
            source'.2.2.2.1 source'.2.2.2.2 move) :
    stepDirections t (Sum.inr (Sum.inr (Sum.inl source')))
        (Sum.inr (Sum.inr (Sum.inl data))) =
      [Sum.inr (Sum.inl (Classical.choose h).2)] := by
  simp only [stepDirections]
  rw [dif_pos h]

theorem stepDirections_blockR_blockR
    (source' data :
      RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
          (Out₂ := Out₂) A (ULift.{max u v x y, s} t.Control) ×
        ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
            (Out₂ := Out₂) A (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control) ×
        ULift.{max u v x y, s} t.Control × A.State × A.State)
    (h :
      ∃ move : In₂ × In₁,
        (Sum.inr (Sum.inr (Sum.inr (Sum.inl data))) :
            BoundaryGamePosition (In₁ := In₁) A
              (ULift.{max u v x y, s} t.Control)
              (ULift.{max u v x y, s} t.Control)
              (ULift.{max u v x y, s} t.Control)) =
          A.rightContinueTarget source'.1 source'.2.1 source'.2.2.1
            source'.2.2.2.1 source'.2.2.2.2 move) :
    stepDirections t (Sum.inr (Sum.inr (Sum.inr (Sum.inl source'))))
        (Sum.inr (Sum.inr (Sum.inr (Sum.inl data)))) =
      [Sum.inr (Sum.inr (Classical.choose h).2)] := by
  simp only [stepDirections]
  rw [dif_pos h]

/-- The tuple type of the two reversed tiers. -/
private abbrev RevTierData :=
  ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
      A (ULift.{max u v x y, s} t.Control)
      (ULift.{max u v x y, s} t.Control)
      (ULift.{max u v x y, s} t.Control) ×
    ULift.{max u v x y, s} t.Control × (A.State × A.State) ×
      A.State × A.State

@[simp]
theorem stepDirections_revL_bnd
    (data : RevTierData (In₁ := In₁) (A := A) t)
    (atom' : A.State × A.State) :
    stepDirections t
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl data)))))
        (Sum.inl atom') =
      [Sum.inl atom'] :=
  rfl

@[simp]
theorem stepDirections_revR_bnd
    (data : RevTierData (In₁ := In₁) (A := A) t)
    (atom' : A.State × A.State) :
    stepDirections t
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr data)))))
        (Sum.inl atom') =
      [Sum.inl atom'] :=
  rfl

theorem stepDirections_blockL_revR
    (source' :
      LeftBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
          (Out₂ := Out₂) A (ULift.{max u v x y, s} t.Control) ×
        ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
            (Out₂ := Out₂) A (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control) ×
        ULift.{max u v x y, s} t.Control × A.State × A.State)
    (data : RevTierData (In₁ := In₁) (A := A) t)
    (h :
      ∃ move : In₁ × In₂,
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr data)))) :
            BoundaryGamePosition (In₁ := In₁) A
              (ULift.{max u v x y, s} t.Control)
              (ULift.{max u v x y, s} t.Control)
              (ULift.{max u v x y, s} t.Control)) =
          A.leftReverseTarget source'.1 source'.2.1 source'.2.2.1
            source'.2.2.2.1 source'.2.2.2.2 move) :
    stepDirections t (Sum.inr (Sum.inr (Sum.inl source')))
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr data))))) =
      [Sum.inr (Sum.inr (Classical.choose h).1)] := by
  simp only [stepDirections]
  rw [dif_pos h]

theorem stepDirections_blockR_revL
    (source' :
      RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
          (Out₂ := Out₂) A (ULift.{max u v x y, s} t.Control) ×
        ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
            (Out₂ := Out₂) A (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control) ×
        ULift.{max u v x y, s} t.Control × A.State × A.State)
    (data : RevTierData (In₁ := In₁) (A := A) t)
    (h :
      ∃ move : In₂ × In₁,
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl data)))) :
            BoundaryGamePosition (In₁ := In₁) A
              (ULift.{max u v x y, s} t.Control)
              (ULift.{max u v x y, s} t.Control)
              (ULift.{max u v x y, s} t.Control)) =
          A.rightReverseTarget source'.1 source'.2.1 source'.2.2.1
            source'.2.2.2.1 source'.2.2.2.2 move) :
    stepDirections t (Sum.inr (Sum.inr (Sum.inr (Sum.inl source'))))
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl data))))) =
      [Sum.inr (Sum.inl (Classical.choose h).1)] := by
  simp only [stepDirections]
  rw [dif_pos h]

theorem stepDirections_revL_revL
    (source' data : RevTierData (In₁ := In₁) (A := A) t)
    (h :
      ∃ move : In₁ × In₂,
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl data)))) :
            BoundaryGamePosition (In₁ := In₁) A
              (ULift.{max u v x y, s} t.Control)
              (ULift.{max u v x y, s} t.Control)
              (ULift.{max u v x y, s} t.Control)) =
          A.revLeftContinueTarget source'.1 source'.2.1 source'.2.2.1
            source'.2.2.2.1 source'.2.2.2.2 move) :
    stepDirections t
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl source')))))
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl data))))) =
      [Sum.inr (Sum.inl (Classical.choose h).2)] := by
  simp only [stepDirections]
  rw [dif_pos h]

theorem stepDirections_revL_revR
    (source' data : RevTierData (In₁ := In₁) (A := A) t)
    (h :
      ∃ move : In₁ × In₂,
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr data)))) :
            BoundaryGamePosition (In₁ := In₁) A
              (ULift.{max u v x y, s} t.Control)
              (ULift.{max u v x y, s} t.Control)
              (ULift.{max u v x y, s} t.Control)) =
          A.revLeftReverseTarget source'.1 source'.2.1 source'.2.2.1
            source'.2.2.2.1 source'.2.2.2.2 move) :
    stepDirections t
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl source')))))
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr data))))) =
      [Sum.inr (Sum.inr (Classical.choose h).1)] := by
  simp only [stepDirections]
  rw [dif_pos h]

theorem stepDirections_revR_revR
    (source' data : RevTierData (In₁ := In₁) (A := A) t)
    (h :
      ∃ move : In₁ × In₂,
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr data)))) :
            BoundaryGamePosition (In₁ := In₁) A
              (ULift.{max u v x y, s} t.Control)
              (ULift.{max u v x y, s} t.Control)
              (ULift.{max u v x y, s} t.Control)) =
          A.revRightContinueTarget source'.1 source'.2.1 source'.2.2.1
            source'.2.2.2.1 source'.2.2.2.2 move) :
    stepDirections t
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr source')))))
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr data))))) =
      [Sum.inr (Sum.inr (Classical.choose h).1)] := by
  simp only [stepDirections]
  rw [dif_pos h]

theorem stepDirections_revR_revL
    (source' data : RevTierData (In₁ := In₁) (A := A) t)
    (h :
      ∃ move : In₁ × In₂,
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl data)))) :
            BoundaryGamePosition (In₁ := In₁) A
              (ULift.{max u v x y, s} t.Control)
              (ULift.{max u v x y, s} t.Control)
              (ULift.{max u v x y, s} t.Control)) =
          A.revRightReverseTarget source'.1 source'.2.1 source'.2.2.1
            source'.2.2.2.1 source'.2.2.2.2 move) :
    stepDirections t
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr source')))))
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl data))))) =
      [Sum.inr (Sum.inl (Classical.choose h).2)] := by
  simp only [stepDirections]
  rw [dif_pos h]

/-- Arrival at a boundary: the two clause parts assemble. -/
theorem tracks_bnd_arrival
    (path :
      Nat ->
        BoundaryGamePosition (In₁ := In₁) A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control))
    (n : Nat) (atom' : A.State × A.State)
    (hnext : path (n + 1) = Sum.inl atom')
    (hrun' :
      globalRunIn CL CR CC t.labeledTree (Sum.inl (A.initial, A.initial))
          (playNodes t path (n + 1)) =
        Sum.inl atom')
    (hctl' :
      controlAfter t (some (path n)) atom' =
        t.controlAt (playNodes t path (n + 1))) :
    TreeTracks t CL CR CC path (playNodes t path (n + 1)) (n + 1) := by
  unfold TreeTracks
  rw [hnext]
  exact ⟨hrun', by rw [prevOpt_succ]; exact hctl'⟩

/-! ### The tracking invariant holds along consistent plays -/

/-- Along every play of the tree strategy the tracking invariant
holds at every round. -/
theorem treeTracks_of_consistent
    (path :
      Nat ->
        BoundaryGamePosition (In₁ := In₁) A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control))
    (hplay :
      (DetParityAutomaton.boundaryGame A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)).PlayFrom
        (Sum.inl (A.initial, A.initial)) path)
    (hcons :
      CountableParityGame.Strategy.Consistent
        (G :=
          DetParityAutomaton.boundaryGame A
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control))
        (treeStrategy t) path) :
    ∀ n : Nat, TreeTracks t CL CR CC path (playNodes t path n) n := by
  intro n
  induction n with
  | zero =>
      unfold TreeTracks
      rw [hplay.1]
      exact ⟨rfl, rfl⟩
  | succ n ih =>
      have hstep :
          boundaryStep A (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control) (path n) (path (n + 1)) :=
        hplay.2 n
      rcases hpos : path n with
        atom | ⟨pair, plan⟩ | ⟨plan, chain, control, state, minState⟩ |
        ⟨plan, chain, control, state, minState⟩ |
        ⟨chain, control, entry, state, minState⟩ |
        ⟨chain, control, entry, state, minState⟩
      all_goals rw [hpos] at hstep
      all_goals unfold TreeTracks at ih
      all_goals rw [hpos] at ih
      -- boundary: Even commits the tree plan
      · have hnext := treeStrategy_consistent_bnd t path hcons n atom hpos
        obtain ⟨hrun, hctl⟩ := ih
        show TreeTracks t CL CR CC path
          (playNodes t path n ++ stepDirections t (path n) (path (n + 1)))
          (n + 1)
        unfold TreeTracks
        rw [hpos, hnext, stepDirections_bnd, List.append_nil]
        exact
          ⟨⟨atom, hrun, rfl⟩, by rw [dite_prev_eq_prevOpt, hctl]⟩
      -- committed: the environment resolves the round
      · obtain ⟨⟨atom, hrun, hpair⟩, hplan⟩ := ih
        subst hpair
        subst hplan
        have hstep' :
            (∃ move : In₁ × In₂,
              path (n + 1) =
                A.boundaryBothTarget
                  (treeBoundaryPlan t (t.controlAt (playNodes t path n)))
                  atom.1 move) ∨
            (∃ move : In₁ × In₂,
              path (n + 1) =
                A.boundaryOpenLeftTarget
                  (treeBoundaryPlan t (t.controlAt (playNodes t path n)))
                  atom.1 move) ∨
            (∃ move : In₂ × In₁,
              path (n + 1) =
                A.boundaryOpenRightTarget
                  (treeBoundaryPlan t (t.controlAt (playNodes t path n)))
                  atom.1 move) :=
          hstep
        rcases hstep' with ⟨move, hnext⟩ | ⟨move, hnext⟩ | ⟨move, hnext⟩
        · -- synchronizing round
          have hnext' :
              path (n + 1) =
                Sum.inl
                  (A.step atom.1
                      (bothRoundRecord move
                        ((GlobalJournalLabel.leftNarrowed (t.labelOf
                            (t.controlAt (playNodes t path n)))).2
                          (atom.1, atom.1) move)
                        ((GlobalJournalLabel.rightNarrowed (t.labelOf
                            (t.controlAt (playNodes t path n)))).2
                          (atom.1, atom.1) (move.2, move.1))),
                    atom.1) := by
            rw [hnext]
            rfl
          refine tracks_bnd_arrival t CL CR CC path n _ hnext' ?_ ?_
          · show
              globalRunIn CL CR CC t.labeledTree
                  (Sum.inl (A.initial, A.initial))
                  (playNodes t path n ++
                    stepDirections t (path n) (path (n + 1))) =
                _
            rw [hpos, hnext', stepDirections_committed_bnd,
              globalRunIn_append, hrun]
            simp only [globalJournalStep]
            rw [if_pos]
            exact Finset.mem_image.mpr ⟨move, Finset.mem_univ _, rfl⟩
          · show
              controlAfter t (some (path n)) _ =
                t.controlAt
                  (playNodes t path n ++
                    stepDirections t (path n) (path (n + 1)))
            rw [hpos, hnext', stepDirections_committed_bnd,
              controlAt_concat]
            simp only [controlAfter]
            rfl
        · -- left opening
          have hnext' :
              path (n + 1) =
                Sum.inr (Sum.inr (Sum.inl
                  (treeLeftPlan t (t.controlAt (playNodes t path n)),
                    treeChainPlan t,
                    ULift.up
                      (t.step (t.controlAt (playNodes t path n))
                        (Sum.inr (Sum.inl move.2))),
                    A.step atom.1
                      (leftRoundRecord move
                        ((GlobalJournalLabel.leftNarrowed (t.labelOf
                            (t.controlAt (playNodes t path n)))).2
                          (atom.1, atom.1) move)
                        ((GlobalJournalLabel.leftNarrowed (t.labelOf
                            (t.controlAt (playNodes t path n)))).1
                          move.2)),
                    A.minPriorityState atom.1
                      (A.step atom.1
                        (leftRoundRecord move
                          ((GlobalJournalLabel.leftNarrowed (t.labelOf
                              (t.controlAt (playNodes t path n)))).2
                            (atom.1, atom.1) move)
                          ((GlobalJournalLabel.leftNarrowed (t.labelOf
                              (t.controlAt (playNodes t path n)))).1
                            move.2)))))) := by
            rw [hnext]
            rfl
          have hc :
              ∃ move' : In₁ × In₂,
                path (n + 1) =
                  A.boundaryOpenLeftTarget
                    (treeBoundaryPlan t
                      (t.controlAt (playNodes t path n)))
                    (atom.1, atom.1).1 move' :=
            ⟨move, hnext⟩
          rw [hnext'] at hc
          show TreeTracks t CL CR CC path
            (playNodes t path n ++
              stepDirections t (path n) (path (n + 1))) (n + 1)
          unfold TreeTracks
          rw [hpos, hnext', stepDirections_committed_blockL t _ _ _ hc]
          have hspec := Classical.choose_spec hc
          set m' := Classical.choose hc with hm'def
          simp only [boundaryOpenLeftTarget, planOpenOne,
            treeBoundaryPlan, treeLeftPlan, treeRightPlan,
            Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq, true_and]
            at hspec
          obtain ⟨hcEq, hnEq, hmEq⟩ := hspec
          refine ⟨?_, ?_, ⟨t.controlAt (playNodes t path n), rfl⟩, rfl⟩
          · refine
              ⟨CL.monitor.step (CL.start atom.1)
                  (GlobalJournalLabel.leftNarrowed (t.labeledTree (playNodes t path n)))
                  m'.2,
                leftOpenSubset atom
                  (GlobalJournalLabel.leftNarrowed (t.labeledTree (playNodes t path n)))
                  m'.2, ?_, ?_⟩
            · rw [globalRunIn_append, hrun]
              simp only [globalJournalStep]
            · refine
                Finset.mem_image.mpr
                  ⟨m'.1, Finset.mem_univ _, ?_⟩
              show
                (A.step atom.1
                    (leftRoundRecord m'
                      ((GlobalJournalLabel.leftNarrowed (t.labelOf
                          (t.controlAt (playNodes t path n)))).2
                        (atom.1, atom.1) m')
                      ((GlobalJournalLabel.leftNarrowed (t.labelOf
                          (t.controlAt (playNodes t path n)))).1
                        m'.2)),
                  A.minPriorityState atom.1
                    (A.step atom.1
                      (leftRoundRecord m'
                        ((GlobalJournalLabel.leftNarrowed (t.labelOf
                            (t.controlAt (playNodes t path n)))).2
                          (atom.1, atom.1) m')
                        ((GlobalJournalLabel.leftNarrowed (t.labelOf
                            (t.controlAt (playNodes t path n)))).1
                          m'.2)))) =
                  _
              rw [← hnEq]
          · rw [controlAt_concat]
            exact hcEq
        · -- right opening
          have hnext' :
              path (n + 1) =
                Sum.inr (Sum.inr (Sum.inr (Sum.inl
                  (treeRightPlan t (t.controlAt (playNodes t path n)),
                    treeChainPlan t,
                    ULift.up
                      (t.step (t.controlAt (playNodes t path n))
                        (Sum.inr (Sum.inr move.2))),
                    A.step atom.1
                      (rightRoundRecord move
                        ((GlobalJournalLabel.rightNarrowed (t.labelOf
                            (t.controlAt (playNodes t path n)))).1
                          move.2)
                        ((GlobalJournalLabel.rightNarrowed (t.labelOf
                            (t.controlAt (playNodes t path n)))).2
                          (atom.1, atom.1) (move.1, move.2))),
                    A.minPriorityState atom.1
                      (A.step atom.1
                        (rightRoundRecord move
                          ((GlobalJournalLabel.rightNarrowed (t.labelOf
                              (t.controlAt (playNodes t path n)))).1
                            move.2)
                          ((GlobalJournalLabel.rightNarrowed (t.labelOf
                              (t.controlAt (playNodes t path n)))).2
                            (atom.1, atom.1) (move.1, move.2)))))))) := by
            rw [hnext]
            rfl
          have hc :
              ∃ move' : In₂ × In₁,
                path (n + 1) =
                  A.boundaryOpenRightTarget
                    (treeBoundaryPlan t
                      (t.controlAt (playNodes t path n)))
                    (atom.1, atom.1).1 move' :=
            ⟨move, hnext⟩
          rw [hnext'] at hc
          show TreeTracks t CL CR CC path
            (playNodes t path n ++
              stepDirections t (path n) (path (n + 1))) (n + 1)
          unfold TreeTracks
          rw [hpos, hnext', stepDirections_committed_blockR t _ _ _ hc]
          have hspec := Classical.choose_spec hc
          set m' := Classical.choose hc with hm'def
          simp only [boundaryOpenRightTarget, planOpenTwo,
            treeBoundaryPlan, treeLeftPlan, treeRightPlan,
            Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq, true_and] at hspec
          obtain ⟨hcEq, hnEq, hmEq⟩ := hspec
          refine ⟨?_, ?_, ⟨t.controlAt (playNodes t path n), rfl⟩, rfl⟩
          · refine
              ⟨CR.monitor.step (CR.start atom.1)
                  (GlobalJournalLabel.rightNarrowed (t.labeledTree (playNodes t path n)))
                  m'.2,
                rightOpenSubset atom
                  (GlobalJournalLabel.rightNarrowed (t.labeledTree (playNodes t path n)))
                  m'.2, ?_, ?_⟩
            · rw [globalRunIn_append, hrun]
              simp only [globalJournalStep]
            · refine
                Finset.mem_image.mpr
                  ⟨m'.1, Finset.mem_univ _, ?_⟩
              show
                (A.step atom.1
                    (rightRoundRecord m'
                      ((GlobalJournalLabel.rightNarrowed (t.labelOf
                          (t.controlAt (playNodes t path n)))).1
                        m'.2)
                      ((GlobalJournalLabel.rightNarrowed (t.labelOf
                          (t.controlAt (playNodes t path n)))).2
                        (atom.1, atom.1)
                        (m'.1,
                          m'.2))),
                  A.minPriorityState atom.1
                    (A.step atom.1
                      (rightRoundRecord m'
                        ((GlobalJournalLabel.rightNarrowed (t.labelOf
                            (t.controlAt (playNodes t path n)))).1
                          m'.2)
                        ((GlobalJournalLabel.rightNarrowed (t.labelOf
                            (t.controlAt (playNodes t path n)))).2
                          (atom.1, atom.1)
                          (m'.1,
                            m'.2))))) =
                  _
              rw [← hnEq]
          · rw [controlAt_concat]
            exact hcEq
      -- left block: continue or close
      · obtain ⟨⟨checker, threads, hrun, hmem⟩, hctl, ⟨root, hplan⟩,
          hchain⟩ := ih
        subst hplan
        subst hctl
        subst hchain
        have hstep' :
            (∃ move : In₁ × In₂,
              path (n + 1) =
                A.leftContinueTarget (treeLeftPlan t root)
                  (treeChainPlan t)
                  (ULift.up (t.controlAt (playNodes t path n))) state
                  minState move) ∨
            (∃ move : In₁ × In₂,
              path (n + 1) =
                A.leftCloseTarget (treeLeftPlan t root)
                  (ULift.up (t.controlAt (playNodes t path n))) state
                  minState move) ∨
            (∃ move : In₁ × In₂,
              path (n + 1) =
                A.leftReverseTarget (treeLeftPlan t root)
                  (treeChainPlan t)
                  (ULift.up (t.controlAt (playNodes t path n))) state
                  minState move) :=
          hstep
        rcases hstep' with ⟨move, hnext⟩ | ⟨move, hnext⟩ | ⟨move, hnext⟩
        · -- continuation round
          have hnext' :
              path (n + 1) =
                Sum.inr (Sum.inr (Sum.inl
                  (treeLeftPlan t root,
                    treeChainPlan t,
                    ULift.up
                      (t.step (t.controlAt (playNodes t path n))
                        (Sum.inr (Sum.inl move.2))),
                    A.step state
                      (leftRoundRecord move
                        ((GlobalJournalLabel.leftNarrowed (t.labelOf
                            (t.controlAt (playNodes t path n)))).2
                          (state, minState) move)
                        ((GlobalJournalLabel.leftNarrowed (t.labelOf
                            (t.controlAt (playNodes t path n)))).1
                          move.2)),
                    A.minPriorityState minState
                      (A.step state
                        (leftRoundRecord move
                          ((GlobalJournalLabel.leftNarrowed (t.labelOf
                              (t.controlAt (playNodes t path n)))).2
                            (state, minState) move)
                          ((GlobalJournalLabel.leftNarrowed (t.labelOf
                              (t.controlAt (playNodes t path n)))).1
                            move.2)))))) := by
            rw [hnext]
            rfl
          have hc :
              ∃ move' : In₁ × In₂,
                path (n + 1) =
                  A.leftContinueTarget
                    (treeLeftPlan t root, treeChainPlan t,
                      ULift.up.{max u v x y, s}
                        (t.controlAt (playNodes t path n)), state,
                      minState).1
                    (treeLeftPlan t root, treeChainPlan t,
                      ULift.up.{max u v x y, s}
                        (t.controlAt (playNodes t path n)), state,
                      minState).2.1
                    (treeLeftPlan t root, treeChainPlan t,
                      ULift.up.{max u v x y, s}
                        (t.controlAt (playNodes t path n)), state,
                      minState).2.2.1
                    (treeLeftPlan t root, treeChainPlan t,
                      ULift.up.{max u v x y, s}
                        (t.controlAt (playNodes t path n)), state,
                      minState).2.2.2.1
                    (treeLeftPlan t root, treeChainPlan t,
                      ULift.up.{max u v x y, s}
                        (t.controlAt (playNodes t path n)), state,
                      minState).2.2.2.2 move' :=
            ⟨move, hnext⟩
          rw [hnext'] at hc
          show TreeTracks t CL CR CC path
            (playNodes t path n ++
              stepDirections t (path n) (path (n + 1))) (n + 1)
          unfold TreeTracks
          rw [hpos, hnext', stepDirections_blockL_blockL t _ _ hc]
          have hspec := Classical.choose_spec hc
          set m' := Classical.choose hc with hm'def
          simp only [leftContinueTarget, treeLeftPlan, Sum.inr.injEq,
            Sum.inl.injEq, Prod.mk.injEq, true_and] at hspec
          obtain ⟨hcEq, hnEq, hmEq⟩ := hspec
          refine ⟨?_, ?_, ⟨root, rfl⟩, rfl⟩
          · refine
              ⟨CL.monitor.step checker
                  (GlobalJournalLabel.leftNarrowed (t.labeledTree (playNodes t path n)))
                  m'.2,
                leftStepSubset threads
                  (GlobalJournalLabel.leftNarrowed (t.labeledTree (playNodes t path n)))
                  m'.2, ?_, ?_⟩
            · rw [globalRunIn_append, hrun]
              simp only [globalJournalStep]
            · refine
                Finset.mem_biUnion.mpr
                  ⟨(state, minState), hmem,
                    Finset.mem_image.mpr
                      ⟨m'.1, Finset.mem_univ _, ?_⟩⟩
              show
                (A.step state
                    (leftRoundRecord m'
                      ((GlobalJournalLabel.leftNarrowed (t.labelOf
                          (t.controlAt (playNodes t path n)))).2
                        (state, minState) m')
                      ((GlobalJournalLabel.leftNarrowed (t.labelOf
                          (t.controlAt (playNodes t path n)))).1
                        m'.2)),
                  A.minPriorityState minState
                    (A.step state
                      (leftRoundRecord m'
                        ((GlobalJournalLabel.leftNarrowed (t.labelOf
                            (t.controlAt (playNodes t path n)))).2
                          (state, minState) m')
                        ((GlobalJournalLabel.leftNarrowed (t.labelOf
                            (t.controlAt (playNodes t path n)))).1
                          m'.2)))) =
                  _
              rw [← hnEq]
          · rw [controlAt_concat]
            exact hcEq
        · -- closing round
          have hnext' :
              path (n + 1) =
                Sum.inl
                  (A.step state
                      (bothRoundRecord move
                        ((GlobalJournalLabel.leftNarrowed (t.labelOf
                            (t.controlAt (playNodes t path n)))).2
                          (state, minState) move)
                        (GlobalJournalLabel.leftClose (t.labelOf
                            (t.controlAt (playNodes t path n)))
                          (state, minState) move)),
                    minState) := by
            rw [hnext]
            rfl
          refine tracks_bnd_arrival t CL CR CC path n _ hnext' ?_ ?_
          · show
              globalRunIn CL CR CC t.labeledTree
                  (Sum.inl (A.initial, A.initial))
                  (playNodes t path n ++
                    stepDirections t (path n) (path (n + 1))) =
                _
            rw [hpos, hnext', stepDirections_blockL_bnd,
              globalRunIn_append, hrun]
            simp only [globalJournalStep]
            rw [if_pos]
            exact
              Finset.mem_biUnion.mpr
                ⟨(state, minState), hmem,
                  Finset.mem_image.mpr ⟨move, Finset.mem_univ _, rfl⟩⟩
          · show
              controlAfter t (some (path n)) _ =
                t.controlAt
                  (playNodes t path n ++
                    stepDirections t (path n) (path (n + 1)))
            rw [hpos, hnext', stepDirections_blockL_bnd,
              controlAt_concat]
            simp only [controlAfter]
        · -- directly reversing round
          have hnext' :
              path (n + 1) =
                Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
                  (treeChainPlan t,
                    ULift.up
                      (t.step (t.controlAt (playNodes t path n))
                        (Sum.inr (Sum.inr move.1))),
                    (A.step state
                        (rightRoundRecord (move.2, move.1)
                          (GlobalJournalLabel.leftRev (t.labelOf
                              (t.controlAt (playNodes t path n)))
                            (state, minState) move.1)
                          (GlobalJournalLabel.leftClose (t.labelOf
                              (t.controlAt (playNodes t path n)))
                            (state, minState) move)),
                      A.minPriorityState minState
                        (A.step state
                          (rightRoundRecord (move.2, move.1)
                            (GlobalJournalLabel.leftRev (t.labelOf
                                (t.controlAt (playNodes t path n)))
                              (state, minState) move.1)
                            (GlobalJournalLabel.leftClose (t.labelOf
                                (t.controlAt (playNodes t path n)))
                              (state, minState) move)))),
                    A.step state
                      (rightRoundRecord (move.2, move.1)
                        (GlobalJournalLabel.leftRev (t.labelOf
                            (t.controlAt (playNodes t path n)))
                          (state, minState) move.1)
                        (GlobalJournalLabel.leftClose (t.labelOf
                            (t.controlAt (playNodes t path n)))
                          (state, minState) move)),
                    A.minPriorityState minState
                      (A.step state
                        (rightRoundRecord (move.2, move.1)
                          (GlobalJournalLabel.leftRev (t.labelOf
                              (t.controlAt (playNodes t path n)))
                            (state, minState) move.1)
                          (GlobalJournalLabel.leftClose (t.labelOf
                              (t.controlAt (playNodes t path n)))
                            (state, minState) move)))))))) := by
            rw [hnext]
            rfl
          have hc :
              ∃ move' : In₁ × In₂,
                path (n + 1) =
                  A.leftReverseTarget
                    (treeLeftPlan t root, treeChainPlan t,
                      ULift.up.{max u v x y, s}
                        (t.controlAt (playNodes t path n)), state,
                      minState).1
                    (treeLeftPlan t root, treeChainPlan t,
                      ULift.up.{max u v x y, s}
                        (t.controlAt (playNodes t path n)), state,
                      minState).2.1
                    (treeLeftPlan t root, treeChainPlan t,
                      ULift.up.{max u v x y, s}
                        (t.controlAt (playNodes t path n)), state,
                      minState).2.2.1
                    (treeLeftPlan t root, treeChainPlan t,
                      ULift.up.{max u v x y, s}
                        (t.controlAt (playNodes t path n)), state,
                      minState).2.2.2.1
                    (treeLeftPlan t root, treeChainPlan t,
                      ULift.up.{max u v x y, s}
                        (t.controlAt (playNodes t path n)), state,
                      minState).2.2.2.2 move' :=
            ⟨move, hnext⟩
          rw [hnext'] at hc
          show TreeTracks t CL CR CC path
            (playNodes t path n ++
              stepDirections t (path n) (path (n + 1))) (n + 1)
          unfold TreeTracks
          rw [hpos, hnext', stepDirections_blockL_revR t _ _ hc]
          have hspec := Classical.choose_spec hc
          set m' := Classical.choose hc with hm'def
          simp only [leftReverseTarget, treeLeftPlan, treeChainPlan,
            Sum.inr.injEq, Prod.mk.injEq, true_and] at hspec
          obtain ⟨hcEq, heEq, hnEq, hmEq⟩ := hspec
          refine ⟨?_, ?_, rfl⟩
          · refine
              ⟨CC.start
                  (leftReverseSubset threads
                    (GlobalJournalLabel.leftClose
                      (t.labeledTree (playNodes t path n)))
                    (GlobalJournalLabel.leftRev
                      (t.labeledTree (playNodes t path n)))
                    m'.1),
                leftReverseSubset threads
                  (GlobalJournalLabel.leftClose
                    (t.labeledTree (playNodes t path n)))
                  (GlobalJournalLabel.leftRev
                    (t.labeledTree (playNodes t path n)))
                  m'.1, ?_, ?_⟩
            · rw [globalRunIn_append, hrun]
              simp only [globalJournalStep]
            · refine
                Finset.mem_biUnion.mpr
                  ⟨(state, minState), hmem,
                    Finset.mem_image.mpr
                      ⟨m'.2, Finset.mem_univ _, ?_⟩⟩
              show
                ((A.step state
                    (rightRoundRecord (m'.2, m'.1)
                      (GlobalJournalLabel.leftRev (t.labelOf
                          (t.controlAt (playNodes t path n)))
                        (state, minState) m'.1)
                      (GlobalJournalLabel.leftClose (t.labelOf
                          (t.controlAt (playNodes t path n)))
                        (state, minState) m')),
                    A.minPriorityState minState
                      (A.step state
                        (rightRoundRecord (m'.2, m'.1)
                          (GlobalJournalLabel.leftRev (t.labelOf
                              (t.controlAt (playNodes t path n)))
                            (state, minState) m'.1)
                          (GlobalJournalLabel.leftClose (t.labelOf
                              (t.controlAt (playNodes t path n)))
                            (state, minState) m')))),
                  A.step state
                    (rightRoundRecord (m'.2, m'.1)
                      (GlobalJournalLabel.leftRev (t.labelOf
                          (t.controlAt (playNodes t path n)))
                        (state, minState) m'.1)
                      (GlobalJournalLabel.leftClose (t.labelOf
                          (t.controlAt (playNodes t path n)))
                        (state, minState) m')),
                  A.minPriorityState minState
                    (A.step state
                      (rightRoundRecord (m'.2, m'.1)
                        (GlobalJournalLabel.leftRev (t.labelOf
                            (t.controlAt (playNodes t path n)))
                          (state, minState) m'.1)
                        (GlobalJournalLabel.leftClose (t.labelOf
                            (t.controlAt (playNodes t path n)))
                          (state, minState) m')))) =
                  _
              rw [← hnEq]
          · rw [controlAt_concat]
            exact hcEq
      -- right block: continue or close
      · obtain ⟨⟨checker, threads, hrun, hmem⟩, hctl, ⟨root, hplan⟩,
          hchain⟩ := ih
        subst hplan
        subst hctl
        subst hchain
        have hstep' :
            (∃ move : In₂ × In₁,
              path (n + 1) =
                A.rightContinueTarget (treeRightPlan t root)
                  (treeChainPlan t)
                  (ULift.up (t.controlAt (playNodes t path n))) state
                  minState move) ∨
            (∃ move : In₂ × In₁,
              path (n + 1) =
                A.rightCloseTarget (treeRightPlan t root)
                  (ULift.up (t.controlAt (playNodes t path n))) state
                  minState move) ∨
            (∃ move : In₂ × In₁,
              path (n + 1) =
                A.rightReverseTarget (treeRightPlan t root)
                  (treeChainPlan t)
                  (ULift.up (t.controlAt (playNodes t path n))) state
                  minState move) :=
          hstep
        rcases hstep' with ⟨move, hnext⟩ | ⟨move, hnext⟩ | ⟨move, hnext⟩
        · -- continuation round
          have hnext' :
              path (n + 1) =
                Sum.inr (Sum.inr (Sum.inr (Sum.inl
                  (treeRightPlan t root,
                    treeChainPlan t,
                    ULift.up
                      (t.step (t.controlAt (playNodes t path n))
                        (Sum.inr (Sum.inr move.2))),
                    A.step state
                      (rightRoundRecord move
                        ((GlobalJournalLabel.rightNarrowed (t.labelOf
                            (t.controlAt (playNodes t path n)))).1
                          move.2)
                        ((GlobalJournalLabel.rightNarrowed (t.labelOf
                            (t.controlAt (playNodes t path n)))).2
                          (state, minState) move)),
                    A.minPriorityState minState
                      (A.step state
                        (rightRoundRecord move
                          ((GlobalJournalLabel.rightNarrowed (t.labelOf
                              (t.controlAt (playNodes t path n)))).1
                            move.2)
                          ((GlobalJournalLabel.rightNarrowed (t.labelOf
                              (t.controlAt (playNodes t path n)))).2
                            (state, minState) move))))))) := by
            rw [hnext]
            rfl
          have hc :
              ∃ move' : In₂ × In₁,
                path (n + 1) =
                  A.rightContinueTarget
                    (treeRightPlan t root, treeChainPlan t,
                      ULift.up.{max u v x y, s}
                        (t.controlAt (playNodes t path n)), state,
                      minState).1
                    (treeRightPlan t root, treeChainPlan t,
                      ULift.up.{max u v x y, s}
                        (t.controlAt (playNodes t path n)), state,
                      minState).2.1
                    (treeRightPlan t root, treeChainPlan t,
                      ULift.up.{max u v x y, s}
                        (t.controlAt (playNodes t path n)), state,
                      minState).2.2.1
                    (treeRightPlan t root, treeChainPlan t,
                      ULift.up.{max u v x y, s}
                        (t.controlAt (playNodes t path n)), state,
                      minState).2.2.2.1
                    (treeRightPlan t root, treeChainPlan t,
                      ULift.up.{max u v x y, s}
                        (t.controlAt (playNodes t path n)), state,
                      minState).2.2.2.2 move' :=
            ⟨move, hnext⟩
          rw [hnext'] at hc
          show TreeTracks t CL CR CC path
            (playNodes t path n ++
              stepDirections t (path n) (path (n + 1))) (n + 1)
          unfold TreeTracks
          rw [hpos, hnext', stepDirections_blockR_blockR t _ _ hc]
          have hspec := Classical.choose_spec hc
          set m' := Classical.choose hc with hm'def
          simp only [rightContinueTarget, treeRightPlan, Sum.inr.injEq,
            Sum.inl.injEq, Prod.mk.injEq, true_and] at hspec
          obtain ⟨hcEq, hnEq, hmEq⟩ := hspec
          refine ⟨?_, ?_, ⟨root, rfl⟩, rfl⟩
          · refine
              ⟨CR.monitor.step checker
                  (GlobalJournalLabel.rightNarrowed (t.labeledTree (playNodes t path n)))
                  m'.2,
                rightStepSubset threads
                  (GlobalJournalLabel.rightNarrowed (t.labeledTree (playNodes t path n)))
                  m'.2, ?_, ?_⟩
            · rw [globalRunIn_append, hrun]
              simp only [globalJournalStep]
            · refine
                Finset.mem_biUnion.mpr
                  ⟨(state, minState), hmem,
                    Finset.mem_image.mpr
                      ⟨m'.1, Finset.mem_univ _, ?_⟩⟩
              show
                (A.step state
                    (rightRoundRecord m'
                      ((GlobalJournalLabel.rightNarrowed (t.labelOf
                          (t.controlAt (playNodes t path n)))).1
                        m'.2)
                      ((GlobalJournalLabel.rightNarrowed (t.labelOf
                          (t.controlAt (playNodes t path n)))).2
                        (state, minState) m')),
                  A.minPriorityState minState
                    (A.step state
                      (rightRoundRecord m'
                        ((GlobalJournalLabel.rightNarrowed (t.labelOf
                            (t.controlAt (playNodes t path n)))).1
                          m'.2)
                        ((GlobalJournalLabel.rightNarrowed (t.labelOf
                            (t.controlAt (playNodes t path n)))).2
                          (state, minState) m')))) =
                  _
              rw [← hnEq]
          · rw [controlAt_concat]
            exact hcEq
        · -- closing round
          have hnext' :
              path (n + 1) =
                Sum.inl
                  (A.step state
                      (bothRoundRecord (move.2, move.1)
                        (GlobalJournalLabel.rightClose (t.labelOf
                            (t.controlAt (playNodes t path n)))
                          (state, minState) move)
                        ((GlobalJournalLabel.rightNarrowed (t.labelOf
                            (t.controlAt (playNodes t path n)))).2
                          (state, minState) move)),
                    minState) := by
            rw [hnext]
            rfl
          refine tracks_bnd_arrival t CL CR CC path n _ hnext' ?_ ?_
          · show
              globalRunIn CL CR CC t.labeledTree
                  (Sum.inl (A.initial, A.initial))
                  (playNodes t path n ++
                    stepDirections t (path n) (path (n + 1))) =
                _
            rw [hpos, hnext', stepDirections_blockR_bnd,
              globalRunIn_append, hrun]
            simp only [globalJournalStep]
            rw [if_pos]
            exact
              Finset.mem_biUnion.mpr
                ⟨(state, minState), hmem,
                  Finset.mem_image.mpr ⟨move, Finset.mem_univ _, rfl⟩⟩
          · show
              controlAfter t (some (path n)) _ =
                t.controlAt
                  (playNodes t path n ++
                    stepDirections t (path n) (path (n + 1)))
            rw [hpos, hnext', stepDirections_blockR_bnd,
              controlAt_concat]
            simp only [controlAfter]

        · -- directly reversing round
          have hnext' :
              path (n + 1) =
                Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl
                  (treeChainPlan t,
                    ULift.up
                      (t.step (t.controlAt (playNodes t path n))
                        (Sum.inr (Sum.inl move.1))),
                    (A.step state
                        (leftRoundRecord (move.2, move.1)
                          (GlobalJournalLabel.rightClose (t.labelOf
                              (t.controlAt (playNodes t path n)))
                            (state, minState) move)
                          (GlobalJournalLabel.rightRev (t.labelOf
                              (t.controlAt (playNodes t path n)))
                            (state, minState) move.1)),
                      A.minPriorityState minState
                        (A.step state
                          (leftRoundRecord (move.2, move.1)
                            (GlobalJournalLabel.rightClose (t.labelOf
                                (t.controlAt (playNodes t path n)))
                              (state, minState) move)
                            (GlobalJournalLabel.rightRev (t.labelOf
                                (t.controlAt (playNodes t path n)))
                              (state, minState) move.1)))),
                    A.step state
                      (leftRoundRecord (move.2, move.1)
                        (GlobalJournalLabel.rightClose (t.labelOf
                            (t.controlAt (playNodes t path n)))
                          (state, minState) move)
                        (GlobalJournalLabel.rightRev (t.labelOf
                            (t.controlAt (playNodes t path n)))
                          (state, minState) move.1)),
                    A.minPriorityState minState
                      (A.step state
                        (leftRoundRecord (move.2, move.1)
                          (GlobalJournalLabel.rightClose (t.labelOf
                              (t.controlAt (playNodes t path n)))
                            (state, minState) move)
                          (GlobalJournalLabel.rightRev (t.labelOf
                              (t.controlAt (playNodes t path n)))
                            (state, minState) move.1)))))))) := by
            rw [hnext]
            rfl
          have hc :
              ∃ move' : In₂ × In₁,
                path (n + 1) =
                  A.rightReverseTarget
                    (treeRightPlan t root, treeChainPlan t,
                      ULift.up.{max u v x y, s}
                        (t.controlAt (playNodes t path n)), state,
                      minState).1
                    (treeRightPlan t root, treeChainPlan t,
                      ULift.up.{max u v x y, s}
                        (t.controlAt (playNodes t path n)), state,
                      minState).2.1
                    (treeRightPlan t root, treeChainPlan t,
                      ULift.up.{max u v x y, s}
                        (t.controlAt (playNodes t path n)), state,
                      minState).2.2.1
                    (treeRightPlan t root, treeChainPlan t,
                      ULift.up.{max u v x y, s}
                        (t.controlAt (playNodes t path n)), state,
                      minState).2.2.2.1
                    (treeRightPlan t root, treeChainPlan t,
                      ULift.up.{max u v x y, s}
                        (t.controlAt (playNodes t path n)), state,
                      minState).2.2.2.2 move' :=
            ⟨move, hnext⟩
          rw [hnext'] at hc
          show TreeTracks t CL CR CC path
            (playNodes t path n ++
              stepDirections t (path n) (path (n + 1))) (n + 1)
          unfold TreeTracks
          rw [hpos, hnext', stepDirections_blockR_revL t _ _ hc]
          have hspec := Classical.choose_spec hc
          set m' := Classical.choose hc with hm'def
          simp only [rightReverseTarget, treeRightPlan, treeChainPlan,
            Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq, true_and] at hspec
          obtain ⟨hcEq, heEq, hnEq, hmEq⟩ := hspec
          refine ⟨?_, ?_, rfl⟩
          · refine
              ⟨CC.start
                  (rightReverseSubset threads
                    (GlobalJournalLabel.rightClose
                      (t.labeledTree (playNodes t path n)))
                    (GlobalJournalLabel.rightRev
                      (t.labeledTree (playNodes t path n)))
                    m'.1),
                rightReverseSubset threads
                  (GlobalJournalLabel.rightClose
                    (t.labeledTree (playNodes t path n)))
                  (GlobalJournalLabel.rightRev
                    (t.labeledTree (playNodes t path n)))
                  m'.1, ?_, ?_⟩
            · rw [globalRunIn_append, hrun]
              simp only [globalJournalStep]
            · refine
                Finset.mem_biUnion.mpr
                  ⟨(state, minState), hmem,
                    Finset.mem_image.mpr
                      ⟨m'.2, Finset.mem_univ _, ?_⟩⟩
              show
                ((A.step state
                    (leftRoundRecord (m'.2, m'.1)
                      (GlobalJournalLabel.rightClose (t.labelOf
                          (t.controlAt (playNodes t path n)))
                        (state, minState) m')
                      (GlobalJournalLabel.rightRev (t.labelOf
                          (t.controlAt (playNodes t path n)))
                        (state, minState) m'.1)),
                    A.minPriorityState minState
                      (A.step state
                        (leftRoundRecord (m'.2, m'.1)
                          (GlobalJournalLabel.rightClose (t.labelOf
                              (t.controlAt (playNodes t path n)))
                            (state, minState) m')
                          (GlobalJournalLabel.rightRev (t.labelOf
                              (t.controlAt (playNodes t path n)))
                            (state, minState) m'.1)))),
                  A.step state
                    (leftRoundRecord (m'.2, m'.1)
                      (GlobalJournalLabel.rightClose (t.labelOf
                          (t.controlAt (playNodes t path n)))
                        (state, minState) m')
                      (GlobalJournalLabel.rightRev (t.labelOf
                          (t.controlAt (playNodes t path n)))
                        (state, minState) m'.1)),
                  A.minPriorityState minState
                    (A.step state
                      (leftRoundRecord (m'.2, m'.1)
                        (GlobalJournalLabel.rightClose (t.labelOf
                            (t.controlAt (playNodes t path n)))
                          (state, minState) m')
                        (GlobalJournalLabel.rightRev (t.labelOf
                            (t.controlAt (playNodes t path n)))
                          (state, minState) m'.1)))) =
                  _
              rw [← hnEq]
          · rw [controlAt_concat]
            exact hcEq
      -- reversed left block: continue, close, or reverse again
      · obtain ⟨⟨checker, threads, hrun, hmem⟩, hctl, hchain⟩ := ih
        subst hctl
        subst hchain
        have hstep' :
            (∃ move : In₁ × In₂,
              path (n + 1) =
                A.revLeftContinueTarget (treeChainPlan t)
                  (ULift.up (t.controlAt (playNodes t path n))) entry
                  state minState move) ∨
            (∃ move : In₁ × In₂,
              path (n + 1) =
                A.revLeftCloseTarget (treeChainPlan t)
                  (ULift.up (t.controlAt (playNodes t path n))) entry
                  state minState move) ∨
            (∃ move : In₁ × In₂,
              path (n + 1) =
                A.revLeftReverseTarget (treeChainPlan t)
                  (ULift.up (t.controlAt (playNodes t path n))) entry
                  state minState move) :=
          hstep
        rcases hstep' with ⟨move, hnext⟩ | ⟨move, hnext⟩ | ⟨move, hnext⟩
        · -- continuation round
          have hnext' :
              path (n + 1) =
                Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl
                  (treeChainPlan t,
                    ULift.up
                      (t.step (t.controlAt (playNodes t path n))
                        (Sum.inr (Sum.inl move.2))),
                    entry,
                    A.step state
                      (leftRoundRecord move
                        ((GlobalJournalLabel.revLeft (t.labelOf
                            (t.controlAt (playNodes t path n)))).1
                          (entry, state, minState) move)
                        ((GlobalJournalLabel.revLeft (t.labelOf
                            (t.controlAt (playNodes t path n)))).2.2.1
                          entry move.2)),
                    A.minPriorityState minState
                      (A.step state
                        (leftRoundRecord move
                        ((GlobalJournalLabel.revLeft (t.labelOf
                            (t.controlAt (playNodes t path n)))).1
                          (entry, state, minState) move)
                        ((GlobalJournalLabel.revLeft (t.labelOf
                            (t.controlAt (playNodes t path n)))).2.2.1
                          entry move.2)))))))) := by
            rw [hnext]
            rfl
          have hc :
              ∃ move' : In₁ × In₂,
                path (n + 1) =
                  A.revLeftContinueTarget
                    (treeChainPlan t,
                      ULift.up.{max u v x y, s}
                        (t.controlAt (playNodes t path n)), entry,
                      state, minState).1
                    (treeChainPlan t,
                      ULift.up.{max u v x y, s}
                        (t.controlAt (playNodes t path n)), entry,
                      state, minState).2.1
                    (treeChainPlan t,
                      ULift.up.{max u v x y, s}
                        (t.controlAt (playNodes t path n)), entry,
                      state, minState).2.2.1
                    (treeChainPlan t,
                      ULift.up.{max u v x y, s}
                        (t.controlAt (playNodes t path n)), entry,
                      state, minState).2.2.2.1
                    (treeChainPlan t,
                      ULift.up.{max u v x y, s}
                        (t.controlAt (playNodes t path n)), entry,
                      state, minState).2.2.2.2 move' :=
            ⟨move, hnext⟩
          rw [hnext'] at hc
          show TreeTracks t CL CR CC path
            (playNodes t path n ++
              stepDirections t (path n) (path (n + 1))) (n + 1)
          unfold TreeTracks
          rw [hpos, hnext', stepDirections_revL_revL t _ _ hc]
          have hspec := Classical.choose_spec hc
          set m' := Classical.choose hc with hm'def
          simp only [revLeftContinueTarget, treeChainPlan,
            Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq, true_and] at hspec
          obtain ⟨hcEq, hnEq, hmEq⟩ := hspec
          refine ⟨?_, ?_, rfl⟩
          · refine
              ⟨CC.monitor.step checker
                  (Sum.inl (GlobalJournalLabel.revLeft
                    (t.labeledTree (playNodes t path n))))
                  (Sum.inl m'.2),
                revLeftStepSubset threads
                  (GlobalJournalLabel.revLeft
                    (t.labeledTree (playNodes t path n)))
                  m'.2, ?_, ?_⟩
            · rw [globalRunIn_append, hrun]
              simp only [globalJournalStep]
            · refine
                Finset.mem_biUnion.mpr
                  ⟨(entry, state, minState), hmem,
                    Finset.mem_image.mpr
                      ⟨m'.1, Finset.mem_univ _, ?_⟩⟩
              show
                (entry,
                  A.step state
                    (leftRoundRecord m'
                      ((GlobalJournalLabel.revLeft (t.labelOf
                          (t.controlAt (playNodes t path n)))).1
                          (entry, state, minState) m')
                      ((GlobalJournalLabel.revLeft (t.labelOf
                          (t.controlAt (playNodes t path n)))).2.2.1
                          entry m'.2)),
                  A.minPriorityState minState
                    (A.step state
                      (leftRoundRecord m'
                      ((GlobalJournalLabel.revLeft (t.labelOf
                          (t.controlAt (playNodes t path n)))).1
                          (entry, state, minState) m')
                      ((GlobalJournalLabel.revLeft (t.labelOf
                          (t.controlAt (playNodes t path n)))).2.2.1
                          entry m'.2)))) =
                  _
              rw [← hnEq]
          · rw [controlAt_concat]
            exact hcEq
        · -- closing round
          have hnext' :
              path (n + 1) =
                Sum.inl
                  (A.step state
                      (bothRoundRecord move
                        ((GlobalJournalLabel.revLeft (t.labelOf
                            (t.controlAt (playNodes t path n)))).1
                          (entry, state, minState) move)
                        ((GlobalJournalLabel.revLeft (t.labelOf
                            (t.controlAt (playNodes t path n)))).2.2.2
                          (entry, state, minState) move)),
                    minState) := by
            rw [hnext]
            rfl
          refine tracks_bnd_arrival t CL CR CC path n _ hnext' ?_ ?_
          · show
              globalRunIn CL CR CC t.labeledTree
                  (Sum.inl (A.initial, A.initial))
                  (playNodes t path n ++
                    stepDirections t (path n) (path (n + 1))) =
                _
            rw [hpos, hnext', stepDirections_revL_bnd,
              globalRunIn_append, hrun]
            simp only [globalJournalStep]
            rw [if_pos]
            exact
              Finset.mem_biUnion.mpr
                ⟨(entry, state, minState), hmem,
                  Finset.mem_image.mpr ⟨move, Finset.mem_univ _, rfl⟩⟩
          · show
              controlAfter t (some (path n)) _ =
                t.controlAt
                  (playNodes t path n ++
                    stepDirections t (path n) (path (n + 1)))
            rw [hpos, hnext', stepDirections_revL_bnd,
              controlAt_concat]
            simp only [controlAfter]
        · -- re-reversing round
          have hnext' :
              path (n + 1) =
                Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
                  (treeChainPlan t,
                    ULift.up
                      (t.step (t.controlAt (playNodes t path n))
                        (Sum.inr (Sum.inr move.1))),
                    (A.step state
                        (rightRoundRecord (move.2, move.1)
                          ((GlobalJournalLabel.revLeft (t.labelOf
                              (t.controlAt (playNodes t path n)))).2.1
                            (entry, state, minState) move.1)
                          ((GlobalJournalLabel.revLeft (t.labelOf
                              (t.controlAt (playNodes t path n)))).2.2.2
                            (entry, state, minState) move)),
                      A.minPriorityState minState
                        (A.step state
                          (rightRoundRecord (move.2, move.1)
                          ((GlobalJournalLabel.revLeft (t.labelOf
                              (t.controlAt (playNodes t path n)))).2.1
                            (entry, state, minState) move.1)
                          ((GlobalJournalLabel.revLeft (t.labelOf
                              (t.controlAt (playNodes t path n)))).2.2.2
                            (entry, state, minState) move)))),
                    A.step state
                      (rightRoundRecord (move.2, move.1)
                        ((GlobalJournalLabel.revLeft (t.labelOf
                            (t.controlAt (playNodes t path n)))).2.1
                          (entry, state, minState) move.1)
                        ((GlobalJournalLabel.revLeft (t.labelOf
                            (t.controlAt (playNodes t path n)))).2.2.2
                          (entry, state, minState) move)),
                    A.minPriorityState minState
                      (A.step state
                        (rightRoundRecord (move.2, move.1)
                        ((GlobalJournalLabel.revLeft (t.labelOf
                            (t.controlAt (playNodes t path n)))).2.1
                          (entry, state, minState) move.1)
                        ((GlobalJournalLabel.revLeft (t.labelOf
                            (t.controlAt (playNodes t path n)))).2.2.2
                          (entry, state, minState) move)))))))) := by
            rw [hnext]
            rfl
          have hc :
              ∃ move' : In₁ × In₂,
                path (n + 1) =
                  A.revLeftReverseTarget
                    (treeChainPlan t,
                      ULift.up.{max u v x y, s}
                        (t.controlAt (playNodes t path n)), entry,
                      state, minState).1
                    (treeChainPlan t,
                      ULift.up.{max u v x y, s}
                        (t.controlAt (playNodes t path n)), entry,
                      state, minState).2.1
                    (treeChainPlan t,
                      ULift.up.{max u v x y, s}
                        (t.controlAt (playNodes t path n)), entry,
                      state, minState).2.2.1
                    (treeChainPlan t,
                      ULift.up.{max u v x y, s}
                        (t.controlAt (playNodes t path n)), entry,
                      state, minState).2.2.2.1
                    (treeChainPlan t,
                      ULift.up.{max u v x y, s}
                        (t.controlAt (playNodes t path n)), entry,
                      state, minState).2.2.2.2 move' :=
            ⟨move, hnext⟩
          rw [hnext'] at hc
          show TreeTracks t CL CR CC path
            (playNodes t path n ++
              stepDirections t (path n) (path (n + 1))) (n + 1)
          unfold TreeTracks
          rw [hpos, hnext', stepDirections_revL_revR t _ _ hc]
          have hspec := Classical.choose_spec hc
          set m' := Classical.choose hc with hm'def
          simp only [revLeftReverseTarget, treeChainPlan,
            Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq, true_and] at hspec
          obtain ⟨hcEq, heEq, hnEq, hmEq⟩ := hspec
          refine ⟨?_, ?_, rfl⟩
          · refine
              ⟨CC.monitor.step checker
                  (Sum.inl (GlobalJournalLabel.revLeft
                    (t.labeledTree (playNodes t path n))))
                  (Sum.inr m'.1),
                revLeftReverseSubset threads
                  (GlobalJournalLabel.revLeft
                    (t.labeledTree (playNodes t path n)))
                  m'.1, ?_, ?_⟩
            · rw [globalRunIn_append, hrun]
              simp only [globalJournalStep]
            · refine
                Finset.mem_biUnion.mpr
                  ⟨(entry, state, minState), hmem,
                    Finset.mem_image.mpr
                      ⟨m'.2, Finset.mem_univ _, ?_⟩⟩
              show
                ((A.step state
                      (rightRoundRecord (m'.2, m'.1)
                        ((GlobalJournalLabel.revLeft (t.labelOf
                            (t.controlAt (playNodes t path n)))).2.1
                            (entry, state, minState) m'.1)
                        ((GlobalJournalLabel.revLeft (t.labelOf
                            (t.controlAt (playNodes t path n)))).2.2.2
                            (entry, state, minState) m')),
                    A.minPriorityState minState
                      (A.step state
                        (rightRoundRecord (m'.2, m'.1)
                        ((GlobalJournalLabel.revLeft (t.labelOf
                            (t.controlAt (playNodes t path n)))).2.1
                            (entry, state, minState) m'.1)
                        ((GlobalJournalLabel.revLeft (t.labelOf
                            (t.controlAt (playNodes t path n)))).2.2.2
                            (entry, state, minState) m')))),
                  A.step state
                    (rightRoundRecord (m'.2, m'.1)
                      ((GlobalJournalLabel.revLeft (t.labelOf
                          (t.controlAt (playNodes t path n)))).2.1
                          (entry, state, minState) m'.1)
                      ((GlobalJournalLabel.revLeft (t.labelOf
                          (t.controlAt (playNodes t path n)))).2.2.2
                          (entry, state, minState) m')),
                  A.minPriorityState minState
                    (A.step state
                      (rightRoundRecord (m'.2, m'.1)
                      ((GlobalJournalLabel.revLeft (t.labelOf
                          (t.controlAt (playNodes t path n)))).2.1
                          (entry, state, minState) m'.1)
                      ((GlobalJournalLabel.revLeft (t.labelOf
                          (t.controlAt (playNodes t path n)))).2.2.2
                          (entry, state, minState) m')))) =
                  _
              rw [← hnEq]
          · rw [controlAt_concat]
            exact hcEq
      -- reversed right block: continue, close, or reverse again
      · obtain ⟨⟨checker, threads, hrun, hmem⟩, hctl, hchain⟩ := ih
        subst hctl
        subst hchain
        have hstep' :
            (∃ move : In₁ × In₂,
              path (n + 1) =
                A.revRightContinueTarget (treeChainPlan t)
                  (ULift.up (t.controlAt (playNodes t path n))) entry
                  state minState move) ∨
            (∃ move : In₁ × In₂,
              path (n + 1) =
                A.revRightCloseTarget (treeChainPlan t)
                  (ULift.up (t.controlAt (playNodes t path n))) entry
                  state minState move) ∨
            (∃ move : In₁ × In₂,
              path (n + 1) =
                A.revRightReverseTarget (treeChainPlan t)
                  (ULift.up (t.controlAt (playNodes t path n))) entry
                  state minState move) :=
          hstep
        rcases hstep' with ⟨move, hnext⟩ | ⟨move, hnext⟩ | ⟨move, hnext⟩
        · -- continuation round
          have hnext' :
              path (n + 1) =
                Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
                  (treeChainPlan t,
                    ULift.up
                      (t.step (t.controlAt (playNodes t path n))
                        (Sum.inr (Sum.inr move.1))),
                    entry,
                    A.step state
                      (rightRoundRecord (move.2, move.1)
                        ((GlobalJournalLabel.revRight (t.labelOf
                            (t.controlAt (playNodes t path n)))).2.1
                          entry move.1)
                        ((GlobalJournalLabel.revRight (t.labelOf
                            (t.controlAt (playNodes t path n)))).2.2.2
                          (entry, state, minState) move)),
                    A.minPriorityState minState
                      (A.step state
                        (rightRoundRecord (move.2, move.1)
                        ((GlobalJournalLabel.revRight (t.labelOf
                            (t.controlAt (playNodes t path n)))).2.1
                          entry move.1)
                        ((GlobalJournalLabel.revRight (t.labelOf
                            (t.controlAt (playNodes t path n)))).2.2.2
                          (entry, state, minState) move)))))))) := by
            rw [hnext]
            rfl
          have hc :
              ∃ move' : In₁ × In₂,
                path (n + 1) =
                  A.revRightContinueTarget
                    (treeChainPlan t,
                      ULift.up.{max u v x y, s}
                        (t.controlAt (playNodes t path n)), entry,
                      state, minState).1
                    (treeChainPlan t,
                      ULift.up.{max u v x y, s}
                        (t.controlAt (playNodes t path n)), entry,
                      state, minState).2.1
                    (treeChainPlan t,
                      ULift.up.{max u v x y, s}
                        (t.controlAt (playNodes t path n)), entry,
                      state, minState).2.2.1
                    (treeChainPlan t,
                      ULift.up.{max u v x y, s}
                        (t.controlAt (playNodes t path n)), entry,
                      state, minState).2.2.2.1
                    (treeChainPlan t,
                      ULift.up.{max u v x y, s}
                        (t.controlAt (playNodes t path n)), entry,
                      state, minState).2.2.2.2 move' :=
            ⟨move, hnext⟩
          rw [hnext'] at hc
          show TreeTracks t CL CR CC path
            (playNodes t path n ++
              stepDirections t (path n) (path (n + 1))) (n + 1)
          unfold TreeTracks
          rw [hpos, hnext', stepDirections_revR_revR t _ _ hc]
          have hspec := Classical.choose_spec hc
          set m' := Classical.choose hc with hm'def
          simp only [revRightContinueTarget, treeChainPlan,
            Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq, true_and] at hspec
          obtain ⟨hcEq, hnEq, hmEq⟩ := hspec
          refine ⟨?_, ?_, rfl⟩
          · refine
              ⟨CC.monitor.step checker
                  (Sum.inr (GlobalJournalLabel.revRight
                    (t.labeledTree (playNodes t path n))))
                  (Sum.inr m'.1),
                revRightStepSubset threads
                  (GlobalJournalLabel.revRight
                    (t.labeledTree (playNodes t path n)))
                  m'.1, ?_, ?_⟩
            · rw [globalRunIn_append, hrun]
              simp only [globalJournalStep]
            · refine
                Finset.mem_biUnion.mpr
                  ⟨(entry, state, minState), hmem,
                    Finset.mem_image.mpr
                      ⟨m'.2, Finset.mem_univ _, ?_⟩⟩
              show
                (entry,
                  A.step state
                    (rightRoundRecord (m'.2, m'.1)
                      ((GlobalJournalLabel.revRight (t.labelOf
                          (t.controlAt (playNodes t path n)))).2.1
                          entry m'.1)
                      ((GlobalJournalLabel.revRight (t.labelOf
                          (t.controlAt (playNodes t path n)))).2.2.2
                          (entry, state, minState) m')),
                  A.minPriorityState minState
                    (A.step state
                      (rightRoundRecord (m'.2, m'.1)
                      ((GlobalJournalLabel.revRight (t.labelOf
                          (t.controlAt (playNodes t path n)))).2.1
                          entry m'.1)
                      ((GlobalJournalLabel.revRight (t.labelOf
                          (t.controlAt (playNodes t path n)))).2.2.2
                          (entry, state, minState) m')))) =
                  _
              rw [← hnEq]
          · rw [controlAt_concat]
            exact hcEq
        · -- closing round
          have hnext' :
              path (n + 1) =
                Sum.inl
                  (A.step state
                      (bothRoundRecord move
                        ((GlobalJournalLabel.revRight (t.labelOf
                            (t.controlAt (playNodes t path n)))).1
                          (entry, state, minState) move)
                        ((GlobalJournalLabel.revRight (t.labelOf
                            (t.controlAt (playNodes t path n)))).2.2.2
                          (entry, state, minState) move)),
                    minState) := by
            rw [hnext]
            rfl
          refine tracks_bnd_arrival t CL CR CC path n _ hnext' ?_ ?_
          · show
              globalRunIn CL CR CC t.labeledTree
                  (Sum.inl (A.initial, A.initial))
                  (playNodes t path n ++
                    stepDirections t (path n) (path (n + 1))) =
                _
            rw [hpos, hnext', stepDirections_revR_bnd,
              globalRunIn_append, hrun]
            simp only [globalJournalStep]
            rw [if_pos]
            exact
              Finset.mem_biUnion.mpr
                ⟨(entry, state, minState), hmem,
                  Finset.mem_image.mpr ⟨move, Finset.mem_univ _, rfl⟩⟩
          · show
              controlAfter t (some (path n)) _ =
                t.controlAt
                  (playNodes t path n ++
                    stepDirections t (path n) (path (n + 1)))
            rw [hpos, hnext', stepDirections_revR_bnd,
              controlAt_concat]
            simp only [controlAfter]
        · -- re-reversing round
          have hnext' :
              path (n + 1) =
                Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl
                  (treeChainPlan t,
                    ULift.up
                      (t.step (t.controlAt (playNodes t path n))
                        (Sum.inr (Sum.inl move.2))),
                    (A.step state
                        (leftRoundRecord move
                          ((GlobalJournalLabel.revRight (t.labelOf
                              (t.controlAt (playNodes t path n)))).1
                            (entry, state, minState) move)
                          ((GlobalJournalLabel.revRight (t.labelOf
                              (t.controlAt (playNodes t path n)))).2.2.1
                            (entry, state, minState) move.2)),
                      A.minPriorityState minState
                        (A.step state
                          (leftRoundRecord move
                          ((GlobalJournalLabel.revRight (t.labelOf
                              (t.controlAt (playNodes t path n)))).1
                            (entry, state, minState) move)
                          ((GlobalJournalLabel.revRight (t.labelOf
                              (t.controlAt (playNodes t path n)))).2.2.1
                            (entry, state, minState) move.2)))),
                    A.step state
                      (leftRoundRecord move
                        ((GlobalJournalLabel.revRight (t.labelOf
                            (t.controlAt (playNodes t path n)))).1
                          (entry, state, minState) move)
                        ((GlobalJournalLabel.revRight (t.labelOf
                            (t.controlAt (playNodes t path n)))).2.2.1
                          (entry, state, minState) move.2)),
                    A.minPriorityState minState
                      (A.step state
                        (leftRoundRecord move
                        ((GlobalJournalLabel.revRight (t.labelOf
                            (t.controlAt (playNodes t path n)))).1
                          (entry, state, minState) move)
                        ((GlobalJournalLabel.revRight (t.labelOf
                            (t.controlAt (playNodes t path n)))).2.2.1
                          (entry, state, minState) move.2)))))))) := by
            rw [hnext]
            rfl
          have hc :
              ∃ move' : In₁ × In₂,
                path (n + 1) =
                  A.revRightReverseTarget
                    (treeChainPlan t,
                      ULift.up.{max u v x y, s}
                        (t.controlAt (playNodes t path n)), entry,
                      state, minState).1
                    (treeChainPlan t,
                      ULift.up.{max u v x y, s}
                        (t.controlAt (playNodes t path n)), entry,
                      state, minState).2.1
                    (treeChainPlan t,
                      ULift.up.{max u v x y, s}
                        (t.controlAt (playNodes t path n)), entry,
                      state, minState).2.2.1
                    (treeChainPlan t,
                      ULift.up.{max u v x y, s}
                        (t.controlAt (playNodes t path n)), entry,
                      state, minState).2.2.2.1
                    (treeChainPlan t,
                      ULift.up.{max u v x y, s}
                        (t.controlAt (playNodes t path n)), entry,
                      state, minState).2.2.2.2 move' :=
            ⟨move, hnext⟩
          rw [hnext'] at hc
          show TreeTracks t CL CR CC path
            (playNodes t path n ++
              stepDirections t (path n) (path (n + 1))) (n + 1)
          unfold TreeTracks
          rw [hpos, hnext', stepDirections_revR_revL t _ _ hc]
          have hspec := Classical.choose_spec hc
          set m' := Classical.choose hc with hm'def
          simp only [revRightReverseTarget, treeChainPlan,
            Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq, true_and] at hspec
          obtain ⟨hcEq, heEq, hnEq, hmEq⟩ := hspec
          refine ⟨?_, ?_, rfl⟩
          · refine
              ⟨CC.monitor.step checker
                  (Sum.inr (GlobalJournalLabel.revRight
                    (t.labeledTree (playNodes t path n))))
                  (Sum.inl m'.2),
                revRightReverseSubset threads
                  (GlobalJournalLabel.revRight
                    (t.labeledTree (playNodes t path n)))
                  m'.2, ?_, ?_⟩
            · rw [globalRunIn_append, hrun]
              simp only [globalJournalStep]
            · refine
                Finset.mem_biUnion.mpr
                  ⟨(entry, state, minState), hmem,
                    Finset.mem_image.mpr
                      ⟨m'.1, Finset.mem_univ _, ?_⟩⟩
              show
                ((A.step state
                      (leftRoundRecord m'
                        ((GlobalJournalLabel.revRight (t.labelOf
                            (t.controlAt (playNodes t path n)))).1
                            (entry, state, minState) m')
                        ((GlobalJournalLabel.revRight (t.labelOf
                            (t.controlAt (playNodes t path n)))).2.2.1
                            (entry, state, minState) m'.2)),
                    A.minPriorityState minState
                      (A.step state
                        (leftRoundRecord m'
                        ((GlobalJournalLabel.revRight (t.labelOf
                            (t.controlAt (playNodes t path n)))).1
                            (entry, state, minState) m')
                        ((GlobalJournalLabel.revRight (t.labelOf
                            (t.controlAt (playNodes t path n)))).2.2.1
                            (entry, state, minState) m'.2)))),
                  A.step state
                    (leftRoundRecord m'
                      ((GlobalJournalLabel.revRight (t.labelOf
                          (t.controlAt (playNodes t path n)))).1
                          (entry, state, minState) m')
                      ((GlobalJournalLabel.revRight (t.labelOf
                          (t.controlAt (playNodes t path n)))).2.2.1
                          (entry, state, minState) m'.2)),
                  A.minPriorityState minState
                    (A.step state
                      (leftRoundRecord m'
                      ((GlobalJournalLabel.revRight (t.labelOf
                          (t.controlAt (playNodes t path n)))).1
                          (entry, state, minState) m')
                      ((GlobalJournalLabel.revRight (t.labelOf
                          (t.controlAt (playNodes t path n)))).2.2.1
                          (entry, state, minState) m'.2)))) =
                  _
              rw [← hnEq]
          · rw [controlAt_concat]
            exact hcEq

end Directions

end DetParityAutomaton

end DistributedSynthesis
