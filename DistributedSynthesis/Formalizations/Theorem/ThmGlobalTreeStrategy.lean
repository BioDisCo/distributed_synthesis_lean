/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmGlobalJournalAutomaton

/-!
# From a regular journal tree to a boundary-game strategy

This file begins step HG-C: consuming a transition-rational global
journal tree.  A rational tree is not boundary-Markov: the control
reached after an atom event depends on the whole path, so it does not
directly define a plan family.  It does define an Even strategy of
the boundary game with one step of memory, because every predecessor
of a boundary position carries the control of the tree node that the
play just left: the strategy commits the plan read off the labels
below the freshly entered atom node.  The finite boundary game's own
positional determinacy will later convert the winning history
strategy into a positional one, whose commitments are per atom; that
is where the boundary-Markov collapse happens.

The plan of a control takes the control's node as both block inits,
steps by the tree's sender branches, and reads the narrowed labels
and closing tables off the node labels, so the plan's opening
responses are exactly the label tables at the atom node, matching the
transitions of the global journal automaton.
-/

namespace DistributedSynthesis

universe u v x y s

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

namespace DetParityAutomaton

variable
  {A :
    DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂)}

variable
  (t :
    TransitionRationalTree.{max u v s, max u v x y s, s}
      (GlobalJournalBranch (In₁ := In₁) A)
      (GlobalJournalLabel (In₁ := In₁) A))

/-- The left-block plan below a tree control. -/
def treeLeftPlan (control : t.Control) :
    LeftBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
      A (ULift.{max u v x y, s} t.Control) where
  init := ULift.up control
  step := fun c inputTwo =>
    ULift.up (t.step c.down (Sum.inr (Sum.inl inputTwo)))
  label := fun c => GlobalJournalLabel.leftNarrowed (t.labelOf c.down)
  close := fun c qm move =>
    GlobalJournalLabel.leftClose (t.labelOf c.down) qm move
  rev := fun c qm move =>
    GlobalJournalLabel.leftRev (t.labelOf c.down) qm move

/-- The right-block plan below a tree control. -/
def treeRightPlan (control : t.Control) :
    RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
      A (ULift.{max u v x y, s} t.Control) where
  init := ULift.up control
  step := fun c inputOne =>
    ULift.up (t.step c.down (Sum.inr (Sum.inr inputOne)))
  label := fun c => GlobalJournalLabel.rightNarrowed (t.labelOf c.down)
  close := fun c qm move =>
    GlobalJournalLabel.rightClose (t.labelOf c.down) qm move
  rev := fun c qm move =>
    GlobalJournalLabel.rightRev (t.labelOf c.down) qm move

/-- The chain plan of the tree: the chain control is the tree control
itself, entered identically from either block control, stepping by the
tree's sender branches and reading the reversed four-value labels off
the node labels. -/
def treeChainPlan :
    ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
      A (ULift.{max u v x y, s} t.Control)
      (ULift.{max u v x y, s} t.Control)
      (ULift.{max u v x y, s} t.Control) where
  enterL := id
  enterR := id
  step := fun c dir => ULift.up (t.step c.down (Sum.inr dir))
  labelL := fun c => GlobalJournalLabel.revLeft (t.labelOf c.down)
  labelR := fun c => GlobalJournalLabel.revRight (t.labelOf c.down)

/-- The boundary plan below a tree control. -/
def treeBoundaryPlan (control : t.Control) :
    BoundaryPlan (In₁ := In₁) A (ULift.{max u v x y, s} t.Control)
      (ULift.{max u v x y, s} t.Control)
      (ULift.{max u v x y, s} t.Control) :=
  (treeLeftPlan t control, treeRightPlan t control, treeChainPlan t)

/--
The tree control entered by reaching a boundary atom: read off the
predecessor position of the play, which carries the control of the
node the play just left.  The initial boundary starts at the root.
-/
def controlAfter
    (prev :
      Option
        (BoundaryGamePosition (In₁ := In₁) A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)))
    (atom : A.State × A.State) : t.Control :=
  match prev with
  | some (Sum.inr (Sum.inl (_, plan))) =>
      t.step plan.1.init.down (Sum.inl atom)
  | some (Sum.inr (Sum.inr (Sum.inl (_, _, control, _, _)))) =>
      t.step control.down (Sum.inl atom)
  | some (Sum.inr (Sum.inr (Sum.inr (Sum.inl (_, _, control, _, _))))) =>
      t.step control.down (Sum.inl atom)
  | some (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl
      (_, control, _, _)))))) =>
      t.step control.down (Sum.inl atom)
  | some (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
      (_, control, _, _)))))) =>
      t.step control.down (Sum.inl atom)
  | _ => t.initial

section Strategy

variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂] [DecidableEq A.State]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [DecidableEq t.Control] [Inhabited t.Control]

/--
The Even move of the tree strategy: at a boundary, commit the plan of
the control entered through the predecessor; elsewhere any legal
move.
-/
noncomputable def treeStrategyMove
    (prev :
      Option
        (BoundaryGamePosition (In₁ := In₁) A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)))
    (position :
      BoundaryGamePosition (In₁ := In₁) A
        (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)) :
    BoundaryGamePosition (In₁ := In₁) A
      (ULift.{max u v x y, s} t.Control)
      (ULift.{max u v x y, s} t.Control)
      (ULift.{max u v x y, s} t.Control) :=
  match position with
  | Sum.inl atom =>
      Sum.inr (Sum.inl
        ((atom.1, atom.1), treeBoundaryPlan t (controlAfter t prev atom)))
  | other =>
      Classical.choose
        ((DetParityAutomaton.boundaryGame A
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)).step_total other)

/--
The tree strategy: Even's history strategy of the boundary game
induced by a transition-rational global journal tree.
-/
noncomputable def treeStrategy :
    (DetParityAutomaton.boundaryGame A
        (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)).Strategy
      ParityPlayer.even where
  move n pref :=
    treeStrategyMove t
      (if _h : n = 0 then none else
        some (pref ⟨n - 1, by omega⟩))
      ((DetParityAutomaton.boundaryGame A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)).prefixLast pref)

/-- The tree strategy is legal. -/
theorem treeStrategy_legal : (treeStrategy (A := A) t).Legal := by
  intro n pref _hlegal howner
  show
    (DetParityAutomaton.boundaryGame A
        (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)).step
      ((DetParityAutomaton.boundaryGame A _ _ _).prefixLast pref)
      (treeStrategyMove t _
        ((DetParityAutomaton.boundaryGame A _ _ _).prefixLast pref))
  rcases hpos :
      (DetParityAutomaton.boundaryGame A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)).prefixLast pref with
    atom | ⟨pair, plan⟩ | inBlockL | inBlockR | inRevL | inRevR
  · exact ⟨treeBoundaryPlan t (controlAfter t _ atom), rfl⟩
  · rw [hpos] at howner
    exact absurd howner
      (by simp [DetParityAutomaton.boundaryGame, boundaryOwner])
  · rw [hpos] at howner
    exact absurd howner
      (by simp [DetParityAutomaton.boundaryGame, boundaryOwner])
  · rw [hpos] at howner
    exact absurd howner
      (by simp [DetParityAutomaton.boundaryGame, boundaryOwner])
  · rw [hpos] at howner
    exact absurd howner
      (by simp [DetParityAutomaton.boundaryGame, boundaryOwner])
  · rw [hpos] at howner
    exact absurd howner
      (by simp [DetParityAutomaton.boundaryGame, boundaryOwner])

/-- Consistent plays commit tree plans at every boundary. -/
theorem treeStrategy_consistent_bnd
    (path :
      Nat ->
        BoundaryGamePosition (In₁ := In₁) A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control))
    (hcons :
      CountableParityGame.Strategy.Consistent
        (G :=
          DetParityAutomaton.boundaryGame A
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control))
        (treeStrategy t) path)
    (n : Nat) (atom : A.State × A.State)
    (hpos : path n = Sum.inl atom) :
    path (n + 1) =
      Sum.inr (Sum.inl
        ((atom.1, atom.1),
          treeBoundaryPlan t
            (controlAfter t
              (if _h : n = 0 then none else some (path (n - 1))) atom))) := by
  have hmove := hcons n (by rw [hpos]; rfl)
  rw [hmove]
  show
    treeStrategyMove t _
      ((DetParityAutomaton.boundaryGame A _ _ _).prefixLast
        ((DetParityAutomaton.boundaryGame A _ _ _).prefixOfPath path n)) = _
  rw [CountableParityGame.prefixLast_prefixOfPath, hpos]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rfl
  · have hne : n ≠ 0 := by omega
    simp only [dif_neg hne]
    rfl

end Strategy

end DetParityAutomaton

end DistributedSynthesis
