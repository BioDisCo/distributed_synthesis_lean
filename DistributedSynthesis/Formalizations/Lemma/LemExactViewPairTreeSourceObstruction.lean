/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemDiagonalPairTreeRationalization

/-!
# The exact-view pair monitor does not preserve shared origin

The synchronous exact-view law is an ordinary finite-state safety condition
on a tree over pairs of environment branches.  This does not make the pair
tree a self-product.  The finite controller below is a model-level witness:
it is safe for the exact delay-one equality monitor and its two diagonal
restrictions agree, but one off-diagonal label depends on the other history.

The witness uses no leader or orientation observation.  Its `right/left`
case distinction is only the proof-side branch pair read by the synchronous
pair automaton.  It shows that applying the ordinary rational-tree theorem to
that pair automaton cannot by itself prove exact-view regular uniformization:
a shared source tree (or an equivalent history/source factorization law) is
an additional requirement.
-/

namespace DistributedSynthesis

namespace DetParityAutomaton

/-- The tiny finite control used by the off-diagonal witness. -/
inductive ExactViewPairCrossControl
  | root
  | cross
  | sink
deriving DecidableEq, Fintype

abbrev ExactViewPairCrossEnvironment := EnvironmentRound Unit Unit

abbrev ExactViewPairCrossTable :=
  ExactViewGlobalActionTable
    (In₁ := Unit) (In₂ := Unit) (Out₁ := Bool) (Out₂ := Bool)

/-- The harmless constant table used everywhere except at the crossed node. -/
def exactViewPairCrossFalseTable : ExactViewPairCrossTable :=
  fun _ => (false, false)

/-- At the crossed node only process one's output is changed. -/
def exactViewPairCrossTrueOneTable : ExactViewPairCrossTable :=
  fun _ => (true, false)

/-- Transition function of the crossed controller, named separately so its
absorbing-sink invariant can be reused in the proofs below. -/
def exactViewPairCrossStep
    (control : ExactViewPairCrossControl)
    (branch : ExactViewPairCrossEnvironment ×
      ExactViewPairCrossEnvironment) : ExactViewPairCrossControl :=
  match control with
  | .root =>
      if branch.1.graph = Graph.right ∧ branch.2.graph = Graph.left then
        .cross
      else
        .sink
  | .cross | .sink => .sink

/-- Label function of the crossed controller. -/
def exactViewPairCrossLabel
    (control : ExactViewPairCrossControl) :
    ExactViewPairCrossTable × ExactViewPairCrossTable :=
  match control with
  | .cross =>
      (exactViewPairCrossTrueOneTable, exactViewPairCrossFalseTable)
  | .root | .sink =>
      (exactViewPairCrossFalseTable, exactViewPairCrossFalseTable)

/--
A rational pair tree with one special node.  The node reached by the
off-diagonal first-round pair `(right,left)` receives a crossed label; every
diagonal node and every deeper node receives the constant label.
-/
def exactViewPairCrossTree :
    TransitionRationalTree
      (ExactViewPairCrossEnvironment × ExactViewPairCrossEnvironment)
      (ExactViewPairCrossTable × ExactViewPairCrossTable) where
  Control := ExactViewPairCrossControl
  controlFinite := inferInstance
  initial := .root
  step := exactViewPairCrossStep
  labelOf := exactViewPairCrossLabel

@[simp] theorem exactViewPairCrossStep_sink
    (branch : ExactViewPairCrossEnvironment ×
      ExactViewPairCrossEnvironment) :
    exactViewPairCrossStep .sink branch = .sink :=
  rfl

@[simp] theorem exactViewPairCrossStep_cross
    (branch : ExactViewPairCrossEnvironment ×
      ExactViewPairCrossEnvironment) :
    exactViewPairCrossStep .cross branch = .sink :=
  rfl

theorem exactViewPairCrossStep_foldl_sink
    (node : List (ExactViewPairCrossEnvironment ×
      ExactViewPairCrossEnvironment)) :
    node.foldl exactViewPairCrossStep .sink = .sink := by
  induction node with
  | nil => rfl
  | cons branch tail ih =>
      simpa using ih

/-- After two pair directions the controller is necessarily in its sink. -/
theorem exactViewPairCrossTree_controlAt_two
    (first second : ExactViewPairCrossEnvironment ×
      ExactViewPairCrossEnvironment)
    (tail : List (ExactViewPairCrossEnvironment ×
      ExactViewPairCrossEnvironment)) :
    exactViewPairCrossTree.controlAt (first :: second :: tail) = .sink := by
  change tail.foldl exactViewPairCrossStep
      (exactViewPairCrossStep (exactViewPairCrossStep .root first) second) =
    .sink
  by_cases h : first.1.graph = Graph.right ∧
      first.2.graph = Graph.left
  · rw [show exactViewPairCrossStep .root first = .cross by
      simp [exactViewPairCrossStep, h]]
    rw [exactViewPairCrossStep_cross]
    exact exactViewPairCrossStep_foldl_sink tail
  · rw [show exactViewPairCrossStep .root first = .sink by
      simp [exactViewPairCrossStep, h]]
    rw [exactViewPairCrossStep_sink]
    exact exactViewPairCrossStep_foldl_sink tail

/-- A diagonal first direction can never enter the crossed control. -/
theorem exactViewPairCrossStep_root_diagonal
    (branch : ExactViewPairCrossEnvironment) :
    exactViewPairCrossStep .root (branch, branch) = .sink := by
  rcases branch with ⟨inputOne, inputTwo, graph⟩
  cases graph <;> simp [exactViewPairCrossStep]

/-- The exact delay-one two-bit monitor accepts the crossed pair tree. -/
theorem exactViewPairCrossTree_safe :
    ExactViewGlobalSelfProductSafe exactViewPairCrossTree.labeledTree := by
  intro rounds leftEnv rightEnv
  cases rounds with
  | nil =>
      simp [exactViewPairCrossTree, TransitionRationalTree.labeledTree,
        TransitionRationalTree.controlAt, exactViewPairCrossLabel,
        exactViewPairCrossFalseTable]
  | cons first rest =>
      cases rest with
      | nil =>
          rcases first with ⟨left, right⟩
          rcases left with ⟨leftOne, leftTwo, leftGraph⟩
          rcases right with ⟨rightOne, rightTwo, rightGraph⟩
          rcases leftEnv with ⟨nextLeftOne, nextLeftTwo, nextLeftGraph⟩
          rcases rightEnv with ⟨nextRightOne, nextRightTwo, nextRightGraph⟩
          cases leftGraph <;> cases rightGraph <;>
            cases nextLeftGraph <;> cases nextRightGraph <;>
            simp [exactViewPairCrossTree,
              TransitionRationalTree.labeledTree,
              TransitionRationalTree.controlAt,
              exactViewPairCrossStep, exactViewPairCrossLabel,
              exactViewPairCrossFalseTable,
              exactViewPairCrossTrueOneTable,
              pairedViewEqualityAfter, pairedViewEqualityStep,
              pairedViewEqualityStepOne, pairedViewEqualityStepTwo,
              processOneReceives, processTwoReceives]
      | cons second tail =>
          have hcontrol :
              exactViewPairCrossTree.controlAt (first :: second :: tail) =
                .sink :=
            exactViewPairCrossTree_controlAt_two first second tail
          dsimp only [TransitionRationalTree.labeledTree]
          rw [hcontrol]
          simp [exactViewPairCrossTree, exactViewPairCrossLabel,
            exactViewPairCrossFalseTable]

/-- Both diagonal restrictions of the crossed tree are the same constant
strategy tree. -/
theorem exactViewPairCrossTree_diagonal_agree :
    exactViewPairCrossTree.diagonalLeft.labeledTree =
      exactViewPairCrossTree.diagonalRight.labeledTree := by
  funext node
  rw [TransitionRationalTree.diagonalLeft_labeledTree,
    TransitionRationalTree.diagonalRight_labeledTree]
  cases node with
  | nil => rfl
  | cons branch tail =>
      have hcontrol :
          exactViewPairCrossTree.controlAt
              ((branch :: tail).map fun direction =>
                (direction, direction)) = .sink := by
        simp only [List.map_cons, TransitionRationalTree.controlAt,
          exactViewPairCrossTree, List.foldl_cons]
        rw [exactViewPairCrossStep_root_diagonal]
        exact exactViewPairCrossStep_foldl_sink
          (tail.map fun direction => (direction, direction))
      dsimp only [TransitionRationalTree.labeledTree]
      rw [hcontrol]
      simp [exactViewPairCrossTree, exactViewPairCrossLabel]

/-- Nevertheless the left component at the off-diagonal node is not the
label selected by its own projected history. -/
theorem exactViewPairCrossTree_not_sharedProjections :
    ¬ PairTreeHasSharedProjections exactViewPairCrossTree.labeledTree
        exactViewPairCrossTree.diagonalLeft.labeledTree
        exactViewPairCrossTree.diagonalRight.labeledTree := by
  intro hshared
  let rightRound : ExactViewPairCrossEnvironment :=
    ⟨(), (), Graph.right⟩
  let leftRound : ExactViewPairCrossEnvironment :=
    ⟨(), (), Graph.left⟩
  have hleft := (hshared [(rightRound, leftRound)]).1
  have hvalue := congrFun hleft rightRound
  simp [rightRound, leftRound, exactViewPairCrossTree,
    exactViewPairCrossStep, exactViewPairCrossLabel,
    exactViewPairCrossTrueOneTable, exactViewPairCrossFalseTable,
    TransitionRationalTree.labeledTree, TransitionRationalTree.controlAt,
    TransitionRationalTree.diagonalLeft] at hvalue

/-- Exact model-level fail-fast result: finite rationality, exact-view safety,
and agreement on the diagonal still do not imply one shared-origin tree. -/
theorem exactViewPairCrossTree_safe_diagonal_not_sharedOrigin :
    ExactViewGlobalSelfProductSafe exactViewPairCrossTree.labeledTree ∧
      exactViewPairCrossTree.diagonalLeft.labeledTree =
        exactViewPairCrossTree.diagonalRight.labeledTree ∧
      ¬ RationalPairTreeHasSharedOrigin exactViewPairCrossTree := by
  refine ⟨exactViewPairCrossTree_safe,
    exactViewPairCrossTree_diagonal_agree, ?_⟩
  intro hshared
  exact exactViewPairCrossTree_not_sharedProjections hshared.1

end DetParityAutomaton

end DistributedSynthesis
