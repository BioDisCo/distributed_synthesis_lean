/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledExactViewTree
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenSemanticTree

/-!
# Diagonal restriction of a rational pair tree

A rational tree over synchronous pairs always has rational left and right
diagonal restrictions.  This alone does not say that the pair tree is the
self-product of either restriction: away from the diagonal, one component
may depend on the other history.

`PairTreeHasSharedProjections` is the exact missing preservation law.  Under
that law and agreement of the two diagonal restrictions, the pair tree is
definitionally represented by one shared rational tree.  The final theorem
specializes this generic adapter to the exact-view safety monitor.
-/

namespace DistributedSynthesis

universe u v w

namespace TransitionRationalTree

variable {Branch : Type u} {Alphabet : Type v}

/-- Restrict a rational pair tree to diagonal branches and retain the first
label component. -/
def diagonalLeft
    (tree : TransitionRationalTree.{max u u, max v v, w}
      (Branch × Branch) (Alphabet × Alphabet)) :
    TransitionRationalTree.{u, v, w} Branch Alphabet where
  Control := tree.Control
  controlFinite := tree.controlFinite
  initial := tree.initial
  step control branch := tree.step control (branch, branch)
  labelOf control := (tree.labelOf control).1

/-- Right diagonal restriction. -/
def diagonalRight
    (tree : TransitionRationalTree.{max u u, max v v, w}
      (Branch × Branch) (Alphabet × Alphabet)) :
    TransitionRationalTree.{u, v, w} Branch Alphabet where
  Control := tree.Control
  controlFinite := tree.controlFinite
  initial := tree.initial
  step control branch := tree.step control (branch, branch)
  labelOf control := (tree.labelOf control).2

@[simp] theorem diagonalLeft_controlAt
    (tree : TransitionRationalTree.{max u u, max v v, w}
      (Branch × Branch) (Alphabet × Alphabet))
    (node : TreeNode Branch) :
    (tree.diagonalLeft.controlAt node) =
      tree.controlAt (node.map fun branch => (branch, branch)) := by
  simp [controlAt, diagonalLeft, List.foldl_map]

@[simp] theorem diagonalRight_controlAt
    (tree : TransitionRationalTree.{max u u, max v v, w}
      (Branch × Branch) (Alphabet × Alphabet))
    (node : TreeNode Branch) :
    (tree.diagonalRight.controlAt node) =
      tree.controlAt (node.map fun branch => (branch, branch)) := by
  simp [controlAt, diagonalRight, List.foldl_map]

@[simp] theorem diagonalLeft_labeledTree
    (tree : TransitionRationalTree.{max u u, max v v, w}
      (Branch × Branch) (Alphabet × Alphabet))
    (node : TreeNode Branch) :
    tree.diagonalLeft.labeledTree node =
      (tree.labeledTree (node.map fun branch => (branch, branch))).1 := by
  change (tree.labelOf (tree.diagonalLeft.controlAt node)).1 = _
  rw [diagonalLeft_controlAt]
  rfl

@[simp] theorem diagonalRight_labeledTree
    (tree : TransitionRationalTree.{max u u, max v v, w}
      (Branch × Branch) (Alphabet × Alphabet))
    (node : TreeNode Branch) :
    tree.diagonalRight.labeledTree node =
      (tree.labeledTree (node.map fun branch => (branch, branch))).2 := by
  change (tree.labelOf (tree.diagonalRight.controlAt node)).2 = _
  rw [diagonalRight_controlAt]
  rfl

/-- Form the synchronous square only after one rational tree has been
selected.  The two controls advance independently, so the resulting pair
tree has a genuine shared origin. -/
def selfProduct
    (tree : TransitionRationalTree.{u, v, w} Branch Alphabet) :
    TransitionRationalTree.{max u u, max v v, max w w}
      (Branch × Branch) (Alphabet × Alphabet) where
  Control := tree.Control × tree.Control
  controlFinite := inferInstance
  initial := (tree.initial, tree.initial)
  step control branch :=
    (tree.step control.1 branch.1, tree.step control.2 branch.2)
  labelOf control := (tree.labelOf control.1, tree.labelOf control.2)

@[simp] theorem selfProduct_controlAt_fst
    (tree : TransitionRationalTree.{u, v, w} Branch Alphabet)
    (node : TreeNode (Branch × Branch)) :
    (tree.selfProduct.controlAt node).1 =
      tree.controlAt (node.map Prod.fst) := by
  have aux : ∀ (control : tree.Control × tree.Control)
      (node : List (Branch × Branch)),
      (node.foldl tree.selfProduct.step control).1 =
        (node.map Prod.fst).foldl tree.step control.1 := by
    intro control node
    induction node generalizing control with
    | nil => rfl
    | cons branch node ih =>
        exact ih (tree.selfProduct.step control branch)
  change (List.foldl tree.selfProduct.step
      (tree.initial, tree.initial) node).1 =
    List.foldl tree.step tree.initial (node.map Prod.fst)
  exact aux (tree.initial, tree.initial) node

@[simp] theorem selfProduct_controlAt_snd
    (tree : TransitionRationalTree.{u, v, w} Branch Alphabet)
    (node : TreeNode (Branch × Branch)) :
    (tree.selfProduct.controlAt node).2 =
      tree.controlAt (node.map Prod.snd) := by
  have aux : ∀ (control : tree.Control × tree.Control)
      (node : List (Branch × Branch)),
      (node.foldl tree.selfProduct.step control).2 =
        (node.map Prod.snd).foldl tree.step control.2 := by
    intro control node
    induction node generalizing control with
    | nil => rfl
    | cons branch node ih =>
        exact ih (tree.selfProduct.step control branch)
  change (List.foldl tree.selfProduct.step
      (tree.initial, tree.initial) node).2 =
    List.foldl tree.step tree.initial (node.map Prod.snd)
  exact aux (tree.initial, tree.initial) node

end TransitionRationalTree

/-- Synchronous self-product of one labeled tree. -/
def labeledTreeSelfProduct
    {Branch : Type u} {Alphabet : Type v}
    (tree : LabeledTree Branch Alphabet) :
    LabeledTree (Branch × Branch) (Alphabet × Alphabet) :=
  fun node => (tree (node.map Prod.fst), tree (node.map Prod.snd))

/-- Both components of a pair tree are projections of their own history.
This is stronger than rationality and stronger than a node-local pair-safety
condition. -/
def PairTreeHasSharedProjections
    {Branch : Type u} {Alphabet : Type v}
    (tree : LabeledTree (Branch × Branch) (Alphabet × Alphabet))
    (left right : LabeledTree Branch Alphabet) : Prop :=
  ∀ node,
    (tree node).1 = left (node.map Prod.fst) ∧
      (tree node).2 = right (node.map Prod.snd)

/-- A rational pair tree has one shared origin when its two history
projections agree on the diagonal. -/
def RationalPairTreeHasSharedOrigin
    {Branch : Type u} {Alphabet : Type v}
    (tree : TransitionRationalTree.{max u u, max v v, w}
      (Branch × Branch) (Alphabet × Alphabet)) : Prop :=
  PairTreeHasSharedProjections tree.labeledTree
      tree.diagonalLeft.labeledTree tree.diagonalRight.labeledTree ∧
    tree.diagonalLeft.labeledTree = tree.diagonalRight.labeledTree

/-- Shared projections plus diagonal agreement recover the pair tree as the
square of one rational tree. -/
theorem labeledTree_eq_selfProduct_diagonalLeft_of_sharedOrigin
    {Branch : Type u} {Alphabet : Type v}
    (tree : TransitionRationalTree.{max u u, max v v, w}
      (Branch × Branch) (Alphabet × Alphabet))
    (hshared : RationalPairTreeHasSharedOrigin tree) :
    tree.labeledTree =
      labeledTreeSelfProduct tree.diagonalLeft.labeledTree := by
  funext node
  apply Prod.ext
  · exact (hshared.1 node).1
  · calc
      (tree.labeledTree node).2 =
          tree.diagonalRight.labeledTree (node.map Prod.snd) :=
        (hshared.1 node).2
      _ = tree.diagonalLeft.labeledTree (node.map Prod.snd) :=
        congrFun hshared.2 (node.map Prod.snd) |>.symm
      _ = (labeledTreeSelfProduct tree.diagonalLeft.labeledTree node).2 := rfl

/-- A self-product built from one rational tree has exactly the expected
labeled self-product semantics. -/
theorem TransitionRationalTree.selfProduct_labeledTree
    {Branch : Type u} {Alphabet : Type v}
    (tree : TransitionRationalTree.{u, v, w} Branch Alphabet) :
    tree.selfProduct.labeledTree = labeledTreeSelfProduct tree.labeledTree := by
  funext node
  change (tree.labelOf (tree.selfProduct.controlAt node).1,
      tree.labelOf (tree.selfProduct.controlAt node).2) = _
  rw [TransitionRationalTree.selfProduct_controlAt_fst,
    TransitionRationalTree.selfProduct_controlAt_snd]
  rfl

@[simp] theorem TransitionRationalTree.selfProduct_diagonalLeft_labeledTree
    {Branch : Type u} {Alphabet : Type v}
    (tree : TransitionRationalTree.{u, v, w} Branch Alphabet) :
    tree.selfProduct.diagonalLeft.labeledTree = tree.labeledTree := by
  funext node
  rw [TransitionRationalTree.diagonalLeft_labeledTree]
  rw [TransitionRationalTree.selfProduct_labeledTree]
  simp [labeledTreeSelfProduct, Function.comp_def]

@[simp] theorem TransitionRationalTree.selfProduct_diagonalRight_labeledTree
    {Branch : Type u} {Alphabet : Type v}
    (tree : TransitionRationalTree.{u, v, w} Branch Alphabet) :
    tree.selfProduct.diagonalRight.labeledTree = tree.labeledTree := by
  funext node
  rw [TransitionRationalTree.diagonalRight_labeledTree]
  rw [TransitionRationalTree.selfProduct_labeledTree]
  simp [labeledTreeSelfProduct, Function.comp_def]

/-- Rationalize first, self-compose second: this ordering always preserves
one shared strategy tree. -/
theorem TransitionRationalTree.selfProduct_hasSharedOrigin
    {Branch : Type u} {Alphabet : Type v}
    (tree : TransitionRationalTree.{u, v, w} Branch Alphabet) :
    RationalPairTreeHasSharedOrigin tree.selfProduct := by
  rw [RationalPairTreeHasSharedOrigin,
    TransitionRationalTree.selfProduct_diagonalLeft_labeledTree,
    TransitionRationalTree.selfProduct_diagonalRight_labeledTree,
    TransitionRationalTree.selfProduct_labeledTree]
  constructor
  · intro node
    exact ⟨rfl, rfl⟩
  · rfl

/-! ## Fail-fast separation

Finite rationality of a pair tree does not imply shared origin.  This tiny
crossed controller makes its left label depend on the right branch and vice
versa. -/

def crossedBoolPairTree :
    TransitionRationalTree (Bool × Bool) (Bool × Bool) where
  Control := Bool × Bool
  controlFinite := inferInstance
  initial := (false, false)
  step _ branch := branch
  labelOf control := (control.2, control.1)

theorem crossedBoolPairTree_not_sharedOrigin :
    ¬ RationalPairTreeHasSharedOrigin crossedBoolPairTree := by
  intro hshared
  have hleft := (hshared.1 [(false, true)]).1
  simp [crossedBoolPairTree, TransitionRationalTree.labeledTree,
    TransitionRationalTree.controlAt, TransitionRationalTree.diagonalLeft]
    at hleft

/-- The exact-view self-product is the generic self-product. -/
theorem exactViewGlobalSelfProduct_eq_labeledTreeSelfProduct
    {In₁ : Type u} {In₂ : Type v} {Out₁ Out₂ : Type w}
    (tree : LabeledTree (EnvironmentRound In₁ In₂)
      (DetParityAutomaton.ExactViewGlobalActionTable
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))) :
    DetParityAutomaton.exactViewGlobalSelfProduct tree =
      labeledTreeSelfProduct tree :=
  rfl

namespace DetParityAutomaton

universe x y s

/-- Adapter theorem for the delay-one exact-view test.  If a rationalized
pair tree retains shared projections, then its finite safety proof genuinely
belongs to one shared rational strategy tree. -/
theorem exactViewGlobalSelfProductSafe_diagonalLeft_of_sharedOrigin
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    [Inhabited In₁] [Inhabited In₂]
    [DecidableEq In₁] [DecidableEq In₂]
    (tree : TransitionRationalTree.{max u v, max u v x y, s}
      (EnvironmentRound In₁ In₂ × EnvironmentRound In₁ In₂)
      (ExactViewGlobalActionTable
          (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) ×
        ExactViewGlobalActionTable
          (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)))
    (hshared : RationalPairTreeHasSharedOrigin tree)
    (hsafe : ExactViewGlobalSelfProductSafe tree.labeledTree) :
    ExactViewGlobalSelfProductSafe
      (exactViewGlobalSelfProduct tree.diagonalLeft.labeledTree) := by
  have htree : exactViewGlobalSelfProduct tree.diagonalLeft.labeledTree =
      tree.labeledTree := by
    change labeledTreeSelfProduct tree.diagonalLeft.labeledTree =
      tree.labeledTree
    exact (labeledTree_eq_selfProduct_diagonalLeft_of_sharedOrigin
      tree hshared).symm
  simpa only [htree] using hsafe

/-- The already-built observable-class extraction automatically passes the
shared-origin test when it is squared only after its one-tree
rationalization.  Its remaining premise is exactly the global semantic parity
statement, not another diagonal obligation. -/
theorem exists_finite_profiledOpenSemanticTable_with_sharedOrigin_of_globalParity
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    (A : DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (initial : ProfiledOpenSemanticObservation A strategy hwin basis)
    (hparity : ProfiledOpenSemanticGlobalParity A strategy hwin basis initial) :
    ∃ table : RunParityTreeAutomaton.StateControlledTreeTable
        (profiledOpenSemanticTreeMonitor A strategy hwin basis initial).toRunAutomaton,
      (profiledOpenSemanticTreeMonitor A strategy hwin basis initial).WinningTree
          table.toTransitionRationalTree.labeledTree ∧
        RationalPairTreeHasSharedOrigin
          table.toTransitionRationalTree.selfProduct := by
  rcases exists_finite_profiledOpenSemanticTable_of_globalParity A strategy
      hwin basis initial hparity with ⟨table, htable⟩
  exact ⟨table, htable,
    TransitionRationalTree.selfProduct_hasSharedOrigin
      table.toTransitionRationalTree⟩

end DetParityAutomaton

end DistributedSynthesis
