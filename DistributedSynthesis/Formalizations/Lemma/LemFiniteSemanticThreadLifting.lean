/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteSemanticFibreImage

/-!
# Lifting a persistent finite descriptor thread to one semantic branch

Hidden-code continuity prevents a public family controller from reselecting
an unrelated finite descriptor at every level.  To transfer semantic parity,
one further local fact is required: every advertised finite edge can be
realized from the *current* semantic representative.  This file packages that
fact as `SemanticEdgeLifter` and proves the corresponding infinite path
lifting theorem.

The theorem is intentionally stronger than pairwise existence of edge
witnesses.  One selector is applied recursively to the semantic state reached
at the preceding step, so the resulting branch has one literal origin.  This
is the generic anti-mosaic bridge needed by the staged profiled construction.
-/

namespace DistributedSynthesis

universe u v w x y

section

variable {Semantic : Type u} {Direction : Type v}
variable {Descriptor : Type w} {Move : Type x} {Family : Type y}

/-- A model-specific one-step path lifting operation.  `direction` is
proof-side data.  The public controller sees only `move` and `family`; it is
not given the current semantic representative or the chosen direction. -/
structure SemanticEdgeLifter
    (step : Semantic → Direction → Semantic)
    (descriptor : Semantic → Descriptor)
    (Edge : Descriptor → Move → Family → Descriptor → Prop) where
  direction : Semantic → Move → Family → Descriptor → Direction
  lifts : ∀ semantic move family next,
    Edge (descriptor semantic) move family next →
      descriptor
          (step semantic (direction semantic move family next)) = next

namespace SemanticEdgeLifter

variable
  (step : Semantic → Direction → Semantic)
  (descriptor : Semantic → Descriptor)
  (Edge : Descriptor → Move → Family → Descriptor → Prop)
  (lifter : SemanticEdgeLifter step descriptor Edge)
  (initial : Semantic)
  (word : OmegaWord (Move × Family))
  (thread : HiddenCodeContinuityThread (descriptor initial) Edge word)

/-- Semantic state obtained by following the edge selector recursively. -/
noncomputable def liftedStateAt : Nat → Semantic
  | 0 => initial
  | n + 1 =>
      step (liftedStateAt n)
        (lifter.direction (liftedStateAt n) (word n).1 (word n).2
          (thread.code (n + 1)))

/-- Proof-side direction chosen at one lifted depth. -/
noncomputable def liftedBranch (n : Nat) : Direction :=
  lifter.direction (lifter.liftedStateAt step descriptor Edge initial word
      thread n) (word n).1 (word n).2 (thread.code (n + 1))

@[simp] theorem liftedStateAt_zero :
    lifter.liftedStateAt step descriptor Edge initial word thread 0 =
      initial :=
  rfl

theorem liftedStateAt_succ (n : Nat) :
    lifter.liftedStateAt step descriptor Edge initial word thread (n + 1) =
      step
        (lifter.liftedStateAt step descriptor Edge initial word thread n)
        (lifter.liftedBranch step descriptor Edge initial word thread n) :=
  rfl

/-- At every depth the lifted semantic state has exactly the persistent
descriptor selected by the hidden thread. -/
theorem descriptor_liftedStateAt (n : Nat) :
    descriptor
        (lifter.liftedStateAt step descriptor Edge initial word thread n) =
      thread.code n := by
  induction n with
  | zero => exact thread.initial.symm
  | succ n ih =>
      rw [liftedStateAt_succ]
      apply lifter.lifts
      simpa only [ih] using thread.edge n

/-- Ordinary semantic fold along a finite direction node. -/
def semanticStateAtNode (node : TreeNode Direction) : Semantic :=
  node.foldl step initial

@[simp] theorem semanticStateAtNode_nil :
    semanticStateAtNode step initial [] = initial :=
  rfl

theorem semanticStateAtNode_append
    (node : TreeNode Direction) (direction : Direction) :
    semanticStateAtNode step initial (node ++ [direction]) =
      step (semanticStateAtNode step initial node) direction := by
  simp [semanticStateAtNode, List.foldl_append]

/-- The recursively selected states are exactly the ordinary semantic states
along the selected branch. -/
theorem semanticStateAtNode_branchNode (n : Nat) :
    semanticStateAtNode step initial
        (branchNode
          (lifter.liftedBranch step descriptor Edge initial word thread) n) =
      lifter.liftedStateAt step descriptor Edge initial word thread n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show branchNode
          (lifter.liftedBranch step descriptor Edge initial word thread)
            (n + 1) =
        branchNode
            (lifter.liftedBranch step descriptor Edge initial word thread) n ++
          [lifter.liftedBranch step descriptor Edge initial word thread n]
        from rfl,
        semanticStateAtNode_append, ih, liftedStateAt_succ]

/-- The complete hidden descriptor word is the positive-time descriptor word
of one literal semantic branch. -/
theorem childDescriptorWord_eq :
    thread.childCodeWord = fun n =>
      descriptor
        (semanticStateAtNode step initial
          (branchNode
            (lifter.liftedBranch step descriptor Edge initial word thread)
            (n + 1))) := by
  funext n
  change thread.code (n + 1) = _
  rw [semanticStateAtNode_branchNode]
  exact (SemanticEdgeLifter.descriptor_liftedStateAt
    (step := step) (descriptor := descriptor) (Edge := Edge)
    (lifter := lifter) (initial := initial) (word := word)
    (thread := thread) (n := n + 1)).symm

end SemanticEdgeLifter

/-! ## Direct parity transfer -/

variable [Fintype Descriptor]

omit [Fintype Descriptor] in
/-- Universal acceptance of literal semantic branches transfers to every
persistent finite descriptor thread once the local edge lifter is supplied. -/
theorem hiddenThread_accepts_of_semanticEdgeLifter
    (D : DetParityAutomaton.{w, u} Descriptor)
    (step : Semantic → Direction → Semantic)
    (descriptor : Semantic → Descriptor)
    (Edge : Descriptor → Move → Family → Descriptor → Prop)
    (lifter : SemanticEdgeLifter step descriptor Edge)
    (initial : Semantic)
    (word : OmegaWord (Move × Family))
    (thread : HiddenCodeContinuityThread (descriptor initial) Edge word)
    (haccepts : ∀ branch : Nat → Direction,
      D.Accepts (fun n => descriptor
        ((branchNode branch (n + 1)).foldl step initial))) :
    D.Accepts thread.childCodeWord := by
  let branch := lifter.liftedBranch step descriptor Edge initial word thread
  have hword := SemanticEdgeLifter.childDescriptorWord_eq
    (lifter := lifter) (initial := initial) (word := word) (thread := thread)
  rw [hword]
  exact haccepts branch

end

end DistributedSynthesis
