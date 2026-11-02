/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemSourceFreeBeliefParentLinkedFiniteAnnotation

/-!
# Persistent finite annotations for source-free belief trees

`parentLinkFiniteAnnotation` is safe only when the annotation of a semantic
child is already part of that child's semantic state.  In a hybrid hierarchy
tree the bare semantic state can forget which finite controller package was
installed at the preceding common-to-strict boundary.  Recomputing a package
from the bare child would reintroduce the representative mosaic.

This file supplies the reusable repair.  It extends the proof-side semantic
state by a finite annotation, and the parent transition installs the child's
annotation through a model-specific `advance` function.  The ordinary public
code, raw move, and code-parity objective are unchanged.  The carried tree can
then be fed to `parentLinkFiniteAnnotation` with `Prod.snd`; consequently the
finite rational policy stores exactly the package selected by its parent.

The annotation is controller bookkeeping only.  It does not reveal a graph,
orientation, leader, strict leader, history, or local view to a process.
-/

namespace DistributedSynthesis

universe u v w z a b

section

variable {Direction : Type u} {Move : Type v} {BeliefCode : Type z}
variable {Annotation : Type b}

/-- Extend an exact semantic unfolding by a finite annotation that is carried
across transitions.  `advance source current direction` is evaluated at the
parent and becomes the annotation stored by the literal child. -/
def SourceFreeBeliefSemanticTree.carryFiniteAnnotation
    (raw : SourceFreeBeliefSemanticTree.{u, v, z, a}
      Direction Move BeliefCode)
    (initialAnnotation : Annotation)
    (advance : raw.Semantic → Annotation → Direction → Annotation) :
    SourceFreeBeliefSemanticTree.{u, v, z, max a b}
      Direction Move BeliefCode where
  Semantic := raw.Semantic × Annotation
  initial := (raw.initial, initialAnnotation)
  step := fun state direction ↦
    (raw.step state.1 direction, advance state.1 state.2 direction)
  code := fun state ↦ raw.code state.1
  move := fun state ↦ raw.move state.1

namespace SourceFreeBeliefSemanticTree

variable
  (raw : SourceFreeBeliefSemanticTree.{u, v, z, a}
    Direction Move BeliefCode)
  (initialAnnotation : Annotation)
  (advance : raw.Semantic → Annotation → Direction → Annotation)

@[simp] theorem carryFiniteAnnotation_initial_fst :
    (raw.carryFiniteAnnotation initialAnnotation advance).initial.1 =
      raw.initial :=
  rfl

@[simp] theorem carryFiniteAnnotation_initial_snd :
    (raw.carryFiniteAnnotation initialAnnotation advance).initial.2 =
      initialAnnotation :=
  rfl

@[simp] theorem carryFiniteAnnotation_step_fst
    (state : raw.Semantic × Annotation) (direction : Direction) :
    ((raw.carryFiniteAnnotation initialAnnotation advance).step state
      direction).1 = raw.step state.1 direction :=
  rfl

@[simp] theorem carryFiniteAnnotation_step_snd
    (state : raw.Semantic × Annotation) (direction : Direction) :
    ((raw.carryFiniteAnnotation initialAnnotation advance).step state
      direction).2 = advance state.1 state.2 direction :=
  rfl

@[simp] theorem carryFiniteAnnotation_code
    (state : raw.Semantic × Annotation) :
    (raw.carryFiniteAnnotation initialAnnotation advance).code state =
      raw.code state.1 :=
  rfl

@[simp] theorem carryFiniteAnnotation_move
    (state : raw.Semantic × Annotation) :
    (raw.carryFiniteAnnotation initialAnnotation advance).move state =
      raw.move state.1 :=
  rfl

/-- Forgetting the carried annotation after any finite direction history
recovers the literal state of the original semantic tree. -/
@[simp] theorem carryFiniteAnnotation_stateAt_fst
    (node : TreeNode Direction) :
    ((raw.carryFiniteAnnotation initialAnnotation advance).stateAt node).1 =
      raw.stateAt node := by
  induction node using List.reverseRecOn with
  | nil => rfl
  | append_singleton node direction ih =>
      rw [(raw.carryFiniteAnnotation initialAnnotation advance).stateAt_append,
        raw.stateAt_append]
      exact congrArg (fun state ↦ raw.step state direction) ih

/-- The carried annotation at a literal child is exactly the value computed
by the transition from its literal parent. -/
theorem carryFiniteAnnotation_stateAt_append_snd
    (node : TreeNode Direction) (direction : Direction) :
    ((raw.carryFiniteAnnotation initialAnnotation advance).stateAt
      (node ++ [direction])).2 =
      advance
        ((raw.carryFiniteAnnotation initialAnnotation advance).stateAt node).1
        ((raw.carryFiniteAnnotation initialAnnotation advance).stateAt node).2
        direction := by
  rw [(raw.carryFiniteAnnotation initialAnnotation advance).stateAt_append]
  rfl

/-- Any source/annotation invariant preserved by `advance` holds at every
literal node of the carried semantic tree.

This is the generic safe way to retain provenance that relates the *current*
semantic source to the annotation installed by its predecessor.  Such a
relation must be established before rationalization; it cannot in general be
recovered later from equality of the finite public code alone. -/
theorem carryFiniteAnnotation_invariant
    (Invariant : raw.Semantic → Annotation → Prop)
    (initial_invariant : Invariant raw.initial initialAnnotation)
    (step_invariant : ∀ (source : raw.Semantic) (current : Annotation)
      (direction : Direction),
      Invariant source current →
        Invariant (raw.step source direction)
          (advance source current direction))
    (node : TreeNode Direction) :
    Invariant
      ((raw.carryFiniteAnnotation initialAnnotation advance).stateAt node).1
      ((raw.carryFiniteAnnotation initialAnnotation advance).stateAt node).2 := by
  induction node using List.reverseRecOn with
  | nil => exact initial_invariant
  | append_singleton node direction ih =>
      rw [(raw.carryFiniteAnnotation initialAnnotation advance).stateAt_append]
      exact step_invariant _ _ direction ih

/-- Carrying finite controller data leaves the objective word unchanged. -/
theorem carryFiniteAnnotation_childCodeWord
    (branch : Nat → Direction) :
    (raw.carryFiniteAnnotation initialAnnotation advance).childCodeWord branch =
      raw.childCodeWord branch := by
  funext n
  change raw.code
      (((raw.carryFiniteAnnotation initialAnnotation advance).stateAt
        (branchNode branch (n + 1))).1) =
    raw.code (raw.stateAt (branchNode branch (n + 1)))
  rw [raw.carryFiniteAnnotation_stateAt_fst initialAnnotation advance]

end SourceFreeBeliefSemanticTree

namespace SourceFreeBeliefCodeParityCertificate

variable
  (D : DetParityAutomaton.{z, w} BeliefCode)
  (initialCode : BeliefCode)
  (Valid : BeliefCode → Move → Prop)
  (next : BeliefCode → Move → Direction → BeliefCode)
  (raw : SourceFreeBeliefSemanticTree.{u, v, z, a}
    Direction Move BeliefCode)
  (certificate : SourceFreeBeliefCodeParityCertificate D initialCode Valid next
    raw)

include certificate

/-- A code-parity certificate is invariant under adding finite persistent
proof/controller data to its exact semantic state. -/
theorem carryFiniteAnnotation
    (initialAnnotation : Annotation)
    (advance : raw.Semantic → Annotation → Direction → Annotation) :
    SourceFreeBeliefCodeParityCertificate D initialCode Valid next
      (raw.carryFiniteAnnotation initialAnnotation advance) := by
  refine {
    initial_code := certificate.initial_code
    valid := ?_
    next_code := ?_
    accepts := ?_ }
  · intro node
    simpa only [SourceFreeBeliefSemanticTree.carryFiniteAnnotation_code,
      SourceFreeBeliefSemanticTree.carryFiniteAnnotation_move,
      raw.carryFiniteAnnotation_stateAt_fst initialAnnotation advance] using
      certificate.valid node
  · intro node direction
    simpa only [SourceFreeBeliefSemanticTree.carryFiniteAnnotation_code,
      SourceFreeBeliefSemanticTree.carryFiniteAnnotation_move,
      SourceFreeBeliefSemanticTree.carryFiniteAnnotation_step_fst,
      raw.carryFiniteAnnotation_stateAt_fst initialAnnotation advance] using
      certificate.next_code node direction
  · intro branch
    rw [raw.carryFiniteAnnotation_childCodeWord initialAnnotation advance]
    exact certificate.accepts branch

end SourceFreeBeliefCodeParityCertificate

section ParentLink

variable {Source : Type a}

/-- The canonical parent-link law for a carried annotation.  A concrete
model normally conjoins this equation with its package-local legality law. -/
def sourceFreeBeliefCarriedLinkValid
    (advance : Source → Annotation → Direction → Annotation)
    (source : Source) (current : Annotation) (_move : Move)
    (children : Direction → Annotation) : Prop :=
  children = advance source current

theorem sourceFreeBeliefCarriedLinkValid_exact
    (advance : Source → Annotation → Direction → Annotation)
    (source : Source) (current : Annotation) (move : Move) :
    sourceFreeBeliefCarriedLinkValid advance source current move
      (fun direction ↦ advance source current direction) :=
  rfl

end ParentLink

end

end DistributedSynthesis
