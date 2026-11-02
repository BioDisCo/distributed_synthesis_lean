/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFamilyAwareHiddenDescriptorThreadLifting
import DistributedSynthesis.Formalizations.Lemma.LemGuardedSemanticFamilyTree

/-!
# Canonical exact threads from pointed semantic edges

The descriptor-free `Supported family move direction nextFamily` interface is
useful when one advertised child family works for every live descriptor in a
public family.  The delayed full-view construction needs a weaker fact: after
the joint receive has recovered the actual current descriptor, its finite
plan supplies an exact edge for that pointed descriptor.

This file records the corresponding non-vacuity theorem.  A pointed semantic
edge builder gives the literal exact edge and DPA control update at every
semantic state and direction.  It directly constructs the canonical infinite
descriptor thread.  No common child family for all members of the advertised
family is assumed.

The construction is proof-side.  It does not expose the current descriptor,
direction, lane, orientation, or strict leader to either process; the model
adapter must still show that a real full-view receive evaluates the carried
finite pointed plan at the actual descriptor.
-/

namespace DistributedSynthesis

universe u v m b f x y

section

variable {Code : Type u} {MoveIdentity : Type v}
variable (D : DetParityAutomaton.{u, x} Code)
variable {FamilyMove : Type m} {Direction : Type b} {Family : Type f}
variable {Semantic : Type y}

/-- Pointed existence law for the literal semantic successor.  Unlike the
older descriptor-free support predicate, the old descriptor is fixed by the
semantic state before the child family is selected. -/
structure FamilyAwareSemanticExactEdge
    (semanticStep : Semantic → Direction → Semantic)
    (semanticDescriptor : Semantic → HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity))
    (familyOf : Semantic → Family)
    (semanticMove : Semantic → FamilyMove)
    (ExactEdge : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      FamilyMove → Direction → Family →
        HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop) :
    Prop where
  exactEdge : ∀ state direction,
    ExactEdge (semanticDescriptor state) (semanticMove state) direction
      (familyOf (semanticStep state direction))
      (semanticDescriptor (semanticStep state direction))
  controlStep : ∀ state direction,
    (semanticDescriptor (semanticStep state direction)).control =
      D.step (semanticDescriptor state).control
        (semanticDescriptor (semanticStep state direction)).code

/-- The literal public word of a semantic direction branch. -/
def familyAwareSemanticWord
    (initial : Semantic)
    (semanticStep : Semantic → Direction → Semantic)
    (familyOf : Semantic → Family)
    (semanticMove : Semantic → FamilyMove)
    (branch : Nat → Direction) :
    OmegaWord (HiddenDescriptorFamilyLetter
      (FamilyMove := FamilyMove) (Direction := Direction)
      (FamilyCode := Family)) := fun n =>
  let current := guardedSemanticFamilyIterate initial semanticStep branch n
  let next := semanticStep current (branch n)
  (semanticMove current, (branch n, familyOf next))

namespace FamilyAwareSemanticExactEdge

variable
  (semanticStep : Semantic → Direction → Semantic)
  (semanticDescriptor : Semantic → HiddenCodeControlDescriptor D
    (MoveIdentity := MoveIdentity))
  (familyOf : Semantic → Family)
  (semanticMove : Semantic → FamilyMove)
  (ExactEdge : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity) →
    FamilyMove → Direction → Family →
      HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
  (builder : FamilyAwareSemanticExactEdge D semanticStep semanticDescriptor
    familyOf semanticMove ExactEdge)
  (initial : Semantic)

/-- The everywhere-live exact thread obtained from one literal semantic
branch.  Its existence is independent of any all-members support law. -/
def thread (branch : Nat → Direction) :
    HiddenDescriptorContinuityThread D (semanticDescriptor initial) ExactEdge
      (familyAwareSemanticWord initial semanticStep familyOf semanticMove
        branch) where
  descriptor := fun n => semanticDescriptor
    (guardedSemanticFamilyIterate initial semanticStep branch n)
  initial := rfl
  exactEdge := by
    intro n
    exact builder.exactEdge
      (guardedSemanticFamilyIterate initial semanticStep branch n) (branch n)
  controlStep := by
    intro n
    exact builder.controlStep
      (guardedSemanticFamilyIterate initial semanticStep branch n) (branch n)

include builder

/-- The canonical pointed exact thread is genuinely nonempty. -/
theorem thread_nonempty (branch : Nat → Direction) :
    Nonempty
      (HiddenDescriptorContinuityThread D (semanticDescriptor initial)
        ExactEdge
        (familyAwareSemanticWord initial semanticStep familyOf semanticMove
          branch)) :=
  ⟨FamilyAwareSemanticExactEdge.thread
    (D := D) (semanticStep := semanticStep)
    (semanticDescriptor := semanticDescriptor) (familyOf := familyOf)
    (semanticMove := semanticMove) (ExactEdge := ExactEdge)
    (builder := builder) (initial := initial) branch⟩

/-- Its child-code word is the literal semantic child-code word. -/
@[simp] theorem thread_childCodeWord (branch : Nat → Direction) :
    (FamilyAwareSemanticExactEdge.thread
      (D := D) (semanticStep := semanticStep)
      (semanticDescriptor := semanticDescriptor) (familyOf := familyOf)
      (semanticMove := semanticMove) (ExactEdge := ExactEdge)
      (builder := builder) (initial := initial) branch).childCodeWord =
      fun n =>
        (semanticDescriptor
          (guardedSemanticFamilyIterate initial semanticStep branch (n + 1))).code :=
  rfl

/-- Literal semantic branch parity transfers to the pointed exact thread. -/
theorem thread_accepts
    (haccepts : ∀ branch : Nat → Direction,
      D.Accepts (fun n ↦
        (semanticDescriptor
          (guardedSemanticFamilyIterate initial semanticStep branch
            (n + 1))).code))
    (branch : Nat → Direction) :
    D.Accepts
      (FamilyAwareSemanticExactEdge.thread
        (D := D) (semanticStep := semanticStep)
        (semanticDescriptor := semanticDescriptor) (familyOf := familyOf)
        (semanticMove := semanticMove) (ExactEdge := ExactEdge)
        (builder := builder) (initial := initial) branch).childCodeWord := by
  rw [FamilyAwareSemanticExactEdge.thread_childCodeWord
    (D := D) (semanticStep := semanticStep)
    (semanticDescriptor := semanticDescriptor) (familyOf := familyOf)
    (semanticMove := semanticMove) (ExactEdge := ExactEdge)
    (builder := builder) (initial := initial) branch]
  exact haccepts branch

end FamilyAwareSemanticExactEdge

/-! ## Identification with the canonical guarded-tree branch -/

variable [Inhabited Direction] [DecidableEq Family]

/-- The direct semantic word is exactly the word read from the canonical
coherent branch of the totalized guarded tree. -/
theorem familyAwareSemanticWord_eq_guardedObservableWord
    (initial : Semantic)
    (semanticStep : Semantic → Direction → Semantic)
    (familyOf : Semantic → Family)
    (semanticMove : Semantic → FamilyMove)
    (Valid : Family → FamilyMove → Prop)
    (htotal : ∀ family, ∃ move, Valid family move)
    (branch : Nat → Direction) :
    familyAwareSemanticWord initial semanticStep familyOf semanticMove branch =
      observableThreadWord
        (guardedSemanticFamilyTree initial semanticStep familyOf semanticMove
          Valid htotal)
        (guardedSemanticFamilyObservationBranch initial semanticStep familyOf
          branch) := by
  funext n
  change
    (semanticMove
        (guardedSemanticFamilyIterate initial semanticStep branch n),
      (branch n,
        familyOf
          (semanticStep
            (guardedSemanticFamilyIterate initial semanticStep branch n)
            (branch n)))) =
      (guardedSemanticFamilyTree initial semanticStep familyOf semanticMove
          Valid htotal
          (branchNode
            (guardedSemanticFamilyObservationBranch initial semanticStep
              familyOf branch) n),
        (branch n,
          familyOf
            (guardedSemanticFamilyIterate initial semanticStep branch
              (n + 1))))
  rw [guardedSemanticFamilyTree_branchNode initial semanticStep familyOf
    semanticMove Valid htotal branch n]
  rfl

/-- Pointed semantic existence therefore supplies a nonempty exact thread on
the guarded tree's canonical coherent branch, without descriptor-free
support. -/
theorem nonempty_guardedCanonicalThread_of_semanticExactEdge
    (semanticDescriptor : Semantic → HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity))
    (ExactEdge : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      FamilyMove → Direction → Family →
        HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
    (initial : Semantic)
    (semanticStep : Semantic → Direction → Semantic)
    (familyOf : Semantic → Family)
    (semanticMove : Semantic → FamilyMove)
    (Valid : Family → FamilyMove → Prop)
    (htotal : ∀ family, ∃ move, Valid family move)
    (builder : FamilyAwareSemanticExactEdge D semanticStep semanticDescriptor
      familyOf semanticMove ExactEdge)
    (branch : Nat → Direction) :
    Nonempty
      (HiddenDescriptorContinuityThread D (semanticDescriptor initial)
        ExactEdge
        (observableThreadWord
          (guardedSemanticFamilyTree initial semanticStep familyOf semanticMove
            Valid htotal)
          (guardedSemanticFamilyObservationBranch initial semanticStep familyOf
            branch))) := by
  rw [← familyAwareSemanticWord_eq_guardedObservableWord initial semanticStep
    familyOf semanticMove Valid htotal branch]
  exact FamilyAwareSemanticExactEdge.thread_nonempty
    (D := D) (semanticStep := semanticStep)
    (semanticDescriptor := semanticDescriptor) (familyOf := familyOf)
    (semanticMove := semanticMove) (ExactEdge := ExactEdge)
    (builder := builder) (initial := initial) branch

end

end DistributedSynthesis
