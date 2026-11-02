/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteSemanticThreadLifting
import DistributedSynthesis.Formalizations.Lemma.LemHiddenDescriptorContinuityBundle

/-!
# One-origin lifting for control-aware hidden descriptor threads

`HiddenDescriptorContinuityThread` retains the literal finite descriptor

```
((code, objective control), installed move identity)
```

across a staged family word.  This file connects that thread type to the
generic recursive `SemanticEdgeLifter`.  The finite direction and computed
next family code are kept together as the generic lifter's public `Family`
argument; the recursive selector remains proof-side data.

This conversion is deliberately exact.  It does not turn pairwise witnesses
for descriptor edges into a semantic path.  A concrete model must still
supply one `SemanticEdgeLifter` whose `lifts` field works from the current
semantic representative reached at the preceding step.
-/

namespace DistributedSynthesis

universe u v m b f x y z

section

variable {Code : Type u} {MoveIdentity : Type v}
variable (D : DetParityAutomaton.{u, x} Code)
variable {FamilyMove : Type m} {PublicDirection : Type b}
variable {FamilyCode : Type f}
variable {Semantic : Type y} {SemanticDirection : Type z}
variable [Fintype Code] [Fintype MoveIdentity]

/-- Curry a staged descriptor edge into the generic edge shape. -/
abbrev hiddenDescriptorEdge
    (ExactEdge : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      FamilyMove → PublicDirection → FamilyCode →
        HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop) :
    HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) →
      FamilyMove → (PublicDirection × FamilyCode) →
        HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop :=
  fun current move publicData target =>
    ExactEdge current move publicData.1 publicData.2 target

/-- A control-aware descriptor thread viewed as the descriptor-valued thread
consumed by `SemanticEdgeLifter`. -/
def HiddenDescriptorContinuityThread.asCodeThread
    (initialDescriptor : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity))
    (ExactEdge : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      FamilyMove → PublicDirection → FamilyCode →
        HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
    (word : OmegaWord (HiddenDescriptorFamilyLetter
      (FamilyMove := FamilyMove) (Direction := PublicDirection)
      (FamilyCode := FamilyCode)))
    (thread : HiddenDescriptorContinuityThread D initialDescriptor ExactEdge
      word) :
    HiddenCodeContinuityThread initialDescriptor
      (hiddenDescriptorEdge D ExactEdge) word where
  code := thread.descriptor
  initial := thread.initial
  edge := by
    intro n
    exact thread.exactEdge n

omit [Fintype Code] [Fintype MoveIdentity] in
@[simp] theorem HiddenDescriptorContinuityThread.asCodeThread_code
    (initialDescriptor : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity))
    (ExactEdge : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      FamilyMove → PublicDirection → FamilyCode →
        HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
    (word : OmegaWord (HiddenDescriptorFamilyLetter
      (FamilyMove := FamilyMove) (Direction := PublicDirection)
      (FamilyCode := FamilyCode)))
    (thread : HiddenDescriptorContinuityThread D initialDescriptor ExactEdge
      word) (n : Nat) :
    (thread.asCodeThread D initialDescriptor ExactEdge word).code n =
      thread.descriptor n :=
  rfl

omit [Fintype Code] [Fintype MoveIdentity] in
@[simp] theorem HiddenDescriptorContinuityThread.asCodeThread_childCodeWord
    (initialDescriptor : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity))
    (ExactEdge : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      FamilyMove → PublicDirection → FamilyCode →
        HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
    (word : OmegaWord (HiddenDescriptorFamilyLetter
      (FamilyMove := FamilyMove) (Direction := PublicDirection)
      (FamilyCode := FamilyCode)))
    (thread : HiddenDescriptorContinuityThread D initialDescriptor ExactEdge
      word) :
    (thread.asCodeThread D initialDescriptor ExactEdge word).childCodeWord =
      fun n => thread.descriptor (n + 1) :=
  rfl

/-- Exact one-origin semantic lifting surface for the full descriptor. -/
abbrev HiddenDescriptorSemanticEdgeLifter
    (semanticStep : Semantic → SemanticDirection → Semantic)
    (semanticDescriptor : Semantic → HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity))
    (ExactEdge : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      FamilyMove → PublicDirection → FamilyCode →
        HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop) :=
  SemanticEdgeLifter semanticStep semanticDescriptor
    (hiddenDescriptorEdge D ExactEdge)

namespace HiddenDescriptorSemanticEdgeLifter

variable
  (semanticStep : Semantic → SemanticDirection → Semantic)
  (semanticDescriptor : Semantic → HiddenCodeControlDescriptor D
    (MoveIdentity := MoveIdentity))
  (initial : Semantic)
  (ExactEdge : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity) →
    FamilyMove → PublicDirection → FamilyCode →
      HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
  (lifter : HiddenDescriptorSemanticEdgeLifter D semanticStep
    semanticDescriptor ExactEdge)
  (word : OmegaWord (HiddenDescriptorFamilyLetter
    (FamilyMove := FamilyMove) (Direction := PublicDirection)
    (FamilyCode := FamilyCode)))
  (thread : HiddenDescriptorContinuityThread D
    (semanticDescriptor initial) ExactEdge word)

/-- Proof-side semantic direction selected recursively from the current
semantic representative and the next full hidden descriptor. -/
noncomputable def liftedBranch (n : Nat) : SemanticDirection :=
  SemanticEdgeLifter.liftedBranch semanticStep semanticDescriptor
    (hiddenDescriptorEdge D ExactEdge) lifter initial word
    (thread.asCodeThread D (semanticDescriptor initial) ExactEdge word) n

omit [Fintype Code] [Fintype MoveIdentity] in
/-- The entire full-descriptor thread is the positive-time descriptor word
of one literal semantic branch. -/
theorem childDescriptorWord_eq :
    (fun n => thread.descriptor (n + 1)) = fun n =>
      semanticDescriptor
        ((branchNode
          (HiddenDescriptorSemanticEdgeLifter.liftedBranch
            (D := D) (semanticStep := semanticStep)
            (semanticDescriptor := semanticDescriptor) (initial := initial)
            (ExactEdge := ExactEdge) (lifter := lifter) (word := word)
            (thread := thread))
          (n + 1)).foldl semanticStep initial) := by
  exact SemanticEdgeLifter.childDescriptorWord_eq
    (lifter := lifter) (initial := initial) (word := word)
    (thread := thread.asCodeThread D (semanticDescriptor initial) ExactEdge
      word)

omit [Fintype Code] [Fintype MoveIdentity] in
/-- Projecting the preceding exact equality to the objective alphabet gives
the child code word needed by the code DPA. -/
theorem childCodeWord_eq :
    thread.childCodeWord = fun n =>
      (semanticDescriptor
        ((branchNode
          (HiddenDescriptorSemanticEdgeLifter.liftedBranch
            (D := D) (semanticStep := semanticStep)
            (semanticDescriptor := semanticDescriptor) (initial := initial)
            (ExactEdge := ExactEdge) (lifter := lifter) (word := word)
            (thread := thread))
          (n + 1)).foldl semanticStep initial)).code :=
    by
  funext n
  have h := congrFun
    (HiddenDescriptorSemanticEdgeLifter.childDescriptorWord_eq
      (D := D) (semanticStep := semanticStep)
      (semanticDescriptor := semanticDescriptor) (initial := initial)
      (ExactEdge := ExactEdge) (lifter := lifter) (word := word)
      (thread := thread)) n
  exact congrArg HiddenCodeControlDescriptor.code h

end HiddenDescriptorSemanticEdgeLifter

/-! ## Direct parity and universal-system transfer -/

omit [Fintype Code] [Fintype MoveIdentity] in
/-- Universal acceptance of all literal semantic branches transfers to one
persistent control-aware hidden descriptor thread. -/
theorem hiddenDescriptorThread_accepts_of_semanticEdgeLifter
    (semanticStep : Semantic → SemanticDirection → Semantic)
    (semanticDescriptor : Semantic → HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity))
    (initial : Semantic)
    (ExactEdge : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      FamilyMove → PublicDirection → FamilyCode →
        HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
    (lifter : HiddenDescriptorSemanticEdgeLifter D semanticStep
      semanticDescriptor ExactEdge)
    (word : OmegaWord (HiddenDescriptorFamilyLetter
      (FamilyMove := FamilyMove) (Direction := PublicDirection)
      (FamilyCode := FamilyCode)))
    (thread : HiddenDescriptorContinuityThread D
      (semanticDescriptor initial) ExactEdge word)
    (haccepts : ∀ branch : Nat → SemanticDirection,
      D.Accepts (fun n =>
        (semanticDescriptor
          ((branchNode branch (n + 1)).foldl semanticStep initial)).code)) :
    D.Accepts thread.childCodeWord := by
  rw [HiddenDescriptorSemanticEdgeLifter.childCodeWord_eq
    (D := D) (semanticStep := semanticStep)
    (semanticDescriptor := semanticDescriptor) (initial := initial)
    (ExactEdge := ExactEdge) (lifter := lifter) (word := word)
    (thread := thread)]
  exact haccepts _

/-- End-to-end word acceptance of the control-aware universal thread system
from the local current-state edge lifter and the already proved semantic
branch parity theorem. -/
theorem hiddenDescriptorContinuitySystem_accepts_of_semanticEdgeLifter
    (semanticStep : Semantic → SemanticDirection → Semantic)
    (semanticDescriptor : Semantic → HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity))
    (initial : Semantic)
    (hinitialControl : (semanticDescriptor initial).control = D.initial)
    (ExactEdge : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      FamilyMove → PublicDirection → FamilyCode →
        HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
    (lifter : HiddenDescriptorSemanticEdgeLifter D semanticStep
      semanticDescriptor ExactEdge)
    (word : OmegaWord (HiddenDescriptorFamilyLetter
      (FamilyMove := FamilyMove) (Direction := PublicDirection)
      (FamilyCode := FamilyCode)))
    (haccepts : ∀ branch : Nat → SemanticDirection,
      D.Accepts (fun n =>
        (semanticDescriptor
          ((branchNode branch (n + 1)).foldl semanticStep initial)).code)) :
    (hiddenDescriptorContinuitySystem D (semanticDescriptor initial)
      ExactEdge).universalRunDPA.Accepts word := by
  rw [hiddenDescriptorContinuitySystem_universalRunDPA_accepts_iff D
    (semanticDescriptor initial) hinitialControl ExactEdge word]
  intro thread
  exact hiddenDescriptorThread_accepts_of_semanticEdgeLifter D semanticStep
    semanticDescriptor initial ExactEdge lifter word thread haccepts

end

end DistributedSynthesis
