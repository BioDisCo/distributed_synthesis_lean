/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemHiddenDescriptorFamilyTotality

/-!
# Descriptor-pointed supported successors

`HiddenDescriptorFamilyTotality` uses a support predicate whose arguments do
not include the current hidden descriptor.  Consequently, once a public
successor family is called supported, it must admit an exact successor from
*every* live member of the current family.  That uniform law is useful when it
is true, but it is stronger than the relational handoff needed after a full
view receive: the sender may carry one finite table assigning a possibly
different answer to every possible current descriptor, and the receiver can
apply the entry indexed by the descriptor recovered at that receive.

This file records the parallel pointed interface

```
Supported current currentFamily move direction nextFamily.
```

It provides a finite relational selector and a word certificate which yields
a genuine, nonempty exact descriptor thread.  No child family is required to
be a function of the unpointed `(family, move, direction)` data.  The current
descriptor is proof-side finite state; this construction does not expose it,
an orientation, a lane, or a strict-leader bit to either process.  A concrete
model must separately prove that the later joint receive reconstructs the
query used to index the carried table.
-/

namespace DistributedSynthesis

universe u v m b x

section

variable {Code : Type u} {MoveIdentity : Type v}
variable (D : DetParityAutomaton.{u, x} Code)
variable {FamilyMove : Type m} {Direction : Type b}
variable [Fintype Code] [Fintype MoveIdentity]

/-- Descriptor-pointed one-step totality.  Unlike the unpointed interface,
two different live descriptors in one public family may support different
successor families for the same public move and direction. -/
structure PointedHiddenDescriptorFamilyTotality
    (Represented : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Prop)
    (Live : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Prop)
    (ExactEdge : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      FamilyMove → Direction →
        HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) →
      HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
    (Valid : HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → FamilyMove → Prop)
    (Supported : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) →
      FamilyMove → Direction →
        HiddenDescriptorTwoFibreFamily D
          (MoveIdentity := MoveIdentity) → Prop) : Prop where
  live_represented : ∀ current currentFamily,
    Live current currentFamily → Represented current currentFamily
  supported_exists : ∀ current currentFamily move direction,
    Live current currentFamily →
    Valid currentFamily move →
    ∃ nextFamily, Supported current currentFamily move direction nextFamily
  target_live : ∀ current currentFamily move direction nextFamily target,
    Live current currentFamily →
    Valid currentFamily move →
    Supported current currentFamily move direction nextFamily →
    ExactEdge current move direction nextFamily target →
    Live target nextFamily
  covers : ∀ current currentFamily move direction nextFamily,
    Live current currentFamily →
    Valid currentFamily move →
    Supported current currentFamily move direction nextFamily →
    ∃ target,
      ExactEdge current move direction nextFamily target ∧
        target.control = D.step current.control target.code

/-! ## One finite descriptor-to-answer plan -/

/-- All data indexing one pointed successor-table lookup. -/
structure PointedSupportedSuccessorQuery where
  current : HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity)
  currentFamily : HiddenDescriptorTwoFibreFamily D
    (MoveIdentity := MoveIdentity)
  move : FamilyMove
  direction : Direction

noncomputable instance [Fintype FamilyMove] [Fintype Direction] :
    Fintype (PointedSupportedSuccessorQuery D
      (MoveIdentity := MoveIdentity) (FamilyMove := FamilyMove)
      (Direction := Direction)) := by
  classical
  let encode := fun query : PointedSupportedSuccessorQuery D
      (MoveIdentity := MoveIdentity) (FamilyMove := FamilyMove)
      (Direction := Direction) =>
    (query.current, query.currentFamily, query.move, query.direction)
  exact Fintype.ofInjective encode (by
    intro left right heq
    rcases left with ⟨leftCurrent, leftFamily, leftMove, leftDirection⟩
    rcases right with ⟨rightCurrent, rightFamily, rightMove,
      rightDirection⟩
    simp only [encode, Prod.mk.injEq] at heq
    rcases heq with ⟨rfl, rfl, rfl, rfl⟩
    rfl)

/-- A selected public successor family together with its exact target. -/
abbrev PointedSupportedSuccessorAnswer :=
  HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) ×
    HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity)

/-- The complete relation checked by a pointed successor table. -/
def PointedSupportedSuccessorGood
    (ExactEdge : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      FamilyMove → Direction →
        HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) →
      HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
    (Supported : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) →
      FamilyMove → Direction →
        HiddenDescriptorTwoFibreFamily D
          (MoveIdentity := MoveIdentity) → Prop)
    (query : PointedSupportedSuccessorQuery D
      (MoveIdentity := MoveIdentity) (FamilyMove := FamilyMove)
      (Direction := Direction))
    (answer : PointedSupportedSuccessorAnswer D
      (MoveIdentity := MoveIdentity)) : Prop :=
  Supported query.current query.currentFamily query.move query.direction
      answer.1 ∧
    ExactEdge query.current query.move query.direction answer.1 answer.2 ∧
      answer.2.control = D.step query.current.control answer.2.code

/-- The finite carried plan.  `none` is reserved for non-live or invalid
queries; live valid queries are proved to select `some`. -/
abbrev PointedSupportedSuccessorTable :=
  PointedSupportedSuccessorQuery D
      (MoveIdentity := MoveIdentity) (FamilyMove := FamilyMove)
      (Direction := Direction) →
    Option (PointedSupportedSuccessorAnswer D
      (MoveIdentity := MoveIdentity))

/-- Select one answer without imposing uniqueness on the relational image. -/
noncomputable def pointedSupportedSuccessor?
    (ExactEdge : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      FamilyMove → Direction →
        HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) →
      HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
    (Supported : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) →
      FamilyMove → Direction →
        HiddenDescriptorTwoFibreFamily D
          (MoveIdentity := MoveIdentity) → Prop) :
    PointedSupportedSuccessorTable D
      (MoveIdentity := MoveIdentity) (FamilyMove := FamilyMove)
      (Direction := Direction) := by
  classical
  exact fun query =>
    if h : ∃ answer, PointedSupportedSuccessorGood D ExactEdge Supported
        query answer then
      some (Classical.choose h)
    else
      none

/-- Pointed totality makes the finite plan nonempty on every live valid
query, and the selected answer satisfies support, exactness, and the DPA
control step simultaneously. -/
theorem pointedSupportedSuccessor?_spec
    (Represented : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Prop)
    (Live : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Prop)
    (ExactEdge : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      FamilyMove → Direction →
        HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) →
      HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
    (Valid : HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → FamilyMove → Prop)
    (Supported : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) →
      FamilyMove → Direction →
        HiddenDescriptorTwoFibreFamily D
          (MoveIdentity := MoveIdentity) → Prop)
    (totality : PointedHiddenDescriptorFamilyTotality D Represented Live
      ExactEdge Valid Supported)
    (query : PointedSupportedSuccessorQuery D
      (MoveIdentity := MoveIdentity) (FamilyMove := FamilyMove)
      (Direction := Direction))
    (hlive : Live query.current query.currentFamily)
    (hvalid : Valid query.currentFamily query.move) :
    ∃ answer,
      pointedSupportedSuccessor? D ExactEdge Supported query = some answer ∧
        PointedSupportedSuccessorGood D ExactEdge Supported query answer := by
  classical
  obtain ⟨nextFamily, hsupported⟩ := totality.supported_exists
    query.current query.currentFamily query.move query.direction hlive hvalid
  obtain ⟨target, hedge, hcontrol⟩ := totality.covers query.current
    query.currentFamily query.move query.direction nextFamily hlive hvalid
    hsupported
  let answer : PointedSupportedSuccessorAnswer D
      (MoveIdentity := MoveIdentity) := (nextFamily, target)
  have hgood : PointedSupportedSuccessorGood D ExactEdge Supported query
      answer := ⟨hsupported, hedge, hcontrol⟩
  let hexists : ∃ answer,
      PointedSupportedSuccessorGood D ExactEdge Supported query answer :=
    ⟨answer, hgood⟩
  refine ⟨Classical.choose hexists, ?_, Classical.choose_spec hexists⟩
  simp only [pointedSupportedSuccessor?, dif_pos hexists]

/-- A blocked live query is the exact fail-fast witness for the pointed
route.  Distinct successful answers are not a failure. -/
theorem not_pointedHiddenDescriptorFamilyTotality_of_blocked
    (Represented : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Prop)
    (Live : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Prop)
    (ExactEdge : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      FamilyMove → Direction →
        HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) →
      HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
    (Valid : HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → FamilyMove → Prop)
    (Supported : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) →
      FamilyMove → Direction →
        HiddenDescriptorTwoFibreFamily D
          (MoveIdentity := MoveIdentity) → Prop)
    (query : PointedSupportedSuccessorQuery D
      (MoveIdentity := MoveIdentity) (FamilyMove := FamilyMove)
      (Direction := Direction))
    (hlive : Live query.current query.currentFamily)
    (hvalid : Valid query.currentFamily query.move)
    (hblocked : ∀ answer,
      ¬ PointedSupportedSuccessorGood D ExactEdge Supported query answer) :
    ¬ PointedHiddenDescriptorFamilyTotality D Represented Live ExactEdge
      Valid Supported := by
  intro totality
  obtain ⟨answer, _, hgood⟩ := pointedSupportedSuccessor?_spec D
    Represented Live ExactEdge Valid Supported totality query hlive hvalid
  exact hblocked answer hgood

/-! ## Pointed public-word certificate -/

/-- A public word together with the particular live descriptor trajectory
which justifies each descriptor-indexed support lookup.  This is the pointed
replacement for `HiddenDescriptorFamilyWordAdmissible`; it is deliberately a
certificate, not an observable extension of the word alphabet. -/
structure PointedHiddenDescriptorFamilyWordAdmissible
    (Live : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Prop)
    (ExactEdge : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      FamilyMove → Direction →
        HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) →
      HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
    (Valid : HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → FamilyMove → Prop)
    (Supported : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) →
      FamilyMove → Direction →
        HiddenDescriptorTwoFibreFamily D
          (MoveIdentity := MoveIdentity) → Prop)
    (initialDescriptor : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity))
    (initialFamily : HiddenDescriptorTwoFibreFamily D
      (MoveIdentity := MoveIdentity))
    (word : OmegaWord (HiddenDescriptorFamilyLetter
      (FamilyMove := FamilyMove) (Direction := Direction)
      (FamilyCode := HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity)))) where
  descriptor : Nat → HiddenCodeControlDescriptor D
    (MoveIdentity := MoveIdentity)
  initial : descriptor 0 = initialDescriptor
  live : ∀ n,
    Live (descriptor n) (hiddenDescriptorFamilyAt D initialFamily word n)
  valid : ∀ n,
    Valid (hiddenDescriptorFamilyAt D initialFamily word n) (word n).1
  supported : ∀ n,
    Supported (descriptor n) (hiddenDescriptorFamilyAt D initialFamily word n)
      (word n).1 (word n).2.1 (word n).2.2
  exactEdge : ∀ n,
    ExactEdge (descriptor n) (word n).1 (word n).2.1 (word n).2.2
      (descriptor (n + 1))
  controlStep : ∀ n, (descriptor (n + 1)).control =
    D.step (descriptor n).control (descriptor (n + 1)).code

namespace PointedHiddenDescriptorFamilyWordAdmissible

/-- Forgetting the proof-side support witnesses leaves exactly a persistent
thread of the existing hidden-descriptor continuity system. -/
noncomputable def toContinuityThread
    (Live : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Prop)
    (ExactEdge : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      FamilyMove → Direction →
        HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) →
      HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
    (Valid : HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → FamilyMove → Prop)
    (Supported : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) →
      FamilyMove → Direction →
        HiddenDescriptorTwoFibreFamily D
          (MoveIdentity := MoveIdentity) → Prop)
    (initialDescriptor : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity))
    (initialFamily : HiddenDescriptorTwoFibreFamily D
      (MoveIdentity := MoveIdentity))
    (word : OmegaWord (HiddenDescriptorFamilyLetter
      (FamilyMove := FamilyMove) (Direction := Direction)
      (FamilyCode := HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity))))
    (admissible : PointedHiddenDescriptorFamilyWordAdmissible D Live ExactEdge
      Valid Supported initialDescriptor initialFamily word) :
    HiddenDescriptorContinuityThread D initialDescriptor ExactEdge word where
  descriptor := admissible.descriptor
  initial := admissible.initial
  exactEdge := admissible.exactEdge
  controlStep := admissible.controlStep

/-- Descriptor-pointed admissibility is explicitly non-vacuous. -/
theorem nonempty_continuityThread
    (Live : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Prop)
    (ExactEdge : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      FamilyMove → Direction →
        HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) →
      HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
    (Valid : HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → FamilyMove → Prop)
    (Supported : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) →
      FamilyMove → Direction →
        HiddenDescriptorTwoFibreFamily D
          (MoveIdentity := MoveIdentity) → Prop)
    (initialDescriptor : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity))
    (initialFamily : HiddenDescriptorTwoFibreFamily D
      (MoveIdentity := MoveIdentity))
    (word : OmegaWord (HiddenDescriptorFamilyLetter
      (FamilyMove := FamilyMove) (Direction := Direction)
      (FamilyCode := HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity))))
    (admissible : PointedHiddenDescriptorFamilyWordAdmissible D Live ExactEdge
      Valid Supported initialDescriptor initialFamily word) :
    Nonempty (HiddenDescriptorContinuityThread D initialDescriptor ExactEdge
      word) :=
  ⟨admissible.toContinuityThread D Live ExactEdge Valid Supported
    initialDescriptor initialFamily word⟩

end PointedHiddenDescriptorFamilyWordAdmissible

end

end DistributedSynthesis
