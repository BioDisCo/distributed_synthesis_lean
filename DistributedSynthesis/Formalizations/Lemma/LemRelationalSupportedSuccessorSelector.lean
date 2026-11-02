/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemActualFullViewFamilyRecovery
import DistributedSynthesis.Formalizations.Lemma.LemFamilyAwareHiddenDescriptorThreadLifting

/-!
# Finite relational selection of supported exact successors

An operational receiver need not compute a preordained literal semantic child
family as a function of its finite state.  It is enough to retain the current
public family, current live descriptor, selected move, and finite direction
query, and choose *some* pair `(nextFamily, target)` satisfying the supported
exact-edge relation and the DPA control update.

This file packages that alternative precisely.  The query and answer types
are finite whenever their four coordinates are finite.  The selector is
totalized with `Option`: it returns `some` on every live, valid query covered
by the model and may return `none` on impossible public data.  Multiple good
answers are harmless; unlike functional child-family factorization, a
same-query collision does not refute this construction.

The bridge from `HiddenDescriptorFamilyTotality` shows where existence comes
from.  The bridge to `FamilyAwareHiddenDescriptorEdgeLifter` shows why any
selected exact answer remains one-origin semantic: validity at the current
family and the exact edge identify both the literal semantic child descriptor
and its public family.

This does not claim that a real receive has reconstructed the current query
and descriptor.  That remains the model-specific full-view/readback invariant
guarded by `LemActualFullViewFamilyRecovery`; no bit, lane, orientation, or
strict-leader signal is added here.
-/

namespace DistributedSynthesis

universe f d m b c u v x y

/-- All finite data available when choosing a relational successor. -/
structure RelationalSupportedSuccessorQuery
    (Family : Type f) (Descriptor : Type d) (Move : Type m)
    (Direction : Type b) where
  family : Family
  descriptor : Descriptor
  move : Move
  direction : Direction
  deriving Fintype

/-- The selected public child family and exact target descriptor. -/
abbrev RelationalSupportedSuccessorAnswer
    (Family : Type f) (Descriptor : Type d) := Family × Descriptor

/-- One acceptable answer to a relational successor query. -/
def RelationalSupportedSuccessorGood
    {Family : Type f} {Descriptor : Type d} {Move : Type m}
    {Direction : Type b}
    (Supported : Family → Move → Direction → Family → Prop)
    (ExactEdge : Descriptor → Move → Direction → Family →
      Descriptor → Prop)
    (ControlStep : Descriptor → Descriptor → Prop)
    (query : RelationalSupportedSuccessorQuery Family Descriptor Move Direction)
    (answer : RelationalSupportedSuccessorAnswer Family Descriptor) : Prop :=
  Supported query.family query.move query.direction answer.1 ∧
    ExactEdge query.descriptor query.move query.direction answer.1 answer.2 ∧
      ControlStep query.descriptor answer.2

/-- Every live, node-valid query has at least one supported exact answer. -/
def RelationalSupportedSuccessorCoverage
    {Family : Type f} {Descriptor : Type d} {Move : Type m}
    {Direction : Type b}
    (Supported : Family → Move → Direction → Family → Prop)
    (ExactEdge : Descriptor → Move → Direction → Family →
      Descriptor → Prop)
    (ControlStep : Descriptor → Descriptor → Prop)
    (Live : Descriptor → Family → Prop)
    (Valid : Family → Move → Prop) : Prop :=
  ∀ query : RelationalSupportedSuccessorQuery Family Descriptor Move Direction,
    Live query.descriptor query.family →
    Valid query.family query.move →
    ∃ answer,
      RelationalSupportedSuccessorGood Supported ExactEdge ControlStep query
        answer

/-- A total finite-state table, with `none` reserved for uncovered public
queries. -/
abbrev RelationalSupportedSuccessorTable
    (Family : Type f) (Descriptor : Type d) (Move : Type m)
    (Direction : Type b) :=
  RelationalSupportedSuccessorQuery Family Descriptor Move Direction →
    Option (RelationalSupportedSuccessorAnswer Family Descriptor)

noncomputable instance relationalSupportedSuccessorTable_fintype
    {Family : Type f} {Descriptor : Type d} {Move : Type m}
    {Direction : Type b}
    [Fintype Family] [Fintype Descriptor] [Fintype Move] [Fintype Direction] :
    Fintype
      (RelationalSupportedSuccessorTable Family Descriptor Move Direction) := by
  classical
  infer_instance

/-- The semantic specification of a totalized relational selector table. -/
def RelationalSupportedSuccessorTableWorks
    {Family : Type f} {Descriptor : Type d} {Move : Type m}
    {Direction : Type b}
    (Supported : Family → Move → Direction → Family → Prop)
    (ExactEdge : Descriptor → Move → Direction → Family →
      Descriptor → Prop)
    (ControlStep : Descriptor → Descriptor → Prop)
    (Live : Descriptor → Family → Prop)
    (Valid : Family → Move → Prop)
    (table : RelationalSupportedSuccessorTable Family Descriptor Move
      Direction) : Prop :=
  ∀ query,
    Live query.descriptor query.family →
    Valid query.family query.move →
    ∃ answer,
      table query = some answer ∧
        RelationalSupportedSuccessorGood Supported ExactEdge ControlStep query
          answer

/-- Classical selector of one supported exact answer.  In the intended use
all domains are finite, so this is one finite table. -/
noncomputable def relationalSupportedSuccessor?
    {Family : Type f} {Descriptor : Type d} {Move : Type m}
    {Direction : Type b}
    (Supported : Family → Move → Direction → Family → Prop)
    (ExactEdge : Descriptor → Move → Direction → Family →
      Descriptor → Prop)
    (ControlStep : Descriptor → Descriptor → Prop) :
    RelationalSupportedSuccessorTable Family Descriptor Move Direction := by
  classical
  exact fun query =>
    if h : ∃ answer,
        RelationalSupportedSuccessorGood Supported ExactEdge ControlStep query
          answer then
      some (Classical.choose h)
    else
      none

/-- Whenever a good answer exists, the selected answer is good. -/
theorem relationalSupportedSuccessor?_spec_of_exists
    {Family : Type f} {Descriptor : Type d} {Move : Type m}
    {Direction : Type b}
    (Supported : Family → Move → Direction → Family → Prop)
    (ExactEdge : Descriptor → Move → Direction → Family →
      Descriptor → Prop)
    (ControlStep : Descriptor → Descriptor → Prop)
    (query : RelationalSupportedSuccessorQuery Family Descriptor Move Direction)
    (hexists : ∃ answer,
      RelationalSupportedSuccessorGood Supported ExactEdge ControlStep query
        answer) :
    ∃ answer,
      relationalSupportedSuccessor? Supported ExactEdge ControlStep query =
          some answer ∧
        RelationalSupportedSuccessorGood Supported ExactEdge ControlStep query
          answer := by
  classical
  refine ⟨Classical.choose hexists, ?_, Classical.choose_spec hexists⟩
  simp only [relationalSupportedSuccessor?, dif_pos hexists]

/-- Covered live queries never take the `none` fallback. -/
theorem relationalSupportedSuccessor?_spec_of_coverage
    {Family : Type f} {Descriptor : Type d} {Move : Type m}
    {Direction : Type b}
    (Supported : Family → Move → Direction → Family → Prop)
    (ExactEdge : Descriptor → Move → Direction → Family →
      Descriptor → Prop)
    (ControlStep : Descriptor → Descriptor → Prop)
    (Live : Descriptor → Family → Prop)
    (Valid : Family → Move → Prop)
    (coverage : RelationalSupportedSuccessorCoverage Supported ExactEdge
      ControlStep Live Valid)
    (query : RelationalSupportedSuccessorQuery Family Descriptor Move Direction)
    (hlive : Live query.descriptor query.family)
    (hvalid : Valid query.family query.move) :
    ∃ answer,
      relationalSupportedSuccessor? Supported ExactEdge ControlStep query =
          some answer ∧
        RelationalSupportedSuccessorGood Supported ExactEdge ControlStep query
          answer :=
  relationalSupportedSuccessor?_spec_of_exists Supported ExactEdge ControlStep
    query (coverage query hlive hvalid)

/-- Coverage is exactly the existence of one totalized selector table which
returns a good answer on all live valid queries.  With finite coordinates the
witness belongs to the finite table type above. -/
theorem relationalSupportedSuccessorCoverage_iff_exists_table
    {Family : Type f} {Descriptor : Type d} {Move : Type m}
    {Direction : Type b}
    (Supported : Family → Move → Direction → Family → Prop)
    (ExactEdge : Descriptor → Move → Direction → Family →
      Descriptor → Prop)
    (ControlStep : Descriptor → Descriptor → Prop)
    (Live : Descriptor → Family → Prop)
    (Valid : Family → Move → Prop) :
    RelationalSupportedSuccessorCoverage Supported ExactEdge ControlStep Live
        Valid ↔
      ∃ table : RelationalSupportedSuccessorTable Family Descriptor Move
          Direction,
        RelationalSupportedSuccessorTableWorks Supported ExactEdge ControlStep
          Live Valid table := by
  constructor
  · intro coverage
    exact ⟨relationalSupportedSuccessor? Supported ExactEdge ControlStep,
      fun query hlive hvalid =>
        relationalSupportedSuccessor?_spec_of_coverage Supported ExactEdge
          ControlStep Live Valid coverage query hlive hvalid⟩
  · rintro ⟨table, htable⟩ query hlive hvalid
    obtain ⟨answer, _, hgood⟩ := htable query hlive hvalid
    exact ⟨answer, hgood⟩

/-- Exact fallback characterization. -/
theorem relationalSupportedSuccessor?_eq_none_iff
    {Family : Type f} {Descriptor : Type d} {Move : Type m}
    {Direction : Type b}
    (Supported : Family → Move → Direction → Family → Prop)
    (ExactEdge : Descriptor → Move → Direction → Family →
      Descriptor → Prop)
    (ControlStep : Descriptor → Descriptor → Prop)
    (query : RelationalSupportedSuccessorQuery Family Descriptor Move Direction) :
    relationalSupportedSuccessor? Supported ExactEdge ControlStep query = none ↔
      ¬ ∃ answer,
        RelationalSupportedSuccessorGood Supported ExactEdge ControlStep query
          answer := by
  classical
  simp [relationalSupportedSuccessor?]

/-- A blocked live and valid query refutes the proposed coverage law.  This is
the relational fail-fast witness. -/
theorem not_relationalSupportedSuccessorCoverage_of_blocked
    {Family : Type f} {Descriptor : Type d} {Move : Type m}
    {Direction : Type b}
    (Supported : Family → Move → Direction → Family → Prop)
    (ExactEdge : Descriptor → Move → Direction → Family →
      Descriptor → Prop)
    (ControlStep : Descriptor → Descriptor → Prop)
    (Live : Descriptor → Family → Prop)
    (Valid : Family → Move → Prop)
    (query : RelationalSupportedSuccessorQuery Family Descriptor Move Direction)
    (hlive : Live query.descriptor query.family)
    (hvalid : Valid query.family query.move)
    (hblocked : ∀ answer,
      ¬ RelationalSupportedSuccessorGood Supported ExactEdge ControlStep
        query answer) :
    ¬ RelationalSupportedSuccessorCoverage Supported ExactEdge ControlStep
      Live Valid := by
  intro coverage
  obtain ⟨answer, hgood⟩ := coverage query hlive hvalid
  exact hblocked answer hgood

/-- Unlike functional factorization, two distinct good answers do not create
an obstruction: the selector simply chooses one of them. -/
theorem relationalSupportedSuccessor?_survives_nonunique_answers
    {Family : Type f} {Descriptor : Type d} {Move : Type m}
    {Direction : Type b}
    (Supported : Family → Move → Direction → Family → Prop)
    (ExactEdge : Descriptor → Move → Direction → Family →
      Descriptor → Prop)
    (ControlStep : Descriptor → Descriptor → Prop)
    (query : RelationalSupportedSuccessorQuery Family Descriptor Move Direction)
    (left right : RelationalSupportedSuccessorAnswer Family Descriptor)
    (hleft : RelationalSupportedSuccessorGood Supported ExactEdge ControlStep
      query left)
    (_hright : RelationalSupportedSuccessorGood Supported ExactEdge ControlStep
      query right)
    (_hne : left ≠ right) :
    ∃ answer,
      relationalSupportedSuccessor? Supported ExactEdge ControlStep query =
          some answer ∧
        RelationalSupportedSuccessorGood Supported ExactEdge ControlStep query
          answer :=
  relationalSupportedSuccessor?_spec_of_exists Supported ExactEdge ControlStep
    query ⟨left, hleft⟩

/-! ## Hidden-descriptor coverage supplies the relational selector -/

section HiddenDescriptor

variable {Code : Type u} {MoveIdentity : Type v}
variable (D : DetParityAutomaton.{u, x} Code)
variable {FamilyMove : Type m} {Direction : Type b}
variable [Fintype Code] [Fintype MoveIdentity]

variable
  (Represented : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity) →
    HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) → Prop)
  (Live : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity) →
    HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) → Prop)
  (ExactEdge : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity) →
    FamilyMove → Direction →
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) →
    HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
  (Valid : HiddenDescriptorTwoFibreFamily D
      (MoveIdentity := MoveIdentity) → FamilyMove → Prop)
  (Supported : HiddenDescriptorTwoFibreFamily D
      (MoveIdentity := MoveIdentity) → FamilyMove → Direction →
    HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) → Prop)

/-- If every live valid query has at least one supported public child family,
`HiddenDescriptorFamilyTotality.covers` supplies the target and the control
step, hence the whole relational coverage law. -/
theorem HiddenDescriptorFamilyTotality.relationalSuccessorCoverage
    (totality : HiddenDescriptorFamilyTotality D Represented Live ExactEdge
      Valid Supported)
    (hsupported : ∀ current currentFamily move direction,
      Live current currentFamily →
      Valid currentFamily move →
      ∃ nextFamily, Supported currentFamily move direction nextFamily) :
    RelationalSupportedSuccessorCoverage Supported ExactEdge
      (fun current target =>
        target.control = D.step current.control target.code)
      Live Valid := by
  intro query hlive hvalid
  obtain ⟨nextFamily, hsupported⟩ :=
    hsupported query.descriptor query.family query.move query.direction hlive
      hvalid
  obtain ⟨target, hedge, hcontrol⟩ :=
    totality.covers query.descriptor query.family query.move query.direction
      nextFamily hlive hvalid hsupported
  exact ⟨(nextFamily, target), hsupported, hedge, hcontrol⟩

end HiddenDescriptor

/-! ## Any selected exact answer lifts to one literal semantic child -/

section FamilyAwareLift

variable {Code : Type u} {MoveIdentity : Type v}
variable (D : DetParityAutomaton.{u, x} Code)
variable {FamilyMove : Type m} {Direction : Type b} {Family : Type f}
variable {Semantic : Type y}
variable [Fintype Code] [Fintype MoveIdentity]

variable
  (semanticStep : Semantic → Direction → Semantic)
  (semanticDescriptor : Semantic → HiddenCodeControlDescriptor D
    (MoveIdentity := MoveIdentity))
  (familyOf : Semantic → Family)
  (ExactEdge : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity) →
    FamilyMove → Direction → Family →
      HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
  (Valid : Family → FamilyMove → Prop)

omit [Fintype Code] [Fintype MoveIdentity] in
/-- Once the current semantic state is aligned with the retained finite query,
every relationally selected exact answer is its literal semantic child.  No
functional child-family computation is assumed. -/
theorem FamilyAwareHiddenDescriptorEdgeLifter.relationalAnswer_lifts
    (Supported : Family → FamilyMove → Direction → Family → Prop)
    (ControlStep : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
    (lifter : FamilyAwareHiddenDescriptorEdgeLifter D semanticStep
      semanticDescriptor familyOf ExactEdge Valid)
    (state : Semantic)
    (query : RelationalSupportedSuccessorQuery Family
      (HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity))
      FamilyMove Direction)
    (answer : RelationalSupportedSuccessorAnswer Family
      (HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity)))
    (hfamily : query.family = familyOf state)
    (hdescriptor : query.descriptor = semanticDescriptor state)
    (hvalid : Valid query.family query.move)
    (hgood : RelationalSupportedSuccessorGood Supported ExactEdge ControlStep
      query answer) :
    semanticDescriptor (semanticStep state query.direction) = answer.2 ∧
      familyOf (semanticStep state query.direction) = answer.1 := by
  apply FamilyAwareHiddenDescriptorEdgeLifter.lifts lifter state query.move
    query.direction answer.1 answer.2
  · simpa only [hfamily] using hvalid
  · simpa only [hdescriptor] using hgood.2.1

end FamilyAwareLift

end DistributedSynthesis
