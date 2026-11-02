/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenHiddenDescriptorFamilyAlphabet

/-!
# The exact successor-family factorization seam

A finite state can compute an exact semantic child family precisely when the
semantic child-family map is constant on every fibre of the finite data that
the state retains.  The first part of this file records that elementary but
useful equivalence and its collision refutation principle.

The second part defines the smallest *candidate* enrichment needed at the
root-pinned hidden-descriptor seam.  For each side it retains the selected
union controller's finite rational control and the corresponding pinned union
monitor state.  Both sides are present uniformly, including when a descriptor
carrier is empty.  In particular, the type contains no leader, orientation,
or lane bit.

Nothing here claims that this enrichment determines the next semantic family.
That claim is exactly the fibre-constancy obligation above and must be proved
from the model, not inferred from finiteness or from a one-bit argument.
-/

namespace DistributedSynthesis

universe a b c d i u v x y s

/-! ## Generic factorization criterion -/

/-- The semantic child family is constant whenever the currently retained
family and move agree.  The tag is the finite block/direction query supplied
to both semantic states. -/
def SemanticChildFamilyFibreConstant
    {Semantic : Type a} {Family : Type b} {Move : Type c} {Tag : Type d}
    (semanticStep : Semantic → Tag → Semantic)
    (familyOf : Semantic → Family) (moveOf : Semantic → Move) : Prop :=
  ∀ left right tag,
    familyOf left = familyOf right →
    moveOf left = moveOf right →
    familyOf (semanticStep left tag) =
      familyOf (semanticStep right tag)

/-- There is an exact finite-data transition computing the next semantic
family from the current family, current move, and tag. -/
def SemanticChildFamilyFactorizes
    {Semantic : Type a} {Family : Type b} {Move : Type c} {Tag : Type d}
    (semanticStep : Semantic → Tag → Semantic)
    (familyOf : Semantic → Family) (moveOf : Semantic → Move) : Prop :=
  ∃ nextFamily : Family → Move → Tag → Family,
    ∀ state tag,
      nextFamily (familyOf state) (moveOf state) tag =
        familyOf (semanticStep state tag)

/-- Exact successor-family computation is equivalent to constancy on the
fibres of the retained current family and move.  The fallback on an
unrepresented `(family, move)` pair is the supplied family itself, so no
inhabitedness assumption is hidden in this equivalence. -/
theorem semanticChildFamilyFibreConstant_iff_factorizes
    {Semantic : Type a} {Family : Type b} {Move : Type c} {Tag : Type d}
    (semanticStep : Semantic → Tag → Semantic)
    (familyOf : Semantic → Family) (moveOf : Semantic → Move) :
    SemanticChildFamilyFibreConstant semanticStep familyOf moveOf ↔
      SemanticChildFamilyFactorizes semanticStep familyOf moveOf := by
  constructor
  · intro hconstant
    classical
    let nextFamily : Family → Move → Tag → Family :=
      fun family move tag =>
        if h : ∃ state, familyOf state = family ∧ moveOf state = move then
          familyOf (semanticStep (Classical.choose h) tag)
        else
          family
    refine ⟨nextFamily, ?_⟩
    intro state tag
    simp only [nextFamily]
    split
    next hrepresented =>
      exact hconstant (Classical.choose hrepresented) state tag
        (Classical.choose_spec hrepresented).1
        (Classical.choose_spec hrepresented).2
    next hunrepresented =>
      exact (hunrepresented ⟨state, rfl, rfl⟩).elim
  · rintro ⟨nextFamily, hnext⟩ left right tag hfamily hmove
    calc
      familyOf (semanticStep left tag) =
          nextFamily (familyOf left) (moveOf left) tag :=
        (hnext left tag).symm
      _ = nextFamily (familyOf right) (moveOf right) tag := by
        rw [hfamily, hmove]
      _ = familyOf (semanticStep right tag) := hnext right tag

/-- Finite-alphabet spelling of the generic equivalence.  Finiteness is what
makes the factor map usable as a finite transition table; it is not needed to
prove the underlying logical equivalence. -/
theorem finiteSemanticChildFamilyFibreConstant_iff_factorizes
    {Semantic : Type a} {Family : Type b} {Move : Type c} {Tag : Type d}
    [Fintype Family] [Fintype Move] [Fintype Tag]
    (semanticStep : Semantic → Tag → Semantic)
    (familyOf : Semantic → Family) (moveOf : Semantic → Move) :
    SemanticChildFamilyFibreConstant semanticStep familyOf moveOf ↔
      SemanticChildFamilyFactorizes semanticStep familyOf moveOf :=
  semanticChildFamilyFibreConstant_iff_factorizes semanticStep familyOf moveOf

/-- A single same-fibre pair with different child families refutes every
purported exact successor-family transition on the retained finite data. -/
theorem not_semanticChildFamilyFactorizes_of_collision
    {Semantic : Type a} {Family : Type b} {Move : Type c} {Tag : Type d}
    (semanticStep : Semantic → Tag → Semantic)
    (familyOf : Semantic → Family) (moveOf : Semantic → Move)
    (left right : Semantic) (tag : Tag)
    (hfamily : familyOf left = familyOf right)
    (hmove : moveOf left = moveOf right)
    (hchild : familyOf (semanticStep left tag) ≠
      familyOf (semanticStep right tag)) :
    ¬ SemanticChildFamilyFactorizes semanticStep familyOf moveOf := by
  intro hfactor
  have hconstant :
      SemanticChildFamilyFibreConstant semanticStep familyOf moveOf :=
    (semanticChildFamilyFibreConstant_iff_factorizes
      semanticStep familyOf moveOf).mpr hfactor
  exact hchild (hconstant left right tag hfamily hmove)

namespace DetParityAutomaton

variable {I : Type i}
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Fintype I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-! ## Uniform root-pinned block queries -/

/-- The finite monitor for the entire right descriptor/root union after every
member monitor has been pinned to its expected root record. -/
noncomputable abbrev ProfiledOpenHiddenDescriptorRightPinnedUnionMonitor
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A
      (I := I) initialCode)
    (expected : ProfiledOpenHiddenDescriptorRightExpected A family) :=
  finiteRootFamilyMonitor
    (descriptorRootUnionMonitor
      (fun descriptor : ProfiledOpenHiddenDescriptorRightCarrier A family =>
        ProfiledOpenHiddenDescriptorRightRoot A (I := I) descriptor.1)
      (descriptorRootPinnedMonitor
        (fun descriptor : ProfiledOpenHiddenDescriptorRightCarrier A family =>
          ProfiledOpenHiddenDescriptorRightRoot A (I := I) descriptor.1)
        (fun descriptor root =>
          profiledOpenHiddenDescriptorRightMonitor A descriptor.1 root)
        expected))

/-- Left mirror of the pinned union monitor. -/
noncomputable abbrev ProfiledOpenHiddenDescriptorLeftPinnedUnionMonitor
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A
      (I := I) initialCode)
    (expected : ProfiledOpenHiddenDescriptorLeftExpected A family) :=
  finiteRootFamilyMonitor
    (descriptorRootUnionMonitor
      (fun descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A family =>
        ProfiledOpenHiddenDescriptorLeftRoot A (I := I) descriptor.1)
      (descriptorRootPinnedMonitor
        (fun descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A family =>
          ProfiledOpenHiddenDescriptorLeftRoot A (I := I) descriptor.1)
        (fun descriptor root =>
          profiledOpenHiddenDescriptorLeftMonitor A descriptor.1 root)
        expected))

/-- One right block query: the selected union table's rational control and
the state of its pinned union monitor. -/
noncomputable abbrev ProfiledOpenHiddenDescriptorRightPinnedBlockQuery
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A
      (I := I) initialCode)
    (expected : ProfiledOpenHiddenDescriptorRightExpected A family)
    (move : ProfiledOpenHiddenDescriptorRightPinnedFamilyMove A family
      expected) :=
  move.1.toTransitionRationalTree.Control ×
    (ProfiledOpenHiddenDescriptorRightPinnedUnionMonitor A family
      expected).State

/-- Left block query. -/
noncomputable abbrev ProfiledOpenHiddenDescriptorLeftPinnedBlockQuery
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A
      (I := I) initialCode)
    (expected : ProfiledOpenHiddenDescriptorLeftExpected A family)
    (move : ProfiledOpenHiddenDescriptorLeftPinnedFamilyMove A family
      expected) :=
  move.1.toTransitionRationalTree.Control ×
    (ProfiledOpenHiddenDescriptorLeftPinnedUnionMonitor A family
      expected).State

/-- Both block queries over one selected pinned family move.  The product is
uniform: an empty right or left descriptor carrier still contributes the
finite control/state type of its empty union monitor. -/
noncomputable abbrev ProfiledOpenHiddenDescriptorPairedPinnedBlockQueryAt
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A
      (I := I) initialCode)
    (move : ProfiledOpenHiddenDescriptorPairedPinnedFamilyMoveAt A family) :=
  ProfiledOpenHiddenDescriptorRightPinnedBlockQuery A family move.1
      move.2.2.1 ×
    ProfiledOpenHiddenDescriptorLeftPinnedBlockQuery A family move.2.1
      move.2.2.2

/-- Dependent paired block-query type for a fully selected family move. -/
noncomputable abbrev ProfiledOpenHiddenDescriptorPairedPinnedBlockQuery
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (move : ProfiledOpenHiddenDescriptorPairedPinnedFamilyMove A
      initialCode) :=
  ProfiledOpenHiddenDescriptorPairedPinnedBlockQueryAt A move.1 move.2

/-- A fixed finite direction alphabet retaining the old finite direction tag
and, symmetrically, both new pinned-union block queries.  The family move is
stored first because the query type depends on it. -/
noncomputable abbrev ProfiledOpenHiddenDescriptorPairedPinnedBlockQueryTag
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)) :=
  Σ move : ProfiledOpenHiddenDescriptorPairedPinnedFamilyMove A initialCode,
    ProfiledOpenHiddenDescriptorPairedPinnedBlockQuery A move ×
      ProfiledOpenIndexedFiniteDirectionTag A (I := I)

set_option synthInstance.maxHeartbeats 800000 in
noncomputable instance
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A
      (I := I) initialCode)
    (move : ProfiledOpenHiddenDescriptorPairedPinnedFamilyMoveAt A family) :
    Fintype
      (ProfiledOpenHiddenDescriptorPairedPinnedBlockQueryAt A family move) := by
  classical
  infer_instance

set_option synthInstance.maxHeartbeats 800000 in
noncomputable instance
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    (move : ProfiledOpenHiddenDescriptorPairedPinnedFamilyMove A initialCode) :
    Fintype (ProfiledOpenHiddenDescriptorPairedPinnedBlockQuery A move) := by
  classical
  infer_instance

set_option synthInstance.maxHeartbeats 1600000 in
noncomputable instance
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)) :
    Fintype
      (ProfiledOpenHiddenDescriptorPairedPinnedBlockQueryTag A initialCode) := by
  classical
  infer_instance

end

end DetParityAutomaton

end DistributedSynthesis
