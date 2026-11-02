/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemSemanticChildFamilyFactorization
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenOptionalControlledFamily

/-!
# The concrete optional-state block-query factorization seam

This file specializes `SemanticChildFamilyFibreConstant` to the total
optional controlled semantics and the symmetric pinned block-query alphabet.
The semantic successor consumes the old finite direction component of the
query.  The two pinned-union control components are retained in the tag, but
they are not silently assumed to describe the current exact histories.

The existing indexed direction-summary construction already proves an exact
and useful part of the desired result: once the *current full hidden
descriptor* is fixed, the finite direction component determines the child
public code and literal parity control.  We prove that bridge below.

What remains is deliberately stated at its semantic granularity.  Two child
states must have the same lane shape and, on every active side, lie in the
same exact local-view fibre.  This `ChildFibreAlignment` is sufficient for
equality of their public child families.  Proving that equal coherent pinned
block queries imply this alignment is the later full-view recovery theorem;
it is not a consequence of finiteness, of a bounded hidden bit, or of knowing
which side is the strict leader.
-/

namespace DistributedSynthesis

universe i u v x y s

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

variable (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
variable (hwin : ∀ env : EnvironmentSequence In₁ In₂,
  A.Accepts (execution strategy env))
variable (basis : ∀ state : PairedProfiledTreeState A,
  (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
variable (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))

/-! ## Concrete specialization of the generic factorization criterion -/

/-- The total optional semantic step driven by the old finite-direction
component of a symmetric pinned block query.  The other query components are
not discarded from the alphabet; their required coherence with the exact
history is a separate predicate below. -/
noncomputable def profiledOpenOptionalControlledBlockQuerySemanticNext
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode)
    (tag : ProfiledOpenHiddenDescriptorPairedPinnedBlockQueryTag.{i, u, v, x,
      y, s, 0, 0, 0, 0} A (I := I) initialCode) :
    ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin basis
      initialCode :=
  profiledOpenIndexedOptionalControlledSemanticNext A strategy hwin basis
    initialCode point tag.2.2

/-- The exact child-family constancy statement for the concrete finite data:
current public family, selected fixed pinned move, and symmetric block query. -/
def ProfiledOpenOptionalControlledBlockQueryFibreConstant : Prop :=
  SemanticChildFamilyFibreConstant
    (profiledOpenOptionalControlledBlockQuerySemanticNext A strategy hwin
      basis initialCode)
    (profiledOpenOptionalControlledFamilyOf A strategy hwin basis initialCode)
    (profiledOpenOptionalControlledMoveOf A strategy hwin basis initialCode)

/-- Existence of the corresponding finite exact child-family transition. -/
def ProfiledOpenOptionalControlledBlockQueryFactorizes : Prop :=
  SemanticChildFamilyFactorizes
    (profiledOpenOptionalControlledBlockQuerySemanticNext A strategy hwin
      basis initialCode)
    (profiledOpenOptionalControlledFamilyOf A strategy hwin basis initialCode)
    (profiledOpenOptionalControlledMoveOf A strategy hwin basis initialCode)

/-- The concrete finite transition exists exactly when the child family is
constant on the concrete fibres. -/
theorem profiledOpenOptionalControlledBlockQueryFibreConstant_iff_factorizes :
    ProfiledOpenOptionalControlledBlockQueryFibreConstant A strategy hwin
        basis initialCode ↔
      ProfiledOpenOptionalControlledBlockQueryFactorizes A strategy hwin basis
        initialCode :=
  semanticChildFamilyFibreConstant_iff_factorizes
    (profiledOpenOptionalControlledBlockQuerySemanticNext A strategy hwin
      basis initialCode)
    (profiledOpenOptionalControlledFamilyOf A strategy hwin basis initialCode)
    (profiledOpenOptionalControlledMoveOf A strategy hwin basis initialCode)

/-- A same-public-fibre collision with distinct child families is the exact
finite counterexample to the concrete factorization. -/
theorem not_profiledOpenOptionalControlledBlockQueryFactorizes_of_collision
    (left right : ProfiledOpenIndexedOptionalControlledSemanticState A
      strategy hwin basis initialCode)
    (tag : ProfiledOpenHiddenDescriptorPairedPinnedBlockQueryTag.{i, u, v, x,
      y, s, 0, 0, 0, 0} A (I := I) initialCode)
    (hfamily :
      profiledOpenOptionalControlledFamilyOf A strategy hwin basis initialCode
          left =
        profiledOpenOptionalControlledFamilyOf A strategy hwin basis
          initialCode right)
    (hmove :
      profiledOpenOptionalControlledMoveOf A strategy hwin basis initialCode
          left =
        profiledOpenOptionalControlledMoveOf A strategy hwin basis initialCode
          right)
    (hchild :
      profiledOpenOptionalControlledFamilyOf A strategy hwin basis initialCode
          (profiledOpenOptionalControlledBlockQuerySemanticNext A strategy hwin
            basis initialCode left tag) ≠
        profiledOpenOptionalControlledFamilyOf A strategy hwin basis initialCode
          (profiledOpenOptionalControlledBlockQuerySemanticNext A strategy hwin
            basis initialCode right tag)) :
    ¬ ProfiledOpenOptionalControlledBlockQueryFactorizes A strategy hwin basis
        initialCode :=
  not_semanticChildFamilyFactorizes_of_collision
    (profiledOpenOptionalControlledBlockQuerySemanticNext A strategy hwin
      basis initialCode)
    (profiledOpenOptionalControlledFamilyOf A strategy hwin basis initialCode)
    (profiledOpenOptionalControlledMoveOf A strategy hwin basis initialCode)
    left right tag hfamily hmove hchild

/-! ## What the old direction summary already determines exactly -/

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- The child public code is computed by the established finite-tag
successor.  Thus the unbounded tagged prefixes have already disappeared at
this layer. -/
theorem profiledOpenOptionalControlledBlockQuerySemanticNext_code
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode)
    (tag : ProfiledOpenHiddenDescriptorPairedPinnedBlockQueryTag.{i, u, v, x,
      y, s, 0, 0, 0, 0} A (I := I) initialCode) :
    (profiledOpenOptionalControlledBlockQuerySemanticNext A strategy hwin basis
        initialCode point tag).1.state.code A strategy hwin basis =
      profiledOpenIndexedBiBeliefNextFiniteTag A
        (point.1.state.code A strategy hwin basis)
        (point.1.state.move A strategy hwin basis) tag.2.2 := by
  exact profiledOpenIndexedCorrelatedSemanticNext_code A strategy hwin basis
    point.1.state
    (profiledOpenIndexedRawDirectionOfFiniteTag A
      (point.1.state.code A strategy hwin basis)
      (point.1.state.move A strategy hwin basis) tag.2.2)

/-- Equal current full hidden descriptors force equal child public codes for
the same symmetric query.  Only the old finite-direction component is needed
for this conclusion. -/
theorem
    profiledOpenOptionalControlledBlockQuerySemanticNext_code_eq_of_descriptor_eq
    (left right : ProfiledOpenIndexedOptionalControlledSemanticState A
      strategy hwin basis initialCode)
    (tag : ProfiledOpenHiddenDescriptorPairedPinnedBlockQueryTag.{i, u, v, x,
      y, s, 0, 0, 0, 0} A (I := I) initialCode)
    (hdescriptor :
      profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
          basis initialCode left =
        profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
          basis initialCode right) :
    (profiledOpenOptionalControlledBlockQuerySemanticNext A strategy hwin basis
        initialCode left tag).1.state.code A strategy hwin basis =
      (profiledOpenOptionalControlledBlockQuerySemanticNext A strategy hwin
        basis initialCode right tag).1.state.code A strategy hwin basis := by
  have hcode := congrArg
    (fun descriptor : ProfiledOpenIndexedOldMoveHiddenDescriptor A
      (I := I) initialCode ↦ descriptor.code) hdescriptor
  have hmove := congrArg
    (fun descriptor : ProfiledOpenIndexedOldMoveHiddenDescriptor A
      (I := I) initialCode ↦ descriptor.moveIdentity) hdescriptor
  rw [profiledOpenOptionalControlledBlockQuerySemanticNext_code A strategy hwin
      basis initialCode left tag,
    profiledOpenOptionalControlledBlockQuerySemanticNext_code A strategy hwin
      basis initialCode right tag]
  have hcode' : left.1.state.code A strategy hwin basis =
      right.1.state.code A strategy hwin basis := by
    simpa using hcode
  have hmove' : left.1.state.move A strategy hwin basis =
      right.1.state.move A strategy hwin basis := by
    simpa using hmove
  rw [hcode', hmove']

/-- Equal current hidden descriptors also force equal literal parity controls
after the query, because both controls are updated on the equal child code. -/
theorem
    profiledOpenOptionalControlledBlockQuerySemanticNext_control_eq_of_descriptor_eq
    (left right : ProfiledOpenIndexedOptionalControlledSemanticState A
      strategy hwin basis initialCode)
    (tag : ProfiledOpenHiddenDescriptorPairedPinnedBlockQueryTag.{i, u, v, x,
      y, s, 0, 0, 0, 0} A (I := I) initialCode)
    (hdescriptor :
      profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
          basis initialCode left =
        profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
          basis initialCode right) :
    (profiledOpenOptionalControlledBlockQuerySemanticNext A strategy hwin basis
        initialCode left tag).2 =
      (profiledOpenOptionalControlledBlockQuerySemanticNext A strategy hwin
        basis initialCode right tag).2 := by
  have hcontrol := congrArg
    (fun descriptor : ProfiledOpenIndexedOldMoveHiddenDescriptor A
      (I := I) initialCode ↦ descriptor.control) hdescriptor
  have hcode :=
    profiledOpenOptionalControlledBlockQuerySemanticNext_code_eq_of_descriptor_eq
      A strategy hwin basis initialCode left right tag hdescriptor
  change
    (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).step left.2
        ((profiledOpenOptionalControlledBlockQuerySemanticNext A strategy hwin
          basis initialCode left tag).1.state.code A strategy hwin basis) =
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).step right.2
        ((profiledOpenOptionalControlledBlockQuerySemanticNext A strategy hwin
          basis initialCode right tag).1.state.code A strategy hwin basis)
  exact congrArg₂
    (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).step
    (by simpa using hcontrol) hcode

end

/-! ## The exact local-fibre residual -/

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] in
/-- The right-only exact-view relation has agreeing fibres. -/
theorem profiledOpenIndexedRightOnlyLocalFibreRel_fibresAgree :
    RelationFibresAgree
      (ProfiledOpenIndexedRightOnlyLocalFibreRel A strategy hwin basis
        (I := I)) := by
  apply relationFibresAgree_of_symmetric_transitive
  · intro left right hrel
    exact hrel.symm
  · exact ⟨fun _ _ _ hleft hright => hleft.trans hright⟩

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] in
/-- Left-only mirror. -/
theorem profiledOpenIndexedLeftOnlyLocalFibreRel_fibresAgree :
    RelationFibresAgree
      (ProfiledOpenIndexedLeftOnlyLocalFibreRel A strategy hwin basis
        (I := I)) := by
  apply relationFibresAgree_of_symmetric_transitive
  · intro left right hrel
    exact hrel.symm
  · exact ⟨fun _ _ _ hleft hright => hleft.trans hright⟩

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- Related right-only sources expose the same fixed public family. -/
theorem profiledOpenOptionalRightOnlyFamilyCode_eq_of_rel
    (control : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
        (I := I) →
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)
    (left right : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy
      hwin basis (I := I))
    (hrel : ProfiledOpenIndexedRightOnlyLocalFibreRel A strategy hwin basis
      left right) :
    profiledOpenOptionalRightOnlyFamilyCode A strategy hwin basis initialCode
        control left =
      profiledOpenOptionalRightOnlyFamilyCode A strategy hwin basis initialCode
        control right := by
  classical
  letI : DecidableEq
      (ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode) :=
    Classical.decEq _
  apply Prod.ext
  · exact semanticFibreImage_eq_of_rel
      (profiledOpenRightOnlyDescriptor A strategy hwin basis
        (profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
          initialCode control))
      (ProfiledOpenIndexedRightOnlyLocalFibreRel A strategy hwin basis)
      (profiledOpenIndexedRightOnlyLocalFibreRel_fibresAgree A strategy hwin
        basis) hrel
  · rfl

/-- Related left-only sources expose the same fixed public family. -/
theorem profiledOpenOptionalLeftOnlyFamilyCode_eq_of_rel
    (control : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
        (I := I) →
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)
    (left right : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy
      hwin basis (I := I))
    (hrel : ProfiledOpenIndexedLeftOnlyLocalFibreRel A strategy hwin basis
      left right) :
    profiledOpenOptionalLeftOnlyFamilyCode A strategy hwin basis initialCode
        control left =
      profiledOpenOptionalLeftOnlyFamilyCode A strategy hwin basis initialCode
        control right := by
  classical
  letI : DecidableEq
      (ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode) :=
    Classical.decEq _
  apply Prod.ext
  · rfl
  · exact semanticFibreImage_eq_of_rel
      (profiledOpenLeftOnlyDescriptor A strategy hwin basis
        (profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
          initialCode control))
      (ProfiledOpenIndexedLeftOnlyLocalFibreRel A strategy hwin basis)
      (profiledOpenIndexedLeftOnlyLocalFibreRel_fibresAgree A strategy hwin
        basis) hrel

/-- A pair of exact local-view equalities determines the two-live fixed
public family. -/
theorem profiledOpenFixedPinnedFamilyCode_eq_of_localFibres
    (control : ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin basis
        (I := I) →
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)
    (left right : ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin
      basis (I := I))
    (hone : ProfiledOpenIndexedProcessOneLocalFibreRel A strategy hwin basis
      left right)
    (htwo : ProfiledOpenIndexedProcessTwoLocalFibreRel A strategy hwin basis
      left right) :
    profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode control
        left =
      profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode control
        right := by
  classical
  letI : DecidableEq
      (ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode) :=
    Classical.decEq _
  apply Prod.ext
  · exact semanticFibreImage_eq_of_rel
      (profiledOpenFixedPinnedSemanticDescriptor A strategy hwin basis
        initialCode control)
      (ProfiledOpenIndexedProcessOneLocalFibreRel A strategy hwin basis)
      (profiledOpenIndexedProcessOneLocalFibreRel_fibresAgree A strategy hwin
        basis) hone
  · exact semanticFibreImage_eq_of_rel
      (profiledOpenFixedPinnedSemanticDescriptor A strategy hwin basis
        initialCode control)
      (ProfiledOpenIndexedProcessTwoLocalFibreRel A strategy hwin basis)
      (profiledOpenIndexedProcessTwoLocalFibreRel_fibresAgree A strategy hwin
        basis) htwo

end

/-- Four-way proof-side alignment of two optional controlled states.  Active
sides must agree in their exact local-view relation.  No constructor is a
runtime lane or leader signal. -/
inductive ProfiledOpenOptionalControlledChildFibreAlignment
    (left right : ProfiledOpenIndexedOptionalControlledSemanticState A
      strategy hwin basis initialCode) : Prop
  | inactive
      (leftRight : left.1.state.right = none)
      (leftLeft : left.1.state.left = none)
      (rightRight : right.1.state.right = none)
      (rightLeft : right.1.state.left = none)
      (leftShape : left.1.state.laneShape A strategy hwin basis =
        .inactive leftRight leftLeft)
      (rightShape : right.1.state.laneShape A strategy hwin basis =
        .inactive rightRight rightLeft)
  | rightOnly
      (leftLane : ProfiledOpenIndexedRightSemanticLane A strategy hwin basis
        (I := I))
      (rightLane : ProfiledOpenIndexedRightSemanticLane A strategy hwin basis
        (I := I))
      (leftRight : left.1.state.right = some leftLane)
      (leftLeft : left.1.state.left = none)
      (rightRight : right.1.state.right = some rightLane)
      (rightLeft : right.1.state.left = none)
      (leftShape : left.1.state.laneShape A strategy hwin basis =
        .rightOnly leftLane leftRight leftLeft)
      (rightShape : right.1.state.laneShape A strategy hwin basis =
        .rightOnly rightLane rightRight rightLeft)
      (rel : ProfiledOpenIndexedRightOnlyLocalFibreRel A strategy hwin basis
        (left.1.toRightOnly A strategy hwin basis leftLane leftRight leftLeft)
        (right.1.toRightOnly A strategy hwin basis rightLane rightRight
          rightLeft))
  | leftOnly
      (leftLane : ProfiledOpenIndexedLeftSemanticLane A strategy hwin basis
        (I := I))
      (rightLane : ProfiledOpenIndexedLeftSemanticLane A strategy hwin basis
        (I := I))
      (leftRight : left.1.state.right = none)
      (leftLeft : left.1.state.left = some leftLane)
      (rightRight : right.1.state.right = none)
      (rightLeft : right.1.state.left = some rightLane)
      (leftShape : left.1.state.laneShape A strategy hwin basis =
        .leftOnly leftLane leftRight leftLeft)
      (rightShape : right.1.state.laneShape A strategy hwin basis =
        .leftOnly rightLane rightRight rightLeft)
      (rel : ProfiledOpenIndexedLeftOnlyLocalFibreRel A strategy hwin basis
        (left.1.toLeftOnly A strategy hwin basis leftLane leftRight leftLeft)
        (right.1.toLeftOnly A strategy hwin basis rightLane rightRight
          rightLeft))
  | both
      (leftRightLane : ProfiledOpenIndexedRightSemanticLane A strategy hwin
        basis (I := I))
      (leftLeftLane : ProfiledOpenIndexedLeftSemanticLane A strategy hwin
        basis (I := I))
      (rightRightLane : ProfiledOpenIndexedRightSemanticLane A strategy hwin
        basis (I := I))
      (rightLeftLane : ProfiledOpenIndexedLeftSemanticLane A strategy hwin
        basis (I := I))
      (leftRight : left.1.state.right = some leftRightLane)
      (leftLeft : left.1.state.left = some leftLeftLane)
      (rightRight : right.1.state.right = some rightRightLane)
      (rightLeft : right.1.state.left = some rightLeftLane)
      (leftShape : left.1.state.laneShape A strategy hwin basis =
        .both leftRightLane leftLeftLane leftRight leftLeft)
      (rightShape : right.1.state.laneShape A strategy hwin basis =
        .both rightRightLane rightLeftLane rightRight rightLeft)
      (relOne : ProfiledOpenIndexedProcessOneLocalFibreRel A strategy hwin
        basis
        (left.1.toLiveFresh A strategy hwin basis leftRightLane leftLeftLane
          leftRight leftLeft)
        (right.1.toLiveFresh A strategy hwin basis rightRightLane rightLeftLane
          rightRight rightLeft))
      (relTwo : ProfiledOpenIndexedProcessTwoLocalFibreRel A strategy hwin
        basis
        (left.1.toLiveFresh A strategy hwin basis leftRightLane leftLeftLane
          leftRight leftLeft)
        (right.1.toLiveFresh A strategy hwin basis rightRightLane rightLeftLane
          rightRight rightLeft))

/-! `ProfiledOpenOptionalControlledChildFibreAlignment` is intentionally left
as the semantic recovery target, not turned into a theorem about the chosen
`familyOf` here.  Doing so requires proving that the pinned query is coherent
with the particular source-bank constructor selected at each child.  The
three equality lemmas above show that, once that constructor and its exact
local fibre are recovered, equality of the corresponding public finite image
is routine. -/

/-! ## Pointed relational successor tables

Child-family functionality is stronger than the construction needs.  The
sender may instead carry a finite table with one row for every possible
current hidden descriptor.  The public family and pinned query select the
table; at the joint receive, the actual (proof-side) descriptor selects its
row.  Thus different live descriptors may choose different child families.

This does not make the descriptor observable and does not introduce a lane,
orientation, or strict-leader signal.  It only packages finitely many
conditional answers in one finite message. -/

abbrev ProfiledOpenOptionalControlledPinnedFamily :=
  ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I) initialCode

abbrev ProfiledOpenOptionalControlledPinnedDescriptor :=
  ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode

abbrev ProfiledOpenOptionalControlledPinnedMove :=
  ProfiledOpenHiddenDescriptorPairedPinnedFamilyMove.{i, u, v, x, y, s, 0, 0}
    A (I := I) initialCode

abbrev ProfiledOpenOptionalControlledPinnedTag :=
  ProfiledOpenHiddenDescriptorPairedPinnedBlockQueryTag.{i, u, v, x, y, s,
    0, 0, 0, 0} A (I := I) initialCode

/-- A relational query is pointed at the current descriptor.  The move is
already the first coordinate of the symmetric pinned tag, so it is not stored
twice. -/
structure ProfiledOpenOptionalControlledPinnedPointedQuery where
  family : ProfiledOpenOptionalControlledPinnedFamily A initialCode
  descriptor : ProfiledOpenOptionalControlledPinnedDescriptor A initialCode
  tag : ProfiledOpenOptionalControlledPinnedTag A initialCode
  deriving Fintype

/-- The selected public child family and exact target descriptor. -/
abbrev ProfiledOpenOptionalControlledPinnedPointedAnswer :=
  ProfiledOpenOptionalControlledPinnedFamily A initialCode ×
    ProfiledOpenOptionalControlledPinnedDescriptor A initialCode

/-- Literal parity-control step at the pointed descriptor. -/
def profiledOpenOptionalControlledPinnedControlStep
    (current target : ProfiledOpenOptionalControlledPinnedDescriptor A
      initialCode) : Prop :=
  target.control =
    (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).step
      current.control target.code

/-- One acceptable pointed answer.  Crucially, `Supported` sees the current
descriptor: it is not required to pick one child family uniformly for every
descriptor represented by the same public family. -/
def ProfiledOpenOptionalControlledPinnedPointedGood
    (Supported :
      ProfiledOpenOptionalControlledPinnedDescriptor A initialCode →
      ProfiledOpenOptionalControlledPinnedFamily A initialCode →
      ProfiledOpenOptionalControlledPinnedMove A initialCode →
      ProfiledOpenOptionalControlledPinnedTag A initialCode →
      ProfiledOpenOptionalControlledPinnedFamily A initialCode → Prop)
    (ExactEdge :
      ProfiledOpenOptionalControlledPinnedDescriptor A initialCode →
      ProfiledOpenOptionalControlledPinnedMove A initialCode →
      ProfiledOpenOptionalControlledPinnedTag A initialCode →
      ProfiledOpenOptionalControlledPinnedFamily A initialCode →
      ProfiledOpenOptionalControlledPinnedDescriptor A initialCode → Prop)
    (query : ProfiledOpenOptionalControlledPinnedPointedQuery A initialCode)
    (answer : ProfiledOpenOptionalControlledPinnedPointedAnswer A
      initialCode) : Prop :=
  Supported query.descriptor query.family query.tag.1 query.tag answer.1 ∧
    ExactEdge query.descriptor query.tag.1 query.tag answer.1 answer.2 ∧
      profiledOpenOptionalControlledPinnedControlStep A initialCode
        query.descriptor answer.2

/-- Every live, valid pointed query has at least one exact supported answer.
This is the positive relational obligation. -/
def ProfiledOpenOptionalControlledPinnedPointedCoverage
    (Supported :
      ProfiledOpenOptionalControlledPinnedDescriptor A initialCode →
      ProfiledOpenOptionalControlledPinnedFamily A initialCode →
      ProfiledOpenOptionalControlledPinnedMove A initialCode →
      ProfiledOpenOptionalControlledPinnedTag A initialCode →
      ProfiledOpenOptionalControlledPinnedFamily A initialCode → Prop)
    (ExactEdge :
      ProfiledOpenOptionalControlledPinnedDescriptor A initialCode →
      ProfiledOpenOptionalControlledPinnedMove A initialCode →
      ProfiledOpenOptionalControlledPinnedTag A initialCode →
      ProfiledOpenOptionalControlledPinnedFamily A initialCode →
      ProfiledOpenOptionalControlledPinnedDescriptor A initialCode → Prop)
    (Live : ProfiledOpenOptionalControlledPinnedDescriptor A initialCode →
      ProfiledOpenOptionalControlledPinnedFamily A initialCode → Prop)
    (Valid : ProfiledOpenOptionalControlledPinnedFamily A initialCode →
      ProfiledOpenOptionalControlledPinnedMove A initialCode → Prop) : Prop :=
  ∀ query,
    Live query.descriptor query.family →
    Valid query.family query.tag.1 →
    ∃ answer,
      ProfiledOpenOptionalControlledPinnedPointedGood A initialCode Supported
        ExactEdge query answer

/-- The finite payload sent for a fixed public family and pinned query: one
optional answer for every possible hidden descriptor. -/
abbrev ProfiledOpenOptionalControlledPinnedDescriptorTable :=
  ProfiledOpenOptionalControlledPinnedDescriptor A initialCode →
    Option
      (ProfiledOpenOptionalControlledPinnedPointedAnswer A initialCode)

noncomputable instance
    profiledOpenOptionalControlledPinnedDescriptorTable_fintype :
    Fintype
      (ProfiledOpenOptionalControlledPinnedDescriptorTable A initialCode) := by
  classical
  infer_instance

/-- The entire finite controller table, whose `(family, tag)` slice is the
descriptor-indexed payload used at that query. -/
abbrev ProfiledOpenOptionalControlledPinnedPointedTables :=
  ProfiledOpenOptionalControlledPinnedFamily A initialCode →
    ProfiledOpenOptionalControlledPinnedTag A initialCode →
      ProfiledOpenOptionalControlledPinnedDescriptorTable A initialCode

noncomputable instance
    profiledOpenOptionalControlledPinnedPointedTables_fintype :
    Fintype
      (ProfiledOpenOptionalControlledPinnedPointedTables A initialCode) := by
  classical
  infer_instance

/-- A descriptor-table slice is correct on every live row. -/
def ProfiledOpenOptionalControlledPinnedDescriptorTableWorks
    (Supported :
      ProfiledOpenOptionalControlledPinnedDescriptor A initialCode →
      ProfiledOpenOptionalControlledPinnedFamily A initialCode →
      ProfiledOpenOptionalControlledPinnedMove A initialCode →
      ProfiledOpenOptionalControlledPinnedTag A initialCode →
      ProfiledOpenOptionalControlledPinnedFamily A initialCode → Prop)
    (ExactEdge :
      ProfiledOpenOptionalControlledPinnedDescriptor A initialCode →
      ProfiledOpenOptionalControlledPinnedMove A initialCode →
      ProfiledOpenOptionalControlledPinnedTag A initialCode →
      ProfiledOpenOptionalControlledPinnedFamily A initialCode →
      ProfiledOpenOptionalControlledPinnedDescriptor A initialCode → Prop)
    (Live : ProfiledOpenOptionalControlledPinnedDescriptor A initialCode →
      ProfiledOpenOptionalControlledPinnedFamily A initialCode → Prop)
    (Valid : ProfiledOpenOptionalControlledPinnedFamily A initialCode →
      ProfiledOpenOptionalControlledPinnedMove A initialCode → Prop)
    (family : ProfiledOpenOptionalControlledPinnedFamily A initialCode)
    (tag : ProfiledOpenOptionalControlledPinnedTag A initialCode)
    (table : ProfiledOpenOptionalControlledPinnedDescriptorTable A
      initialCode) : Prop :=
  ∀ current,
    Live current family →
    Valid family tag.1 →
    ∃ answer,
      table current = some answer ∧
        ProfiledOpenOptionalControlledPinnedPointedGood A initialCode Supported
          ExactEdge { family := family, descriptor := current, tag := tag }
            answer

/-- Select every row independently.  This is a finite table, not a function
of the unknown runtime descriptor chosen by either process. -/
noncomputable def profiledOpenOptionalControlledPinnedDescriptorTable?
    (Supported :
      ProfiledOpenOptionalControlledPinnedDescriptor A initialCode →
      ProfiledOpenOptionalControlledPinnedFamily A initialCode →
      ProfiledOpenOptionalControlledPinnedMove A initialCode →
      ProfiledOpenOptionalControlledPinnedTag A initialCode →
      ProfiledOpenOptionalControlledPinnedFamily A initialCode → Prop)
    (ExactEdge :
      ProfiledOpenOptionalControlledPinnedDescriptor A initialCode →
      ProfiledOpenOptionalControlledPinnedMove A initialCode →
      ProfiledOpenOptionalControlledPinnedTag A initialCode →
      ProfiledOpenOptionalControlledPinnedFamily A initialCode →
      ProfiledOpenOptionalControlledPinnedDescriptor A initialCode → Prop)
    (family : ProfiledOpenOptionalControlledPinnedFamily A initialCode)
    (tag : ProfiledOpenOptionalControlledPinnedTag A initialCode) :
    ProfiledOpenOptionalControlledPinnedDescriptorTable A initialCode := by
  classical
  exact fun current =>
    if h : ∃ answer,
        ProfiledOpenOptionalControlledPinnedPointedGood A initialCode Supported
          ExactEdge { family := family, descriptor := current, tag := tag }
            answer then
      some (Classical.choose h)
    else
      none

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

/-- A row with an available good answer is filled by a good answer. -/
theorem profiledOpenOptionalControlledPinnedDescriptorTable?_spec_of_exists
    (Supported :
      ProfiledOpenOptionalControlledPinnedDescriptor A initialCode →
      ProfiledOpenOptionalControlledPinnedFamily A initialCode →
      ProfiledOpenOptionalControlledPinnedMove A initialCode →
      ProfiledOpenOptionalControlledPinnedTag A initialCode →
      ProfiledOpenOptionalControlledPinnedFamily A initialCode → Prop)
    (ExactEdge :
      ProfiledOpenOptionalControlledPinnedDescriptor A initialCode →
      ProfiledOpenOptionalControlledPinnedMove A initialCode →
      ProfiledOpenOptionalControlledPinnedTag A initialCode →
      ProfiledOpenOptionalControlledPinnedFamily A initialCode →
      ProfiledOpenOptionalControlledPinnedDescriptor A initialCode → Prop)
    (family : ProfiledOpenOptionalControlledPinnedFamily A initialCode)
    (tag : ProfiledOpenOptionalControlledPinnedTag A initialCode)
    (current : ProfiledOpenOptionalControlledPinnedDescriptor A initialCode)
    (hexists : ∃ answer,
      ProfiledOpenOptionalControlledPinnedPointedGood A initialCode Supported
        ExactEdge { family := family, descriptor := current, tag := tag }
          answer) :
    ∃ answer,
      profiledOpenOptionalControlledPinnedDescriptorTable? A initialCode
          Supported ExactEdge family tag current = some answer ∧
        ProfiledOpenOptionalControlledPinnedPointedGood A initialCode Supported
          ExactEdge { family := family, descriptor := current, tag := tag }
            answer := by
  classical
  refine ⟨Classical.choose hexists, ?_, Classical.choose_spec hexists⟩
  simp only [profiledOpenOptionalControlledPinnedDescriptorTable?,
    dif_pos hexists]

/-- Pointed coverage is exactly the existence of one finite family/tag table
whose descriptor rows are all correct on live valid queries. -/
theorem
    profiledOpenOptionalControlledPinnedPointedCoverage_iff_exists_tables
    (Supported :
      ProfiledOpenOptionalControlledPinnedDescriptor A initialCode →
      ProfiledOpenOptionalControlledPinnedFamily A initialCode →
      ProfiledOpenOptionalControlledPinnedMove A initialCode →
      ProfiledOpenOptionalControlledPinnedTag A initialCode →
      ProfiledOpenOptionalControlledPinnedFamily A initialCode → Prop)
    (ExactEdge :
      ProfiledOpenOptionalControlledPinnedDescriptor A initialCode →
      ProfiledOpenOptionalControlledPinnedMove A initialCode →
      ProfiledOpenOptionalControlledPinnedTag A initialCode →
      ProfiledOpenOptionalControlledPinnedFamily A initialCode →
      ProfiledOpenOptionalControlledPinnedDescriptor A initialCode → Prop)
    (Live : ProfiledOpenOptionalControlledPinnedDescriptor A initialCode →
      ProfiledOpenOptionalControlledPinnedFamily A initialCode → Prop)
    (Valid : ProfiledOpenOptionalControlledPinnedFamily A initialCode →
      ProfiledOpenOptionalControlledPinnedMove A initialCode → Prop) :
    ProfiledOpenOptionalControlledPinnedPointedCoverage A initialCode Supported
        ExactEdge Live Valid ↔
      ∃ tables :
          ProfiledOpenOptionalControlledPinnedPointedTables A initialCode,
        ∀ family tag,
          ProfiledOpenOptionalControlledPinnedDescriptorTableWorks A
            initialCode Supported ExactEdge Live Valid family tag
              (tables family tag) := by
  constructor
  · intro coverage
    let tables :
        ProfiledOpenOptionalControlledPinnedPointedTables A initialCode :=
      fun family tag =>
        profiledOpenOptionalControlledPinnedDescriptorTable? A initialCode
          Supported ExactEdge family tag
    refine ⟨tables, ?_⟩
    intro family tag current hlive hvalid
    apply
      profiledOpenOptionalControlledPinnedDescriptorTable?_spec_of_exists A
        initialCode Supported ExactEdge family tag current
    exact coverage
      { family := family, descriptor := current, tag := tag } hlive hvalid
  · rintro ⟨tables, htables⟩ query hlive hvalid
    obtain ⟨answer, _, hgood⟩ :=
      htables query.family query.tag query.descriptor hlive hvalid
    exact ⟨answer, hgood⟩

/-- A blocked live row is the exact fail-fast witness for the relational
route.  Non-uniqueness is not a failure; absence of every exact answer is. -/
theorem
    not_profiledOpenOptionalControlledPinnedPointedCoverage_of_blocked
    (Supported :
      ProfiledOpenOptionalControlledPinnedDescriptor A initialCode →
      ProfiledOpenOptionalControlledPinnedFamily A initialCode →
      ProfiledOpenOptionalControlledPinnedMove A initialCode →
      ProfiledOpenOptionalControlledPinnedTag A initialCode →
      ProfiledOpenOptionalControlledPinnedFamily A initialCode → Prop)
    (ExactEdge :
      ProfiledOpenOptionalControlledPinnedDescriptor A initialCode →
      ProfiledOpenOptionalControlledPinnedMove A initialCode →
      ProfiledOpenOptionalControlledPinnedTag A initialCode →
      ProfiledOpenOptionalControlledPinnedFamily A initialCode →
      ProfiledOpenOptionalControlledPinnedDescriptor A initialCode → Prop)
    (Live : ProfiledOpenOptionalControlledPinnedDescriptor A initialCode →
      ProfiledOpenOptionalControlledPinnedFamily A initialCode → Prop)
    (Valid : ProfiledOpenOptionalControlledPinnedFamily A initialCode →
      ProfiledOpenOptionalControlledPinnedMove A initialCode → Prop)
    (query : ProfiledOpenOptionalControlledPinnedPointedQuery A initialCode)
    (hlive : Live query.descriptor query.family)
    (hvalid : Valid query.family query.tag.1)
    (hblocked : ∀ answer,
      ¬ ProfiledOpenOptionalControlledPinnedPointedGood A initialCode
        Supported ExactEdge query answer) :
    ¬ ProfiledOpenOptionalControlledPinnedPointedCoverage A initialCode
      Supported ExactEdge Live Valid := by
  intro coverage
  obtain ⟨answer, hgood⟩ := coverage query hlive hvalid
  exact hblocked answer hgood

end

/-! ## One represented semantic edge fills one pointed row -/

/-- The concrete semantic source and its pinned tag form the pointed query
whose row the receive transition will use. -/
noncomputable def profiledOpenOptionalControlledPinnedSemanticQuery
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode)
    (tag : ProfiledOpenOptionalControlledPinnedTag A initialCode) :
    ProfiledOpenOptionalControlledPinnedPointedQuery A initialCode :=
  { family := profiledOpenOptionalControlledFamilyOf A strategy hwin basis
      initialCode point
    descriptor :=
      profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis initialCode point
    tag := tag }

/-- The literal semantic child supplies the corresponding answer. -/
noncomputable def profiledOpenOptionalControlledPinnedSemanticAnswer
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode)
    (tag : ProfiledOpenOptionalControlledPinnedTag A initialCode) :
    ProfiledOpenOptionalControlledPinnedPointedAnswer A initialCode :=
  let child := profiledOpenOptionalControlledBlockQuerySemanticNext A strategy
    hwin basis initialCode point tag
  (profiledOpenOptionalControlledFamilyOf A strategy hwin basis initialCode
      child,
    profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
      basis initialCode child)

/-- Supportedness and the exact literal semantic edge make the literal child
a good pointed answer.  The control component is already proved by the total
optional semantic step. -/
theorem profiledOpenOptionalControlledPinnedSemanticAnswer_good
    (Supported :
      ProfiledOpenOptionalControlledPinnedDescriptor A initialCode →
      ProfiledOpenOptionalControlledPinnedFamily A initialCode →
      ProfiledOpenOptionalControlledPinnedMove A initialCode →
      ProfiledOpenOptionalControlledPinnedTag A initialCode →
      ProfiledOpenOptionalControlledPinnedFamily A initialCode → Prop)
    (ExactEdge :
      ProfiledOpenOptionalControlledPinnedDescriptor A initialCode →
      ProfiledOpenOptionalControlledPinnedMove A initialCode →
      ProfiledOpenOptionalControlledPinnedTag A initialCode →
      ProfiledOpenOptionalControlledPinnedFamily A initialCode →
      ProfiledOpenOptionalControlledPinnedDescriptor A initialCode → Prop)
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode)
    (tag : ProfiledOpenOptionalControlledPinnedTag A initialCode)
    (hsupported : Supported
      (profiledOpenOptionalControlledPinnedSemanticQuery A strategy hwin basis
        initialCode point tag).descriptor
      (profiledOpenOptionalControlledPinnedSemanticQuery A strategy hwin basis
        initialCode point tag).family
      tag.1 tag
      (profiledOpenOptionalControlledPinnedSemanticAnswer A strategy hwin basis
        initialCode point tag).1)
    (hedge : ExactEdge
      (profiledOpenOptionalControlledPinnedSemanticQuery A strategy hwin basis
        initialCode point tag).descriptor
      tag.1 tag
      (profiledOpenOptionalControlledPinnedSemanticAnswer A strategy hwin basis
        initialCode point tag).1
      (profiledOpenOptionalControlledPinnedSemanticAnswer A strategy hwin basis
        initialCode point tag).2) :
    ProfiledOpenOptionalControlledPinnedPointedGood A initialCode Supported
      ExactEdge
      (profiledOpenOptionalControlledPinnedSemanticQuery A strategy hwin basis
        initialCode point tag)
      (profiledOpenOptionalControlledPinnedSemanticAnswer A strategy hwin basis
        initialCode point tag) := by
  refine ⟨hsupported, hedge, ?_⟩
  exact profiledOpenIndexedOptionalControlledSemanticNext_control A strategy
    hwin basis initialCode point tag.2.2

/-- The exact positive model input at represented semantic points. -/
def ProfiledOpenOptionalControlledPinnedSemanticEdgeCoverage
    (Supported :
      ProfiledOpenOptionalControlledPinnedDescriptor A initialCode →
      ProfiledOpenOptionalControlledPinnedFamily A initialCode →
      ProfiledOpenOptionalControlledPinnedMove A initialCode →
      ProfiledOpenOptionalControlledPinnedTag A initialCode →
      ProfiledOpenOptionalControlledPinnedFamily A initialCode → Prop)
    (ExactEdge :
      ProfiledOpenOptionalControlledPinnedDescriptor A initialCode →
      ProfiledOpenOptionalControlledPinnedMove A initialCode →
      ProfiledOpenOptionalControlledPinnedTag A initialCode →
      ProfiledOpenOptionalControlledPinnedFamily A initialCode →
      ProfiledOpenOptionalControlledPinnedDescriptor A initialCode → Prop)
    (Coherent :
      ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin basis
          initialCode →
        ProfiledOpenOptionalControlledPinnedTag A initialCode → Prop) : Prop :=
  ∀ point tag,
    Coherent point tag →
    Supported
        (profiledOpenOptionalControlledPinnedSemanticQuery A strategy hwin
          basis initialCode point tag).descriptor
        (profiledOpenOptionalControlledPinnedSemanticQuery A strategy hwin
          basis initialCode point tag).family
        tag.1 tag
        (profiledOpenOptionalControlledPinnedSemanticAnswer A strategy hwin
          basis initialCode point tag).1 ∧
      ExactEdge
        (profiledOpenOptionalControlledPinnedSemanticQuery A strategy hwin
          basis initialCode point tag).descriptor
        tag.1 tag
        (profiledOpenOptionalControlledPinnedSemanticAnswer A strategy hwin
          basis initialCode point tag).1
        (profiledOpenOptionalControlledPinnedSemanticAnswer A strategy hwin
          basis initialCode point tag).2

/-- Strong provenance/recovery is needed only existentially, one query at a
time: every live pointed row has some semantic representative carrying the
same family and exact descriptor.  No comparison between two representatives
and no child-family constancy is requested. -/
def ProfiledOpenOptionalControlledPinnedPointedRecovery
    (Live : ProfiledOpenOptionalControlledPinnedDescriptor A initialCode →
      ProfiledOpenOptionalControlledPinnedFamily A initialCode → Prop)
    (Valid : ProfiledOpenOptionalControlledPinnedFamily A initialCode →
      ProfiledOpenOptionalControlledPinnedMove A initialCode → Prop)
    (Coherent :
      ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin basis
          initialCode →
        ProfiledOpenOptionalControlledPinnedTag A initialCode → Prop) : Prop :=
  ∀ query,
    Live query.descriptor query.family →
    Valid query.family query.tag.1 →
    ∃ point,
      profiledOpenOptionalControlledPinnedSemanticQuery A strategy hwin basis
          initialCode point query.tag = query ∧
        Coherent point query.tag

/-- The exact remaining positive bridge: existential recovery plus one
supported semantic edge fills every row of the finite descriptor table.
Neither hypothesis contains a functional child-family requirement. -/
theorem
    profiledOpenOptionalControlledPinnedPointedCoverage_of_semanticEdges
    (Supported :
      ProfiledOpenOptionalControlledPinnedDescriptor A initialCode →
      ProfiledOpenOptionalControlledPinnedFamily A initialCode →
      ProfiledOpenOptionalControlledPinnedMove A initialCode →
      ProfiledOpenOptionalControlledPinnedTag A initialCode →
      ProfiledOpenOptionalControlledPinnedFamily A initialCode → Prop)
    (ExactEdge :
      ProfiledOpenOptionalControlledPinnedDescriptor A initialCode →
      ProfiledOpenOptionalControlledPinnedMove A initialCode →
      ProfiledOpenOptionalControlledPinnedTag A initialCode →
      ProfiledOpenOptionalControlledPinnedFamily A initialCode →
      ProfiledOpenOptionalControlledPinnedDescriptor A initialCode → Prop)
    (Live : ProfiledOpenOptionalControlledPinnedDescriptor A initialCode →
      ProfiledOpenOptionalControlledPinnedFamily A initialCode → Prop)
    (Valid : ProfiledOpenOptionalControlledPinnedFamily A initialCode →
      ProfiledOpenOptionalControlledPinnedMove A initialCode → Prop)
    (Coherent :
      ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin basis
          initialCode →
        ProfiledOpenOptionalControlledPinnedTag A initialCode → Prop)
    (recovery :
      ProfiledOpenOptionalControlledPinnedPointedRecovery A strategy hwin basis
        initialCode Live Valid Coherent)
    (edges :
      ProfiledOpenOptionalControlledPinnedSemanticEdgeCoverage A strategy hwin
        basis initialCode Supported ExactEdge Coherent) :
    ProfiledOpenOptionalControlledPinnedPointedCoverage A initialCode Supported
      ExactEdge Live Valid := by
  intro query hlive hvalid
  obtain ⟨point, hquery, hcoherent⟩ :=
    recovery query hlive hvalid
  obtain ⟨hsupported, hedge⟩ := edges point query.tag hcoherent
  refine ⟨profiledOpenOptionalControlledPinnedSemanticAnswer A strategy hwin
    basis initialCode point query.tag, ?_⟩
  rw [← hquery]
  exact profiledOpenOptionalControlledPinnedSemanticAnswer_good A strategy hwin
    basis initialCode Supported ExactEdge point query.tag hsupported hedge

end

end DetParityAutomaton

end DistributedSynthesis
