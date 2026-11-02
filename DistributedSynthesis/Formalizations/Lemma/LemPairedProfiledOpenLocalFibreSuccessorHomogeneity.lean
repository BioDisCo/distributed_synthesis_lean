/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenFixedCoordinateCommonMove
import DistributedSynthesis.Formalizations.Lemma.LemSidewiseLocalClassReadout

/-!
# Process-local homogeneity after a semantic handoff

This file isolates the runtime-selection fact needed by the fixed sidewise
controller bank.  The proof never reflects equality of finite fibre images
back to equality of exact views.  It uses only the safe forward direction:
two literal children in the same exact process-local fibre have the same
corresponding finite family coordinate.

There are two distinct obligations which must not be conflated.

* `childRel` below is a proof about the literal post-transition views.  It is
  allowed to know which proof-side coordinate is being verified, but no such
  side is passed to a process.
* an operational candidate set must contain only children in one such local
  fibre.  The subset lemmas turn that representation invariant into the
  class-homogeneity/readout property consumed by the bank.

The same-transition premise is intentionally expressed at the child, not by
assuming that a permanently hidden bit is harmless.  A later receive/switch
adapter must prove the premise from the actual locally observable transition.
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

private abbrev LocalCoordinateTaggedCandidate :=
  RelationalFamilyCandidate
    (SidewiseTaggedFamily
      (ProfiledOpenFixedCoordinateSideClass A initialCode)
      (ProfiledOpenFixedCoordinateSideClass A initialCode)
      (ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I)
        initialCode))
    (ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode)

/-! ## Exact child-coordinate equality -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Process-one form: exact post-transition local-fibre equality forces
equality of the target's process-one family coordinate.  The control map is
one proof-side map on the whole semantic carrier; it is not selected from a
finite image and no converse to `semanticFibreImage_eq_of_rel` is used. -/
theorem profiledOpenFixedChildFamily_fst_eq_of_localFibre
    (control : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
        (I := I) →
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)
    (left right : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I))
    (hrel : ProfiledOpenIndexedProcessOneLocalFibreRel A strategy hwin basis
      left right) :
    (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
        control left).1 =
      (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
        control right).1 := by
  classical
  unfold profiledOpenFixedPinnedFamilyCode
  exact semanticTwoFibreCode_fst_eq_of_rel
    (profiledOpenFixedPinnedSemanticDescriptor A strategy hwin basis
      initialCode control)
    (ProfiledOpenIndexedProcessOneLocalFibreRel A strategy hwin basis)
    (ProfiledOpenIndexedProcessTwoLocalFibreRel A strategy hwin basis)
    (profiledOpenIndexedProcessOneLocalFibreRel_fibresAgree A strategy hwin
      basis) hrel

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Process-two mirror. -/
theorem profiledOpenFixedChildFamily_snd_eq_of_localFibre
    (control : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
        (I := I) →
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)
    (left right : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I))
    (hrel : ProfiledOpenIndexedProcessTwoLocalFibreRel A strategy hwin basis
      left right) :
    (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
        control left).2 =
      (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
        control right).2 := by
  classical
  unfold profiledOpenFixedPinnedFamilyCode
  exact semanticTwoFibreCode_snd_eq_of_rel
    (profiledOpenFixedPinnedSemanticDescriptor A strategy hwin basis
      initialCode control)
    (ProfiledOpenIndexedProcessOneLocalFibreRel A strategy hwin basis)
    (ProfiledOpenIndexedProcessTwoLocalFibreRel A strategy hwin basis)
    (profiledOpenIndexedProcessTwoLocalFibreRel_fibresAgree A strategy hwin
      basis) hrel

/-! ## Shape-aware optional family equations -/

/-- Inactive optional semantics exposes the empty family. -/
theorem profiledOpenOptionalControlledFamilyOf_eq_sink
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode)
    (hright : point.1.state.right = none)
    (hleft : point.1.state.left = none) :
    profiledOpenOptionalControlledFamilyOf A strategy hwin basis initialCode
        point =
      profiledOpenOptionalSinkFamilyCode A (I := I) initialCode := by
  classical
  letI : DecidableEq
      (ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode) :=
    Classical.decEq _
  change
    (profiledOpenOptionalFixedPinnedSemanticMoveOfWinning A strategy hwin
      basis initialCode (fun _ ↦ point.2) point.1).1 = _
  unfold profiledOpenOptionalFixedPinnedSemanticMoveOfWinning
  generalize hbank :
    profiledOpenIndexedOptionalSourceFibreProvenanceBankOfWinning A strategy
      hwin basis
      (profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
        initialCode (fun _ ↦ point.2)) point.1 = bank
  cases bank with
  | sink => rfl
  | rightOnly lane hactive _ _ => rw [hright] at hactive; cases hactive
  | leftOnly lane _ hactive _ => rw [hleft] at hactive; cases hactive
  | both laneOne laneTwo hactive _ _ =>
      rw [hright] at hactive
      cases hactive

/-- Exact right-only reduction of the optional family constructor. -/
theorem profiledOpenOptionalControlledFamilyOf_eq_rightOnly
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode)
    (lane : ProfiledOpenIndexedRightSemanticLane A strategy hwin basis
      (I := I))
    (hright : point.1.state.right = some lane)
    (hleft : point.1.state.left = none) :
    profiledOpenOptionalControlledFamilyOf A strategy hwin basis initialCode
        point =
      profiledOpenOptionalRightOnlyFamilyCode A strategy hwin basis
        initialCode (fun _ ↦ point.2)
        (point.1.toRightOnly A strategy hwin basis lane hright hleft) := by
  classical
  letI : DecidableEq
      (ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode) :=
    Classical.decEq _
  change
    (profiledOpenOptionalFixedPinnedSemanticMoveOfWinning A strategy hwin
      basis initialCode (fun _ ↦ point.2) point.1).1 = _
  unfold profiledOpenOptionalFixedPinnedSemanticMoveOfWinning
  generalize hbank :
    profiledOpenIndexedOptionalSourceFibreProvenanceBankOfWinning A strategy
      hwin basis
      (profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
        initialCode (fun _ ↦ point.2)) point.1 = bank
  cases bank with
  | sink hnone _ => rw [hright] at hnone; cases hnone
  | rightOnly other hactive _ _ =>
      have hlane : other = lane :=
        Option.some.inj (hactive.symm.trans hright)
      subst other
      rfl
  | leftOnly other hnone _ _ => rw [hright] at hnone; cases hnone
  | both other _ _ hactive _ => rw [hleft] at hactive; cases hactive

/-- Exact left-only reduction. -/
theorem profiledOpenOptionalControlledFamilyOf_eq_leftOnly
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode)
    (lane : ProfiledOpenIndexedLeftSemanticLane A strategy hwin basis
      (I := I))
    (hright : point.1.state.right = none)
    (hleft : point.1.state.left = some lane) :
    profiledOpenOptionalControlledFamilyOf A strategy hwin basis initialCode
        point =
      profiledOpenOptionalLeftOnlyFamilyCode A strategy hwin basis initialCode
        (fun _ ↦ point.2)
        (point.1.toLeftOnly A strategy hwin basis lane hright hleft) := by
  classical
  letI : DecidableEq
      (ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode) :=
    Classical.decEq _
  change
    (profiledOpenOptionalFixedPinnedSemanticMoveOfWinning A strategy hwin
      basis initialCode (fun _ ↦ point.2) point.1).1 = _
  unfold profiledOpenOptionalFixedPinnedSemanticMoveOfWinning
  generalize hbank :
    profiledOpenIndexedOptionalSourceFibreProvenanceBankOfWinning A strategy
      hwin basis
      (profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
        initialCode (fun _ ↦ point.2)) point.1 = bank
  cases bank with
  | sink _ hnone => rw [hleft] at hnone; cases hnone
  | rightOnly other _ hnone _ => rw [hleft] at hnone; cases hnone
  | leftOnly other _ hactive _ =>
      have hlane : other = lane :=
        Option.some.inj (hactive.symm.trans hleft)
      subst other
      rfl
  | both _ other hactive _ _ => rw [hright] at hactive; cases hactive

/-- Exact two-live reduction. -/
theorem profiledOpenOptionalControlledFamilyOf_eq_both
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode)
    (rightLane : ProfiledOpenIndexedRightSemanticLane A strategy hwin basis
      (I := I))
    (leftLane : ProfiledOpenIndexedLeftSemanticLane A strategy hwin basis
      (I := I))
    (hright : point.1.state.right = some rightLane)
    (hleft : point.1.state.left = some leftLane) :
    profiledOpenOptionalControlledFamilyOf A strategy hwin basis initialCode
        point =
      profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
        (fun _ ↦ point.2)
        (point.1.toLiveFresh A strategy hwin basis rightLane leftLane hright
          hleft) := by
  classical
  letI : DecidableEq
      (ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode) :=
    Classical.decEq _
  change
    (profiledOpenOptionalFixedPinnedSemanticMoveOfWinning A strategy hwin
      basis initialCode (fun _ ↦ point.2) point.1).1 = _
  unfold profiledOpenOptionalFixedPinnedSemanticMoveOfWinning
  generalize hbank :
    profiledOpenIndexedOptionalSourceFibreProvenanceBankOfWinning A strategy
      hwin basis
      (profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
        initialCode (fun _ ↦ point.2)) point.1 = bank
  cases bank with
  | sink hnone _ => rw [hright] at hnone; cases hnone
  | rightOnly other _ hnone _ => rw [hleft] at hnone; cases hnone
  | leftOnly other hnone _ _ => rw [hright] at hnone; cases hnone
  | both otherRight otherLeft hactiveRight hactiveLeft _ =>
      have hrightLane : otherRight = rightLane :=
        Option.some.inj (hactiveRight.symm.trans hright)
      have hleftLane : otherLeft = leftLane :=
        Option.some.inj (hactiveLeft.symm.trans hleft)
      subst otherRight
      subst otherLeft
      rfl

/-- Shape-aware exact child-family equality.  Equality of literal parity
control is necessary: each optional family freezes that control while taking
its exact-view fibre image. -/
theorem profiledOpenOptionalControlledFamily_eq_of_childFibreAlignment
    (left right : ProfiledOpenIndexedOptionalControlledSemanticState A
      strategy hwin basis initialCode)
    (hcontrol : left.2 = right.2)
    (halign : ProfiledOpenOptionalControlledChildFibreAlignment A strategy
      hwin basis initialCode left right) :
    profiledOpenOptionalControlledFamilyOf A strategy hwin basis initialCode
        left =
      profiledOpenOptionalControlledFamilyOf A strategy hwin basis initialCode
        right := by
  cases halign with
  | inactive leftRight leftLeft rightRight rightLeft _ _ =>
      rw [profiledOpenOptionalControlledFamilyOf_eq_sink A strategy hwin basis
          initialCode left leftRight leftLeft,
        profiledOpenOptionalControlledFamilyOf_eq_sink A strategy hwin basis
          initialCode right rightRight rightLeft]
  | rightOnly leftLane rightLane leftRight leftLeft rightRight rightLeft
      _ _ hrel =>
      rw [profiledOpenOptionalControlledFamilyOf_eq_rightOnly A strategy hwin
          basis initialCode left leftLane leftRight leftLeft,
        profiledOpenOptionalControlledFamilyOf_eq_rightOnly A strategy hwin
          basis initialCode right rightLane rightRight rightLeft]
      simpa only [hcontrol] using
        (profiledOpenOptionalRightOnlyFamilyCode_eq_of_rel A strategy hwin
          basis initialCode (fun _ ↦ left.2) _ _ hrel)
  | leftOnly leftLane rightLane leftRight leftLeft rightRight rightLeft
      _ _ hrel =>
      rw [profiledOpenOptionalControlledFamilyOf_eq_leftOnly A strategy hwin
          basis initialCode left leftLane leftRight leftLeft,
        profiledOpenOptionalControlledFamilyOf_eq_leftOnly A strategy hwin
          basis initialCode right rightLane rightRight rightLeft]
      simpa only [hcontrol] using
        (profiledOpenOptionalLeftOnlyFamilyCode_eq_of_rel A strategy hwin
          basis initialCode (fun _ ↦ left.2) _ _ hrel)
  | both leftRightLane leftLeftLane rightRightLane rightLeftLane leftRight
      leftLeft rightRight rightLeft _ _ hrelOne hrelTwo =>
      rw [profiledOpenOptionalControlledFamilyOf_eq_both A strategy hwin basis
          initialCode left leftRightLane leftLeftLane leftRight leftLeft,
        profiledOpenOptionalControlledFamilyOf_eq_both A strategy hwin basis
          initialCode right rightRightLane rightLeftLane rightRight rightLeft]
      simpa only [hcontrol] using
        (profiledOpenFixedPinnedFamilyCode_eq_of_localFibres A strategy hwin
          basis initialCode (fun _ ↦ left.2) _ _ hrelOne hrelTwo)

/-! ## The exact receive/switch preservation boundary -/

/-- The finite current descriptor and one common pinned block query preserve
the four-way exact child fibres.  This is the concrete dangerous law: code,
control, and old finite move equality are its only source-side premise.

It is deliberately a named predicate rather than a hidden inference from
finiteness.  The finite descriptor does not contain the literal recursive
views, so proving this law requires the actual receive/restart argument. -/
def ProfiledOpenOptionalControlledBlockQueryChildFibrePreserving : Prop :=
  ∀ (left right : ProfiledOpenIndexedOptionalControlledSemanticState A
      strategy hwin basis initialCode)
    (tag : ProfiledOpenOptionalControlledPinnedTag A initialCode),
    profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis initialCode left =
      profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis initialCode right →
    ProfiledOpenOptionalControlledChildFibreAlignment A strategy hwin basis
      initialCode
      (profiledOpenOptionalControlledBlockQuerySemanticNext A strategy hwin
        basis initialCode left tag)
      (profiledOpenOptionalControlledBlockQuerySemanticNext A strategy hwin
        basis initialCode right tag)

/-- A literal same-finite-source, same-query failure of exact child-fibre
alignment.  Such a witness is the fail-fast obstruction to deriving local
class preservation from the present descriptor alphabet. -/
def ProfiledOpenOptionalControlledBlockQueryChildFibreCollision : Prop :=
  ∃ (left right : ProfiledOpenIndexedOptionalControlledSemanticState A
      strategy hwin basis initialCode)
    (tag : ProfiledOpenOptionalControlledPinnedTag A initialCode),
    profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis initialCode left =
      profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis initialCode right ∧
    ¬ ProfiledOpenOptionalControlledChildFibreAlignment A strategy hwin basis
      initialCode
      (profiledOpenOptionalControlledBlockQuerySemanticNext A strategy hwin
        basis initialCode left tag)
      (profiledOpenOptionalControlledBlockQuerySemanticNext A strategy hwin
        basis initialCode right tag)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Preservation is exactly absence of the concrete collision. -/
theorem
    profiledOpenOptionalControlledBlockQueryChildFibrePreserving_iff_noCollision :
    ProfiledOpenOptionalControlledBlockQueryChildFibrePreserving A strategy
        hwin basis initialCode ↔
      ¬ ProfiledOpenOptionalControlledBlockQueryChildFibreCollision A strategy
        hwin basis initialCode := by
  constructor
  · intro hpreserve
    rintro ⟨left, right, tag, hdescriptor, hnot⟩
    exact hnot (hpreserve left right tag hdescriptor)
  · intro hno left right tag hdescriptor
    by_contra hnot
    exact hno ⟨left, right, tag, hdescriptor, hnot⟩

/-- Once the receive/switch law is supplied, the child public family is
functional at equal finite source descriptors.  Literal parity-control
equality is not an additional residual: it follows from the already proved
finite code/control step. -/
theorem
    profiledOpenOptionalControlledBlockQuery_childFamily_eq_of_preserving
    (hpreserve :
      ProfiledOpenOptionalControlledBlockQueryChildFibrePreserving A strategy
        hwin basis initialCode)
    (left right : ProfiledOpenIndexedOptionalControlledSemanticState A
      strategy hwin basis initialCode)
    (tag : ProfiledOpenOptionalControlledPinnedTag A initialCode)
    (hdescriptor :
      profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
          basis initialCode left =
        profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy
          hwin basis initialCode right) :
    profiledOpenOptionalControlledFamilyOf A strategy hwin basis initialCode
        (profiledOpenOptionalControlledBlockQuerySemanticNext A strategy hwin
          basis initialCode left tag) =
      profiledOpenOptionalControlledFamilyOf A strategy hwin basis initialCode
        (profiledOpenOptionalControlledBlockQuerySemanticNext A strategy hwin
          basis initialCode right tag) := by
  apply profiledOpenOptionalControlledFamily_eq_of_childFibreAlignment A
    strategy hwin basis initialCode
  · exact
      profiledOpenOptionalControlledBlockQuerySemanticNext_control_eq_of_descriptor_eq
        A strategy hwin basis initialCode left right tag hdescriptor
  · exact hpreserve left right tag hdescriptor

/-! ## Cross-shape audit -/

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- Exact child-fibre alignment preserves both lane-activity bits.  These are
proof-side facts only; the theorem does not make either bit observable. -/
theorem profiledOpenOptionalControlledChildFibreAlignment_activity
    (left right : ProfiledOpenIndexedOptionalControlledSemanticState A
      strategy hwin basis initialCode)
    (halign : ProfiledOpenOptionalControlledChildFibreAlignment A strategy
      hwin basis initialCode left right) :
    ((∃ lane, left.1.state.right = some lane) ↔
        ∃ lane, right.1.state.right = some lane) ∧
      ((∃ lane, left.1.state.left = some lane) ↔
        ∃ lane, right.1.state.left = some lane) := by
  cases halign with
  | inactive leftRight leftLeft rightRight rightLeft _ _ =>
      simp [leftRight, leftLeft, rightRight, rightLeft]
  | rightOnly leftLane rightLane leftRight leftLeft rightRight rightLeft
      _ _ _ =>
      simp [leftRight, leftLeft, rightRight, rightLeft]
  | leftOnly leftLane rightLane leftRight leftLeft rightRight rightLeft
      _ _ _ =>
      simp [leftRight, leftLeft, rightRight, rightLeft]
  | both leftRightLane leftLeftLane rightRightLane rightLeftLane leftRight
      leftLeft rightRight rightLeft _ _ _ _ =>
      simp [leftRight, leftLeft, rightRight, rightLeft]

/-- A right-only child and a two-live child can never satisfy the current
full alignment predicate, even though process one's own local view need not
reveal whether the opposite lane exists. -/
theorem not_profiledOpenOptionalControlledChildFibreAlignment_rightOnly_both
    (left right : ProfiledOpenIndexedOptionalControlledSemanticState A
      strategy hwin basis initialCode)
    (leftRightLane : ProfiledOpenIndexedRightSemanticLane A strategy hwin
      basis (I := I))
    (rightRightLane : ProfiledOpenIndexedRightSemanticLane A strategy hwin
      basis (I := I))
    (rightLeftLane : ProfiledOpenIndexedLeftSemanticLane A strategy hwin
      basis (I := I))
    (leftRight : left.1.state.right = some leftRightLane)
    (leftLeft : left.1.state.left = none)
    (rightRight : right.1.state.right = some rightRightLane)
    (rightLeft : right.1.state.left = some rightLeftLane) :
    ¬ ProfiledOpenOptionalControlledChildFibreAlignment A strategy hwin basis
      initialCode left right := by
  intro halign
  have hactivity :=
    (profiledOpenOptionalControlledChildFibreAlignment_activity A strategy hwin
      basis initialCode left right halign).2
  obtain ⟨lane, hactive⟩ := hactivity.mpr ⟨rightLeftLane, rightLeft⟩
  rw [leftLeft] at hactive
  cases hactive

/-- Process-two dangerous cross-shape: left-only versus two-live. -/
theorem not_profiledOpenOptionalControlledChildFibreAlignment_leftOnly_both
    (left right : ProfiledOpenIndexedOptionalControlledSemanticState A
      strategy hwin basis initialCode)
    (leftLeftLane : ProfiledOpenIndexedLeftSemanticLane A strategy hwin basis
      (I := I))
    (rightRightLane : ProfiledOpenIndexedRightSemanticLane A strategy hwin
      basis (I := I))
    (rightLeftLane : ProfiledOpenIndexedLeftSemanticLane A strategy hwin basis
      (I := I))
    (leftRight : left.1.state.right = none)
    (leftLeft : left.1.state.left = some leftLeftLane)
    (rightRight : right.1.state.right = some rightRightLane)
    (rightLeft : right.1.state.left = some rightLeftLane) :
    ¬ ProfiledOpenOptionalControlledChildFibreAlignment A strategy hwin basis
      initialCode left right := by
  intro halign
  have hactivity :=
    (profiledOpenOptionalControlledChildFibreAlignment_activity A strategy hwin
      basis initialCode left right halign).1
  obtain ⟨lane, hactive⟩ := hactivity.mpr ⟨rightRightLane, rightRight⟩
  rw [leftRight] at hactive
  cases hactive

/-- The process-one class used by the present family construction separates
right-only and two-live shapes *unconditionally*.  The reason is structural:
every descriptor in the right-only fibre has a sink left move, whereas the
current descriptor of a two-live fibre has a genuine left move.

Thus a candidate set containing locally indistinguishable right-only and
two-live children cannot be process-one class-homogeneous merely by the
existing exact-fibre theorem. -/
theorem profiledOpenOptionalRightOnlyFamily_fst_ne_both
    (rightControl :
      ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
          (I := I) →
        (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)
    (bothControl :
      ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis (I := I) →
        (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)
    (rightSource : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy
      hwin basis (I := I))
    (bothSource : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I)) :
    (profiledOpenOptionalRightOnlyFamilyCode A strategy hwin basis initialCode
        rightControl rightSource).1 ≠
      (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
        bothControl bothSource).1 := by
  classical
  let bothDescriptor :=
    profiledOpenFixedPinnedSemanticDescriptor A strategy hwin basis initialCode
      bothControl bothSource
  have hboth : bothDescriptor ∈
      (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
        bothControl bothSource).1 :=
    (descriptor_mem_semanticTwoFibreCode
      (profiledOpenFixedPinnedSemanticDescriptor A strategy hwin basis
        initialCode bothControl)
      (ProfiledOpenIndexedProcessOneLocalFibreRel A strategy hwin basis)
      (ProfiledOpenIndexedProcessTwoLocalFibreRel A strategy hwin basis)
      (profiledOpenIndexedProcessOneLocalFibreRel_reflexive A strategy hwin
        basis).refl
      (profiledOpenIndexedProcessTwoLocalFibreRel_reflexive A strategy hwin
        basis).refl bothSource).1
  intro heq
  have hright : bothDescriptor ∈
      (profiledOpenOptionalRightOnlyFamilyCode A strategy hwin basis
        initialCode rightControl rightSource).1 := by
    rw [heq]
    exact hboth
  let member : ProfiledOpenHiddenDescriptorRightCarrier A
      (profiledOpenOptionalRightOnlyFamilyCode A strategy hwin basis
        initialCode rightControl rightSource) := ⟨bothDescriptor, hright⟩
  let rightPoint :=
    profiledOpenOptionalRightOnlyPoint A strategy hwin basis initialCode
      rightControl rightSource member
  have hdescriptor :=
    profiledOpenOptionalRightOnlyPoint_descriptor A strategy hwin basis
      initialCode rightControl rightSource member
  have hmove := congrArg
    (fun descriptor : ProfiledOpenIndexedOldMoveHiddenDescriptor A
      (I := I) initialCode ↦ descriptor.moveIdentity.2) hdescriptor
  have hmove' :
      (profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
        initialCode rightControl rightPoint.optional.state).moveIdentity.2 =
        bothDescriptor.moveIdentity.2 := by
    simpa [member] using hmove
  have hsink :
      (profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
        initialCode rightControl rightPoint.optional.state).moveIdentity.2 =
        ProfiledOpenClassifiedMove.sink := by
    simp only [profiledOpenOptionalFixedSemanticDescriptor_moveIdentity]
    exact rightPoint.move_left A strategy hwin basis
  have hleft : bothDescriptor.moveIdentity.2 =
      ProfiledOpenClassifiedMove.left bothSource.leftLane.source
        ((bothSource.leftLane.realization.coherentTable A).table.toClassified A
          bothSource.leftLane.source) := by
    simp [bothDescriptor, profiledOpenFixedPinnedSemanticDescriptor,
      ProfiledOpenIndexedCorrelatedSemanticState.move, bothSource.left_eq,
      ProfiledOpenIndexedLeftSemanticShadow.move]
  rw [hsink, hleft] at hmove'
  cases hmove'

/-- Process-two mirror: left-only and two-live public second coordinates are
always distinct in the present construction. -/
theorem profiledOpenOptionalLeftOnlyFamily_snd_ne_both
    (leftControl :
      ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
          (I := I) →
        (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)
    (bothControl :
      ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis (I := I) →
        (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)
    (leftSource : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy
      hwin basis (I := I))
    (bothSource : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I)) :
    (profiledOpenOptionalLeftOnlyFamilyCode A strategy hwin basis initialCode
        leftControl leftSource).2 ≠
      (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
        bothControl bothSource).2 := by
  classical
  let bothDescriptor :=
    profiledOpenFixedPinnedSemanticDescriptor A strategy hwin basis initialCode
      bothControl bothSource
  have hboth : bothDescriptor ∈
      (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
        bothControl bothSource).2 :=
    (descriptor_mem_semanticTwoFibreCode
      (profiledOpenFixedPinnedSemanticDescriptor A strategy hwin basis
        initialCode bothControl)
      (ProfiledOpenIndexedProcessOneLocalFibreRel A strategy hwin basis)
      (ProfiledOpenIndexedProcessTwoLocalFibreRel A strategy hwin basis)
      (profiledOpenIndexedProcessOneLocalFibreRel_reflexive A strategy hwin
        basis).refl
      (profiledOpenIndexedProcessTwoLocalFibreRel_reflexive A strategy hwin
        basis).refl bothSource).2
  intro heq
  have hleftMem : bothDescriptor ∈
      (profiledOpenOptionalLeftOnlyFamilyCode A strategy hwin basis initialCode
        leftControl leftSource).2 := by
    rw [heq]
    exact hboth
  let member : ProfiledOpenHiddenDescriptorLeftCarrier A
      (profiledOpenOptionalLeftOnlyFamilyCode A strategy hwin basis initialCode
        leftControl leftSource) := ⟨bothDescriptor, hleftMem⟩
  let leftPoint :=
    profiledOpenOptionalLeftOnlyPoint A strategy hwin basis initialCode
      leftControl leftSource member
  have hdescriptor :=
    profiledOpenOptionalLeftOnlyPoint_descriptor A strategy hwin basis
      initialCode leftControl leftSource member
  have hmove := congrArg
    (fun descriptor : ProfiledOpenIndexedOldMoveHiddenDescriptor A
      (I := I) initialCode ↦ descriptor.moveIdentity.1) hdescriptor
  have hmove' :
      (profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
        initialCode leftControl leftPoint.optional.state).moveIdentity.1 =
        bothDescriptor.moveIdentity.1 := by
    simpa [member] using hmove
  have hsink :
      (profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
        initialCode leftControl leftPoint.optional.state).moveIdentity.1 =
        ProfiledOpenClassifiedMove.sink := by
    simp only [profiledOpenOptionalFixedSemanticDescriptor_moveIdentity]
    exact leftPoint.move_right A strategy hwin basis
  have hright : bothDescriptor.moveIdentity.1 =
      ProfiledOpenClassifiedMove.right bothSource.rightLane.source
        ((bothSource.rightLane.realization.coherentTable A).table.toClassified A
          bothSource.rightLane.source) := by
    simp [bothDescriptor, profiledOpenFixedPinnedSemanticDescriptor,
      ProfiledOpenIndexedCorrelatedSemanticState.move, bothSource.right_eq,
      ProfiledOpenIndexedRightSemanticShadow.move]
  rw [hsink, hright] at hmove'
  cases hmove'

end

/-! ## Candidate-set preservation -/

/-- A finite candidate set is represented inside one exact process-one child
fibre when every member has a literal semantic witness related to one anchor.
This is the exact invariant an operational receive/switch adapter must
preserve; it contains no selected leader or lane in the runtime data. -/
def ProfiledOpenFixedRightChildFibreRepresented
    (control : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
        (I := I) →
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)
    (anchor : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I))
    (candidates : Finset (LocalCoordinateTaggedCandidate A initialCode)) : Prop :=
  ∀ candidate ∈ candidates,
    ∃ point : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
        (I := I),
      ProfiledOpenIndexedProcessOneLocalFibreRel A strategy hwin basis
          anchor point ∧
        candidate = profiledOpenFixedCoordinateCandidateOf A strategy hwin
          basis initialCode control point

/-- Process-two mirror. -/
def ProfiledOpenFixedLeftChildFibreRepresented
    (control : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
        (I := I) →
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)
    (anchor : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I))
    (candidates : Finset (LocalCoordinateTaggedCandidate A initialCode)) : Prop :=
  ∀ candidate ∈ candidates,
    ∃ point : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
        (I := I),
      ProfiledOpenIndexedProcessTwoLocalFibreRel A strategy hwin basis
          anchor point ∧
        candidate = profiledOpenFixedCoordinateCandidateOf A strategy hwin
          basis initialCode control point

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Representation in one exact child fibre is downward closed. -/
theorem ProfiledOpenFixedRightChildFibreRepresented.mono
    (control : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
        (I := I) →
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)
    (anchor : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I))
    {large small : Finset (LocalCoordinateTaggedCandidate A initialCode)}
    (hrep : ProfiledOpenFixedRightChildFibreRepresented A strategy hwin basis
      initialCode control anchor large)
    (hsub : small ⊆ large) :
    ProfiledOpenFixedRightChildFibreRepresented A strategy hwin basis
      initialCode control anchor small := by
  intro candidate hcandidate
  exact hrep candidate (hsub hcandidate)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Process-two downward closure. -/
theorem ProfiledOpenFixedLeftChildFibreRepresented.mono
    (control : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
        (I := I) →
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)
    (anchor : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I))
    {large small : Finset (LocalCoordinateTaggedCandidate A initialCode)}
    (hrep : ProfiledOpenFixedLeftChildFibreRepresented A strategy hwin basis
      initialCode control anchor large)
    (hsub : small ⊆ large) :
    ProfiledOpenFixedLeftChildFibreRepresented A strategy hwin basis
      initialCode control anchor small := by
  intro candidate hcandidate
  exact hrep candidate (hsub hcandidate)

/-- Every represented process-one child set is homogeneous in the bank
coordinate process one must read. -/
theorem profiledOpenFixedRightChildFibreRepresented_homogeneous
    (control : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
        (I := I) →
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)
    (anchor : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I))
    (candidates : Finset (LocalCoordinateTaggedCandidate A initialCode))
    (hrep : ProfiledOpenFixedRightChildFibreRepresented A strategy hwin basis
      initialCode control anchor candidates) :
    ProfiledOpenFixedRightCoordinateHomogeneous A strategy hwin basis
      initialCode candidates := by
  intro left hleft _ _ right hright _ _
  obtain ⟨leftPoint, hleftRel, rfl⟩ := hrep left hleft
  obtain ⟨rightPoint, hrightRel, rfl⟩ := hrep right hright
  exact
    (profiledOpenFixedChildFamily_fst_eq_of_localFibre A strategy hwin basis
      initialCode control anchor leftPoint hleftRel).symm.trans
      (profiledOpenFixedChildFamily_fst_eq_of_localFibre A strategy hwin basis
        initialCode control anchor rightPoint hrightRel)

/-- Process-two mirror. -/
theorem profiledOpenFixedLeftChildFibreRepresented_homogeneous
    (control : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
        (I := I) →
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)
    (anchor : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I))
    (candidates : Finset (LocalCoordinateTaggedCandidate A initialCode))
    (hrep : ProfiledOpenFixedLeftChildFibreRepresented A strategy hwin basis
      initialCode control anchor candidates) :
    ProfiledOpenFixedLeftCoordinateHomogeneous A strategy hwin basis
      initialCode candidates := by
  intro left hleft _ _ right hright _ _
  obtain ⟨leftPoint, hleftRel, rfl⟩ := hrep left hleft
  obtain ⟨rightPoint, hrightRel, rfl⟩ := hrep right hright
  exact
    (profiledOpenFixedChildFamily_snd_eq_of_localFibre A strategy hwin basis
      initialCode control anchor leftPoint hleftRel).symm.trans
      (profiledOpenFixedChildFamily_snd_eq_of_localFibre A strategy hwin basis
        initialCode control anchor rightPoint hrightRel)

end

end DetParityAutomaton

end DistributedSynthesis
