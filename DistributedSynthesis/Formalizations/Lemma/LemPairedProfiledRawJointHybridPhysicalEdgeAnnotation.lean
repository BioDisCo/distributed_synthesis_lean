/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointCommonHybridSemanticTree
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointFinitePhysicalSiblingMove
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridCarriedParentLinkedAnnotation

/-!
# Finite physical annotations on whole-block hybrid edges

The whole-block hybrid tree chooses one literal raw family before the hidden
common/strict interpretation is resolved.  At that same semantic edge we can
extract the already proved finite sibling tables.  We retain both optional
orientations: a lane is `none` exactly when the corresponding semantic child
lane is absent.

This is deliberately an *edge* annotation.  After a strict transition the
one-sided child need not reconstruct the table from its public incidence code;
the parent installs the table selected from its one literal source.  The
annotation type is finite, although the hybrid direction contains whole block
histories.  No executable projection receives the graph, hierarchy side,
strict leader, or semantic history.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

/-- The finite operational datum retained across one hybrid edge.  A common
child normally carries both sibling tables; a one-sided child carries the
table of its live lane. -/
noncomputable abbrev ProfiledRawJointHybridPhysicalEdgeAnnotation :=
  Option (ProfiledRawJointRightPhysicalSiblingMove A) ×
    Option (ProfiledRawJointLeftPhysicalSiblingMove A)

noncomputable instance :
    Fintype (ProfiledRawJointHybridPhysicalEdgeAnnotation A) := by
  classical
  infer_instance

/-- Extract the finite process-one sibling table when the literal simultaneous
child has a live process-one member. -/
noncomputable def profiledRawJointRightPhysicalSiblingMoveOption
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    Option (ProfiledRawJointRightPhysicalSiblingMove A) := by
  classical
  exact if hmember : ∃ semanticMember,
      (family.semanticChild A direction).right () = some semanticMember then
    some (profiledRawJointRightPhysicalSiblingMoveOf A hwin family direction
      hmember.choose hmember.choose_spec)
  else none

/-- Process-two mirror. -/
noncomputable def profiledRawJointLeftPhysicalSiblingMoveOption
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    Option (ProfiledRawJointLeftPhysicalSiblingMove A) := by
  classical
  exact if hmember : ∃ semanticMember,
      (family.semanticChild A direction).left () = some semanticMember then
    some (profiledRawJointLeftPhysicalSiblingMoveOf A hwin family direction
      hmember.choose hmember.choose_spec)
  else none

/-- Both finite sibling tables selected from one literal family/direction
pair, before the hidden member is resolved. -/
noncomputable def profiledRawJointHybridPhysicalAnnotationOf
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridPhysicalEdgeAnnotation A :=
  (profiledRawJointRightPhysicalSiblingMoveOption A strategy hwin family
      direction,
    profiledRawJointLeftPhysicalSiblingMoveOption A strategy hwin family
      direction)

/-- A stored right table still has the exact semantic provenance from which
it was selected.  This is the elimination rule needed by later physical
carriers: the classical choice is made only while constructing the finite
annotation, never again at runtime. -/
theorem profiledRawJointRightPhysicalSiblingMoveOption_spec
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (hmove : profiledRawJointRightPhysicalSiblingMoveOption A strategy hwin
        family direction = some move) :
    ∃ semanticMember : ProcOnePairedEntryRep strategy × A.State,
      ∃ hmember : (family.semanticChild A direction).right () =
          some semanticMember,
        move = profiledRawJointRightPhysicalSiblingMoveOf A hwin family
          direction semanticMember hmember := by
  classical
  unfold profiledRawJointRightPhysicalSiblingMoveOption at hmove
  split at hmove
  next hex =>
    let semanticMember := hex.choose
    have hmember : (family.semanticChild A direction).right () =
        some semanticMember := by
      simpa [semanticMember] using hex.choose_spec
    refine ⟨semanticMember, hmember, ?_⟩
    simpa [semanticMember] using (Option.some.inj hmove).symm
  next => simp at hmove

/-- Left-table mirror of the provenance eliminator. -/
theorem profiledRawJointLeftPhysicalSiblingMoveOption_spec
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hmove : profiledRawJointLeftPhysicalSiblingMoveOption A strategy hwin
        family direction = some move) :
    ∃ semanticMember : ProcTwoPairedEntryRep strategy × A.State,
      ∃ hmember : (family.semanticChild A direction).left () =
          some semanticMember,
        move = profiledRawJointLeftPhysicalSiblingMoveOf A hwin family
          direction semanticMember hmember := by
  classical
  unfold profiledRawJointLeftPhysicalSiblingMoveOption at hmove
  split at hmove
  next hex =>
    let semanticMember := hex.choose
    have hmember : (family.semanticChild A direction).left () =
        some semanticMember := by
      simpa [semanticMember] using hex.choose_spec
    refine ⟨semanticMember, hmember, ?_⟩
    simpa [semanticMember] using (Option.some.inj hmove).symm
  next => simp at hmove

/-- Initial marker before a physical sibling table has been installed. -/
noncomputable def profiledRawJointHybridInitialPhysicalAnnotation :
    ProfiledRawJointHybridPhysicalEdgeAnnotation A :=
  (none, none)

/-- Install the finite tables belonging to the actual whole-block hybrid
edge.  The old annotation is intentionally ignored: this is the
replace-not-accumulate update. -/
noncomputable def profiledRawJointHybridPhysicalAnnotationAdvance
    (source : ProfiledRawJointHybridSemanticState A strategy)
    (_current : ProfiledRawJointHybridPhysicalEdgeAnnotation A)
    (direction : ProfiledRawJointHybridDirection
      (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridPhysicalEdgeAnnotation A :=
  match source, direction with
  | .common world, .simultaneous input =>
      profiledRawJointHybridPhysicalAnnotationOf A strategy hwin
        (profiledRawJointCommonWorldFamily A world)
        (profiledRawJointBothRestartDirection input)
  | .common world, .strict actual =>
      profiledRawJointHybridPhysicalAnnotationOf A strategy hwin
        (profiledRawJointCommonWorldFamily A world)
        (profiledRawJointCommonActualDirection actual).direction
  | .oneSided source, .strict actual =>
      profiledRawJointHybridPhysicalAnnotationOf A strategy hwin source.family
        actual.direction
  | _, _ => profiledRawJointHybridInitialPhysicalAnnotation A

@[simp] theorem profiledRawJointHybridPhysicalAnnotationAdvance_common_both
    (world : ProfiledRawJointCommonBaseWorld A strategy)
    (current : ProfiledRawJointHybridPhysicalEdgeAnnotation A)
    (input : In₁ × In₂) :
    profiledRawJointHybridPhysicalAnnotationAdvance A strategy hwin
        (.common world) current (.simultaneous input) =
      profiledRawJointHybridPhysicalAnnotationOf A strategy hwin
        (profiledRawJointCommonWorldFamily A world)
        (profiledRawJointBothRestartDirection input) :=
  rfl

@[simp] theorem profiledRawJointHybridPhysicalAnnotationAdvance_common_strict
    (world : ProfiledRawJointCommonBaseWorld A strategy)
    (current : ProfiledRawJointHybridPhysicalEdgeAnnotation A)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    profiledRawJointHybridPhysicalAnnotationAdvance A strategy hwin
        (.common world) current (.strict actual) =
      profiledRawJointHybridPhysicalAnnotationOf A strategy hwin
        (profiledRawJointCommonWorldFamily A world)
        (profiledRawJointCommonActualDirection actual).direction :=
  rfl

@[simp] theorem profiledRawJointHybridPhysicalAnnotationAdvance_oneSided_strict
    (source : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (current : ProfiledRawJointHybridPhysicalEdgeAnnotation A)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    profiledRawJointHybridPhysicalAnnotationAdvance A strategy hwin
        (.oneSided source) current (.strict actual) =
      profiledRawJointHybridPhysicalAnnotationOf A strategy hwin source.family
        actual.direction :=
  rfl

/-- Exact right-table projection.  It is the table extracted from this one
semantic occurrence, not from an incidence-code representative. -/
theorem profiledRawJointHybridPhysicalAnnotationOf_right
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember) :
    ∃ move : ProfiledRawJointRightPhysicalSiblingMove A,
      (profiledRawJointHybridPhysicalAnnotationOf A strategy hwin family
        direction).1 = some move := by
  classical
  let hex : ∃ member,
      family.leftSelectedChild A direction () = some member :=
    ⟨semanticMember, by simpa using hmember⟩
  refine ⟨profiledRawJointRightPhysicalSiblingMoveOf A hwin family direction
    hex.choose hex.choose_spec, ?_⟩
  simp only [profiledRawJointHybridPhysicalAnnotationOf,
    profiledRawJointRightPhysicalSiblingMoveOption,
    ProfiledRawJointSemanticFamily.semanticChild_right]
  rw [dif_pos hex]

/-- Exact left-table projection. -/
theorem profiledRawJointHybridPhysicalAnnotationOf_left
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember) :
    ∃ move : ProfiledRawJointLeftPhysicalSiblingMove A,
      (profiledRawJointHybridPhysicalAnnotationOf A strategy hwin family
        direction).2 = some move := by
  classical
  let hex : ∃ member,
      family.rightSelectedChild A direction () = some member :=
    ⟨semanticMember, by simpa using hmember⟩
  refine ⟨profiledRawJointLeftPhysicalSiblingMoveOf A hwin family direction
    hex.choose hex.choose_spec, ?_⟩
  simp only [profiledRawJointHybridPhysicalAnnotationOf,
    profiledRawJointLeftPhysicalSiblingMoveOption,
    ProfiledRawJointSemanticFamily.semanticChild_left]
  rw [dif_pos hex]

/-! ## The strict child root is already in the carried table -/

/-- After an actual right block, the source descriptor of the installed left
table is literally the live left root of the one-sided semantic child.  This
is the root-lineage equation needed at the next physical cut; no row, side,
or leader flag is missing from the finite annotation. -/
theorem profiledRawJointHybridPhysicalAnnotationOf_rightActual_liveRoot
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember) :
    ∃ move : ProfiledRawJointLeftPhysicalSiblingMove A,
      (profiledRawJointHybridPhysicalAnnotationOf A strategy hwin family
          direction).2 = some move ∧
        profiledRawJointOneSidedCurrentSlots A .left
            ((family.rightActualChild A direction).incidenceCode A) () =
          some (.inr move.1.source) := by
  classical
  obtain ⟨move, hmove⟩ :=
    profiledRawJointHybridPhysicalAnnotationOf_left A strategy hwin family
      direction semanticMember hmember
  obtain ⟨member, hmember', rfl⟩ :=
    profiledRawJointLeftPhysicalSiblingMoveOption_spec A strategy hwin family
      direction move (by simpa [profiledRawJointHybridPhysicalAnnotationOf]
        using hmove)
  refine ⟨_, hmove, ?_⟩
  simp only [profiledRawJointOneSidedCurrentSlots,
    ProfiledRawJointSemanticFamily.incidenceCode,
    ProfiledRawJointSemanticFamily.rightActualChild_left,
    ProfiledRawJointSemanticFamily.code]
  rw [← ProfiledRawJointSemanticFamily.semanticChild_left]
  rw [hmember']
  rfl

/-- Mirror: an actual left block installs a right table whose descriptor
source is exactly the live right root of its one-sided child. -/
theorem profiledRawJointHybridPhysicalAnnotationOf_leftActual_liveRoot
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember) :
    ∃ move : ProfiledRawJointRightPhysicalSiblingMove A,
      (profiledRawJointHybridPhysicalAnnotationOf A strategy hwin family
          direction).1 = some move ∧
        profiledRawJointOneSidedCurrentSlots A .right
            ((family.leftActualChild A direction).incidenceCode A) () =
          some (.inl move.1.source) := by
  classical
  obtain ⟨move, hmove⟩ :=
    profiledRawJointHybridPhysicalAnnotationOf_right A strategy hwin family
      direction semanticMember hmember
  obtain ⟨member, hmember', rfl⟩ :=
    profiledRawJointRightPhysicalSiblingMoveOption_spec A strategy hwin family
      direction move (by simpa [profiledRawJointHybridPhysicalAnnotationOf]
        using hmove)
  refine ⟨_, hmove, ?_⟩
  simp only [profiledRawJointOneSidedCurrentSlots,
    ProfiledRawJointSemanticFamily.incidenceCode,
    ProfiledRawJointSemanticFamily.leftActualChild_right,
    ProfiledRawJointSemanticFamily.code]
  rw [← ProfiledRawJointSemanticFamily.semanticChild_right]
  rw [hmember']
  rfl

/-- Read the proof-side live root selected by a strict edge annotation.  The
actual side chooses which already-carried table is active; the value itself
contains no side bit and both endpoint controllers were fixed before this
proof-side projection. -/
def profiledRawJointHybridStrictPhysicalCutRoot
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (annotation : ProfiledRawJointHybridPhysicalEdgeAnnotation A) :
    Option (ProfiledRawJointThreadRoot A) :=
  match actual.side with
  | .right => annotation.2.map fun move ↦ .inr move.1.source
  | .left => annotation.1.map fun move ↦ .inl move.1.source

/-- Complete right-block cut equation, including the inactive case: reading
the carried left table gives exactly the current live-root option in the
actual one-sided semantic child. -/
theorem profiledRawJointHybridPhysicalAnnotationOf_rightActual_root_eq
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    (profiledRawJointHybridPhysicalAnnotationOf A strategy hwin family
        direction).2.map (fun move ↦
          (.inr move.1.source : ProfiledRawJointThreadRoot A)) =
      profiledRawJointOneSidedCurrentSlots A .left
        ((family.rightActualChild A direction).incidenceCode A) () := by
  classical
  cases hmember : (family.semanticChild A direction).left () with
  | none =>
      have hselected : family.rightSelectedChild A direction () = none := by
        simpa using hmember
      have hoption :
          (profiledRawJointHybridPhysicalAnnotationOf A strategy hwin family
            direction).2 = none := by
        cases hmove :
            (profiledRawJointHybridPhysicalAnnotationOf A strategy hwin family
              direction).2 with
        | none => rfl
        | some move =>
            obtain ⟨member, hmember', _⟩ :=
              profiledRawJointLeftPhysicalSiblingMoveOption_spec A strategy
                hwin family direction move (by
                  simpa [profiledRawJointHybridPhysicalAnnotationOf]
                    using hmove)
            rw [hmember] at hmember'
            contradiction
      simp [hoption, profiledRawJointOneSidedCurrentSlots,
        ProfiledRawJointSemanticFamily.incidenceCode,
        ProfiledRawJointSemanticFamily.code,
        ProfiledRawJointSemanticFamily.rightActualChild, hselected]
  | some semanticMember =>
      obtain ⟨move, hmove, hroot⟩ :=
        profiledRawJointHybridPhysicalAnnotationOf_rightActual_liveRoot A
          strategy hwin family direction semanticMember hmember
      rw [hmove]
      simpa using hroot.symm

/-- Complete left-block mirror. -/
theorem profiledRawJointHybridPhysicalAnnotationOf_leftActual_root_eq
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    (profiledRawJointHybridPhysicalAnnotationOf A strategy hwin family
        direction).1.map (fun move ↦
          (.inl move.1.source : ProfiledRawJointThreadRoot A)) =
      profiledRawJointOneSidedCurrentSlots A .right
        ((family.leftActualChild A direction).incidenceCode A) () := by
  classical
  cases hmember : (family.semanticChild A direction).right () with
  | none =>
      have hselected : family.leftSelectedChild A direction () = none := by
        simpa using hmember
      have hoption :
          (profiledRawJointHybridPhysicalAnnotationOf A strategy hwin family
            direction).1 = none := by
        cases hmove :
            (profiledRawJointHybridPhysicalAnnotationOf A strategy hwin family
              direction).1 with
        | none => rfl
        | some move =>
            obtain ⟨member, hmember', _⟩ :=
              profiledRawJointRightPhysicalSiblingMoveOption_spec A strategy
                hwin family direction move (by
                  simpa [profiledRawJointHybridPhysicalAnnotationOf]
                    using hmove)
            rw [hmember] at hmember'
            contradiction
      simp [hoption, profiledRawJointOneSidedCurrentSlots,
        ProfiledRawJointSemanticFamily.incidenceCode,
        ProfiledRawJointSemanticFamily.code,
        ProfiledRawJointSemanticFamily.leftActualChild, hselected]
  | some semanticMember =>
      obtain ⟨move, hmove, hroot⟩ :=
        profiledRawJointHybridPhysicalAnnotationOf_leftActual_liveRoot A
          strategy hwin family direction semanticMember hmember
      rw [hmove]
      simpa using hroot.symm

/-- The root option present in an exact hybrid semantic state.  Strict edges
always land in the one-sided constructor at real nodes; the total dead mode
is represented by `none`. -/
def ProfiledRawJointHybridSemanticState.strictLiveRoot
    (source : ProfiledRawJointHybridSemanticState A strategy)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    Option (ProfiledRawJointThreadRoot A) :=
  match source.step A (.strict actual) with
  | .oneSided child =>
      profiledRawJointOneSidedCurrentSlots A actual.side.other (child.code A) ()
  | _ => none

/-- **Strict-cut bridge.**  On every whole-block strict edge, reading the
table installed by the one global carried policy gives exactly the canonical
live-root option of the literal semantic child.  This equality is total, so
it also handles branches whose selected lane is absent. -/
theorem profiledRawJointHybridPhysicalAnnotationAdvance_strict_root_eq
    (source : ProfiledRawJointHybridSemanticState A strategy)
    (current : ProfiledRawJointHybridPhysicalEdgeAnnotation A)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    profiledRawJointHybridStrictPhysicalCutRoot A actual
        (profiledRawJointHybridPhysicalAnnotationAdvance A strategy hwin
          source current (.strict actual)) =
      source.strictLiveRoot A strategy actual := by
  cases source with
  | common world =>
      cases hside : actual.side with
      | right =>
          simpa [profiledRawJointHybridStrictPhysicalCutRoot,
            ProfiledRawJointHybridSemanticState.strictLiveRoot,
            ProfiledRawJointHybridSemanticState.step,
            profiledRawJointCommonExitState, hside] using
            profiledRawJointHybridPhysicalAnnotationOf_rightActual_root_eq A
              strategy hwin (profiledRawJointCommonWorldFamily A world)
                (profiledRawJointCommonActualDirection actual).direction
      | left =>
          simpa [profiledRawJointHybridStrictPhysicalCutRoot,
            ProfiledRawJointHybridSemanticState.strictLiveRoot,
            ProfiledRawJointHybridSemanticState.step,
            profiledRawJointCommonExitState, hside] using
            profiledRawJointHybridPhysicalAnnotationOf_leftActual_root_eq A
              strategy hwin (profiledRawJointCommonWorldFamily A world)
                (profiledRawJointCommonActualDirection actual).direction
  | oneSided state =>
      cases hside : actual.side with
      | right =>
          simpa [profiledRawJointHybridStrictPhysicalCutRoot,
            ProfiledRawJointHybridSemanticState.strictLiveRoot,
            ProfiledRawJointHybridSemanticState.step,
            ProfiledRawJointOneSidedSemanticState.step, hside] using
            profiledRawJointHybridPhysicalAnnotationOf_rightActual_root_eq A
              strategy hwin state.family actual.direction
      | left =>
          simpa [profiledRawJointHybridStrictPhysicalCutRoot,
            ProfiledRawJointHybridSemanticState.strictLiveRoot,
            ProfiledRawJointHybridSemanticState.step,
            ProfiledRawJointOneSidedSemanticState.step, hside] using
            profiledRawJointHybridPhysicalAnnotationOf_leftActual_root_eq A
              strategy hwin state.family actual.direction
  | dead =>
      cases hside : actual.side <;>
        simp [profiledRawJointHybridStrictPhysicalCutRoot,
          profiledRawJointHybridPhysicalAnnotationAdvance,
          profiledRawJointHybridInitialPhysicalAnnotation,
          ProfiledRawJointHybridSemanticState.strictLiveRoot,
          ProfiledRawJointHybridSemanticState.step, hside]

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
/-- Semantic normalization used by the carried-policy alignment: the
strict-root option is exactly what the tagged child code exposes to the
canonical alternating-lineage monitor. -/
theorem ProfiledRawJointHybridSemanticState.strictLiveRoot_eq_currentSlots
    (source : ProfiledRawJointHybridSemanticState A strategy)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    source.strictLiveRoot A strategy actual =
      profiledRawJointHybridCurrentSlots A actual.side.other
        ((source.step A (.strict actual)).code A) () := by
  cases source <;> rfl

/-- The retained right table cannot distinguish its simultaneous and
strict-left explanations, at every already reached sender control. -/
theorem profiledRawJointHybridPhysicalAnnotationOf_right_sender_eq
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (word : List In₁) :
    let move := profiledRawJointRightPhysicalSiblingMoveOf A hwin family
      direction semanticMember hmember
    ((move.memberController A false).labeledTree word).1 =
      ((move.memberController A true).labeledTree word).1 := by
  dsimp only
  rfl

/-- Left-table mirror. -/
theorem profiledRawJointHybridPhysicalAnnotationOf_left_sender_eq
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (word : List In₂) :
    let move := profiledRawJointLeftPhysicalSiblingMoveOf A hwin family
      direction semanticMember hmember
    ((move.memberController A false).labeledTree word).1 =
      ((move.memberController A true).labeledTree word).1 := by
  dsimp only
  rfl

/-! ## One unconditional carried hybrid policy -/

/-- The concrete one-global policy obtained by installing the physical edge
annotation before the single whole-block rationalization. -/
noncomputable abbrev ProfiledRawJointHybridPhysicalCarriedRationalPolicy
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridCarriedParentLinkedRationalPolicy A strategy initial
    (profiledRawJointHybridInitialPhysicalAnnotation A)
    (profiledRawJointHybridPhysicalAnnotationAdvance A strategy hwin)

noncomputable abbrev ProfiledRawJointHybridPhysicalCarriedPolicyState
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridCarriedParentLinkedPolicyState A strategy initial
    (profiledRawJointHybridInitialPhysicalAnnotation A)
    (profiledRawJointHybridPhysicalAnnotationAdvance A strategy hwin)

abbrev ProfiledRawJointHybridPhysicalCarriedReachable
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (policy : ProfiledRawJointHybridPhysicalCarriedRationalPolicy A strategy
      hwin initial)
    (state : ProfiledRawJointHybridPhysicalCarriedPolicyState A strategy hwin
      initial) : Prop :=
  ProfiledRawJointHybridCarriedParentLinkedReachable A strategy initial
    (profiledRawJointHybridInitialPhysicalAnnotation A)
    (profiledRawJointHybridPhysicalAnnotationAdvance A strategy hwin)
    policy state

/-- A winning distributed strategy yields the one finite policy with physical
sibling-table lineage, without a rational-run-basis or compatibility premise. -/
theorem nonempty_profiledRawJointHybridPhysicalCarriedRationalPolicy
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :
    Nonempty
      (ProfiledRawJointHybridPhysicalCarriedRationalPolicy A strategy hwin
        initial) :=
  nonempty_profiledRawJointHybridCarriedParentLinkedRationalPolicy A strategy
    hwin initial (profiledRawJointHybridInitialPhysicalAnnotation A)
      (profiledRawJointHybridPhysicalAnnotationAdvance A strategy hwin)

/-- Concrete strong inversion.  At every reachable state one literal hybrid
source supplies the current raw lambda family and the complete table of exact
finite physical annotations installed at all whole-block children. -/
theorem exists_profiledRawJointHybridPhysicalCarriedSemanticSource
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (policy : ProfiledRawJointHybridPhysicalCarriedRationalPolicy A strategy
      hwin initial)
    (state : ProfiledRawJointHybridPhysicalCarriedPolicyState A strategy hwin
      initial)
    (hreachable : ProfiledRawJointHybridPhysicalCarriedReachable A strategy
      hwin initial policy state) :
    ∃ move : SourceFreeBeliefParentLinkedMove
        (Direction := ProfiledRawJointHybridDirection
          (In₁ := In₁) (In₂ := In₂))
        (Move := ProfiledRawJointHybridMove A)
        (Annotation := ProfiledRawJointHybridPhysicalEdgeAnnotation A),
      ∃ source : ProfiledRawJointHybridSemanticState A strategy,
        source.code A = state.1.1 ∧
          source.move A = move.1 ∧
          (∀ direction,
            profiledRawJointHybridPhysicalAnnotationAdvance A strategy hwin
                source state.1.2 direction =
              move.2 direction) ∧
          ∀ direction : ProfiledRawJointHybridDirection
              (In₁ := In₁) (In₂ := In₂),
            policy.successor state
                (sourceFreeBeliefParentLinkedNext
                  (profiledRawJointHybridNext A) state.1 move direction) =
              let childCode := sourceFreeBeliefParentLinkedNext
                (profiledRawJointHybridNext A) state.1 move direction
              (childCode,
                (sourceFreeBeliefParentLinkedCodeParityDPA
                  (Annotation :=
                    ProfiledRawJointHybridPhysicalEdgeAnnotation A)
                  (profiledRawJointHybridCodeParityDPA A
                    (.common ((profiledRawJointCommonWorldFamily A initial
                      ).incidenceCode A)))).step state.2 childCode) := by
  exact exists_profiledRawJointHybridCarriedParentLinkedSemanticSource A
    strategy initial (profiledRawJointHybridInitialPhysicalAnnotation A)
      (profiledRawJointHybridPhysicalAnnotationAdvance A strategy hwin)
      policy state hreachable

/-- **One-step hidden-lineage alignment.**  At a reachable state of the one
global carried policy, follow any strict linked child chosen by the explaining
parent move.  The root read from that child's installed physical table is
exactly the live root read by the canonical alternating-lineage monitor from
the child's bare hybrid code.

This is a state/root equality only.  It does not compare the universal-DPA
policy-state priority with a physical priority, and it does not choose a new
ordinary policy at the cut. -/
theorem
    exists_profiledRawJointHybridPhysicalCarriedStrictSuccessorRootAlignment
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (policy : ProfiledRawJointHybridPhysicalCarriedRationalPolicy A strategy
      hwin initial)
    (state : ProfiledRawJointHybridPhysicalCarriedPolicyState A strategy hwin
      initial)
    (hreachable : ProfiledRawJointHybridPhysicalCarriedReachable A strategy
      hwin initial policy state)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    ∃ move : SourceFreeBeliefParentLinkedMove
        (Direction := ProfiledRawJointHybridDirection
          (In₁ := In₁) (In₂ := In₂))
        (Move := ProfiledRawJointHybridMove A)
        (Annotation := ProfiledRawJointHybridPhysicalEdgeAnnotation A),
      ∃ source : ProfiledRawJointHybridSemanticState A strategy,
        source.code A = state.1.1 ∧
          source.move A = move.1 ∧
          let childCode := sourceFreeBeliefParentLinkedNext
            (profiledRawJointHybridNext A) state.1 move (.strict actual)
          let childState := policy.successor state childCode
          profiledRawJointHybridStrictPhysicalCutRoot A actual childState.1.2 =
            profiledRawJointHybridCurrentSlots A actual.side.other
              childState.1.1 () := by
  rcases
      exists_profiledRawJointHybridPhysicalCarriedSemanticSource A strategy
        hwin initial policy state hreachable with
    ⟨move, source, hcode, hmove, hchildren, hsuccessor⟩
  refine ⟨move, source, hcode, hmove, ?_⟩
  dsimp only
  rw [hsuccessor (.strict actual)]
  change
    profiledRawJointHybridStrictPhysicalCutRoot A actual
        (move.2 (.strict actual)) =
      profiledRawJointHybridCurrentSlots A actual.side.other
        (profiledRawJointHybridNext A state.1.1 move.1 (.strict actual)) ()
  rw [← hchildren (.strict actual)]
  rw [profiledRawJointHybridPhysicalAnnotationAdvance_strict_root_eq A
    strategy hwin source state.1.2 actual]
  rw [source.strictLiveRoot_eq_currentSlots A strategy actual]
  congr 2
  exact source.step_code A (.strict actual) |>.trans (by rw [hcode, hmove])

end

end DetParityAutomaton

end DistributedSynthesis
