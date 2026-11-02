/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenFixedSideClassTag
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenFixedSidewiseBankAlphabet

/-!
# Fixed sticky classes for the sidewise pinned-bank alphabet

This file combines two independent finite constructions:

* `IndexedLineageLocalClassTag` is the root-free row assignment of one
  generated equality class;
* `ProfiledOpenFixedRightPinnedValue` and its left mirror are literal
  one-side parent-controller identities in strategy-independent finite types.

A process-one child is generated from the left parent family, so its fixed
class is `(left pinned parent value, left row-slot class)`.  A process-two
child uses the symmetric right pair.  This cross assignment is proof-side
process identity, not a dynamic orientation or leader test.

The final `ProfiledOpenFixedStickySideClassSound` predicate is the exact
remaining semantic obligation for cross-parent iteration.  It does not claim
that an old rational move factors the original raw sender: state-controlled
Rabin extraction preserves winning and receiver-table provenance, not the
literal raw sender labels.
-/

namespace DistributedSynthesis

universe g i u v x y s f

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

variable (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))

/-! ## The two fixed class alphabets -/

/-- A process-one successor class retains the left parent controller that
generated it and the selected left equality class. -/
noncomputable abbrev ProfiledOpenFixedProcessOneSideClass :=
  StickyIndexedLineageLocalClassTag
    (ProfiledOpenFixedLeftPinnedValue A initialCode) I

/-- A process-two successor class retains the right parent controller. -/
noncomputable abbrev ProfiledOpenFixedProcessTwoSideClass :=
  StickyIndexedLineageLocalClassTag
    (ProfiledOpenFixedRightPinnedValue A initialCode) I

noncomputable instance : Fintype
    (ProfiledOpenFixedProcessOneSideClass A initialCode) := by
  classical
  infer_instance

noncomputable instance : Fintype
    (ProfiledOpenFixedProcessTwoSideClass A initialCode) := by
  classical
  infer_instance

/-- The concrete fixed bank at the two sticky class alphabets. -/
noncomputable abbrev ProfiledOpenFixedStickySidewisePinnedBank :=
  ProfiledOpenFixedSidewisePinnedBank A initialCode
    (ProfiledOpenFixedProcessOneSideClass A initialCode)
    (ProfiledOpenFixedProcessTwoSideClass A initialCode)

set_option synthInstance.maxHeartbeats 800000 in
noncomputable instance : Fintype
    (ProfiledOpenFixedStickySidewisePinnedBank A initialCode) := by
  classical
  infer_instance

/-! ## Tagging one generated transition -/

/-- Fixed process-one class selected by one literal paired pinned parent
move and one indexed proof-side direction. -/
noncomputable def profiledOpenFixedProcessOneSideClassOf
    (parent : ProfiledOpenHiddenDescriptorPairedPinnedFamilyMove A
      initialCode)
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    ProfiledOpenFixedProcessOneSideClass A initialCode :=
  stickyIndexedLineageLocalClassTag
    (parent.leftValue A initialCode) code.leftPattern direction.leftPivot

/-- Fixed process-two mirror. -/
noncomputable def profiledOpenFixedProcessTwoSideClassOf
    (parent : ProfiledOpenHiddenDescriptorPairedPinnedFamilyMove A
      initialCode)
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    ProfiledOpenFixedProcessTwoSideClass A initialCode :=
  stickyIndexedLineageLocalClassTag
    (parent.rightValue A initialCode) code.rightPattern direction.rightPivot

/-- Both independent fixed classes of one transition. -/
noncomputable def profiledOpenFixedSideClassesOf
    (parent : ProfiledOpenHiddenDescriptorPairedPinnedFamilyMove A
      initialCode)
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    ProfiledOpenFixedProcessOneSideClass A initialCode ×
      ProfiledOpenFixedProcessTwoSideClass A initialCode :=
  (profiledOpenFixedProcessOneSideClassOf A initialCode parent code direction,
    profiledOpenFixedProcessTwoSideClassOf A initialCode parent code direction)

/-- Attach the fixed side classes to an arbitrary old full family payload. -/
noncomputable def profiledOpenFixedSidewiseTaggedFamilyOf
    (parent : ProfiledOpenHiddenDescriptorPairedPinnedFamilyMove A
      initialCode)
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (family : Type f) (value : family) :
    SidewiseTaggedFamily
      (ProfiledOpenFixedProcessOneSideClass A initialCode)
      (ProfiledOpenFixedProcessTwoSideClass A initialCode) family :=
  (profiledOpenFixedSideClassesOf A initialCode parent code direction, value)

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledOpenFixedSideClassesOf_one_parent
    (parent : ProfiledOpenHiddenDescriptorPairedPinnedFamilyMove A
      initialCode)
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    (profiledOpenFixedSideClassesOf A initialCode parent code direction).1.1 =
      parent.leftValue A initialCode :=
  rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledOpenFixedSideClassesOf_two_parent
    (parent : ProfiledOpenHiddenDescriptorPairedPinnedFamilyMove A
      initialCode)
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    (profiledOpenFixedSideClassesOf A initialCode parent code direction).2.1 =
      parent.rightValue A initialCode :=
  rfl

/-! ## Exact cross-parent semantic boundary -/

variable {Global : Type g}

/-- The fixed left parent identity and row class determine the process-one
semantic class on the global candidates under consideration. -/
def ProfiledOpenFixedProcessOneStickyClassSound
    (parent : Global →
      ProfiledOpenHiddenDescriptorPairedPinnedFamilyMove A initialCode)
    (code : Global → ProfiledOpenIndexedBiBeliefCode A (I := I))
    (direction : Global → ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (RelOne : Global → Global → Prop) : Prop :=
  StickyParentDeterminesLocalClass
    (fun candidate ↦ (parent candidate).leftValue A initialCode)
    (fun candidate ↦ (code candidate).leftPattern)
    (fun candidate ↦ (direction candidate).leftPivot)
    RelOne

/-- Right-parent/process-two mirror. -/
def ProfiledOpenFixedProcessTwoStickyClassSound
    (parent : Global →
      ProfiledOpenHiddenDescriptorPairedPinnedFamilyMove A initialCode)
    (code : Global → ProfiledOpenIndexedBiBeliefCode A (I := I))
    (direction : Global → ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (RelTwo : Global → Global → Prop) : Prop :=
  StickyParentDeterminesLocalClass
    (fun candidate ↦ (parent candidate).rightValue A initialCode)
    (fun candidate ↦ (code candidate).rightPattern)
    (fun candidate ↦ (direction candidate).rightPivot)
    RelTwo

/-- The exact two-sided semantic premise needed to use the fixed tags as the
`OneClass`/`TwoClass` parameters of the fibre bank across an iterated
candidate set. -/
def ProfiledOpenFixedStickySideClassSound
    (parent : Global →
      ProfiledOpenHiddenDescriptorPairedPinnedFamilyMove A initialCode)
    (code : Global → ProfiledOpenIndexedBiBeliefCode A (I := I))
    (direction : Global → ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (RelOne RelTwo : Global → Global → Prop) : Prop :=
  ProfiledOpenFixedProcessOneStickyClassSound A initialCode parent code
      direction RelOne ∧
    ProfiledOpenFixedProcessTwoStickyClassSound A initialCode parent code
      direction RelTwo

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Under the named soundness premise, equal concrete process-one tags imply
the process-one semantic relation. -/
theorem profiledOpenFixedProcessOneRel_of_class_eq
    (parent : Global →
      ProfiledOpenHiddenDescriptorPairedPinnedFamilyMove A initialCode)
    (code : Global → ProfiledOpenIndexedBiBeliefCode A (I := I))
    (direction : Global → ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (RelOne : Global → Global → Prop)
    (hsound : ProfiledOpenFixedProcessOneStickyClassSound A initialCode
      parent code direction RelOne)
    {left right : Global}
    (hclass :
      profiledOpenFixedProcessOneSideClassOf A initialCode (parent left)
          (code left) (direction left) =
        profiledOpenFixedProcessOneSideClassOf A initialCode (parent right)
          (code right) (direction right)) :
    RelOne left right := by
  exact rel_of_stickyIndexedLineageLocalClassTag_eq
    (fun candidate ↦ (parent candidate).leftValue A initialCode)
    (fun candidate ↦ (code candidate).leftPattern)
    (fun candidate ↦ (direction candidate).leftPivot)
    RelOne hsound hclass

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Process-two mirror. -/
theorem profiledOpenFixedProcessTwoRel_of_class_eq
    (parent : Global →
      ProfiledOpenHiddenDescriptorPairedPinnedFamilyMove A initialCode)
    (code : Global → ProfiledOpenIndexedBiBeliefCode A (I := I))
    (direction : Global → ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (RelTwo : Global → Global → Prop)
    (hsound : ProfiledOpenFixedProcessTwoStickyClassSound A initialCode
      parent code direction RelTwo)
    {left right : Global}
    (hclass :
      profiledOpenFixedProcessTwoSideClassOf A initialCode (parent left)
          (code left) (direction left) =
        profiledOpenFixedProcessTwoSideClassOf A initialCode (parent right)
          (code right) (direction right)) :
    RelTwo left right := by
  exact rel_of_stickyIndexedLineageLocalClassTag_eq
    (fun candidate ↦ (parent candidate).rightValue A initialCode)
    (fun candidate ↦ (code candidate).rightPattern)
    (fun candidate ↦ (direction candidate).rightPivot)
    RelTwo hsound hclass

end

end DetParityAutomaton

end DistributedSynthesis
