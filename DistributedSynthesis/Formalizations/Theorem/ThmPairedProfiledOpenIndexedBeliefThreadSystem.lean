/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemCodedAlternatingIndexedLineageThreadSystem
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenIndexedBeliefNode

/-!
# Two-shadow thread monitor for indexed open belief nodes

This file instantiates the generic coded alternating-lineage monitor with the
two finite shadow families of `ProfiledOpenIndexedBiBeliefCode`.  Its public
alphabet is exactly `Move × Direction`.  The finite monitor state retains the
current belief code and a hidden objective coordinate consisting of one side,
one persistent lineage, and its current root.

The hidden side is not an observation or a strict-leader flag.  It is chosen
only by the universal thread resolution at the first step.  Subsequent steps
ignore all resolutions, preserve the selected lineage, and alternate the
right and left shadows.  Thus neither process is asked to know which side is
currently the informed or strict-leading side.
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
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-! ## Exact model-to-generic wiring -/

/-- The ordered root slots currently carried by one of the two shadows. -/
def profiledOpenIndexedBiBeliefCurrentSlots
    (side : IndexedLineageSide)
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I)) :
    I → Option (ProfiledOpenClassifiedAnchor A) :=
  match side with
  | .right => code.rightSlots
  | .left => code.leftSlots

omit [Fintype I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem profiledOpenIndexedBiBeliefCurrentSlots_right
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I)) :
    profiledOpenIndexedBiBeliefCurrentSlots A .right code = code.rightSlots :=
  rfl

omit [Fintype I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem profiledOpenIndexedBiBeliefCurrentSlots_left
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I)) :
    profiledOpenIndexedBiBeliefCurrentSlots A .left code = code.leftSlots :=
  rfl

/-- The pattern-derived successor code for the selected shadow. -/
noncomputable def profiledOpenIndexedBiBeliefChildCode
    (side : IndexedLineageSide)
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    IndexedLineageChildCode I (ProfiledOpenClassifiedAnchor A) :=
  match side with
  | .right => profiledOpenIndexedRightChildCode A code move direction
  | .left => profiledOpenIndexedLeftChildCode A code move direction

omit [Fintype I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledOpenIndexedBiBeliefChildCode_right
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    profiledOpenIndexedBiBeliefChildCode A .right code move direction =
      profiledOpenIndexedRightChildCode A code move direction :=
  rfl

omit [Fintype I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledOpenIndexedBiBeliefChildCode_left
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    profiledOpenIndexedBiBeliefChildCode A .left code move direction =
      profiledOpenIndexedLeftChildCode A code move direction :=
  rfl

/-! ## Concrete finite thread system -/

/-- The finite two-shadow monitor for one initial indexed belief code.  Its
alphabet contains no side or lineage coordinate. -/
noncomputable def profiledOpenIndexedBiBeliefThreadSystem
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)) :
    FiniteThreadSystem
      (ProfiledOpenIndexedBiBeliefMove A ×
        ProfiledOpenIndexedBiBeliefDirection
          (I := I) (In₁ := In₁) (In₂ := In₂)) :=
  codedAlternatingIndexedLineageThreadSystem initialCode
    (profiledOpenIndexedBiBeliefNext A)
    (profiledOpenIndexedBiBeliefCurrentSlots A)
    (profiledOpenIndexedBiBeliefChildCode A)
    (profiledOpenIndexedRootPriority A)

/-- Canonical evolution of one initially selected side and one persistent
lineage.  The generic transition alternates the side after every live step. -/
noncomputable def profiledOpenIndexedBiBeliefThreadRun
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (word : OmegaWord
      (ProfiledOpenIndexedBiBeliefMove A ×
        ProfiledOpenIndexedBiBeliefDirection
          (I := I) (In₁ := In₁) (In₂ := In₂)))
    (initialSide : IndexedLineageSide) (lineage : I) :=
  codedAlternatingIndexedLineageRun initialCode
    (profiledOpenIndexedBiBeliefNext A)
    (profiledOpenIndexedBiBeliefCurrentSlots A)
    (profiledOpenIndexedBiBeliefChildCode A)
    word initialSide lineage

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem profiledOpenIndexedBiBeliefThreadSystem_initial
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)) :
    (profiledOpenIndexedBiBeliefThreadSystem A initialCode).initial =
      (initialCode,
        (AlternatingIndexedLineageThreadState.initial :
          AlternatingIndexedLineageThreadState I
            (ProfiledOpenClassifiedAnchor A))) :=
  rfl

/-- A present right slot follows the right child code and enters the left
shadow, while retaining the selected lineage. -/
theorem profiledOpenIndexedBiBeliefThreadStep_initial_right_of
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (lineage : I) (root child : ProfiledOpenClassifiedAnchor A)
    (row : PairedEntryRow)
    (hcurrent : initialCode.rightSlots lineage = some root)
    (hchild : profiledOpenIndexedRightChildCode A initialCode move direction
      lineage = some (row, child)) :
    (profiledOpenIndexedBiBeliefThreadSystem A initialCode).step
        (initialCode, .initial) (move, direction) (.right, lineage) =
      (profiledOpenIndexedBiBeliefNext A initialCode move direction,
        .live .left lineage child) := by
  exact codedAlternatingIndexedLineageStep_initial_of
    (profiledOpenIndexedBiBeliefNext A)
    (profiledOpenIndexedBiBeliefCurrentSlots A)
    (profiledOpenIndexedBiBeliefChildCode A)
    initialCode move direction .right lineage root child row hcurrent hchild

/-- Left-to-right mirror of the initial transition. -/
theorem profiledOpenIndexedBiBeliefThreadStep_initial_left_of
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (lineage : I) (root child : ProfiledOpenClassifiedAnchor A)
    (row : PairedEntryRow)
    (hcurrent : initialCode.leftSlots lineage = some root)
    (hchild : profiledOpenIndexedLeftChildCode A initialCode move direction
      lineage = some (row, child)) :
    (profiledOpenIndexedBiBeliefThreadSystem A initialCode).step
        (initialCode, .initial) (move, direction) (.left, lineage) =
      (profiledOpenIndexedBiBeliefNext A initialCode move direction,
        .live .right lineage child) := by
  exact codedAlternatingIndexedLineageStep_initial_of
    (profiledOpenIndexedBiBeliefNext A)
    (profiledOpenIndexedBiBeliefCurrentSlots A)
    (profiledOpenIndexedBiBeliefChildCode A)
    initialCode move direction .left lineage root child row hcurrent hchild

/-- A live right shadow ignores the new resolution, keeps its lineage, and
enters the left shadow. -/
theorem profiledOpenIndexedBiBeliefThreadStep_live_right_of
    (initialCode code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (lineage : I) (root child : ProfiledOpenClassifiedAnchor A)
    (row : PairedEntryRow)
    (resolution : IndexedLineageSide × I)
    (hcurrent : code.rightSlots lineage = some root)
    (hchild : profiledOpenIndexedRightChildCode A code move direction lineage =
      some (row, child)) :
    (profiledOpenIndexedBiBeliefThreadSystem A initialCode).step
        (code, .live .right lineage root) (move, direction) resolution =
      (profiledOpenIndexedBiBeliefNext A code move direction,
        .live .left lineage child) := by
  exact codedAlternatingIndexedLineageStep_live_of
    (profiledOpenIndexedBiBeliefNext A)
    (profiledOpenIndexedBiBeliefCurrentSlots A)
    (profiledOpenIndexedBiBeliefChildCode A)
    code move direction .right lineage root child row resolution hcurrent hchild

/-- A live left shadow ignores the new resolution, keeps its lineage, and
enters the right shadow. -/
theorem profiledOpenIndexedBiBeliefThreadStep_live_left_of
    (initialCode code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (lineage : I) (root child : ProfiledOpenClassifiedAnchor A)
    (row : PairedEntryRow)
    (resolution : IndexedLineageSide × I)
    (hcurrent : code.leftSlots lineage = some root)
    (hchild : profiledOpenIndexedLeftChildCode A code move direction lineage =
      some (row, child)) :
    (profiledOpenIndexedBiBeliefThreadSystem A initialCode).step
        (code, .live .left lineage root) (move, direction) resolution =
      (profiledOpenIndexedBiBeliefNext A code move direction,
        .live .right lineage child) := by
  exact codedAlternatingIndexedLineageStep_live_of
    (profiledOpenIndexedBiBeliefNext A)
    (profiledOpenIndexedBiBeliefCurrentSlots A)
    (profiledOpenIndexedBiBeliefChildCode A)
    code move direction .left lineage root child row resolution hcurrent hchild

end

/-! ## Exact acceptance semantics -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- The concrete universal DPA accepts exactly when every initially selected
side and persistent lineage has min-even parity along its canonical
alternating run. -/
theorem profiledOpenIndexedBiBeliefThreadSystem_accepts_iff
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (word : OmegaWord
      (ProfiledOpenIndexedBiBeliefMove A ×
        ProfiledOpenIndexedBiBeliefDirection
          (I := I) (In₁ := In₁) (In₂ := In₂))) :
    (profiledOpenIndexedBiBeliefThreadSystem A initialCode).universalRunDPA.Accepts
        word ↔
      ∀ initialSide lineage,
        NatSeqMinEvenParity (fun n =>
          (profiledOpenIndexedBiBeliefThreadSystem A initialCode).priority
            (profiledOpenIndexedBiBeliefThreadRun A initialCode word
              initialSide lineage n)) := by
  exact codedAlternatingIndexedLineageThreadSystem_accepts_iff initialCode
    (profiledOpenIndexedBiBeliefNext A)
    (profiledOpenIndexedBiBeliefCurrentSlots A)
    (profiledOpenIndexedBiBeliefChildCode A)
    (profiledOpenIndexedRootPriority A) word

end

end DetParityAutomaton

end DistributedSynthesis
