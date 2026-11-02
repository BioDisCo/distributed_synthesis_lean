/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemCodedAlternatingIndexedLineageThreadSystem
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedActualChild

/-!
# Alternating-lineage monitor for one-sided raw joint children

The simultaneous raw joint move contains both orientation responses, but an
actual semantic child has only one live target lane.  This file connects that
one-sided successor to the generic coded alternating-lineage monitor.

`ProfiledRawJointActualDirection.side` is an input-free proof-tree direction:
it says which physical block Nature selected.  It is not a process
observation, a strategy input, or a strict-leader flag.  In particular, the
alphabet below is the alphabet of the objective/tree checker, not a public
local alphabet supplied to either process.

The hidden monitor initially chooses a side and a persistent lineage.  It
advances only when that hidden side agrees with the actual proof-tree side;
the wrong hidden side enters the even dead state.  A live transition keeps
the lineage and crosses to the unique live lane of the one-sided child.
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

/-! ## Source-free one-sided data -/

/-- Nature's actual block orientation together with its raw finite direction.
The side is proof-tree data only; no process is allowed to branch on it. -/
structure ProfiledRawJointActualDirection where
  side : IndexedLineageSide
  direction : ProfiledRawJointFamilyDirection
    (I := I) (In₁ := In₁) (In₂ := In₂)

/-- One finite objective root, tagged by its physical lane. -/
abbrev ProfiledRawJointThreadRoot :=
  ProfiledRawRightSlot A ⊕ ProfiledRawLeftSlot A

noncomputable instance profiledRawJointThreadRootFintype :
    Fintype (ProfiledRawJointThreadRoot A) := by
  classical
  letI : Fintype A.State := A.stateFinite
  exact Fintype.ofFinite _

/-- Source-free one-sided successor.  It depends only on the finite current
code, the raw joint move, and Nature's proof-tree direction. -/
noncomputable def profiledRawJointOneSidedNext
    (code : ProfiledRawJointIncidenceCode A (I := I))
    (move : ProfiledRawJointLambdaFamilyMove A (I := I))
    (actual : ProfiledRawJointActualDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointIncidenceCode A (I := I) :=
  match actual.side with
  | .right => profiledRawJointRightActualIncidenceNext A code.family move
      actual.direction
  | .left => profiledRawJointLeftActualIncidenceNext A code.family move
      actual.direction

/-- The currently live raw slot on either proof-side shadow. -/
def profiledRawJointOneSidedCurrentSlots
    (side : IndexedLineageSide)
    (code : ProfiledRawJointIncidenceCode A (I := I)) :
    I → Option (ProfiledRawJointThreadRoot A) :=
  match side with
  | .right => fun lineage => code.family.right lineage |>.map Sum.inl
  | .left => fun lineage => code.family.left lineage |>.map Sum.inr

/-- Preserve the selected physical row while embedding a right-block child
in the left summand of the thread-root type. -/
def profiledRawJointRightThreadChildCode
    (code : ProfiledRawJointIncidenceCode A (I := I))
    (move : ProfiledRawJointLambdaFamilyMove A (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    IndexedLineageChildCode I (ProfiledRawJointThreadRoot A) :=
  fun lineage =>
    (profiledRawRightIndexedChildCode A code.family move direction lineage).bind
      fun child => child.2.map fun root => (child.1, Sum.inr root)

/-- Left-block mirror, embedding the child in the right summand. -/
def profiledRawJointLeftThreadChildCode
    (code : ProfiledRawJointIncidenceCode A (I := I))
    (move : ProfiledRawJointLambdaFamilyMove A (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    IndexedLineageChildCode I (ProfiledRawJointThreadRoot A) :=
  fun lineage =>
    (profiledRawLeftIndexedChildCode A code.family move direction lineage).bind
      fun child => child.2.map fun root => (child.1, Sum.inl root)

/-- A hidden thread may follow only the block matching its current side.
The wrong side has no child and therefore moves to the even dead state. -/
def profiledRawJointOneSidedChildCode
    (side : IndexedLineageSide)
    (code : ProfiledRawJointIncidenceCode A (I := I))
    (move : ProfiledRawJointLambdaFamilyMove A (I := I))
    (actual : ProfiledRawJointActualDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    IndexedLineageChildCode I (ProfiledRawJointThreadRoot A) :=
  match side, actual.side with
  | .right, .right =>
      profiledRawJointRightThreadChildCode A code move actual.direction
  | .left, .left =>
      profiledRawJointLeftThreadChildCode A code move actual.direction
  | _, _ => fun _ => none

/-- Epoch priority carried by a raw slot.  The action profile is finite
bookkeeping and does not alter the paired-entry priority. -/
def profiledRawJointThreadRootPriority :
    ProfiledRawJointThreadRoot A → Nat
  | .inl root => pairedProfiledEntryPriority A (.inr (.inl root))
  | .inr root => pairedProfiledEntryPriority A (.inr (.inr root))

/-! ## Exact slot compatibility -/

omit [Fintype I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
/-- A right-block child code has exactly the root slots of the unique live
left lane of the one-sided successor. -/
theorem profiledRawJointRightThreadChildCode_rootSlots
    (code : ProfiledRawJointIncidenceCode A (I := I))
    (move : ProfiledRawJointLambdaFamilyMove A (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    (profiledRawJointRightThreadChildCode A code move direction).rootSlots =
      profiledRawJointOneSidedCurrentSlots A .left
        (profiledRawJointRightActualIncidenceNext A code.family move
          direction) := by
  funext lineage
  simp only [profiledRawJointRightThreadChildCode,
    IndexedLineageChildCode.rootSlots,
    profiledRawJointOneSidedCurrentSlots,
    profiledRawJointRightActualIncidenceNext,
    profiledRawJointRightActualFamilyNext,
    profiledRawJointFamilyNext]
  cases hchild :
      profiledRawRightIndexedChildCode A code.family move direction lineage with
  | none => simp [profiledRawOptionalChildSlots, hchild]
  | some child =>
      rcases child with ⟨row, child⟩
      cases child <;> simp [profiledRawOptionalChildSlots, hchild]

omit [Fintype I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
/-- Left-block slot compatibility. -/
theorem profiledRawJointLeftThreadChildCode_rootSlots
    (code : ProfiledRawJointIncidenceCode A (I := I))
    (move : ProfiledRawJointLambdaFamilyMove A (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    (profiledRawJointLeftThreadChildCode A code move direction).rootSlots =
      profiledRawJointOneSidedCurrentSlots A .right
        (profiledRawJointLeftActualIncidenceNext A code.family move
          direction) := by
  funext lineage
  simp only [profiledRawJointLeftThreadChildCode,
    IndexedLineageChildCode.rootSlots,
    profiledRawJointOneSidedCurrentSlots,
    profiledRawJointLeftActualIncidenceNext,
    profiledRawJointLeftActualFamilyNext,
    profiledRawJointFamilyNext]
  cases hchild :
      profiledRawLeftIndexedChildCode A code.family move direction lineage with
  | none => simp [profiledRawOptionalChildSlots, hchild]
  | some child =>
      rcases child with ⟨row, child⟩
      cases child <;> simp [profiledRawOptionalChildSlots, hchild]

/-! ## Concrete alternating-lineage checker -/

/-- Finite hidden-thread checker for the one-sided raw construction.

Its letter contains `actual.side`, but only as an input-free tree direction
read by the proof-side objective automaton.  It is not added to either
process's observation or to the strategy interface. -/
noncomputable def profiledRawJointOneSidedThreadSystem
    (initialCode : ProfiledRawJointIncidenceCode A (I := I)) :
    FiniteThreadSystem
      (ProfiledRawJointLambdaFamilyMove A (I := I) ×
        ProfiledRawJointActualDirection
          (I := I) (In₁ := In₁) (In₂ := In₂)) :=
  codedAlternatingIndexedLineageThreadSystem initialCode
    (profiledRawJointOneSidedNext A)
    (profiledRawJointOneSidedCurrentSlots A)
    (profiledRawJointOneSidedChildCode A)
    (profiledRawJointThreadRootPriority A)

/-- Canonical run for one initially selected proof-side shadow and persistent
lineage. -/
noncomputable def profiledRawJointOneSidedThreadRun
    (initialCode : ProfiledRawJointIncidenceCode A (I := I))
    (word : OmegaWord
      (ProfiledRawJointLambdaFamilyMove A (I := I) ×
        ProfiledRawJointActualDirection
          (I := I) (In₁ := In₁) (In₂ := In₂)))
    (initialSide : IndexedLineageSide) (lineage : I) :=
  codedAlternatingIndexedLineageRun initialCode
    (profiledRawJointOneSidedNext A)
    (profiledRawJointOneSidedCurrentSlots A)
    (profiledRawJointOneSidedChildCode A)
    word initialSide lineage

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- A matching live shadow crosses to the unique live target lane and keeps
its persistent lineage. -/
theorem profiledRawJointOneSidedThreadStep_live_of
    (initialCode code : ProfiledRawJointIncidenceCode A (I := I))
    (move : ProfiledRawJointLambdaFamilyMove A (I := I))
    (actual : ProfiledRawJointActualDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (lineage : I) (root child : ProfiledRawJointThreadRoot A)
    (row : PairedEntryRow) (resolution : IndexedLineageSide × I)
    (hcurrent : profiledRawJointOneSidedCurrentSlots A actual.side code
      lineage = some root)
    (hchild : profiledRawJointOneSidedChildCode A actual.side code move actual
      lineage = some (row, child)) :
    (profiledRawJointOneSidedThreadSystem A initialCode).step
        (code, .live actual.side lineage root) (move, actual) resolution =
      (profiledRawJointOneSidedNext A code move actual,
        .live actual.side.other lineage child) := by
  exact codedAlternatingIndexedLineageStep_live_of
    (profiledRawJointOneSidedNext A)
    (profiledRawJointOneSidedCurrentSlots A)
    (profiledRawJointOneSidedChildCode A)
    code move actual actual.side lineage root child row resolution hcurrent
      hchild

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Exact acceptance semantics: every initially selected side and persistent
lineage satisfies min-even parity along its canonical run.  Mismatching sides
are included and are harmless because they immediately die with priority
zero. -/
theorem profiledRawJointOneSidedThreadSystem_accepts_iff
    (initialCode : ProfiledRawJointIncidenceCode A (I := I))
    (word : OmegaWord
      (ProfiledRawJointLambdaFamilyMove A (I := I) ×
        ProfiledRawJointActualDirection
          (I := I) (In₁ := In₁) (In₂ := In₂))) :
    (profiledRawJointOneSidedThreadSystem A initialCode).universalRunDPA.Accepts
        word ↔
      ∀ initialSide lineage,
        NatSeqMinEvenParity (fun n =>
          (profiledRawJointOneSidedThreadSystem A initialCode).priority
            (profiledRawJointOneSidedThreadRun A initialCode word initialSide
              lineage n)) := by
  exact codedAlternatingIndexedLineageThreadSystem_accepts_iff initialCode
    (profiledRawJointOneSidedNext A)
    (profiledRawJointOneSidedCurrentSlots A)
    (profiledRawJointOneSidedChildCode A)
    (profiledRawJointThreadRootPriority A) word

end

end DetParityAutomaton

end DistributedSynthesis
