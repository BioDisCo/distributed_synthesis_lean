/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalEdgeAnnotation

/-!
# Current-table compatibility for the carried hybrid policy

The parent-linked annotation theorem aligns the table installed at a child
with that child's finite live root.  To use a table for the *next* physical
block we additionally need its finite allowed-target relation to be the
one-sided successor relation of the current literal source.

This file proves that invariant semantically and packages it into the
legality predicate before rationalization.  It is the missing source-aligned
edge law: it is not inferred after the fact from two existential semantic
representatives.  The invariant is finite at runtime (a table truth table and
a finite raw move), while all semantic families and actual sides below remain
proof witnesses.
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

/-! ## Extensional target compatibility -/

/-- Every target allowed by a finite right table is a literal right-actual
successor of the named current family. -/
def ProfiledRawJointRightPhysicalSiblingMove.FollowsFamily
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit)) : Prop :=
  ∀ target, profiledRawJointRightPhysicalSiblingAllowed A move.1 target →
    ∃ row past input,
      target = profiledRawJointOneSidedNext A (family.incidenceCode A)
        (family.move A)
        (profiledRawJointUnitRightActualDirection
          (In₁ := In₁) (In₂ := In₂) row past input)

/-- Left-table mirror. -/
def ProfiledRawJointLeftPhysicalSiblingMove.FollowsFamily
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit)) : Prop :=
  ∀ target, profiledRawJointLeftPhysicalSiblingAllowed A move.1 target →
    ∃ row past input,
      target = profiledRawJointOneSidedNext A (family.incidenceCode A)
        (family.move A)
        (profiledRawJointUnitLeftActualDirection
          (In₁ := In₁) (In₂ := In₂) row past input)

/-- The right table extracted before a strict-left resolution follows the
literal strict-left child family. -/
theorem profiledRawJointRightPhysicalSiblingMoveOf_follows_leftActual
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember) :
    (profiledRawJointRightPhysicalSiblingMoveOf A hwin family direction
      semanticMember hmember).FollowsFamily A strategy
        (family.leftActualChild A direction) := by
  intro target htarget
  have hshared :
      ProfiledRawJointRightSiblingSharedAllowedTarget A family direction
        target :=
    (profiledRawJointRightPhysicalSiblingDescriptorOf_allowed_iff A family
      direction semanticMember target).mp htarget
  have hstrict :
      ProfiledRawJointRightSiblingAllowedTarget A family direction true
        target :=
    (profiledRawJointRightSiblingAllowedTarget_iff_shared A family direction
      true target).mpr hshared
  simpa [ProfiledRawJointRightPhysicalSiblingMove.FollowsFamily,
    ProfiledRawJointRightSiblingAllowedTarget,
    profiledRawJointRightSiblingFamily] using hstrict

/-- Left table after a strict-right resolution. -/
theorem profiledRawJointLeftPhysicalSiblingMoveOf_follows_rightActual
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember) :
    (profiledRawJointLeftPhysicalSiblingMoveOf A hwin family direction
      semanticMember hmember).FollowsFamily A strategy
        (family.rightActualChild A direction) := by
  intro target htarget
  have hshared :
      ProfiledRawJointLeftSiblingSharedAllowedTarget A family direction
        target :=
    (profiledRawJointLeftPhysicalSiblingDescriptorOf_allowed_iff A family
      direction semanticMember target).mp htarget
  have hstrict :
      ProfiledRawJointLeftSiblingAllowedTarget A family direction true
        target :=
    (profiledRawJointLeftSiblingAllowedTarget_iff_shared A family direction
      true target).mpr hshared
  simpa [ProfiledRawJointLeftPhysicalSiblingMove.FollowsFamily,
    ProfiledRawJointLeftSiblingAllowedTarget,
    profiledRawJointLeftSiblingFamily] using hstrict

/-! ## The current one-sided source matches its active table -/

/-- Only live lanes impose an obligation.  A right live lane uses the right
table for the next right block; a left live lane uses the left table. -/
def ProfiledRawJointOneSidedPhysicalAnnotationCompatible
    (state : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (annotation : ProfiledRawJointHybridPhysicalEdgeAnnotation A) : Prop :=
  (∀ semanticMember,
      state.family.right () = some semanticMember →
      ∀ move, annotation.1 = some move →
        move.FollowsFamily A strategy state.family) ∧
    (∀ semanticMember,
      state.family.left () = some semanticMember →
      ∀ move, annotation.2 = some move →
        move.FollowsFamily A strategy state.family)

/-- Common and dead states do not execute a recurrent strict table.  The
first strict exit installs a compatible table in its one-sided child. -/
def ProfiledRawJointHybridPhysicalCurrentCompatible
    (source : ProfiledRawJointHybridSemanticState A strategy)
    (annotation : ProfiledRawJointHybridPhysicalEdgeAnnotation A) : Prop :=
  match source with
  | .oneSided state =>
      ProfiledRawJointOneSidedPhysicalAnnotationCompatible A strategy state
        annotation
  | _ => True

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Fail-fast seam, right orientation: from a compatible current annotation,
every target allowed by its active right table is exactly the code of one
literal strict successor of that same one-sided source. -/
theorem
    ProfiledRawJointOneSidedPhysicalAnnotationCompatible.exists_rightTargetChild
    (state : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (annotation : ProfiledRawJointHybridPhysicalEdgeAnnotation A)
    (hcompatible : ProfiledRawJointOneSidedPhysicalAnnotationCompatible A
      strategy state annotation)
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : state.family.right () = some semanticMember)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (hmove : annotation.1 = some move)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : profiledRawJointRightPhysicalSiblingAllowed A move.1 target) :
    ∃ actual : ProfiledRawJointActualDirection
        (I := Unit) (In₁ := In₁) (In₂ := In₂),
      actual.side = .right ∧ (state.step A actual).code A = target := by
  rcases hcompatible.1 semanticMember hmember move hmove target htarget with
    ⟨row, past, input, htarget⟩
  let actual := profiledRawJointUnitRightActualDirection
    (In₁ := In₁) (In₂ := In₂) row past input
  refine ⟨actual, rfl, ?_⟩
  exact (state.step_code A actual).trans htarget.symm

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Left-orientation mirror. -/
theorem
    ProfiledRawJointOneSidedPhysicalAnnotationCompatible.exists_leftTargetChild
    (state : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (annotation : ProfiledRawJointHybridPhysicalEdgeAnnotation A)
    (hcompatible : ProfiledRawJointOneSidedPhysicalAnnotationCompatible A
      strategy state annotation)
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : state.family.left () = some semanticMember)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hmove : annotation.2 = some move)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : profiledRawJointLeftPhysicalSiblingAllowed A move.1 target) :
    ∃ actual : ProfiledRawJointActualDirection
        (I := Unit) (In₁ := In₁) (In₂ := In₂),
      actual.side = .left ∧ (state.step A actual).code A = target := by
  rcases hcompatible.2 semanticMember hmember move hmove target htarget with
    ⟨row, past, input, htarget⟩
  let actual := profiledRawJointUnitLeftActualDirection
    (In₁ := In₁) (In₂ := In₂) row past input
  refine ⟨actual, rfl, ?_⟩
  exact (state.step_code A actual).trans htarget.symm

/-- A strict-left child and the two preselected tables satisfy the current
compatibility invariant. -/
theorem profiledRawJointHybridPhysicalAnnotationOf_leftActual_compatible
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointOneSidedPhysicalAnnotationCompatible A strategy
      { family := family.leftActualChild A direction
        exactFibre := family.leftActualChild_exactFibreAt A direction }
      (profiledRawJointHybridPhysicalAnnotationOf A strategy hwin family
        direction) := by
  constructor
  · intro semanticMember hmember move hmove
    obtain ⟨member, hmember', rfl⟩ :=
      profiledRawJointRightPhysicalSiblingMoveOption_spec A strategy hwin
        family direction move (by
          simpa [profiledRawJointHybridPhysicalAnnotationOf] using hmove)
    exact profiledRawJointRightPhysicalSiblingMoveOf_follows_leftActual A
      strategy hwin family direction member hmember'
  · intro semanticMember hmember
    simp [ProfiledRawJointSemanticFamily.leftActualChild] at hmember

/-- Strict-right mirror. -/
theorem profiledRawJointHybridPhysicalAnnotationOf_rightActual_compatible
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointOneSidedPhysicalAnnotationCompatible A strategy
      { family := family.rightActualChild A direction
        exactFibre := family.rightActualChild_exactFibreAt A direction }
      (profiledRawJointHybridPhysicalAnnotationOf A strategy hwin family
        direction) := by
  constructor
  · intro semanticMember hmember
    simp [ProfiledRawJointSemanticFamily.rightActualChild] at hmember
  · intro semanticMember hmember move hmove
    obtain ⟨member, hmember', rfl⟩ :=
      profiledRawJointLeftPhysicalSiblingMoveOption_spec A strategy hwin
        family direction move (by
          simpa [profiledRawJointHybridPhysicalAnnotationOf] using hmove)
    exact profiledRawJointLeftPhysicalSiblingMoveOf_follows_rightActual A
      strategy hwin family direction member hmember'

/-- Every strict semantic edge freshly installs a compatible annotation in
its literal child, independently of the old annotation. -/
theorem profiledRawJointHybridPhysicalAnnotationAdvance_strict_compatible
    (source : ProfiledRawJointHybridSemanticState A strategy)
    (current : ProfiledRawJointHybridPhysicalEdgeAnnotation A)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridPhysicalCurrentCompatible A strategy
      (source.step A (.strict actual))
      (profiledRawJointHybridPhysicalAnnotationAdvance A strategy hwin source
        current (.strict actual)) := by
  cases source with
  | common world =>
      cases hside : actual.side with
      | right =>
          simpa [ProfiledRawJointHybridPhysicalCurrentCompatible,
            ProfiledRawJointHybridSemanticState.step,
            profiledRawJointCommonExitState, hside] using
            profiledRawJointHybridPhysicalAnnotationOf_rightActual_compatible
              A strategy hwin (profiledRawJointCommonWorldFamily A world)
                (profiledRawJointCommonActualDirection actual).direction
      | left =>
          simpa [ProfiledRawJointHybridPhysicalCurrentCompatible,
            ProfiledRawJointHybridSemanticState.step,
            profiledRawJointCommonExitState, hside] using
            profiledRawJointHybridPhysicalAnnotationOf_leftActual_compatible A
              strategy hwin (profiledRawJointCommonWorldFamily A world)
                (profiledRawJointCommonActualDirection actual).direction
  | oneSided state =>
      cases hside : actual.side with
      | right =>
          simpa [ProfiledRawJointHybridPhysicalCurrentCompatible,
            ProfiledRawJointHybridSemanticState.step,
            ProfiledRawJointOneSidedSemanticState.step, hside] using
            profiledRawJointHybridPhysicalAnnotationOf_rightActual_compatible
              A strategy hwin state.family actual.direction
      | left =>
          simpa [ProfiledRawJointHybridPhysicalCurrentCompatible,
            ProfiledRawJointHybridSemanticState.step,
            ProfiledRawJointOneSidedSemanticState.step, hside] using
            profiledRawJointHybridPhysicalAnnotationOf_leftActual_compatible A
              strategy hwin state.family actual.direction
  | dead => trivial

/-- Compatibility is an invariant of the exact carried semantic tree. -/
theorem profiledRawJointHybridPhysicalAnnotationAdvance_compatible
    (source : ProfiledRawJointHybridSemanticState A strategy)
    (current : ProfiledRawJointHybridPhysicalEdgeAnnotation A)
    (direction : ProfiledRawJointHybridDirection
      (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridPhysicalCurrentCompatible A strategy
      (source.step A direction)
      (profiledRawJointHybridPhysicalAnnotationAdvance A strategy hwin source
        current direction) := by
  cases direction with
  | strict actual =>
      exact
        profiledRawJointHybridPhysicalAnnotationAdvance_strict_compatible A
          strategy hwin source current actual
  | simultaneous input =>
      cases source <;> trivial

end

end DetParityAutomaton

end DistributedSynthesis
