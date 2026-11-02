/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveBothOutput
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalEdgeAnnotation

/-!
# Occurrence-exact guarded annotations for the phase-live tail

The old physical edge annotation already has the essential replace semantics:
both optional sibling tables are extracted from one semantic
`family, direction` occurrence, and the preceding annotation is discarded.
Its tables are deliberately unguarded, however, so their first narrowed
records need not be the literal records of that occurrence.

This file records the optional guarded analogue and pairs it with the old
annotation.  The product can be carried through the existing parent-linked
rationalization once.  Its first projection preserves every existing
physical-compatible tail interface, while its second projection gives exact
first records for a guarded recurrent anti-mosaic close.

The initial guarded pair is not asserted to persist.  It is installed at the
tagged first child, and every later edge replaces it by the guarded annotation
of that edge's one semantic source.  This is the finite successor-occurrence
payload one would use if a close had to compare independently selected right
and left tables.

The active phase-live route does not make that comparison: at a strict-tail
close both local handlers reconstruct one live table's single receiver
record.  Therefore this stronger product is kept as a proved fallback and is
not a dependency of the one-live-table controller bank.
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

private abbrev HybridState :=
  ProfiledRawJointHybridSemanticState A strategy

private abbrev HybridDirection :=
  ProfiledRawJointHybridDirection (In₁ := In₁) (In₂ := In₂)

private abbrev Tag :=
  ProfiledRawJointHybridShadowPhaseLiveTag A strategy hwin

/-! ## One guarded finite annotation from one literal occurrence -/

/-- Guarded process-one table, when the selected semantic child has a
process-one member. -/
noncomputable def profiledRawJointGuardedRightPhysicalSiblingMoveOption
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    Option (ProfiledRawJointGuardedRightPhysicalSiblingMove A) := by
  classical
  exact if hmember : ∃ semanticMember,
      (family.semanticChild A direction).right () = some semanticMember then
    some (profiledRawJointGuardedRightPhysicalSiblingMoveOf A hwin family
      direction hmember.choose hmember.choose_spec)
  else none

/-- Guarded process-two mirror. -/
noncomputable def profiledRawJointGuardedLeftPhysicalSiblingMoveOption
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    Option (ProfiledRawJointGuardedLeftPhysicalSiblingMove A) := by
  classical
  exact if hmember : ∃ semanticMember,
      (family.semanticChild A direction).left () = some semanticMember then
    some (profiledRawJointGuardedLeftPhysicalSiblingMoveOf A hwin family
      direction hmember.choose hmember.choose_spec)
  else none

/-- Both optional guarded tables are extracted before the actual lane is
selected and from the very same semantic family/direction occurrence. -/
noncomputable abbrev ProfiledRawJointHybridGuardedOccurrenceAnnotation :=
  Option (ProfiledRawJointGuardedRightPhysicalSiblingMove A) ×
    Option (ProfiledRawJointGuardedLeftPhysicalSiblingMove A)

noncomputable instance :
    Fintype (ProfiledRawJointHybridGuardedOccurrenceAnnotation A) := by
  classical
  infer_instance

noncomputable def profiledRawJointHybridGuardedOccurrenceAnnotationOf
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridGuardedOccurrenceAnnotation A :=
  (profiledRawJointGuardedRightPhysicalSiblingMoveOption A strategy hwin
      family direction,
    profiledRawJointGuardedLeftPhysicalSiblingMoveOption A strategy hwin
      family direction)

/-- An explicitly named member gives the exact guarded right table selected
by the optional annotation. -/
theorem profiledRawJointGuardedRightPhysicalSiblingMoveOption_eq_some
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember) :
    profiledRawJointGuardedRightPhysicalSiblingMoveOption A strategy hwin
        family direction =
      some (profiledRawJointGuardedRightPhysicalSiblingMoveOf A hwin family
        direction semanticMember hmember) := by
  classical
  unfold profiledRawJointGuardedRightPhysicalSiblingMoveOption
  split
  next hex =>
    have hchosen : hex.choose = semanticMember := by
      apply Option.some.inj
      exact hex.choose_spec.symm.trans hmember
    subst semanticMember
    rfl
  next hnone =>
    exact (hnone ⟨semanticMember, hmember⟩).elim

/-- Explicit-member left mirror. -/
theorem profiledRawJointGuardedLeftPhysicalSiblingMoveOption_eq_some
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember) :
    profiledRawJointGuardedLeftPhysicalSiblingMoveOption A strategy hwin
        family direction =
      some (profiledRawJointGuardedLeftPhysicalSiblingMoveOf A hwin family
        direction semanticMember hmember) := by
  classical
  unfold profiledRawJointGuardedLeftPhysicalSiblingMoveOption
  split
  next hex =>
    have hchosen : hex.choose = semanticMember := by
      apply Option.some.inj
      exact hex.choose_spec.symm.trans hmember
    subst semanticMember
    rfl
  next hnone =>
    exact (hnone ⟨semanticMember, hmember⟩).elim

/-- Eliminate a stored guarded right table back to the one semantic member
and occurrence from which it was extracted. -/
theorem profiledRawJointGuardedRightPhysicalSiblingMoveOption_spec
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (move : ProfiledRawJointGuardedRightPhysicalSiblingMove A)
    (hmove : profiledRawJointGuardedRightPhysicalSiblingMoveOption A strategy
        hwin family direction = some move) :
    ∃ semanticMember : ProcOnePairedEntryRep strategy × A.State,
      ∃ hmember : (family.semanticChild A direction).right () =
          some semanticMember,
        move = profiledRawJointGuardedRightPhysicalSiblingMoveOf A hwin family
          direction semanticMember hmember := by
  classical
  unfold profiledRawJointGuardedRightPhysicalSiblingMoveOption at hmove
  split at hmove
  next hex =>
    refine ⟨hex.choose, hex.choose_spec, ?_⟩
    exact (Option.some.inj hmove).symm
  next => simp at hmove

/-- Eliminate a stored guarded left table to the same kind of literal
occurrence witness. -/
theorem profiledRawJointGuardedLeftPhysicalSiblingMoveOption_spec
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (move : ProfiledRawJointGuardedLeftPhysicalSiblingMove A)
    (hmove : profiledRawJointGuardedLeftPhysicalSiblingMoveOption A strategy
        hwin family direction = some move) :
    ∃ semanticMember : ProcTwoPairedEntryRep strategy × A.State,
      ∃ hmember : (family.semanticChild A direction).left () =
          some semanticMember,
        move = profiledRawJointGuardedLeftPhysicalSiblingMoveOf A hwin family
          direction semanticMember hmember := by
  classical
  unfold profiledRawJointGuardedLeftPhysicalSiblingMoveOption at hmove
  split at hmove
  next hex =>
    refine ⟨hex.choose, hex.choose_spec, ?_⟩
    exact (Option.some.inj hmove).symm
  next => simp at hmove

/-! ## Replace semantics and product enrichment -/

noncomputable def profiledRawJointHybridInitialGuardedOccurrenceAnnotation :
    ProfiledRawJointHybridGuardedOccurrenceAnnotation A :=
  (none, none)

/-- Install the guarded occurrence of the actual edge.  As in the old
annotation, the preceding value is intentionally ignored. -/
noncomputable def profiledRawJointHybridGuardedOccurrenceAnnotationAdvance
    (source : HybridState A strategy)
    (_current : ProfiledRawJointHybridGuardedOccurrenceAnnotation A)
    (direction : HybridDirection (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridGuardedOccurrenceAnnotation A :=
  match source, direction with
  | .common world, .simultaneous input =>
      profiledRawJointHybridGuardedOccurrenceAnnotationOf A strategy hwin
        (profiledRawJointCommonWorldFamily A world)
        (profiledRawJointBothRestartDirection input)
  | .common world, .strict actual =>
      profiledRawJointHybridGuardedOccurrenceAnnotationOf A strategy hwin
        (profiledRawJointCommonWorldFamily A world)
        (profiledRawJointCommonActualDirection actual).direction
  | .oneSided source, .strict actual =>
      profiledRawJointHybridGuardedOccurrenceAnnotationOf A strategy hwin
        source.family actual.direction
  | _, _ => profiledRawJointHybridInitialGuardedOccurrenceAnnotation A

/-- Formal fail-fast result: an edge update cannot preserve an earlier
occurrence by accumulation; it is independent of the preceding guarded
annotation. -/
theorem profiledRawJointHybridGuardedOccurrenceAnnotationAdvance_current_irrel
    (source : HybridState A strategy)
    (left right : ProfiledRawJointHybridGuardedOccurrenceAnnotation A)
    (direction : HybridDirection (In₁ := In₁) (In₂ := In₂)) :
    profiledRawJointHybridGuardedOccurrenceAnnotationAdvance A strategy hwin
        source left direction =
      profiledRawJointHybridGuardedOccurrenceAnnotationAdvance A strategy hwin
        source right direction := by
  cases source <;> cases direction <;> rfl

/-- Old physical payload plus the exact guarded occurrence payload. -/
noncomputable abbrev ProfiledRawJointHybridOccurrenceExactAnnotation :=
  ProfiledRawJointHybridPhysicalEdgeAnnotation A ×
    ProfiledRawJointHybridGuardedOccurrenceAnnotation A

noncomputable instance :
    Fintype (ProfiledRawJointHybridOccurrenceExactAnnotation A) := by
  classical
  infer_instance

noncomputable def profiledRawJointHybridInitialOccurrenceExactAnnotation :
    ProfiledRawJointHybridOccurrenceExactAnnotation A :=
  (profiledRawJointHybridInitialPhysicalAnnotation A,
    profiledRawJointHybridInitialGuardedOccurrenceAnnotation A)

/-- One joint update retains the old TailPolicy payload in the first
projection and installs the occurrence-exact guarded payload in the second. -/
noncomputable def profiledRawJointHybridOccurrenceExactAnnotationAdvance
    (source : HybridState A strategy)
    (current : ProfiledRawJointHybridOccurrenceExactAnnotation A)
    (direction : HybridDirection (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridOccurrenceExactAnnotation A :=
  (profiledRawJointHybridPhysicalAnnotationAdvance A strategy hwin source
      current.1 direction,
    profiledRawJointHybridGuardedOccurrenceAnnotationAdvance A strategy hwin
      source current.2 direction)

@[simp] theorem profiledRawJointHybridOccurrenceExactAnnotationAdvance_fst
    (source : HybridState A strategy)
    (current : ProfiledRawJointHybridOccurrenceExactAnnotation A)
    (direction : HybridDirection (In₁ := In₁) (In₂ := In₂)) :
    (profiledRawJointHybridOccurrenceExactAnnotationAdvance A strategy hwin
      source current direction).1 =
      profiledRawJointHybridPhysicalAnnotationAdvance A strategy hwin source
        current.1 direction :=
  rfl

@[simp] theorem profiledRawJointHybridOccurrenceExactAnnotationAdvance_snd
    (source : HybridState A strategy)
    (current : ProfiledRawJointHybridOccurrenceExactAnnotation A)
    (direction : HybridDirection (In₁ := In₁) (In₂ := In₂)) :
    (profiledRawJointHybridOccurrenceExactAnnotationAdvance A strategy hwin
      source current direction).2 =
      profiledRawJointHybridGuardedOccurrenceAnnotationAdvance A strategy hwin
        source current.2 direction :=
  rfl

/-! ## The tagged first occurrence -/

/-- Turn the already proved tag-coherent guarded pair into the new annotation
shape. -/
noncomputable def
    ProfiledRawJointHybridShadowPhaseLiveTag.guardedCommonPairAnnotation
    (tag : Tag A strategy hwin) :
    ProfiledRawJointHybridGuardedOccurrenceAnnotation A :=
  let pair := tag.guardedCommonPair A strategy hwin
  (some pair.1.1, some pair.1.2)

/-- At the first tagged occurrence the jointly generated guarded annotation
is exactly the earlier tag-coherent guarded pair. -/
theorem
    ProfiledRawJointHybridShadowPhaseLiveTag.guardedAnnotationOf_eq_pair
    (tag : Tag A strategy hwin) :
    let installed :=
      profiledRawJointHybridShadowPhaseLiveInstalled A strategy hwin tag.origin
    profiledRawJointHybridGuardedOccurrenceAnnotationOf A strategy hwin
        (profiledRawJointCommonWorldFamily A installed.world)
        (profiledRawJointBothRestartDirection tag.input) =
      tag.guardedCommonPairAnnotation A strategy hwin := by
  dsimp only
  let world :=
    (profiledRawJointHybridShadowPhaseLiveInstalled A strategy hwin tag.origin
      ).world
  apply Prod.ext
  · unfold ProfiledRawJointHybridShadowPhaseLiveTag.guardedCommonPairAnnotation
      ProfiledRawJointHybridShadowPhaseLiveTag.guardedCommonPair
      profiledRawJointGuardedCommonPairOfWorld
      profiledRawJointGuardedCommonRightMoveOfWorld
      profiledRawJointHybridGuardedOccurrenceAnnotationOf
    apply profiledRawJointGuardedRightPhysicalSiblingMoveOption_eq_some
  · unfold ProfiledRawJointHybridShadowPhaseLiveTag.guardedCommonPairAnnotation
      ProfiledRawJointHybridShadowPhaseLiveTag.guardedCommonPair
      profiledRawJointGuardedCommonPairOfWorld
      profiledRawJointGuardedCommonLeftMoveOfWorld
      profiledRawJointHybridGuardedOccurrenceAnnotationOf
    apply profiledRawJointGuardedLeftPhysicalSiblingMoveOption_eq_some

/-! ## One unconditional enriched rationalization -/

noncomputable abbrev
    ProfiledRawJointHybridOccurrenceExactCarriedRationalPolicy
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridCarriedParentLinkedRationalPolicy A strategy initial
    (profiledRawJointHybridInitialOccurrenceExactAnnotation A)
    (profiledRawJointHybridOccurrenceExactAnnotationAdvance A strategy hwin)

noncomputable abbrev
    ProfiledRawJointHybridOccurrenceExactCarriedPolicyState
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridCarriedParentLinkedPolicyState A strategy initial
    (profiledRawJointHybridInitialOccurrenceExactAnnotation A)
    (profiledRawJointHybridOccurrenceExactAnnotationAdvance A strategy hwin)

abbrev ProfiledRawJointHybridOccurrenceExactCarriedReachable
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (policy : ProfiledRawJointHybridOccurrenceExactCarriedRationalPolicy A
      strategy hwin initial)
    (state : ProfiledRawJointHybridOccurrenceExactCarriedPolicyState A strategy
      hwin initial) : Prop :=
  ProfiledRawJointHybridCarriedParentLinkedReachable A strategy initial
    (profiledRawJointHybridInitialOccurrenceExactAnnotation A)
    (profiledRawJointHybridOccurrenceExactAnnotationAdvance A strategy hwin)
    policy state

/-- The strengthened annotation costs no premise: it is finite and is
carried through the same one-shot parent-linked rationalization. -/
theorem nonempty_profiledRawJointHybridOccurrenceExactCarriedRationalPolicy
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :
    Nonempty
      (ProfiledRawJointHybridOccurrenceExactCarriedRationalPolicy A strategy
        hwin initial) :=
  nonempty_profiledRawJointHybridCarriedParentLinkedRationalPolicy A strategy
    hwin initial (profiledRawJointHybridInitialOccurrenceExactAnnotation A)
      (profiledRawJointHybridOccurrenceExactAnnotationAdvance A strategy hwin)

end

end DetParityAutomaton

end DistributedSynthesis
