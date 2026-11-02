/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossPreselection
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleExtraAnnotation

/-!
# Literal-prefix tables carried by the physical-compatible hybrid policy

The common-front `LiteralCrossExtra` contains the right and left tables of
one guarded common occurrence.  A recurrent Tail needs the same construction
at every later one-sided edge.  This file performs that construction before
the hybrid tree is rationalized:

* each live right lane receives one `FiniteCrossAnchorLiteralPrefixMove` for
  the two hidden right-block interpretations;
* each live left lane receives its mirror;
* both optional IDs are selected from one semantic family/direction; and
* the old payload is replaced at every edge instead of being accumulated.

The resulting finite payload is carried in the *same* parent-linked policy as
the physical annotation by `PhysicalCompatibleExtraAnnotation`.  It is not a
second policy package and cannot select a different semantic occurrence.

The literal-prefix controller has a guard-extended control type.  It is
therefore intentionally not cast to `ProfiledRawJointRightPhysicalSiblingMove`
or its mirror.  A Tail constructor consuming this payload must retain these
controller types directly; erasing the guard before constructing the Tail
would lose exactly the same-occurrence information established here.

No executable transition below receives a graph, hierarchy side, leader bit,
strict-leader bit, semantic history, or view.
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

/-! ## Literal-prefix moves at an arbitrary semantic edge -/

/-- Simultaneously narrow the two right-block interpretations at an arbitrary
semantic family/direction, retaining their first two literal records. -/
noncomputable def profiledRawJointRightLiteralPrefixMoveOf
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember) :
    ProfiledRawJointGuardedCommonRightLiteralCrossMove A := by
  letI : Inhabited (ProfiledRawJointUnitTarget A) :=
    ⟨family.incidenceCode A⟩
  let descriptor :=
    profiledRawJointRightPhysicalSiblingDescriptorOf A family direction
      semanticMember
  let monitor :=
    profiledRawJointRightPhysicalSiblingMonitor A descriptor false
  apply finiteCrossAnchorLiteralPrefixMove
    (fun descriptor : ProfiledRawJointRightPhysicalSiblingDescriptor A ↦
      profiledRawJointRightPhysicalSiblingMonitor A descriptor false)
    (fun _ ↦ descriptor)
    (fun _ ↦ monitor.initial)
    (fun member ↦
      profiledRawJointRightPhysicalSiblingReceiver A hwin family direction
        semanticMember hmember member)
    (profiledRawJointRightSiblingSender A semanticMember)
  intro member env
  simpa [monitor, descriptor] using
    (profiledRawJointRightPhysicalSiblingMonitor_realizable A hwin family
      direction semanticMember hmember member env)

/-- Left-block mirror.  The state raise is the same harmless universe adapter
used by the common-front literal-cross alphabet. -/
noncomputable def profiledRawJointLeftLiteralPrefixMoveOf
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember) :
    ProfiledRawJointGuardedCommonLeftLiteralCrossMove A := by
  letI : Inhabited (ProfiledRawJointUnitTarget A) :=
    ⟨family.incidenceCode A⟩
  let descriptor :=
    profiledRawJointLeftPhysicalSiblingDescriptorOf A family direction
      semanticMember
  let baseMonitor :=
    profiledRawJointLeftPhysicalSiblingMonitor A descriptor false
  let monitor :=
    profiledRawJointGuardedCommonLeftLiteralCrossMonitor A descriptor
  apply finiteCrossAnchorLiteralPrefixMove
    (fun descriptor : ProfiledRawJointLeftPhysicalSiblingDescriptor A ↦
      profiledRawJointGuardedCommonLeftLiteralCrossMonitor A descriptor)
    (fun _ ↦ descriptor)
    (fun _ ↦ monitor.initial)
    (fun member ↦
      profiledRawJointLeftPhysicalSiblingReceiver A hwin family direction
        semanticMember hmember member)
    (profiledRawJointLeftSiblingSender A semanticMember)
  intro member env
  apply (BlockRecordMonitor.raiseState_winsPlay_iff baseMonitor _).2
  simpa [baseMonitor, descriptor] using
    (profiledRawJointLeftPhysicalSiblingMonitor_realizable A hwin family
      direction semanticMember hmember member env)

/-! ## One uniform optional payload -/

/-- The recurring literal-prefix alphabet.  Absence has the same meaning as
in the physical edge annotation: that semantic child lane is absent. -/
noncomputable abbrev ProfiledRawJointHybridLiteralPrefixEdgeAnnotation :=
  Option (ProfiledRawJointGuardedCommonRightLiteralCrossMove A) ×
    Option (ProfiledRawJointGuardedCommonLeftLiteralCrossMove A)

noncomputable instance :
    Fintype (ProfiledRawJointHybridLiteralPrefixEdgeAnnotation A) := by
  classical
  infer_instance

noncomputable def profiledRawJointRightLiteralPrefixMoveOption
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    Option (ProfiledRawJointGuardedCommonRightLiteralCrossMove A) := by
  classical
  exact if hmember : ∃ semanticMember,
      (family.semanticChild A direction).right () = some semanticMember then
    some (profiledRawJointRightLiteralPrefixMoveOf A strategy hwin family
      direction hmember.choose hmember.choose_spec)
  else none

noncomputable def profiledRawJointLeftLiteralPrefixMoveOption
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    Option (ProfiledRawJointGuardedCommonLeftLiteralCrossMove A) := by
  classical
  exact if hmember : ∃ semanticMember,
      (family.semanticChild A direction).left () = some semanticMember then
    some (profiledRawJointLeftLiteralPrefixMoveOf A strategy hwin family
      direction hmember.choose hmember.choose_spec)
  else none

/-- Both orientations are selected from one literal edge occurrence. -/
noncomputable def profiledRawJointHybridLiteralPrefixAnnotationOf
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridLiteralPrefixEdgeAnnotation A :=
  (profiledRawJointRightLiteralPrefixMoveOption A strategy hwin family
      direction,
    profiledRawJointLeftLiteralPrefixMoveOption A strategy hwin family
      direction)

noncomputable def profiledRawJointHybridInitialLiteralPrefixAnnotation :
    ProfiledRawJointHybridLiteralPrefixEdgeAnnotation A :=
  (none, none)

/-- Replace the payload with the tables of the current literal edge. -/
noncomputable def profiledRawJointHybridLiteralPrefixAnnotationAdvance
    (source : HybridState A strategy)
    (_current : ProfiledRawJointHybridLiteralPrefixEdgeAnnotation A)
    (direction : HybridDirection (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridLiteralPrefixEdgeAnnotation A :=
  match source, direction with
  | .common world, .simultaneous input =>
      profiledRawJointHybridLiteralPrefixAnnotationOf A strategy hwin
        (profiledRawJointCommonWorldFamily A world)
        (profiledRawJointBothRestartDirection input)
  | .common world, .strict actual =>
      profiledRawJointHybridLiteralPrefixAnnotationOf A strategy hwin
        (profiledRawJointCommonWorldFamily A world)
        (profiledRawJointCommonActualDirection actual).direction
  | .oneSided source, .strict actual =>
      profiledRawJointHybridLiteralPrefixAnnotationOf A strategy hwin
        source.family actual.direction
  | _, _ => profiledRawJointHybridInitialLiteralPrefixAnnotation A

@[simp] theorem
    profiledRawJointHybridLiteralPrefixAnnotationAdvance_common_both
    (world : ProfiledRawJointCommonBaseWorld A strategy)
    (current : ProfiledRawJointHybridLiteralPrefixEdgeAnnotation A)
    (input : In₁ × In₂) :
    profiledRawJointHybridLiteralPrefixAnnotationAdvance A strategy hwin
        (.common world) current (.simultaneous input) =
      profiledRawJointHybridLiteralPrefixAnnotationOf A strategy hwin
        (profiledRawJointCommonWorldFamily A world)
        (profiledRawJointBothRestartDirection input) :=
  rfl

@[simp] theorem
    profiledRawJointHybridLiteralPrefixAnnotationAdvance_common_strict
    (world : ProfiledRawJointCommonBaseWorld A strategy)
    (current : ProfiledRawJointHybridLiteralPrefixEdgeAnnotation A)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    profiledRawJointHybridLiteralPrefixAnnotationAdvance A strategy hwin
        (.common world) current (.strict actual) =
      profiledRawJointHybridLiteralPrefixAnnotationOf A strategy hwin
        (profiledRawJointCommonWorldFamily A world)
        (profiledRawJointCommonActualDirection actual).direction :=
  rfl

@[simp] theorem
    profiledRawJointHybridLiteralPrefixAnnotationAdvance_oneSided_strict
    (source : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (current : ProfiledRawJointHybridLiteralPrefixEdgeAnnotation A)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    profiledRawJointHybridLiteralPrefixAnnotationAdvance A strategy hwin
        (.oneSided source) current (.strict actual) =
      profiledRawJointHybridLiteralPrefixAnnotationOf A strategy hwin
        source.family actual.direction :=
  rfl

theorem profiledRawJointRightLiteralPrefixMoveOption_spec
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (move : ProfiledRawJointGuardedCommonRightLiteralCrossMove A)
    (hmove : profiledRawJointRightLiteralPrefixMoveOption A strategy hwin
        family direction = some move) :
    ∃ semanticMember : ProcOnePairedEntryRep strategy × A.State,
      ∃ hmember : (family.semanticChild A direction).right () =
          some semanticMember,
        move = profiledRawJointRightLiteralPrefixMoveOf A strategy hwin family
          direction semanticMember hmember := by
  classical
  unfold profiledRawJointRightLiteralPrefixMoveOption at hmove
  split at hmove
  next hex =>
    let semanticMember := hex.choose
    have hmember : (family.semanticChild A direction).right () =
        some semanticMember := by
      simpa [semanticMember] using hex.choose_spec
    refine ⟨semanticMember, hmember, ?_⟩
    simpa [semanticMember] using (Option.some.inj hmove).symm
  next => simp at hmove

theorem profiledRawJointLeftLiteralPrefixMoveOption_spec
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (move : ProfiledRawJointGuardedCommonLeftLiteralCrossMove A)
    (hmove : profiledRawJointLeftLiteralPrefixMoveOption A strategy hwin
        family direction = some move) :
    ∃ semanticMember : ProcTwoPairedEntryRep strategy × A.State,
      ∃ hmember : (family.semanticChild A direction).left () =
          some semanticMember,
        move = profiledRawJointLeftLiteralPrefixMoveOf A strategy hwin family
          direction semanticMember hmember := by
  classical
  unfold profiledRawJointLeftLiteralPrefixMoveOption at hmove
  split at hmove
  next hex =>
    let semanticMember := hex.choose
    have hmember : (family.semanticChild A direction).left () =
        some semanticMember := by
      simpa [semanticMember] using hex.choose_spec
    refine ⟨semanticMember, hmember, ?_⟩
    simpa [semanticMember] using (Option.some.inj hmove).symm
  next => simp at hmove

/-! ## The one jointly rationalized concrete policy -/

noncomputable abbrev
    ProfiledRawJointHybridPhysicalCompatibleLiteralPrefixRationalPolicy
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleExtraRationalPolicy A strategy hwin
    initial (profiledRawJointHybridInitialLiteralPrefixAnnotation A)
    (profiledRawJointHybridLiteralPrefixAnnotationAdvance A strategy hwin)

noncomputable abbrev
    ProfiledRawJointHybridPhysicalCompatibleLiteralPrefixPolicyState
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleExtraPolicyState A strategy hwin
    initial (profiledRawJointHybridInitialLiteralPrefixAnnotation A)
    (profiledRawJointHybridLiteralPrefixAnnotationAdvance A strategy hwin)

abbrev ProfiledRawJointHybridPhysicalCompatibleLiteralPrefixReachable
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (policy :
      ProfiledRawJointHybridPhysicalCompatibleLiteralPrefixRationalPolicy A
        strategy hwin initial)
    (state :
      ProfiledRawJointHybridPhysicalCompatibleLiteralPrefixPolicyState A
        strategy hwin initial) : Prop :=
  ProfiledRawJointHybridPhysicalCompatibleExtraReachable A strategy hwin
    initial (profiledRawJointHybridInitialLiteralPrefixAnnotation A)
    (profiledRawJointHybridLiteralPrefixAnnotationAdvance A strategy hwin)
    policy state

/-- The recurring literal-prefix enrichment is unconditional: it is selected
as finite edge data inside the same physical-compatible rationalization. -/
theorem
    nonempty_profiledRawJointHybridPhysicalCompatibleLiteralPrefixRationalPolicy
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :
    Nonempty
      (ProfiledRawJointHybridPhysicalCompatibleLiteralPrefixRationalPolicy A
        strategy hwin initial) :=
  nonempty_profiledRawJointHybridPhysicalCompatibleExtraRationalPolicy A
    strategy hwin initial
      (profiledRawJointHybridInitialLiteralPrefixAnnotation A)
      (profiledRawJointHybridLiteralPrefixAnnotationAdvance A strategy hwin)

end

end DetParityAutomaton

end DistributedSynthesis
