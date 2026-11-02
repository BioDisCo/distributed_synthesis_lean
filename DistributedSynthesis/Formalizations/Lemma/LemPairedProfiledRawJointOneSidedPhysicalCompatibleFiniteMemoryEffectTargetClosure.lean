/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEffectCoherence

/-!
# Target closure from finite public-effect coherence

The owner-fibre kernel never asks a policy table for an arbitrary semantic
successor.  At a right (respectively left) boundary it asks for a target
allowed by the installed right (respectively left) physical sibling move.
This file proves that the weak, finite `EffectLocallyValid` condition already
supplies such a child.

The proof chooses one exact source from the canonical cell.  Compatibility of
the installed annotation produces an actual semantic direction reaching the
requested target.  Public-effect coherence then identifies the table's stored
successor with the linked code and objective state of that exact child.  Thus
the raw table resolver recognizes the child and cannot take its fallback.

In particular, no equality of complete raw lambda moves is used.  This closes
the one-round owner-output test at every effect-coherent table cell; the
remaining owner obligation is the infinite trace/parity argument.
-/

namespace DistributedSynthesis

universe u v x y s m

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable {Memory : Type m}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable [Fintype Memory]

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

private abbrev RootKey :=
  ProfiledRawJointOneSidedPhysicalCompatibleRootKey A strategy

private abbrev PhysicalAnnotation :=
  ProfiledRawJointHybridPhysicalEdgeAnnotation A

private abbrev LinkedCode :=
  SourceFreeBeliefParentLinkedCode
    (BeliefCode := ProfiledRawJointIncidenceCode A (I := Unit))
    (Annotation := PhysicalAnnotation A)

private abbrev ActualDirection :=
  ProfiledRawJointActualDirection (I := Unit) (In₁ := In₁) (In₂ := In₂)

private abbrev LinkedMove :=
  SourceFreeBeliefParentLinkedMove
    (Direction := ActualDirection (In₁ := In₁) (In₂ := In₂))
    (Move := ProfiledRawJointLambdaFamilyMove A (I := Unit))
    (Annotation := PhysicalAnnotation A)

private abbrev PolicyDPA
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit)) :=
  sourceFreeBeliefParentLinkedCodeParityDPA
    (Annotation := PhysicalAnnotation A)
    (profiledRawJointOneSidedCodeParityDPA A initialCode)

private noncomputable abbrev PolicyNext :
    LinkedCode A →
      LinkedMove A (In₁ := In₁) (In₂ := In₂) →
        LinkedCode A → LinkedCode A :=
  sourceFreeBeliefFiniteCodeNext
    (sourceFreeBeliefParentLinkedNext (profiledRawJointOneSidedNext A))

private abbrev FixedTable (key : RootKey A strategy) :=
  ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTable
    (Memory := Memory) A strategy key

private abbrev PolicyState (key : RootKey A strategy) :=
  ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyState
    (Memory := Memory) A key.1.1

namespace
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTable

variable
  (initialMemory : RootKey A strategy → Memory)
  (key : RootKey A strategy)
  (table : FixedTable (Memory := Memory) A strategy key)

private abbrev TableFamily :=
  ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection
    (Memory := Memory) A strategy

section
omit [Fintype Memory]

/-- A raw-table realization witness exposes the literal semantic child and
the physical annotation installed at that child.  This statement does not
use table validity; it is an exact elimination rule for `ChildRealizes`. -/
theorem childRealizes_exists_child
    (tables : TableFamily (Memory := Memory) A strategy)
    (bankState :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankControl
        (Memory := Memory) A strategy)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (childCode : LinkedCode A)
    (hrealizes : tables.ChildRealizes A strategy hwin bankState target
      childCode) :
    ∃ source : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit),
      ∃ actual : ActualDirection (In₁ := In₁) (In₂ := In₂),
        (source.step A actual).code A = target ∧
          childCode.2 =
            profiledRawJointOneSidedPhysicalAnnotationAdvance A strategy hwin
              source bankState.2.1.1.2 actual ∧
          ProfiledRawJointOneSidedPhysicalAnnotationCompatible A strategy
            (source.step A actual) childCode.2 := by
  rcases hrealizes with
    ⟨move, source, actual, hcode, hmove, _hcompatible, hchildren,
      hchildCode, hbare, _hsuccessor⟩
  have hstepCode : (source.step A actual).code A = childCode.1 := by
    rw [ProfiledRawJointOneSidedSemanticState.step_code]
    rw [hcode, hmove, hchildCode]
    rfl
  have hannotation :
      childCode.2 =
        profiledRawJointOneSidedPhysicalAnnotationAdvance A strategy hwin
          source bankState.2.1.1.2 actual := by
    rw [hchildCode]
    exact (hchildren actual).symm
  refine ⟨source, actual, hstepCode.trans hbare, hannotation, ?_⟩
  rw [hannotation]
  exact
    profiledRawJointOneSidedPhysicalAnnotationAdvance_compatible A strategy
      hwin source bankState.2.1.1.2 actual

/-- A realized raw packet whose target has a live left slot installs an
actual left physical sibling move. -/
theorem childRealizes_resolvePacket_leftMove_exists
    (tables : TableFamily (Memory := Memory) A strategy)
    (bankState :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankControl
        (Memory := Memory) A strategy)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (hrealizes :
      tables.ChildRealizes A strategy hwin bankState target
        (tables.resolveTarget A strategy hwin bankState target))
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .left target () =
      some root) :
    let packet := tables.resolvePacket A strategy hwin bankState target
    ∃ move : ProfiledRawJointLeftPhysicalSiblingMove A,
      packet.successor.2.1.1.2.2 = some move := by
  dsimp only
  let childCode := tables.resolveTarget A strategy hwin bankState target
  rcases hrealizes with
    ⟨linkedMove, source, actual, hcode, hsourceMove, _hcompatible,
      hchildren, hchildCode, hbare, hsuccessor⟩
  change childCode = sourceFreeBeliefParentLinkedNext
    (profiledRawJointOneSidedNext A) bankState.2.1.1 linkedMove actual at hchildCode
  change childCode.1 = target at hbare
  have hstepCode : (source.step A actual).code A = target := by
    calc
      (source.step A actual).code A = childCode.1 := by
        rw [ProfiledRawJointOneSidedSemanticState.step_code]
        rw [hcode, hsourceMove, hchildCode]
        rfl
      _ = target := hbare
  have hstepRoot :
      profiledRawJointOneSidedCurrentSlots A .left
          ((source.step A actual).code A) () = some root := by
    rw [hstepCode]
    exact hroot
  obtain ⟨semanticMember, hmember, _hrootShape, _hmemory⟩ :=
    (source.step A actual).exists_left_member_of_currentSlot A () root
      hstepRoot
  cases hside : actual.side with
  | left =>
      simp [ProfiledRawJointOneSidedSemanticState.step, hside,
        ProfiledRawJointSemanticFamily.leftActualChild] at hmember
  | right =>
      have hsemanticMember :
          (source.family.semanticChild A actual.direction).left () =
            some semanticMember := by
        simpa [ProfiledRawJointOneSidedSemanticState.step, hside,
          ProfiledRawJointSemanticFamily.rightActualChild] using hmember
      obtain ⟨move, hannotation, _hnextRoot⟩ :=
        profiledRawJointHybridPhysicalAnnotationOf_rightActual_liveRoot A
          strategy hwin source.family actual.direction semanticMember
            hsemanticMember
      have hchildAnnotation :
          childCode.2 =
            profiledRawJointHybridPhysicalAnnotationOf A strategy hwin
              source.family actual.direction := by
        rw [hchildCode]
        change linkedMove.2 actual = _
        rw [← hchildren actual]
        rfl
      have hsuccessorAnnotation :
          (tables.successor A strategy bankState childCode).2.1.1.2 =
            profiledRawJointHybridPhysicalAnnotationOf A strategy hwin
              source.family actual.direction := by
        exact (congrArg (fun publicState ↦ publicState.1.2)
          hsuccessor).trans hchildAnnotation
      refine ⟨move, ?_⟩
      change
        (tables.successor A strategy bankState childCode).2.1.1.2.2 = some move
      rw [hsuccessorAnnotation]
      exact hannotation

/-- Right-orientation mirror of installed-move extraction from a realized raw
packet. -/
theorem childRealizes_resolvePacket_rightMove_exists
    (tables : TableFamily (Memory := Memory) A strategy)
    (bankState :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankControl
        (Memory := Memory) A strategy)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (hrealizes :
      tables.ChildRealizes A strategy hwin bankState target
        (tables.resolveTarget A strategy hwin bankState target))
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .right target () =
      some root) :
    let packet := tables.resolvePacket A strategy hwin bankState target
    ∃ move : ProfiledRawJointRightPhysicalSiblingMove A,
      packet.successor.2.1.1.2.1 = some move := by
  dsimp only
  let childCode := tables.resolveTarget A strategy hwin bankState target
  rcases hrealizes with
    ⟨linkedMove, source, actual, hcode, hsourceMove, _hcompatible,
      hchildren, hchildCode, hbare, hsuccessor⟩
  change childCode = sourceFreeBeliefParentLinkedNext
    (profiledRawJointOneSidedNext A) bankState.2.1.1 linkedMove actual at hchildCode
  change childCode.1 = target at hbare
  have hstepCode : (source.step A actual).code A = target := by
    calc
      (source.step A actual).code A = childCode.1 := by
        rw [ProfiledRawJointOneSidedSemanticState.step_code]
        rw [hcode, hsourceMove, hchildCode]
        rfl
      _ = target := hbare
  have hstepRoot :
      profiledRawJointOneSidedCurrentSlots A .right
          ((source.step A actual).code A) () = some root := by
    rw [hstepCode]
    exact hroot
  obtain ⟨semanticMember, hmember, _hrootShape, _hmemory⟩ :=
    (source.step A actual).exists_right_member_of_currentSlot A () root
      hstepRoot
  cases hside : actual.side with
  | right =>
      simp [ProfiledRawJointOneSidedSemanticState.step, hside,
        ProfiledRawJointSemanticFamily.rightActualChild] at hmember
  | left =>
      have hsemanticMember :
          (source.family.semanticChild A actual.direction).right () =
            some semanticMember := by
        simpa [ProfiledRawJointOneSidedSemanticState.step, hside,
          ProfiledRawJointSemanticFamily.leftActualChild] using hmember
      obtain ⟨move, hannotation, _hnextRoot⟩ :=
        profiledRawJointHybridPhysicalAnnotationOf_leftActual_liveRoot A
          strategy hwin source.family actual.direction semanticMember
            hsemanticMember
      have hchildAnnotation :
          childCode.2 =
            profiledRawJointHybridPhysicalAnnotationOf A strategy hwin
              source.family actual.direction := by
        rw [hchildCode]
        change linkedMove.2 actual = _
        rw [← hchildren actual]
        rfl
      have hsuccessorAnnotation :
          (tables.successor A strategy bankState childCode).2.1.1.2 =
            profiledRawJointHybridPhysicalAnnotationOf A strategy hwin
              source.family actual.direction := by
        exact (congrArg (fun publicState ↦ publicState.1.2)
          hsuccessor).trans hchildAnnotation
      refine ⟨move, ?_⟩
      change
        (tables.successor A strategy bankState childCode).2.1.1.2.1 = some move
      rw [hsuccessorAnnotation]
      exact hannotation

/-- The linked child produced by one exact direction is recognized by the raw
table resolver.  This is the orientation-free core of target closure. -/
theorem EffectLocallyValid.childRealizes_of_actual
    (state : PolicyState (Memory := Memory) A strategy key)
    (hlocal :
      table.EffectLocallyValid A strategy hwin initialMemory key state)
    (exact :
      ProfiledRawJointOneSidedPhysicalExactCommonActionMemory A strategy)
    (hexact :
      table.CanonicalBelief A strategy hwin initialMemory key state exact)
    (actual : ActualDirection (In₁ := In₁) (In₂ := In₂)) :
    let move := profiledRawJointOneSidedSemanticLinkedMove A strategy hwin
      exact.1.1 exact.1.2
    let childCode := sourceFreeBeliefParentLinkedNext
      (profiledRawJointOneSidedNext A) state.1.1 move actual
    (table.family A strategy key).ChildRealizes A strategy hwin
      ⟨key, state⟩ childCode.1 childCode := by
  dsimp only
  let move : LinkedMove A (In₁ := In₁) (In₂ := In₂) :=
    profiledRawJointOneSidedSemanticLinkedMove A strategy hwin exact.1.1
      exact.1.2
  let childCode : LinkedCode A :=
    sourceFreeBeliefParentLinkedNext
      (profiledRawJointOneSidedNext A) state.1.1 move actual
  have hpublic := hlocal.1.2 exact hexact
  have hsignature := congrFun (hlocal.2 exact hexact) childCode
  have hnext :
      PolicyNext A (In₁ := In₁) (In₂ := In₂) state.1.1 move
          childCode =
        childCode := by
    exact sourceFreeBeliefFiniteCodeNext_of_direction
      (sourceFreeBeliefParentLinkedNext (profiledRawJointOneSidedNext A))
      state.1.1 move actual
  refine ⟨move, exact.1.1, actual, hpublic.1, rfl, ?_, ?_, rfl, rfl, ?_⟩
  · rw [← hpublic.2]
    exact exact.2
  · intro direction
    rfl
  · unfold ExactPublicSuccessorSignature StoredPublicSuccessorSignature at hsignature
    change
      sourceFreeBeliefCodeParityControllerNext
          (PolicyDPA A key.1.1) state.1 move
            (PolicyNext A (In₁ := In₁) (In₂ := In₂) state.1.1 move
              childCode) =
        (table.successor state childCode).1 at hsignature
    rw [hnext] at hsignature
    have htable :
        (table.successor state childCode).1 =
          (childCode, (PolicyDPA A key.1.1).step state.1.2 childCode) := by
      simpa only [sourceFreeBeliefCodeParityControllerNext] using
        hsignature.symm
    simpa only [
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.successor,
      family, ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.singletonAt_apply_key]
      using htable

/-- Right installed-table closure requires only the finite public successor
effect of one exact source in the cell. -/
theorem EffectLocallyValid.exists_rightTargetChildRealizes
    (state : PolicyState (Memory := Memory) A strategy key)
    (hlocal :
      table.EffectLocallyValid A strategy hwin initialMemory key state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcurrentCode : state.1.1.1 = currentCode)
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .right currentCode () =
      some root)
    (phaseMove : ProfiledRawJointRightPhysicalSiblingMove A)
    (hphaseMove : state.1.1.2.1 = some phaseMove)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : profiledRawJointRightPhysicalSiblingAllowed A phaseMove.1
      target) :
    ∃ childCode : LinkedCode A,
      childCode.1 = target ∧
        (table.family A strategy key).ChildRealizes A strategy hwin
          ⟨key, state⟩ target childCode := by
  rcases hlocal.1.1 with ⟨exact, hexact⟩
  have hpublic := hlocal.1.2 exact hexact
  have hsourceCode : exact.1.1.code A = currentCode :=
    hpublic.1.trans hcurrentCode
  have hsourceRoot :
      profiledRawJointOneSidedCurrentSlots A .right (exact.1.1.code A) () =
        some root := by
    rw [hsourceCode]
    exact hroot
  obtain ⟨semanticMember, hmember, _hrootShape, _hmemory⟩ :=
    exact.1.1.exists_right_member_of_currentSlot A () root hsourceRoot
  have hcompatible :
      ProfiledRawJointOneSidedPhysicalAnnotationCompatible A strategy
        exact.1.1 state.1.1.2 := by
    rw [← hpublic.2]
    exact exact.2
  obtain ⟨actual, _hside, hactualTarget⟩ :=
    ProfiledRawJointOneSidedPhysicalAnnotationCompatible.exists_rightTargetChild
      A strategy exact.1.1 state.1.1.2 hcompatible semanticMember hmember
        phaseMove hphaseMove target htarget
  let move : LinkedMove A (In₁ := In₁) (In₂ := In₂) :=
    profiledRawJointOneSidedSemanticLinkedMove A strategy hwin exact.1.1
      exact.1.2
  let childCode : LinkedCode A :=
    sourceFreeBeliefParentLinkedNext
      (profiledRawJointOneSidedNext A) state.1.1 move actual
  have hchildBare : childCode.1 = target := by
    change profiledRawJointOneSidedNext A state.1.1.1 move.1 actual = target
    rw [← hpublic.1]
    change profiledRawJointOneSidedNext A (exact.1.1.code A)
      (exact.1.1.move A) actual = target
    rw [← ProfiledRawJointOneSidedSemanticState.step_code]
    exact hactualTarget
  refine ⟨childCode, hchildBare, ?_⟩
  rw [← hchildBare]
  exact hlocal.childRealizes_of_actual A strategy hwin initialMemory key table
    state exact hexact actual

/-- Left-orientation mirror of finite-effect target closure. -/
theorem EffectLocallyValid.exists_leftTargetChildRealizes
    (state : PolicyState (Memory := Memory) A strategy key)
    (hlocal :
      table.EffectLocallyValid A strategy hwin initialMemory key state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcurrentCode : state.1.1.1 = currentCode)
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .left currentCode () =
      some root)
    (phaseMove : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hphaseMove : state.1.1.2.2 = some phaseMove)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : profiledRawJointLeftPhysicalSiblingAllowed A phaseMove.1
      target) :
    ∃ childCode : LinkedCode A,
      childCode.1 = target ∧
        (table.family A strategy key).ChildRealizes A strategy hwin
          ⟨key, state⟩ target childCode := by
  rcases hlocal.1.1 with ⟨exact, hexact⟩
  have hpublic := hlocal.1.2 exact hexact
  have hsourceCode : exact.1.1.code A = currentCode :=
    hpublic.1.trans hcurrentCode
  have hsourceRoot :
      profiledRawJointOneSidedCurrentSlots A .left (exact.1.1.code A) () =
        some root := by
    rw [hsourceCode]
    exact hroot
  obtain ⟨semanticMember, hmember, _hrootShape, _hmemory⟩ :=
    exact.1.1.exists_left_member_of_currentSlot A () root hsourceRoot
  have hcompatible :
      ProfiledRawJointOneSidedPhysicalAnnotationCompatible A strategy
        exact.1.1 state.1.1.2 := by
    rw [← hpublic.2]
    exact exact.2
  obtain ⟨actual, _hside, hactualTarget⟩ :=
    ProfiledRawJointOneSidedPhysicalAnnotationCompatible.exists_leftTargetChild
      A strategy exact.1.1 state.1.1.2 hcompatible semanticMember hmember
        phaseMove hphaseMove target htarget
  let move : LinkedMove A (In₁ := In₁) (In₂ := In₂) :=
    profiledRawJointOneSidedSemanticLinkedMove A strategy hwin exact.1.1
      exact.1.2
  let childCode : LinkedCode A :=
    sourceFreeBeliefParentLinkedNext
      (profiledRawJointOneSidedNext A) state.1.1 move actual
  have hchildBare : childCode.1 = target := by
    change profiledRawJointOneSidedNext A state.1.1.1 move.1 actual = target
    rw [← hpublic.1]
    change profiledRawJointOneSidedNext A (exact.1.1.code A)
      (exact.1.1.move A) actual = target
    rw [← ProfiledRawJointOneSidedSemanticState.step_code]
    exact hactualTarget
  refine ⟨childCode, hchildBare, ?_⟩
  rw [← hchildBare]
  exact hlocal.childRealizes_of_actual A strategy hwin initialMemory key table
    state exact hexact actual

/-- The deterministic raw resolver recognizes an allowed right target and
therefore returns a genuine exact child rather than its fallback. -/
theorem EffectLocallyValid.resolveTarget_realizes_right
    (state : PolicyState (Memory := Memory) A strategy key)
    (hlocal :
      table.EffectLocallyValid A strategy hwin initialMemory key state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcurrentCode : state.1.1.1 = currentCode)
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .right currentCode () =
      some root)
    (phaseMove : ProfiledRawJointRightPhysicalSiblingMove A)
    (hphaseMove : state.1.1.2.1 = some phaseMove)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : profiledRawJointRightPhysicalSiblingAllowed A phaseMove.1
      target) :
    (table.family A strategy key).ChildRealizes A strategy hwin
      ⟨key, state⟩ target
      ((table.family A strategy key).resolveTarget A strategy hwin
        ⟨key, state⟩ target) := by
  obtain ⟨childCode, _hchildBare, hchild⟩ :=
    hlocal.exists_rightTargetChildRealizes A strategy hwin initialMemory key
      table state currentCode hcurrentCode root hroot phaseMove hphaseMove
        target htarget
  apply
    (table.family A strategy key).resolveTarget_realizes A strategy hwin
      ⟨key, state⟩ target
  exact ⟨childCode, hchild⟩

/-- Left-orientation mirror: the raw resolver cannot fall back on an allowed
installed left target. -/
theorem EffectLocallyValid.resolveTarget_realizes_left
    (state : PolicyState (Memory := Memory) A strategy key)
    (hlocal :
      table.EffectLocallyValid A strategy hwin initialMemory key state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcurrentCode : state.1.1.1 = currentCode)
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .left currentCode () =
      some root)
    (phaseMove : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hphaseMove : state.1.1.2.2 = some phaseMove)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : profiledRawJointLeftPhysicalSiblingAllowed A phaseMove.1
      target) :
    (table.family A strategy key).ChildRealizes A strategy hwin
      ⟨key, state⟩ target
      ((table.family A strategy key).resolveTarget A strategy hwin
        ⟨key, state⟩ target) := by
  obtain ⟨childCode, _hchildBare, hchild⟩ :=
    hlocal.exists_leftTargetChildRealizes A strategy hwin initialMemory key
      table state currentCode hcurrentCode root hroot phaseMove hphaseMove
        target htarget
  apply
    (table.family A strategy key).resolveTarget_realizes A strategy hwin
      ⟨key, state⟩ target
  exact ⟨childCode, hchild⟩

/-- Effect coherence at the reachable table states is already enough to
realize every selection-independent honest front context.  Hence the owner
verifier's initial state is never the rejecting sink merely because its
packet resolver used the fallback. -/
theorem EffectEnrichedValidAt.ownerFibreFrontContext_realizes
    (hvalid :
      table.EffectEnrichedValidAt A strategy hwin initialMemory key)
    (context :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreFrontContextAt A strategy
        key) :
    ∃ state :
        ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyLiveState
          (Memory := Memory) A strategy,
      table.RealizesOwnerFibreFrontContext A strategy hwin initialMemory key
        context state := by
  rcases context with context | context
  · rcases context with ⟨parameter, hinstalled, hroot⟩
    rcases parameter with ⟨rightMove, row, leftTemplate, input⟩
    let rightState :=
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.root
        A strategy initialMemory key
    let rightReceiver :=
      initialProfiledRawJointRightPhysicalSiblingReceiver A rightMove row
    let rightOwner := (rightMove.memberController A false).initial
    let data :
        ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData
          (Memory := Memory) A strategy :=
      (rightState, ⟨rightReceiver, rightOwner⟩, leftTemplate)
    let target := data.target (Memory := Memory) A strategy input
    let blockInput : In₂ × In₁ := (input.2, input.1)
    let env : Nat → In₂ × In₁ := omegaOfList [blockInput]
    have hat := profiledRawJointRightPhysicalSibling_treePlay_at_prefix A
      rightMove [] blockInput
    have hsafe := rightMove.memberController_targetSafe A false env 0 row
    have hat' :
        treePlay
            (narrowedInducedTree
              (profiledRawJointRightPhysicalSiblingMonitor A rightMove.1
                false)
              (rightMove.memberController A false).labeledTree)
            env 0 =
          narrowedRecord
            (profiledRawJointRightPhysicalSiblingMonitor A rightMove.1 false)
            ((rightMove.memberController A false).labelOf
              (rightMove.memberController A false).initial)
            (profiledRawJointRightPhysicalSiblingMonitor A rightMove.1 false
              |>.initial)
            blockInput := by
      simpa [env] using hat
    dsimp only at hsafe
    rw [hat'] at hsafe
    dsimp only [narrowedRecord] at hsafe
    have hallowed :
        profiledRawJointRightPhysicalSiblingAllowed A rightMove.1 target := by
      simpa [target, data, rightReceiver, rightOwner, blockInput] using hsafe.2
    obtain ⟨freshSlot, hfreshSlot⟩ :=
      exists_profiledRawJointLeftSlot_of_rightPhysicalTargetSafe A _ _ _ _
        hsafe.1
    have htargetRoot :
        profiledRawJointOneSidedCurrentSlots A .left target () =
          some (.inr freshSlot) := by
      change Option.map Sum.inr (target.family.left ()) =
        some (.inr freshSlot)
      have hfreshSlot' : target.family.left () = some freshSlot := by
        simpa [target, data, rightReceiver, rightOwner, blockInput] using
          hfreshSlot
      simp [hfreshSlot']
    have hlocal :
        table.EffectLocallyValid A strategy hwin initialMemory key
          rightState.2 := by
      simpa only [rightState,
        ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.root,
        sourceFreeBeliefCodeParityFiniteMemoryTransitionStateAt_nil] using
          hvalid []
    have hcurrentCode : rightState.2.1.1.1 = key.1.1 := rfl
    have hcurrentMove : rightState.2.1.1.2.1 = some rightMove := by
      exact hinstalled
    have hrealizes := hlocal.resolveTarget_realizes_right A strategy hwin
      initialMemory key table rightState.2 key.1.1 hcurrentCode
        (.inl rightMove.1.source) hroot rightMove hcurrentMove target hallowed
    obtain ⟨leftMove, hleftMove⟩ :=
      childRealizes_resolvePacket_leftMove_exists (Memory := Memory) A strategy
        hwin (table.family A strategy key) rightState target hrealizes
          (.inr freshSlot) htargetRoot
    let packet := (table.family A strategy key).resolvePacket A strategy hwin
      rightState target
    refine ⟨
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.ownerFibreRightEntryLiveState
        (Memory := Memory) A strategy rightState rightReceiver rightOwner
          leftTemplate packet leftMove, ?_⟩
    exact ⟨leftMove, hleftMove, rfl⟩
  · rcases context with ⟨parameter, hinstalled, hroot⟩
    rcases parameter with ⟨leftMove, row, rightTemplate, input⟩
    let leftState :=
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.root
        A strategy initialMemory key
    let leftReceiver :=
      initialProfiledRawJointLeftPhysicalSiblingReceiver A leftMove row
    let leftOwner := (leftMove.memberController A false).initial
    let data :
        ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData
          (Memory := Memory) A strategy :=
      (leftState, ⟨leftReceiver, leftOwner⟩, rightTemplate)
    let target := data.target (Memory := Memory) A strategy input
    let env : Nat → In₁ × In₂ := omegaOfList [input]
    have hat := profiledRawJointLeftPhysicalSibling_treePlay_at_prefix A
      leftMove [] input
    have hsafe := leftMove.memberController_targetSafe A false env 0 row
    have hat' :
        treePlay
            (narrowedInducedTree
              (profiledRawJointLeftPhysicalSiblingMonitor A leftMove.1 false)
              (leftMove.memberController A false).labeledTree)
            env 0 =
          narrowedRecord
            (profiledRawJointLeftPhysicalSiblingMonitor A leftMove.1 false)
            ((leftMove.memberController A false).labelOf
              (leftMove.memberController A false).initial)
            (profiledRawJointLeftPhysicalSiblingMonitor A leftMove.1 false
              |>.initial)
            input := by
      simpa [env] using hat
    dsimp only at hsafe
    rw [hat'] at hsafe
    dsimp only [narrowedRecord] at hsafe
    have hallowed :
        profiledRawJointLeftPhysicalSiblingAllowed A leftMove.1 target := by
      simpa [target, data, leftReceiver, leftOwner] using hsafe.2
    obtain ⟨freshSlot, hfreshSlot⟩ :=
      exists_profiledRawJointRightSlot_of_leftPhysicalTargetSafe A _ _ _ _
        hsafe.1
    have htargetRoot :
        profiledRawJointOneSidedCurrentSlots A .right target () =
          some (.inl freshSlot) := by
      change Option.map Sum.inl (target.family.right ()) =
        some (.inl freshSlot)
      have hfreshSlot' : target.family.right () = some freshSlot := by
        simpa [target, data, leftReceiver, leftOwner] using hfreshSlot
      simp [hfreshSlot']
    have hlocal :
        table.EffectLocallyValid A strategy hwin initialMemory key
          leftState.2 := by
      simpa only [leftState,
        ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.root,
        sourceFreeBeliefCodeParityFiniteMemoryTransitionStateAt_nil] using
          hvalid []
    have hcurrentCode : leftState.2.1.1.1 = key.1.1 := rfl
    have hcurrentMove : leftState.2.1.1.2.2 = some leftMove := by
      exact hinstalled
    have hrealizes := hlocal.resolveTarget_realizes_left A strategy hwin
      initialMemory key table leftState.2 key.1.1 hcurrentCode
        (.inr leftMove.1.source) hroot leftMove hcurrentMove target hallowed
    obtain ⟨rightMove, hrightMove⟩ :=
      childRealizes_resolvePacket_rightMove_exists (Memory := Memory) A
        strategy hwin (table.family A strategy key) leftState target hrealizes
          (.inl freshSlot) htargetRoot
    let packet := (table.family A strategy key).resolvePacket A strategy hwin
      leftState target
    refine ⟨
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.ownerFibreLeftEntryLiveState
        (Memory := Memory) A strategy leftState leftReceiver leftOwner
          rightTemplate packet rightMove, ?_⟩
    exact ⟨rightMove, hrightMove, rfl⟩

end

/-- Effect coherence excludes the rejecting initial sink for every honest
front context.  The chosen live state is returned together with the exact
raw-table realization used to initialize the owner monitor. -/
theorem EffectEnrichedValidAt.ownerFibreInitialState_eq_some
    (hvalid :
      table.EffectEnrichedValidAt A strategy hwin initialMemory key)
    (context :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreFrontContextAt A strategy
        key) :
    ∃ state :
        ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyLiveState
          (Memory := Memory) A strategy,
      table.ownerFibreInitialState A strategy hwin initialMemory key context =
          some state ∧
        table.RealizesOwnerFibreFrontContext A strategy hwin initialMemory key
          context state := by
  classical
  have hexists :=
    hvalid.ownerFibreFrontContext_realizes A strategy hwin initialMemory key
      table context
  let state := Classical.choose hexists
  have hstate :
      table.RealizesOwnerFibreFrontContext A strategy hwin initialMemory key
        context state :=
    Classical.choose_spec hexists
  refine ⟨state, ?_, hstate⟩
  unfold ownerFibreInitialState
  rw [dif_pos hexists]

/-- In particular, the owner-safety obligation appearing in
`EffectEnrichedChecks` starts from a live state for every context.  Thus an
accepting owner branch can no longer be vacuous through initialization
failure. -/
theorem EffectEnrichedChecks.ownerFibreSafe_from_live_realization
    (hchecks : table.EffectEnrichedChecks A strategy hwin initialMemory key)
    (context :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreFrontContextAt A strategy
        key) :
    ∃ state :
        ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyLiveState
          (Memory := Memory) A strategy,
      table.RealizesOwnerFibreFrontContext A strategy hwin initialMemory key
          context state ∧
        (table.family A strategy key).OwnerFibreSafe A strategy hwin
          (some state) := by
  obtain ⟨state, hinitial, hrealizes⟩ :=
    hchecks.1.ownerFibreInitialState_eq_some A strategy hwin initialMemory key
      table context
  refine ⟨state, hrealizes, ?_⟩
  have hsafe := hchecks.2.2 context
  rw [hinitial] at hsafe
  exact hsafe

omit [Fintype Memory] in
/-- Complete semantic meaning of the packet returned for an allowed right
target.  In particular, its installed physical annotation is the literal
annotation advance of one compatible exact source. -/
theorem EffectLocallyValid.resolvePacket_exactChild_right
    (state : PolicyState (Memory := Memory) A strategy key)
    (hlocal :
      table.EffectLocallyValid A strategy hwin initialMemory key state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcurrentCode : state.1.1.1 = currentCode)
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .right currentCode () =
      some root)
    (phaseMove : ProfiledRawJointRightPhysicalSiblingMove A)
    (hphaseMove : state.1.1.2.1 = some phaseMove)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : profiledRawJointRightPhysicalSiblingAllowed A phaseMove.1
      target) :
    let packet := (table.family A strategy key).resolvePacket A strategy hwin
      ⟨key, state⟩ target
    ∃ source : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit),
      ∃ actual : ActualDirection (In₁ := In₁) (In₂ := In₂),
        (source.step A actual).code A = target ∧
          packet.childCode.2 =
            profiledRawJointOneSidedPhysicalAnnotationAdvance A strategy hwin
              source state.1.1.2 actual ∧
          ProfiledRawJointOneSidedPhysicalAnnotationCompatible A strategy
            (source.step A actual) packet.childCode.2 := by
  dsimp only
  have hrealizes := hlocal.resolveTarget_realizes_right A strategy hwin
    initialMemory key table state currentCode hcurrentCode root hroot phaseMove
      hphaseMove target htarget
  exact childRealizes_exists_child (Memory := Memory) A strategy hwin
    (table.family A strategy key) ⟨key, state⟩ target _ hrealizes

omit [Fintype Memory] in
/-- Complete semantic meaning of the packet returned for an allowed left
target. -/
theorem EffectLocallyValid.resolvePacket_exactChild_left
    (state : PolicyState (Memory := Memory) A strategy key)
    (hlocal :
      table.EffectLocallyValid A strategy hwin initialMemory key state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcurrentCode : state.1.1.1 = currentCode)
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .left currentCode () =
      some root)
    (phaseMove : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hphaseMove : state.1.1.2.2 = some phaseMove)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : profiledRawJointLeftPhysicalSiblingAllowed A phaseMove.1
      target) :
    let packet := (table.family A strategy key).resolvePacket A strategy hwin
      ⟨key, state⟩ target
    ∃ source : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit),
      ∃ actual : ActualDirection (In₁ := In₁) (In₂ := In₂),
        (source.step A actual).code A = target ∧
          packet.childCode.2 =
            profiledRawJointOneSidedPhysicalAnnotationAdvance A strategy hwin
              source state.1.1.2 actual ∧
          ProfiledRawJointOneSidedPhysicalAnnotationCompatible A strategy
            (source.step A actual) packet.childCode.2 := by
  dsimp only
  have hrealizes := hlocal.resolveTarget_realizes_left A strategy hwin
    initialMemory key table state currentCode hcurrentCode root hroot phaseMove
      hphaseMove target htarget
  exact childRealizes_exists_child (Memory := Memory) A strategy hwin
    (table.family A strategy key) ⟨key, state⟩ target _ hrealizes

end
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTable

end

end DetParityAutomaton

end DistributedSynthesis
