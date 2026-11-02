/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEffectTargetClosure

/-!
# The exact semantic table satisfies the finite-effect forward checks

For every admissible root key, retain as proof-side memory the exact semantic
source together with its compatible installed physical annotation.  The
successor table follows the canonical finite-code representative from that
source.  This memory is generally infinite, so this is not yet the desired
finite controller.

The point of the construction is to separate existence from regularization:
the exact table satisfies canonical finite-effect coherence and universal
forward parity directly from `hwin`.  For a finite quotient, the existing
effect target-closure theorem then realizes every honest front context.  The
only property not established here is parity of the complete literal owner
trace.  A later regularization theorem must preserve that trace property while
quotienting the exact memory.
-/

namespace DistributedSynthesis

universe u v x y s m

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

private abbrev ExactMemory :=
  ProfiledRawJointOneSidedPhysicalExactCommonActionMemory A strategy

private abbrev ExactTable (key : RootKey A strategy) :=
  ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTable
    (Memory := ExactMemory A strategy) A strategy key

private abbrev ExactPolicyState (key : RootKey A strategy) :=
  ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyState
    (Memory := ExactMemory A strategy) A key.1.1

private abbrev ExactBankControl :=
  ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankControl
    (Memory := ExactMemory A strategy) A strategy

namespace
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTable

/-! ## The owner condition without a finiteness assumption -/

/-- The rejecting-sink initialization used by the finite verifier, stated
without assuming that the table memory is finite. -/
def ownerFibreInitialStateUnrestricted
    {Memory : Type m}
    (initialMemory : RootKey A strategy → Memory)
    (key : RootKey A strategy)
    (table :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTable
        (Memory := Memory) A strategy key)
    (context :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreFrontContextAt A strategy
        key) :
    ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyState
      (Memory := Memory) A strategy := by
  classical
  letI : Decidable (∃ state,
      table.RealizesOwnerFibreFrontContext A strategy hwin initialMemory key
        context state) := Classical.propDecidable _
  exact if h : ∃ state,
      table.RealizesOwnerFibreFrontContext A strategy hwin initialMemory key
        context state then
    some (Classical.choose h)
  else
    none

/-- Literal owner-fibre parity for a table with arbitrary memory.  This is the
semantic continuation of `EnrichedOwnerSafe` before finite regularization. -/
def EnrichedOwnerSafeUnrestricted
    {Memory : Type m}
    (initialMemory : RootKey A strategy → Memory)
    (key : RootKey A strategy)
    (table :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTable
        (Memory := Memory) A strategy key) : Prop :=
  ∀ context :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreFrontContextAt A strategy
        key,
    (table.family A strategy key).OwnerFibreSafe A strategy hwin
      (ownerFibreInitialStateUnrestricted A strategy hwin initialMemory key
        table context)

/-- The checked-table conjunction with its owner component exposed for
possibly infinite memory. -/
def EffectEnrichedChecksUnrestricted
    {Memory : Type m}
    (initialMemory : RootKey A strategy → Memory)
    (key : RootKey A strategy)
    (table :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTable
        (Memory := Memory) A strategy key) : Prop :=
  table.EffectEnrichedValidAt A strategy hwin initialMemory key ∧
    table.EnrichedForwardAccepts A strategy initialMemory key ∧
    EnrichedOwnerSafeUnrestricted A strategy hwin initialMemory key table

/-- On finite memory, unrestricted initialization is exactly the initializer
used by the finite enriched verifier. -/
theorem ownerFibreInitialStateUnrestricted_eq
    {Memory : Type m} [Fintype Memory]
    (initialMemory : RootKey A strategy → Memory)
    (key : RootKey A strategy)
    (table :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTable
        (Memory := Memory) A strategy key)
    (context :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreFrontContextAt A strategy
        key) :
    ownerFibreInitialStateUnrestricted A strategy hwin initialMemory key table
        context =
      table.ownerFibreInitialState A strategy hwin initialMemory key context := by
  classical
  by_cases h : ∃ state,
      table.RealizesOwnerFibreFrontContext A strategy hwin initialMemory key
        context state
  · simp only [ownerFibreInitialStateUnrestricted, ownerFibreInitialState,
      dif_pos h]
  · simp only [ownerFibreInitialStateUnrestricted, ownerFibreInitialState,
      dif_neg h]

/-- Hence the unrestricted checked-table predicate is a conservative
extension of the finite verifier's target. -/
theorem effectEnrichedChecksUnrestricted_iff_effectEnrichedChecks
    {Memory : Type m} [Fintype Memory]
    (initialMemory : RootKey A strategy → Memory)
    (key : RootKey A strategy)
    (table :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTable
        (Memory := Memory) A strategy key) :
    EffectEnrichedChecksUnrestricted A strategy hwin initialMemory key table ↔
      table.EffectEnrichedChecks A strategy hwin initialMemory key := by
  unfold EffectEnrichedChecksUnrestricted EffectEnrichedChecks
    EnrichedOwnerSafeUnrestricted EnrichedOwnerSafe
  simp only [ownerFibreInitialStateUnrestricted_eq]

/-- The one exact root witness fixed for each admissible public key. -/
def exactInitialMemory (key : RootKey A strategy) : ExactMemory A strategy :=
  canonicalExactInitial A strategy key

/-- Public linked code carried by an exact semantic memory cell. -/
def exactMemoryPublicCode (memory : ExactMemory A strategy) : LinkedCode A :=
  (memory.1.1.code A, memory.1.2)

/-- The perfect-recall transition table.  Its public successor row is the
finite effect of the exact source stored in the current memory cell, and its
memory successor is the corresponding literal exact child. -/
def exactEffectTable (key : RootKey A strategy) : ExactTable A strategy key :=
  ⟨fun state childCode ↦
    let move := profiledRawJointOneSidedSemanticLinkedMove A strategy hwin
      state.2.1.1 state.2.1.2
    let nextCode := PolicyNext A (In₁ := In₁) (In₂ := In₂)
      state.1.1 move childCode
    ((nextCode, (PolicyDPA A key.1.1).step state.1.2 nextCode),
      exactStep A strategy hwin state.2 childCode)⟩

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem exactInitialMemory_apply
    (key : RootKey A strategy) :
    exactInitialMemory A strategy key = canonicalExactInitial A strategy key :=
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem exactMemoryPublicCode_initial
    (key : RootKey A strategy) :
    exactMemoryPublicCode A strategy
        (exactInitialMemory A strategy key) = key.1 := by
  apply Prod.ext
  · exact canonicalExactInitial_code A strategy key
  · exact canonicalExactInitial_annotation A strategy key

@[simp] theorem exactEffectTable_successor_fst
    (key : RootKey A strategy)
    (state : ExactPolicyState A strategy key)
    (childCode : LinkedCode A) :
    (exactEffectTable A strategy hwin key |>.successor state childCode).1 =
      sourceFreeBeliefCodeParityControllerNext
        (PolicyDPA A key.1.1) state.1
        (profiledRawJointOneSidedSemanticLinkedMove A strategy hwin
          state.2.1.1 state.2.1.2)
        (PolicyNext A (In₁ := In₁) (In₂ := In₂) state.1.1
          (profiledRawJointOneSidedSemanticLinkedMove A strategy hwin
            state.2.1.1 state.2.1.2)
          childCode) :=
  rfl

@[simp] theorem exactEffectTable_successor_memory
    (key : RootKey A strategy)
    (state : ExactPolicyState A strategy key)
    (childCode : LinkedCode A) :
    (exactEffectTable A strategy hwin key |>.successor state childCode).2 =
      exactStep A strategy hwin state.2 childCode :=
  rfl

/-! ## Exact alignment beyond ordinary table-reachable states -/

/-- A fixed-key policy state is aligned when its public linked code is
exactly the code and installed annotation of its semantic memory cell.  This
predicate does not require the state to have arisen from the ordinary table
fold, and can therefore be maintained across owner-fibre resolver jumps. -/
def ExactPolicyAligned
    (key : RootKey A strategy)
    (state : ExactPolicyState A strategy key) : Prop :=
  state.1.1 = exactMemoryPublicCode A strategy state.2

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The exact table starts aligned at every admissible root key. -/
theorem exactEffectTable_root_aligned
    (key : RootKey A strategy) :
    ExactPolicyAligned A strategy key
      ((key.1, (PolicyDPA A key.1.1).initial),
        exactInitialMemory A strategy key) := by
  exact (exactMemoryPublicCode_initial A strategy key).symm

/-- Exact alignment is invariant under every public child-code transition,
including child codes chosen by an owner-fibre resolver. -/
theorem ExactPolicyAligned.successor
    (key : RootKey A strategy)
    (state : ExactPolicyState A strategy key)
    (haligned : ExactPolicyAligned A strategy key state)
    (childCode : LinkedCode A) :
    ExactPolicyAligned A strategy key
      ((exactEffectTable A strategy hwin key).successor state childCode) := by
  change
    (PolicyNext A (In₁ := In₁) (In₂ := In₂) state.1.1
        (profiledRawJointOneSidedSemanticLinkedMove A strategy hwin
          state.2.1.1 state.2.1.2)
        childCode) =
      exactMemoryPublicCode A strategy
        (exactStep A strategy hwin state.2 childCode)
  rw [haligned]
  exact (exactStep_publicCode A strategy hwin state.2 childCode).symm

/-- The family-level bank successor preserves exact alignment at its fixed
key.  The theorem is stated at the bank interface used by the owner kernel. -/
theorem ExactPolicyAligned.family_successor
    (key : RootKey A strategy)
    (state : ExactPolicyState A strategy key)
    (haligned : ExactPolicyAligned A strategy key state)
    (childCode : LinkedCode A) :
    ExactPolicyAligned A strategy key
      (((exactEffectTable A strategy hwin key).family A strategy key
          |>.successor A strategy ⟨key, state⟩ childCode).2) := by
  simpa only [family,
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.successor,
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.singletonAt_apply_key]
    using haligned.successor A strategy hwin key state childCode

/-- Every literal semantic direction from an aligned exact cell is visible
to the raw-table resolver as a genuine child realization.  Unlike the
reachable-state closure theorem, this statement remains applicable after an
arbitrary sequence of owner-fibre resolver jumps. -/
theorem ExactPolicyAligned.childRealizes_of_actual
    (key : RootKey A strategy)
    (state : ExactPolicyState A strategy key)
    (haligned : ExactPolicyAligned A strategy key state)
    (actual : ActualDirection (In₁ := In₁) (In₂ := In₂)) :
    let move := profiledRawJointOneSidedSemanticLinkedMove A strategy hwin
      state.2.1.1 state.2.1.2
    let childCode := sourceFreeBeliefParentLinkedNext
      (profiledRawJointOneSidedNext A) state.1.1 move actual
    ((exactEffectTable A strategy hwin key).family A strategy key
      ).ChildRealizes A strategy hwin ⟨key, state⟩ childCode.1 childCode := by
  dsimp only
  let move : LinkedMove A (In₁ := In₁) (In₂ := In₂) :=
    profiledRawJointOneSidedSemanticLinkedMove A strategy hwin state.2.1.1
      state.2.1.2
  let childCode : LinkedCode A :=
    sourceFreeBeliefParentLinkedNext
      (profiledRawJointOneSidedNext A) state.1.1 move actual
  have hcode : state.2.1.1.code A = state.1.1.1 :=
    (congrArg Prod.fst haligned).symm
  have hannotation : state.2.1.2 = state.1.1.2 :=
    (congrArg Prod.snd haligned).symm
  have hnext :
      PolicyNext A (In₁ := In₁) (In₂ := In₂) state.1.1 move
          childCode =
        childCode := by
    exact sourceFreeBeliefFiniteCodeNext_of_direction
      (sourceFreeBeliefParentLinkedNext (profiledRawJointOneSidedNext A))
      state.1.1 move actual
  refine ⟨move, state.2.1.1, actual, hcode, rfl, ?_, ?_, rfl, rfl, ?_⟩
  · rw [← hannotation]
    exact state.2.2
  · intro direction
    change
      profiledRawJointOneSidedPhysicalAnnotationAdvance A strategy hwin
          state.2.1.1 state.1.1.2 direction =
        profiledRawJointOneSidedPhysicalAnnotationAdvance A strategy hwin
          state.2.1.1 state.2.1.2 direction
    rw [← hannotation]
  · simp only [family,
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.successor,
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.singletonAt_apply_key,
      exactEffectTable_successor_fst,
      sourceFreeBeliefCodeParityControllerNext]
    change
      (PolicyNext A (In₁ := In₁) (In₂ := In₂) state.1.1 move
          childCode,
        (PolicyDPA A key.1.1).step state.1.2
          (PolicyNext A (In₁ := In₁) (In₂ := In₂) state.1.1 move
            childCode)) =
        (childCode, (PolicyDPA A key.1.1).step state.1.2 childCode)
    rw [hnext]

/-- At an aligned exact cell, every target allowed by the installed right
physical table has a literal semantic child recognized by the resolver. -/
theorem ExactPolicyAligned.exists_rightTargetChildRealizes
    (key : RootKey A strategy)
    (state : ExactPolicyState A strategy key)
    (haligned : ExactPolicyAligned A strategy key state)
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
        ((exactEffectTable A strategy hwin key).family A strategy key
          ).ChildRealizes A strategy hwin ⟨key, state⟩ target childCode := by
  have hsourceCode : state.2.1.1.code A = currentCode :=
    (congrArg Prod.fst haligned).symm.trans hcurrentCode
  have hsourceRoot :
      profiledRawJointOneSidedCurrentSlots A .right
          (state.2.1.1.code A) () = some root := by
    rw [hsourceCode]
    exact hroot
  obtain ⟨semanticMember, hmember, _hrootShape, _hmemory⟩ :=
    state.2.1.1.exists_right_member_of_currentSlot A () root hsourceRoot
  have hcompatible :
      ProfiledRawJointOneSidedPhysicalAnnotationCompatible A strategy
        state.2.1.1 state.1.1.2 := by
    rw [congrArg Prod.snd haligned]
    exact state.2.2
  obtain ⟨actual, _hside, hactualTarget⟩ :=
    ProfiledRawJointOneSidedPhysicalAnnotationCompatible.exists_rightTargetChild
      A strategy state.2.1.1 state.1.1.2 hcompatible semanticMember hmember
        phaseMove hphaseMove target htarget
  let move : LinkedMove A (In₁ := In₁) (In₂ := In₂) :=
    profiledRawJointOneSidedSemanticLinkedMove A strategy hwin state.2.1.1
      state.2.1.2
  let childCode : LinkedCode A :=
    sourceFreeBeliefParentLinkedNext
      (profiledRawJointOneSidedNext A) state.1.1 move actual
  have hchildBare : childCode.1 = target := by
    change profiledRawJointOneSidedNext A state.1.1.1 move.1 actual = target
    rw [← (congrArg Prod.fst haligned).symm]
    change profiledRawJointOneSidedNext A (state.2.1.1.code A)
      (state.2.1.1.move A) actual = target
    rw [← ProfiledRawJointOneSidedSemanticState.step_code]
    exact hactualTarget
  refine ⟨childCode, hchildBare, ?_⟩
  rw [← hchildBare]
  exact haligned.childRealizes_of_actual A strategy hwin key state actual

/-- Left-orientation mirror of exact aligned target closure. -/
theorem ExactPolicyAligned.exists_leftTargetChildRealizes
    (key : RootKey A strategy)
    (state : ExactPolicyState A strategy key)
    (haligned : ExactPolicyAligned A strategy key state)
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
        ((exactEffectTable A strategy hwin key).family A strategy key
          ).ChildRealizes A strategy hwin ⟨key, state⟩ target childCode := by
  have hsourceCode : state.2.1.1.code A = currentCode :=
    (congrArg Prod.fst haligned).symm.trans hcurrentCode
  have hsourceRoot :
      profiledRawJointOneSidedCurrentSlots A .left
          (state.2.1.1.code A) () = some root := by
    rw [hsourceCode]
    exact hroot
  obtain ⟨semanticMember, hmember, _hrootShape, _hmemory⟩ :=
    state.2.1.1.exists_left_member_of_currentSlot A () root hsourceRoot
  have hcompatible :
      ProfiledRawJointOneSidedPhysicalAnnotationCompatible A strategy
        state.2.1.1 state.1.1.2 := by
    rw [congrArg Prod.snd haligned]
    exact state.2.2
  obtain ⟨actual, _hside, hactualTarget⟩ :=
    ProfiledRawJointOneSidedPhysicalAnnotationCompatible.exists_leftTargetChild
      A strategy state.2.1.1 state.1.1.2 hcompatible semanticMember hmember
        phaseMove hphaseMove target htarget
  let move : LinkedMove A (In₁ := In₁) (In₂ := In₂) :=
    profiledRawJointOneSidedSemanticLinkedMove A strategy hwin state.2.1.1
      state.2.1.2
  let childCode : LinkedCode A :=
    sourceFreeBeliefParentLinkedNext
      (profiledRawJointOneSidedNext A) state.1.1 move actual
  have hchildBare : childCode.1 = target := by
    change profiledRawJointOneSidedNext A state.1.1.1 move.1 actual = target
    rw [← (congrArg Prod.fst haligned).symm]
    change profiledRawJointOneSidedNext A (state.2.1.1.code A)
      (state.2.1.1.move A) actual = target
    rw [← ProfiledRawJointOneSidedSemanticState.step_code]
    exact hactualTarget
  refine ⟨childCode, hchildBare, ?_⟩
  rw [← hchildBare]
  exact haligned.childRealizes_of_actual A strategy hwin key state actual

/-- Hence the deterministic resolver cannot use its fallback on an allowed
right target, even after earlier resolver jumps have left the ordinary table
fold. -/
theorem ExactPolicyAligned.resolveTarget_realizes_right
    (key : RootKey A strategy)
    (state : ExactPolicyState A strategy key)
    (haligned : ExactPolicyAligned A strategy key state)
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
    ((exactEffectTable A strategy hwin key).family A strategy key
      ).ChildRealizes A strategy hwin ⟨key, state⟩ target
        (((exactEffectTable A strategy hwin key).family A strategy key
          ).resolveTarget A strategy hwin ⟨key, state⟩ target) := by
  obtain ⟨childCode, _hchildBare, hchild⟩ :=
    haligned.exists_rightTargetChildRealizes A strategy hwin key state
      currentCode hcurrentCode root hroot phaseMove hphaseMove target htarget
  apply
    ((exactEffectTable A strategy hwin key).family A strategy key
      ).resolveTarget_realizes A strategy hwin ⟨key, state⟩ target
  exact ⟨childCode, hchild⟩

/-- Left-orientation mirror: the exact resolver cannot fall back on an
allowed installed left target. -/
theorem ExactPolicyAligned.resolveTarget_realizes_left
    (key : RootKey A strategy)
    (state : ExactPolicyState A strategy key)
    (haligned : ExactPolicyAligned A strategy key state)
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
    ((exactEffectTable A strategy hwin key).family A strategy key
      ).ChildRealizes A strategy hwin ⟨key, state⟩ target
        (((exactEffectTable A strategy hwin key).family A strategy key
          ).resolveTarget A strategy hwin ⟨key, state⟩ target) := by
  obtain ⟨childCode, _hchildBare, hchild⟩ :=
    haligned.exists_leftTargetChildRealizes A strategy hwin key state
      currentCode hcurrentCode root hroot phaseMove hphaseMove target htarget
  apply
    ((exactEffectTable A strategy hwin key).family A strategy key
      ).resolveTarget_realizes A strategy hwin ⟨key, state⟩ target
  exact ⟨childCode, hchild⟩

/-- Every resolved packet from an aligned exact cell carries an aligned
successor.  Target closure is needed to identify the requested bare target,
but not to preserve the semantic-memory synchronization itself. -/
theorem ExactPolicyAligned.resolvePacket_successor
    (key : RootKey A strategy)
    (state : ExactPolicyState A strategy key)
    (haligned : ExactPolicyAligned A strategy key state)
    (target : ProfiledRawJointIncidenceCode A (I := Unit)) :
    ExactPolicyAligned A strategy key
      ((((exactEffectTable A strategy hwin key).family A strategy key
        ).resolvePacket A strategy hwin ⟨key, state⟩ target).successor.2) := by
  exact haligned.family_successor A strategy hwin key state
    (((exactEffectTable A strategy hwin key).family A strategy key
      ).resolveTarget A strategy hwin ⟨key, state⟩ target)

/-- A child accepted by the raw realization predicate is also the literal
public child of the exact memory stored in the same aligned cell.  This is
the key anti-mosaic consequence of retaining perfect-recall memory: the
existential source inside `ChildRealizes` cannot redirect the executable
successor away from the stored exact source. -/
theorem ExactPolicyAligned.childRealizes_exactStep_publicCode
    (key : RootKey A strategy)
    (state : ExactPolicyState A strategy key)
    (haligned : ExactPolicyAligned A strategy key state)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (childCode : LinkedCode A)
    (hrealizes :
      ((exactEffectTable A strategy hwin key).family A strategy key
        ).ChildRealizes A strategy hwin ⟨key, state⟩ target childCode) :
    exactMemoryPublicCode A strategy
        (exactStep A strategy hwin state.2 childCode) =
      childCode := by
  rcases hrealizes with
    ⟨_move, _source, _actual, _hcode, _hmove, _hcompatible, _hchildren,
      _hchildCode, _hbare, hsuccessor⟩
  have hnextAligned :=
    haligned.family_successor A strategy hwin key state childCode
  simpa only [family,
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.successor,
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.singletonAt_apply_key,
    exactEffectTable_successor_memory] using
      hnextAligned.symm.trans (congrArg Prod.fst hsuccessor)

/-- Every realized child of an aligned exact cell advances the semantic
source stored in that cell to the requested bare target. -/
theorem ExactPolicyAligned.childRealizes_exactStep_code
    (key : RootKey A strategy)
    (state : ExactPolicyState A strategy key)
    (haligned : ExactPolicyAligned A strategy key state)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (childCode : LinkedCode A)
    (hrealizes :
      ((exactEffectTable A strategy hwin key).family A strategy key
        ).ChildRealizes A strategy hwin ⟨key, state⟩ target childCode) :
    (exactStep A strategy hwin state.2 childCode).1.1.code A = target := by
  have hpublic := haligned.childRealizes_exactStep_publicCode A strategy hwin
    key state target childCode hrealizes
  have hbare : childCode.1 = target := by
    rcases hrealizes with
      ⟨_move, _source, _actual, _hcode, _hmove, _hcompatible, _hchildren,
        _hchildCode, hbare, _hsuccessor⟩
    exact hbare
  exact (congrArg Prod.fst hpublic).trans hbare

/-- The semantic direction chosen internally by `exactStep` has the right
orientation whenever the realized target exposes a live left slot. -/
theorem ExactPolicyAligned.childRealizes_exactStep_side_right
    (key : RootKey A strategy)
    (state : ExactPolicyState A strategy key)
    (haligned : ExactPolicyAligned A strategy key state)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (childCode : LinkedCode A)
    (hrealizes :
      ((exactEffectTable A strategy hwin key).family A strategy key
        ).ChildRealizes A strategy hwin ⟨key, state⟩ target childCode)
    (root : ProfiledRawJointThreadRoot A)
    (htargetRoot :
      profiledRawJointOneSidedCurrentSlots A .left target () = some root) :
    let move := profiledRawJointOneSidedSemanticLinkedMove A strategy hwin
      state.2.1.1 state.2.1.2
    let actual := profiledRawJointOneSidedPhysicalActualOfChildCode A
      (state.2.1.1.code A, state.2.1.2) move childCode
    actual.side = .right := by
  dsimp only
  let move := profiledRawJointOneSidedSemanticLinkedMove A strategy hwin
    state.2.1.1 state.2.1.2
  let actual := profiledRawJointOneSidedPhysicalActualOfChildCode A
    (state.2.1.1.code A, state.2.1.2) move childCode
  have hstepCode : (state.2.1.1.step A actual).code A = target := by
    simpa only [exactStep, move, actual] using
      haligned.childRealizes_exactStep_code A strategy hwin key state target
        childCode hrealizes
  apply profiledRawJoint_actualSide_eq_of_next_currentSlot A .right
    (state.2.1.1.code A) state.2.1.1.move actual () root
  rw [← ProfiledRawJointOneSidedSemanticState.step_code, hstepCode]
  exact htargetRoot

/-- Left-orientation mirror of exact-step side recovery. -/
theorem ExactPolicyAligned.childRealizes_exactStep_side_left
    (key : RootKey A strategy)
    (state : ExactPolicyState A strategy key)
    (haligned : ExactPolicyAligned A strategy key state)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (childCode : LinkedCode A)
    (hrealizes :
      ((exactEffectTable A strategy hwin key).family A strategy key
        ).ChildRealizes A strategy hwin ⟨key, state⟩ target childCode)
    (root : ProfiledRawJointThreadRoot A)
    (htargetRoot :
      profiledRawJointOneSidedCurrentSlots A .right target () = some root) :
    let move := profiledRawJointOneSidedSemanticLinkedMove A strategy hwin
      state.2.1.1 state.2.1.2
    let actual := profiledRawJointOneSidedPhysicalActualOfChildCode A
      (state.2.1.1.code A, state.2.1.2) move childCode
    actual.side = .left := by
  dsimp only
  let move := profiledRawJointOneSidedSemanticLinkedMove A strategy hwin
    state.2.1.1 state.2.1.2
  let actual := profiledRawJointOneSidedPhysicalActualOfChildCode A
    (state.2.1.1.code A, state.2.1.2) move childCode
  have hstepCode : (state.2.1.1.step A actual).code A = target := by
    simpa only [exactStep, move, actual] using
      haligned.childRealizes_exactStep_code A strategy hwin key state target
        childCode hrealizes
  apply profiledRawJoint_actualSide_eq_of_next_currentSlot A .left
    (state.2.1.1.code A) state.2.1.1.move actual () root
  rw [← ProfiledRawJointOneSidedSemanticState.step_code, hstepCode]
  exact htargetRoot

/-- Complete semantic edge certificate for an allowed right resolver jump.
The packet's stored memory is not merely code-compatible with some witness:
it is the literal right semantic child of the exact source already stored in
the parent cell, with the literal advanced physical annotation. -/
theorem ExactPolicyAligned.resolvePacket_exact_right
    (key : RootKey A strategy)
    (state : ExactPolicyState A strategy key)
    (haligned : ExactPolicyAligned A strategy key state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcurrentCode : state.1.1.1 = currentCode)
    (currentRoot : ProfiledRawJointThreadRoot A)
    (hcurrentRoot :
      profiledRawJointOneSidedCurrentSlots A .right currentCode () =
        some currentRoot)
    (phaseMove : ProfiledRawJointRightPhysicalSiblingMove A)
    (hphaseMove : state.1.1.2.1 = some phaseMove)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : profiledRawJointRightPhysicalSiblingAllowed A phaseMove.1
      target)
    (targetRoot : ProfiledRawJointThreadRoot A)
    (htargetRoot :
      profiledRawJointOneSidedCurrentSlots A .left target () =
        some targetRoot) :
    let tables := (exactEffectTable A strategy hwin key).family A strategy key
    let packet := tables.resolvePacket A strategy hwin ⟨key, state⟩ target
    ∃ actual : ActualDirection (In₁ := In₁) (In₂ := In₂),
      actual.side = .right ∧
        packet.childCode.1 = target ∧
        packet.successor.2.2.1.1 = state.2.1.1.step A actual ∧
        packet.successor.2.2.1.2 =
          profiledRawJointOneSidedPhysicalAnnotationAdvance A strategy hwin
            state.2.1.1 state.2.1.2 actual := by
  dsimp only
  let tables := (exactEffectTable A strategy hwin key).family A strategy key
  let childCode := tables.resolveTarget A strategy hwin ⟨key, state⟩ target
  let move := profiledRawJointOneSidedSemanticLinkedMove A strategy hwin
    state.2.1.1 state.2.1.2
  let actual := profiledRawJointOneSidedPhysicalActualOfChildCode A
    (state.2.1.1.code A, state.2.1.2) move childCode
  have hrealizes := haligned.resolveTarget_realizes_right A strategy hwin key
    state currentCode hcurrentCode currentRoot hcurrentRoot phaseMove
      hphaseMove target htarget
  have hbare : childCode.1 = target := by
    rcases hrealizes with
      ⟨_move, _source, _actual, _hcode, _hmove, _hcompatible, _hchildren,
        _hchildCode, hbare, _hsuccessor⟩
    exact hbare
  have hside : actual.side = .right := by
    exact haligned.childRealizes_exactStep_side_right A strategy hwin key
      state target childCode hrealizes targetRoot htargetRoot
  refine ⟨actual, hside, hbare, ?_, ?_⟩
  · simp [tables, childCode,
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.resolvePacket,
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.successor,
      family, exactEffectTable, exactStep, actual, move]
  · simp [tables, childCode,
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.resolvePacket,
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.successor,
      family, exactEffectTable, exactStep, actual, move]

/-- Left-orientation mirror of the complete exact resolver-edge
certificate. -/
theorem ExactPolicyAligned.resolvePacket_exact_left
    (key : RootKey A strategy)
    (state : ExactPolicyState A strategy key)
    (haligned : ExactPolicyAligned A strategy key state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcurrentCode : state.1.1.1 = currentCode)
    (currentRoot : ProfiledRawJointThreadRoot A)
    (hcurrentRoot :
      profiledRawJointOneSidedCurrentSlots A .left currentCode () =
        some currentRoot)
    (phaseMove : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hphaseMove : state.1.1.2.2 = some phaseMove)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : profiledRawJointLeftPhysicalSiblingAllowed A phaseMove.1
      target)
    (targetRoot : ProfiledRawJointThreadRoot A)
    (htargetRoot :
      profiledRawJointOneSidedCurrentSlots A .right target () =
        some targetRoot) :
    let tables := (exactEffectTable A strategy hwin key).family A strategy key
    let packet := tables.resolvePacket A strategy hwin ⟨key, state⟩ target
    ∃ actual : ActualDirection (In₁ := In₁) (In₂ := In₂),
      actual.side = .left ∧
        packet.childCode.1 = target ∧
        packet.successor.2.2.1.1 = state.2.1.1.step A actual ∧
        packet.successor.2.2.1.2 =
          profiledRawJointOneSidedPhysicalAnnotationAdvance A strategy hwin
            state.2.1.1 state.2.1.2 actual := by
  dsimp only
  let tables := (exactEffectTable A strategy hwin key).family A strategy key
  let childCode := tables.resolveTarget A strategy hwin ⟨key, state⟩ target
  let move := profiledRawJointOneSidedSemanticLinkedMove A strategy hwin
    state.2.1.1 state.2.1.2
  let actual := profiledRawJointOneSidedPhysicalActualOfChildCode A
    (state.2.1.1.code A, state.2.1.2) move childCode
  have hrealizes := haligned.resolveTarget_realizes_left A strategy hwin key
    state currentCode hcurrentCode currentRoot hcurrentRoot phaseMove
      hphaseMove target htarget
  have hbare : childCode.1 = target := by
    rcases hrealizes with
      ⟨_move, _source, _actual, _hcode, _hmove, _hcompatible, _hchildren,
        _hchildCode, hbare, _hsuccessor⟩
    exact hbare
  have hside : actual.side = .left := by
    exact haligned.childRealizes_exactStep_side_left A strategy hwin key
      state target childCode hrealizes targetRoot htargetRoot
  refine ⟨actual, hside, hbare, ?_, ?_⟩
  · simp [tables, childCode,
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.resolvePacket,
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.successor,
      family, exactEffectTable, exactStep, actual, move]
  · simp [tables, childCode,
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.resolvePacket,
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.successor,
      family, exactEffectTable, exactStep, actual, move]


/-- The table fold never loses the exact semantic source stored in its memory
coordinate. -/
theorem exactEffectTable_stateAt_memory
    (key : RootKey A strategy)
    (node : TreeNode (LinkedCode A)) :
    (sourceFreeBeliefCodeParityFiniteMemoryTransitionStateAt
      (PolicyDPA A key.1.1) key.1 (exactInitialMemory A strategy key)
      (exactEffectTable A strategy hwin key) node).2 =
        exactStateAt A strategy hwin (canonicalExactInitial A strategy key)
          node := by
  induction node using List.reverseRecOn with
  | nil => rfl
  | append_singleton node childCode ih =>
      rw [sourceFreeBeliefCodeParityFiniteMemoryTransitionStateAt_append,
        exactStateAt_append, exactEffectTable_successor_memory, ih]

/-- The independently defined exact fold is the semantic-tree fold of the
perfect-recall common-action certificate. -/
theorem exactStateAt_eq_exactSemanticTree_stateAt
    (key : RootKey A strategy)
    (node : TreeNode (LinkedCode A)) :
    exactStateAt A strategy hwin (canonicalExactInitial A strategy key) node =
      (profiledRawJointOneSidedPhysicalExactCommonActionCertificate A strategy
        hwin
        (profiledRawJointOneSidedPhysicalCompatibleBankSource A strategy key)
        key.1.2
        (profiledRawJointOneSidedPhysicalCompatibleBankSource_compatible A
          strategy key)).semanticTree.stateAt node := by
  induction node using List.reverseRecOn with
  | nil => rfl
  | append_singleton node childCode ih =>
      rw [exactStateAt_append,
        SourceFreeBeliefSemanticTree.stateAt_append, ih]
      rfl

/-- At every reachable table state, the public linked code is exactly the
code and installed annotation of its exact memory cell. -/
theorem exactEffectTable_stateAt_public
    (key : RootKey A strategy)
    (node : TreeNode (LinkedCode A)) :
    let state :=
      sourceFreeBeliefCodeParityFiniteMemoryTransitionStateAt
        (PolicyDPA A key.1.1) key.1 (exactInitialMemory A strategy key)
        (exactEffectTable A strategy hwin key) node
    state.1.1 = exactMemoryPublicCode A strategy state.2 := by
  induction node using List.reverseRecOn with
  | nil =>
      exact (exactMemoryPublicCode_initial A strategy key).symm
  | append_singleton node childCode ih =>
      rw [sourceFreeBeliefCodeParityFiniteMemoryTransitionStateAt_append]
      change
        PolicyNext A (In₁ := In₁) (In₂ := In₂)
            _
            (profiledRawJointOneSidedSemanticLinkedMove A strategy hwin
              _ _) childCode =
          exactMemoryPublicCode A strategy
            (exactStep A strategy hwin _ childCode)
      rw [ih]
      exact (exactStep_publicCode A strategy hwin _ childCode).symm

/-- The objective coordinate of the exact table fold is the DPA run on the
successive public codes of the exact semantic memory tree. -/
theorem exactEffectTable_stateAt_dpa
    (key : RootKey A strategy)
    (node : TreeNode (LinkedCode A)) :
    let tableState :=
      sourceFreeBeliefCodeParityFiniteMemoryTransitionStateAt
        (PolicyDPA A key.1.1) key.1 (exactInitialMemory A strategy key)
        (exactEffectTable A strategy hwin key) node
    let semantic :=
      (profiledRawJointOneSidedPhysicalExactCommonActionCertificate A strategy
        hwin
        (profiledRawJointOneSidedPhysicalCompatibleBankSource A strategy key)
        key.1.2
        (profiledRawJointOneSidedPhysicalCompatibleBankSource_compatible A
          strategy key)).semanticTree
    tableState.1.2 = (semantic.codeParityStateAt (PolicyDPA A key.1.1) node).2 := by
  induction node using List.reverseRecOn with
  | nil => rfl
  | append_singleton node childCode ih =>
      rw [sourceFreeBeliefCodeParityFiniteMemoryTransitionStateAt_append]
      simp only
      rw [SourceFreeBeliefSemanticTree.codeParityStateAt_append]
      simp only
      rw [exactEffectTable_successor_fst]
      unfold sourceFreeBeliefCodeParityControllerNext
      simp only
      rw [ih]
      congr 1
      rw [SourceFreeBeliefSemanticTree.codeParityStateAt_fst]
      rw [exactEffectTable_stateAt_public,
        exactEffectTable_stateAt_memory,
        exactStateAt_eq_exactSemanticTree_stateAt]
      exact (exactStep_publicCode A strategy hwin _ childCode).symm

/-- Every exact history represented by a reachable exact-table cell is
literally the cell's exact memory coordinate. -/
theorem canonicalBelief_exactEffectTable_eq_memory
    (key : RootKey A strategy)
    (state : ExactPolicyState A strategy key)
    (exact : ExactMemory A strategy)
    (hbelief :
      (exactEffectTable A strategy hwin key).CanonicalBelief A strategy hwin
        (exactInitialMemory A strategy) key state exact) :
    exact = state.2 := by
  rcases hbelief with ⟨node, hstate, hexact⟩
  calc
    exact = exactStateAt A strategy hwin
        (canonicalExactInitial A strategy key) node := hexact.symm
    _ =
        (sourceFreeBeliefCodeParityFiniteMemoryTransitionStateAt
          (PolicyDPA A key.1.1) key.1 (exactInitialMemory A strategy key)
          (exactEffectTable A strategy hwin key) node).2 :=
      (exactEffectTable_stateAt_memory A strategy hwin key node).symm
    _ = state.2 := congrArg Prod.snd hstate

/-- The exact perfect-recall table satisfies finite public-effect coherence
at every reachable state. -/
theorem exactEffectTable_effectEnrichedValidAt
    (key : RootKey A strategy) :
    (exactEffectTable A strategy hwin key).EffectEnrichedValidAt A strategy
      hwin (exactInitialMemory A strategy) key := by
  intro node
  let state :=
    sourceFreeBeliefCodeParityFiniteMemoryTransitionStateAt
      (PolicyDPA A key.1.1) key.1 (exactInitialMemory A strategy key)
      (exactEffectTable A strategy hwin key) node
  have hpublic := exactEffectTable_stateAt_public A strategy hwin key node
  constructor
  · constructor
    · refine ⟨state.2, node, rfl, ?_⟩
      exact (exactEffectTable_stateAt_memory A strategy hwin key node).symm
    · intro exact hexact
      have heq := canonicalBelief_exactEffectTable_eq_memory A strategy hwin
        key state exact hexact
      subst exact
      exact ⟨(congrArg Prod.fst hpublic).symm,
        (congrArg Prod.snd hpublic).symm⟩
  · intro exact hexact
    have heq := canonicalBelief_exactEffectTable_eq_memory A strategy hwin
      key state exact hexact
    subst exact
    funext childCode
    unfold ExactPublicSuccessorSignature StoredPublicSuccessorSignature
    exact (exactEffectTable_successor_fst A strategy hwin key state
      childCode).symm

/-- Universal forward parity of the exact table is inherited from the
literal winning semantic tree. -/
theorem exactEffectTable_enrichedForwardAccepts
    (key : RootKey A strategy) :
    (exactEffectTable A strategy hwin key).EnrichedForwardAccepts A strategy
      (exactInitialMemory A strategy) key := by
  intro branch
  let source :=
    profiledRawJointOneSidedPhysicalCompatibleBankSource A strategy key
  let certificate :=
    profiledRawJointOneSidedPhysicalExactCommonActionCertificate A strategy
      hwin source key.1.2
        (profiledRawJointOneSidedPhysicalCompatibleBankSource_compatible A
          strategy key)
  have haccepts :=
    (certificate.codeParityCertificate A strategy hwin source key.1.2).accepts
      branch
  have hsourceCode : source.code A = key.1.1 := by
    exact profiledRawJointOneSidedPhysicalCompatibleBankSource_code A strategy
      key
  rw [hsourceCode] at haccepts
  rw [(PolicyDPA A key.1.1).accepts_iff_natSeqMinEvenParity] at haccepts
  let tablePriorities : Nat → Nat := fun n ↦
    (PolicyDPA A key.1.1).priority
      (sourceFreeBeliefCodeParityFiniteMemoryTransitionStateAt
        (PolicyDPA A key.1.1) key.1 (exactInitialMemory A strategy key)
        (exactEffectTable A strategy hwin key)
        (branchNode branch n)).1.2
  let semanticPriorities : Nat → Nat := fun n ↦
    (PolicyDPA A key.1.1).priority
      ((certificate.semanticTree.codeParityStateAt
        (PolicyDPA A key.1.1) (branchNode branch n)).2)
  have heq : tablePriorities = semanticPriorities := by
    funext n
    exact congrArg (PolicyDPA A key.1.1).priority
      (exactEffectTable_stateAt_dpa A strategy hwin key
        (branchNode branch n))
  have hsemantic : NatSeqMinEvenParity semanticPriorities := by
    have hrun : ∀ n,
        (certificate.semanticTree.codeParityStateAt
          (PolicyDPA A key.1.1) (branchNode branch n)).2 =
        (PolicyDPA A key.1.1).run
          (certificate.semanticTree.childCodeWord branch) n :=
      fun n ↦
        certificate.semanticTree.codeParityStateAt_snd_branchNode
          (PolicyDPA A key.1.1) branch n
    simpa only [semanticPriorities, hrun] using haccepts
  change NatSeqMinEvenParity tablePriorities
  rw [heq]
  exact hsemantic

/-- For the perfect-recall table, the complete unrestricted enriched-table target is
equivalent to the one still-unproved literal owner-trace obligation.  Thus
neither canonical effect coherence nor forward parity remains part of the
mathematical gap. -/
theorem exactEffectTable_effectEnrichedChecksUnrestricted_iff_ownerSafe
    (key : RootKey A strategy) :
    EffectEnrichedChecksUnrestricted A strategy hwin
        (exactInitialMemory A strategy) key
        (exactEffectTable A strategy hwin key) ↔
      EnrichedOwnerSafeUnrestricted A strategy hwin
        (exactInitialMemory A strategy) key
        (exactEffectTable A strategy hwin key) := by
  constructor
  · intro hchecks
    exact hchecks.2.2
  · intro howner
    exact ⟨exactEffectTable_effectEnrichedValidAt A strategy hwin key,
      exactEffectTable_enrichedForwardAccepts A strategy hwin key, howner⟩

/-- `hwin` therefore supplies all non-owner components of the checked-table
target without any finiteness hypothesis on the semantic memory. -/
theorem exists_exactEffectTable_forwardChecks
    (key : RootKey A strategy) :
    ∃ table : ExactTable A strategy key,
      table.EffectEnrichedValidAt A strategy hwin
          (exactInitialMemory A strategy) key ∧
        table.EnrichedForwardAccepts A strategy
          (exactInitialMemory A strategy) key :=
  ⟨exactEffectTable A strategy hwin key,
    exactEffectTable_effectEnrichedValidAt A strategy hwin key,
    exactEffectTable_enrichedForwardAccepts A strategy hwin key⟩

end
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTable

end

end DetParityAutomaton

end DistributedSynthesis
