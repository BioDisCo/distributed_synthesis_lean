/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionPostResolveLinkedPayload
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatiblePolicyBank

/-!
# Installing post-resolution targets in the recurrent policy bank

The linked post-resolution table returns a bare target code together with the
physical annotation selected at the same semantic occurrence before
narrowing.  This file proves that the pair is an admissible root of the
finite recurrent bank.

The delicate case is the simultaneous member.  Its current semantic family
need not satisfy the all-directions `ExactFibreAt` predicate.  That stronger
predicate is unnecessary here: after an actual right block only the old
right family survives, and after an actual left block only the old left
family survives.  The sidewise erasure theorems therefore identify the
literal actual child's incidence code with the emitted target without using
the dummy opposite pivot.
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

private abbrev CommonPoint :=
  ProfiledRawJointGuardedCommonSemanticPoint A strategy

private abbrev OneSidedState :=
  ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)

private abbrev EdgeAnnotation :=
  ProfiledRawJointHybridPhysicalEdgeAnnotation A

private abbrev RootKey :=
  ProfiledRawJointOneSidedPhysicalCompatibleRootKey A strategy

/-! ## Process-one block: actual right child -/

/-- Exact recursively closed target source named by one process-one linked
activation. -/
noncomputable def profiledRawJointStrictLeftPostResolveRecurrentTargetSource
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) (row : PairedEntryRow) (past : List (In₂ × In₁))
    (nextInput : In₂ × In₁) :
    OneSidedState A strategy :=
  let actual := profiledRawJointUnitRightActualDirection
    (In₁ := In₁) (In₂ := In₂) row past nextInput
  let family :=
    profiledRawJointStrictLeftPostResolveLinkedSourceFamily A strategy hwin
      initial entry input member
  { family := family.rightActualChild A actual.direction
    exactFibre := family.rightActualChild_exactFibreAt A actual.direction }

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- The exact target source has the full emitted incidence code, including
its row-equality pattern and empty cross-incidence matrix. -/
theorem profiledRawJointStrictLeftPostResolveRecurrentTargetSource_code
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) (row : PairedEntryRow) (past : List (In₂ × In₁))
    (nextInput : In₂ × In₁) :
    (profiledRawJointStrictLeftPostResolveRecurrentTargetSource A strategy
      hwin initial entry input member row past nextInput).code A =
      (profiledRawJointStrictLeftPostResolveLinkedActivation A strategy hwin
        initial entry input member).target row past nextInput := by
  let actual := profiledRawJointUnitRightActualDirection
    (In₁ := In₁) (In₂ := In₂) row past nextInput
  let family :=
    profiledRawJointStrictLeftPostResolveLinkedSourceFamily A strategy hwin
      initial entry input member
  calc
    (profiledRawJointStrictLeftPostResolveRecurrentTargetSource A strategy
        hwin initial entry input member row past nextInput).code A =
        profiledRawJointRightActualIncidenceNext A (family.code A)
          (family.move A) actual.direction := by
      exact family.rightActualChild_incidenceCode_eq_sidewise A
        actual.direction
    _ = profiledRawJointOneSidedNext A (family.incidenceCode A)
          (family.move A) actual := by
      rfl
    _ = (profiledRawJointStrictLeftPostResolveLinkedActivation A strategy hwin
          initial entry input member).target row past nextInput := by
      symm
      exact profiledRawJointStrictLeftPostResolveLinkedActivation_target A
        strategy hwin initial entry input member row past nextInput

/-- The member-selected payload is compatible with that same exact target
source. -/
theorem
    profiledRawJointStrictLeftPostResolveRecurrentTargetSource_compatible
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) (row : PairedEntryRow) (past : List (In₂ × In₁))
    (nextInput : In₂ × In₁) :
    let actual := profiledRawJointUnitRightActualDirection
      (In₁ := In₁) (In₂ := In₂) row past nextInput
    ProfiledRawJointOneSidedPhysicalAnnotationCompatible A strategy
      (profiledRawJointStrictLeftPostResolveRecurrentTargetSource A strategy
        hwin initial entry input member row past nextInput)
      (profiledRawJointStrictLeftPostResolveLinkedChildren A strategy hwin
        initial entry input (.strict actual) member) := by
  dsimp only
  let family :=
    profiledRawJointStrictLeftPostResolveLinkedSourceFamily A strategy hwin
      initial entry input member
  let actual := profiledRawJointUnitRightActualDirection
    (In₁ := In₁) (In₂ := In₂) row past nextInput
  simpa [profiledRawJointStrictLeftPostResolveRecurrentTargetSource,
    profiledRawJointStrictLeftPostResolveLinkedChildren] using
    (profiledRawJointHybridPhysicalAnnotationOf_rightActual_compatible A
      strategy hwin family actual.direction)

/-- Finite recurrent-bank key carried by a process-one target. -/
noncomputable def profiledRawJointStrictLeftPostResolveRecurrentTargetKey
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) (row : PairedEntryRow) (past : List (In₂ × In₁))
    (nextInput : In₂ × In₁) : RootKey A strategy :=
  let actual := profiledRawJointUnitRightActualDirection
    (In₁ := In₁) (In₂ := In₂) row past nextInput
  profiledRawJointOneSidedPhysicalCompatibleRootKeyOf A strategy
    (profiledRawJointStrictLeftPostResolveRecurrentTargetSource A strategy hwin
      initial entry input member row past nextInput)
    (profiledRawJointStrictLeftPostResolveLinkedChildren A strategy hwin
      initial entry input (.strict actual) member)
    (profiledRawJointStrictLeftPostResolveRecurrentTargetSource_compatible A
      strategy hwin initial entry input member row past nextInput)

theorem profiledRawJointStrictLeftPostResolveRecurrentTargetKey_data
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) (row : PairedEntryRow) (past : List (In₂ × In₁))
    (nextInput : In₂ × In₁) :
    let actual := profiledRawJointUnitRightActualDirection
      (In₁ := In₁) (In₂ := In₂) row past nextInput
    (profiledRawJointStrictLeftPostResolveRecurrentTargetKey A strategy hwin
      initial entry input member row past nextInput).1 =
      ((profiledRawJointStrictLeftPostResolveLinkedActivation A strategy hwin
          initial entry input member).target row past nextInput,
        profiledRawJointStrictLeftPostResolveLinkedChildren A strategy hwin
          initial entry input (.strict actual) member) := by
  dsimp only
  apply Prod.ext
  · exact profiledRawJointStrictLeftPostResolveRecurrentTargetSource_code A
      strategy hwin initial entry input member row past nextInput
  · rfl

/-! ## Process-two block: actual left child -/

/-- Mirrored exact recursively closed target source. -/
noncomputable def profiledRawJointStrictRightPostResolveRecurrentTargetSource
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) (row : PairedEntryRow) (past : List (In₁ × In₂))
    (nextInput : In₁ × In₂) :
    OneSidedState A strategy :=
  let actual := profiledRawJointUnitLeftActualDirection
    (In₁ := In₁) (In₂ := In₂) row past nextInput
  let family :=
    profiledRawJointStrictRightPostResolveLinkedSourceFamily A strategy hwin
      initial entry input member
  { family := family.leftActualChild A actual.direction
    exactFibre := family.leftActualChild_exactFibreAt A actual.direction }

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
theorem profiledRawJointStrictRightPostResolveRecurrentTargetSource_code
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) (row : PairedEntryRow) (past : List (In₁ × In₂))
    (nextInput : In₁ × In₂) :
    (profiledRawJointStrictRightPostResolveRecurrentTargetSource A strategy
      hwin initial entry input member row past nextInput).code A =
      (profiledRawJointStrictRightPostResolveLinkedActivation A strategy hwin
        initial entry input member).target row past nextInput := by
  let actual := profiledRawJointUnitLeftActualDirection
    (In₁ := In₁) (In₂ := In₂) row past nextInput
  let family :=
    profiledRawJointStrictRightPostResolveLinkedSourceFamily A strategy hwin
      initial entry input member
  calc
    (profiledRawJointStrictRightPostResolveRecurrentTargetSource A strategy
        hwin initial entry input member row past nextInput).code A =
        profiledRawJointLeftActualIncidenceNext A (family.code A)
          (family.move A) actual.direction := by
      exact family.leftActualChild_incidenceCode_eq_sidewise A
        actual.direction
    _ = profiledRawJointOneSidedNext A (family.incidenceCode A)
          (family.move A) actual := by
      rfl
    _ = (profiledRawJointStrictRightPostResolveLinkedActivation A strategy
          hwin initial entry input member).target row past nextInput := by
      symm
      exact profiledRawJointStrictRightPostResolveLinkedActivation_target A
        strategy hwin initial entry input member row past nextInput

theorem
    profiledRawJointStrictRightPostResolveRecurrentTargetSource_compatible
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) (row : PairedEntryRow) (past : List (In₁ × In₂))
    (nextInput : In₁ × In₂) :
    let actual := profiledRawJointUnitLeftActualDirection
      (In₁ := In₁) (In₂ := In₂) row past nextInput
    ProfiledRawJointOneSidedPhysicalAnnotationCompatible A strategy
      (profiledRawJointStrictRightPostResolveRecurrentTargetSource A strategy
        hwin initial entry input member row past nextInput)
      (profiledRawJointStrictRightPostResolveLinkedChildren A strategy hwin
        initial entry input (.strict actual) member) := by
  dsimp only
  let family :=
    profiledRawJointStrictRightPostResolveLinkedSourceFamily A strategy hwin
      initial entry input member
  let actual := profiledRawJointUnitLeftActualDirection
    (In₁ := In₁) (In₂ := In₂) row past nextInput
  simpa [profiledRawJointStrictRightPostResolveRecurrentTargetSource,
    profiledRawJointStrictRightPostResolveLinkedChildren] using
    (profiledRawJointHybridPhysicalAnnotationOf_leftActual_compatible A
      strategy hwin family actual.direction)

noncomputable def profiledRawJointStrictRightPostResolveRecurrentTargetKey
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) (row : PairedEntryRow) (past : List (In₁ × In₂))
    (nextInput : In₁ × In₂) : RootKey A strategy :=
  let actual := profiledRawJointUnitLeftActualDirection
    (In₁ := In₁) (In₂ := In₂) row past nextInput
  profiledRawJointOneSidedPhysicalCompatibleRootKeyOf A strategy
    (profiledRawJointStrictRightPostResolveRecurrentTargetSource A strategy
      hwin initial entry input member row past nextInput)
    (profiledRawJointStrictRightPostResolveLinkedChildren A strategy hwin
      initial entry input (.strict actual) member)
    (profiledRawJointStrictRightPostResolveRecurrentTargetSource_compatible A
      strategy hwin initial entry input member row past nextInput)

theorem profiledRawJointStrictRightPostResolveRecurrentTargetKey_data
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) (row : PairedEntryRow) (past : List (In₁ × In₂))
    (nextInput : In₁ × In₂) :
    let actual := profiledRawJointUnitLeftActualDirection
      (In₁ := In₁) (In₂ := In₂) row past nextInput
    (profiledRawJointStrictRightPostResolveRecurrentTargetKey A strategy hwin
      initial entry input member row past nextInput).1 =
      ((profiledRawJointStrictRightPostResolveLinkedActivation A strategy hwin
          initial entry input member).target row past nextInput,
        profiledRawJointStrictRightPostResolveLinkedChildren A strategy hwin
          initial entry input (.strict actual) member) := by
  dsimp only
  apply Prod.ext
  · exact profiledRawJointStrictRightPostResolveRecurrentTargetSource_code A
      strategy hwin initial entry input member row past nextInput
  · rfl

/-! ## Arbitrary-prefix entry into the recurrent bank -/

/-- Every row target produced at an arbitrary depth of the executable
process-one post-resolution play determines an admissible bank key.  The
root of the policy selected at that key exposes exactly the delivered bare
target and the delivered member's physical table. -/
theorem
    profiledRawJointStrictLeftPostResolveLinkedMovePlay_bankRoot_exists
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow) :
    let play := profiledRawJointStrictLeftPostResolveLinkedMovePlay A strategy
      hwin initial entry input member env
    let projected := BlockRecordMonitor.projectReceiverPlay
      (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A)
      play
    ∃ past nextInput,
      let key :=
        profiledRawJointStrictLeftPostResolveRecurrentTargetKey A strategy hwin
          initial entry input member row past nextInput
      let delivered :=
        (((projected n).2.1.target row).1,
          (profiledRawJointHybridFinitePayloadLinkedTargetPayload A
            ((projected n).2.1.target row)) member)
      key.1 = delivered ∧
        (profiledRawJointOneSidedPhysicalCompatibleBankRoot A strategy hwin
          key).2.1 = delivered ∧
        ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy
          hwin
          (profiledRawJointOneSidedPhysicalCompatibleBankRoot A strategy hwin
            key) := by
  dsimp only
  obtain ⟨past, nextInput, htarget⟩ :=
    profiledRawJointStrictLeftPostResolveLinkedMovePlay_target_exists A
      strategy hwin initial entry input member env n row
  let play := profiledRawJointStrictLeftPostResolveLinkedMovePlay A strategy
    hwin initial entry input member env
  let projected := BlockRecordMonitor.projectReceiverPlay
    (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A)
    play
  let key :=
    profiledRawJointStrictLeftPostResolveRecurrentTargetKey A strategy hwin
      initial entry input member row past nextInput
  have hdata :
      key.1 =
        (((projected n).2.1.target row).1,
          (profiledRawJointHybridFinitePayloadLinkedTargetPayload A
            ((projected n).2.1.target row)) member) := by
    rw [htarget]
    simpa [key] using
      (profiledRawJointStrictLeftPostResolveRecurrentTargetKey_data A strategy
        hwin initial entry input member row past nextInput)
  refine ⟨past, nextInput, hdata, ?_, ?_⟩
  · exact
      (profiledRawJointOneSidedPhysicalCompatibleBankRoot_data A strategy hwin
        key).trans hdata
  · exact
      profiledRawJointOneSidedPhysicalCompatibleBankRoot_reachable A strategy
        hwin key

/-- Process-two mirror: every executable row target, at every finite depth,
enters the policy bank at the delivered bare target and member-selected
physical table. -/
theorem
    profiledRawJointStrictRightPostResolveLinkedMovePlay_bankRoot_exists
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) (env : Nat → In₁ × In₂) (n : Nat)
    (row : PairedEntryRow) :
    let play := profiledRawJointStrictRightPostResolveLinkedMovePlay A strategy
      hwin initial entry input member env
    let projected := BlockRecordMonitor.projectReceiverPlay
      (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
      play
    ∃ past nextInput,
      let key :=
        profiledRawJointStrictRightPostResolveRecurrentTargetKey A strategy hwin
          initial entry input member row past nextInput
      let delivered :=
        (((projected n).2.1.target row).1,
          (profiledRawJointHybridFinitePayloadLinkedTargetPayload A
            ((projected n).2.1.target row)) member)
      key.1 = delivered ∧
        (profiledRawJointOneSidedPhysicalCompatibleBankRoot A strategy hwin
          key).2.1 = delivered ∧
        ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy
          hwin
          (profiledRawJointOneSidedPhysicalCompatibleBankRoot A strategy hwin
            key) := by
  dsimp only
  obtain ⟨past, nextInput, htarget⟩ :=
    profiledRawJointStrictRightPostResolveLinkedMovePlay_target_exists A
      strategy hwin initial entry input member env n row
  let play := profiledRawJointStrictRightPostResolveLinkedMovePlay A strategy
    hwin initial entry input member env
  let projected := BlockRecordMonitor.projectReceiverPlay
    (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
    play
  let key :=
    profiledRawJointStrictRightPostResolveRecurrentTargetKey A strategy hwin
      initial entry input member row past nextInput
  have hdata :
      key.1 =
        (((projected n).2.1.target row).1,
          (profiledRawJointHybridFinitePayloadLinkedTargetPayload A
            ((projected n).2.1.target row)) member) := by
    rw [htarget]
    simpa [key] using
      (profiledRawJointStrictRightPostResolveRecurrentTargetKey_data A strategy
        hwin initial entry input member row past nextInput)
  refine ⟨past, nextInput, hdata, ?_, ?_⟩
  · exact
      (profiledRawJointOneSidedPhysicalCompatibleBankRoot_data A strategy hwin
        key).trans hdata
  · exact
      profiledRawJointOneSidedPhysicalCompatibleBankRoot_reachable A strategy
        hwin key

end

end DetParityAutomaton

end DistributedSynthesis
