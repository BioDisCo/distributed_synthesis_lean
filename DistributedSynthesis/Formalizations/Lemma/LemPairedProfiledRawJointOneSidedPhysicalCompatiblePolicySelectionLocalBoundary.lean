/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatiblePolicyBankSelection
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatiblePolicyBankLocalBoundary

/-!
# Endpoint-local packet resolution for a replaceable policy selection

This file lifts the first executable reversal boundary from the legacy
arbitrary policy bank to an explicit policy selection.  The packet type does
not depend on the selection: it stores only finite public data, a linked code,
and the resulting bank-control state.  Its construction and correctness do
depend on the selected policy.

The final bridge lemmas identify the old packet functions with the default
selection.  Thus this is a genuine parameterization of the existing runtime
operation, rather than a parallel unconnected construction.
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

private abbrev BankControl :=
  ProfiledRawJointOneSidedPhysicalCompatibleBankControl A strategy hwin

private abbrev PolicySelection :=
  ProfiledRawJointOneSidedPhysicalCompatiblePolicySelection A strategy hwin

namespace ProfiledRawJointOneSidedPhysicalCompatiblePolicySelection

variable (selection : PolicySelection A strategy hwin)

/-! ## Selection-relative executable packets -/

/-- Resolve a locally computed target using the policy selected at the
state's root key. -/
noncomputable def resolvePacket
    (state : BankControl A strategy hwin)
    (target : ProfiledRawJointIncidenceCode A (I := Unit)) :
    ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
      hwin :=
  let childCode := selection.resolveTarget A strategy hwin state target
  ⟨target, childCode,
    selection.successor A strategy hwin state childCode⟩

/-- Resolve one row of a right-receiver record. -/
noncomputable def resolveRightRecord
    (state : BankControl A strategy hwin)
    (record : ProfiledRawJointTargetRightReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂)
      (ProfiledRawJointIncidenceCode A (I := Unit)))
    (row : PairedEntryRow) :
    ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
      hwin :=
  selection.resolvePacket A strategy hwin state (record.target row)

/-- Resolve one row of a left-receiver record. -/
noncomputable def resolveLeftRecord
    (state : BankControl A strategy hwin)
    (record : ProfiledRawJointTargetLeftReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂)
      (ProfiledRawJointIncidenceCode A (I := Unit)))
    (row : PairedEntryRow) :
    ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
      hwin :=
  selection.resolvePacket A strategy hwin state (record.target row)

@[simp] theorem resolvePacket_target
    (state : BankControl A strategy hwin)
    (target : ProfiledRawJointIncidenceCode A (I := Unit)) :
    (selection.resolvePacket A strategy hwin state target).target = target :=
  rfl

@[simp] theorem resolvePacket_childCode
    (state : BankControl A strategy hwin)
    (target : ProfiledRawJointIncidenceCode A (I := Unit)) :
    (selection.resolvePacket A strategy hwin state target).childCode =
      selection.resolveTarget A strategy hwin state target :=
  rfl

@[simp] theorem resolvePacket_successor
    (state : BankControl A strategy hwin)
    (target : ProfiledRawJointIncidenceCode A (I := Unit)) :
    (selection.resolvePacket A strategy hwin state target).successor =
      selection.successor A strategy hwin state
        (selection.resolveTarget A strategy hwin state target) :=
  rfl

@[simp] theorem resolveRightRecord_target
    (state : BankControl A strategy hwin)
    (record : ProfiledRawJointTargetRightReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂)
      (ProfiledRawJointIncidenceCode A (I := Unit)))
    (row : PairedEntryRow) :
    (selection.resolveRightRecord A strategy hwin state record row).target =
      record.target row :=
  rfl

@[simp] theorem resolveLeftRecord_target
    (state : BankControl A strategy hwin)
    (record : ProfiledRawJointTargetLeftReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂)
      (ProfiledRawJointIncidenceCode A (I := Unit)))
    (row : PairedEntryRow) :
    (selection.resolveLeftRecord A strategy hwin state record row).target =
      record.target row :=
  rfl

/-! ## Correctness at a legal installed target -/

/-- A legal right-table target yields an exact, same-key, reachable packet. -/
theorem resolveRightPacket_spec
    (state : BankControl A strategy hwin)
    (hreachable : selection.Reachable A strategy hwin state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcurrentCode : state.2.1.1 = currentCode)
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .right currentCode () =
      some root)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (hmove : state.2.1.2.1 = some move)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : profiledRawJointRightPhysicalSiblingAllowed A move.1 target) :
    let packet := selection.resolvePacket A strategy hwin state target
    packet.childCode.1 = target ∧
      selection.ChildRealizes A strategy hwin state target packet.childCode ∧
      packet.successor.1 = state.1 ∧
      selection.Reachable A strategy hwin packet.successor := by
  dsimp only
  exact selection.resolveRightTarget_spec A strategy hwin state hreachable
    currentCode hcurrentCode root hroot move hmove target htarget

/-- A legal left-table target yields an exact, same-key, reachable packet. -/
theorem resolveLeftPacket_spec
    (state : BankControl A strategy hwin)
    (hreachable : selection.Reachable A strategy hwin state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcurrentCode : state.2.1.1 = currentCode)
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .left currentCode () =
      some root)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hmove : state.2.1.2.2 = some move)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : profiledRawJointLeftPhysicalSiblingAllowed A move.1 target) :
    let packet := selection.resolvePacket A strategy hwin state target
    packet.childCode.1 = target ∧
      selection.ChildRealizes A strategy hwin state target packet.childCode ∧
      packet.successor.1 = state.1 ∧
      selection.Reachable A strategy hwin packet.successor := by
  dsimp only
  exact selection.resolveLeftTarget_spec A strategy hwin state hreachable
    currentCode hcurrentCode root hroot move hmove target htarget

/-- Packet construction depends only on the policy selected at the packet
source's fixed root key. -/
theorem resolvePacket_congr_at
    (other : PolicySelection A strategy hwin)
    (key : ProfiledRawJointOneSidedPhysicalCompatibleRootKey A strategy)
    (state : BankControl A strategy hwin)
    (hkey : state.1 = key)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (hagrees : selection.AgreeAt A strategy hwin other key) :
    selection.resolvePacket A strategy hwin state target =
      other.resolvePacket A strategy hwin state target := by
  dsimp only [resolvePacket]
  rw [selection.resolveTarget_congr_at A strategy hwin other key state hkey
    target hagrees]
  rw [selection.successor_congr_at A strategy hwin other key state hkey
    (other.resolveTarget A strategy hwin state target) hagrees]

/-! ## The fallback is unreachable at a genuine reversal -/

/-- If an exactly resolved target has a live left slot, the selected-policy
successor contains a left physical move. -/
theorem resolvePacket_leftMove_exists
    (state : BankControl A strategy hwin)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (hrealizes : selection.ChildRealizes A strategy hwin state target
      (selection.resolveTarget A strategy hwin state target))
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .left target () =
      some root) :
    let packet := selection.resolvePacket A strategy hwin state target
    ∃ move : ProfiledRawJointLeftPhysicalSiblingMove A,
      packet.successor.2.1.2.2 = some move := by
  dsimp only
  let childCode := selection.resolveTarget A strategy hwin state target
  rcases hrealizes with
    ⟨linkedMove, source, actual, hcode, hsourceMove, _hcompatible,
      hchildren, hchildCode, hbare, hsuccessor⟩
  change childCode = sourceFreeBeliefParentLinkedNext
    (profiledRawJointOneSidedNext A) state.2.1 linkedMove actual at hchildCode
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
      have hsuccessorData :
          (selection.successor A strategy hwin state childCode).2.1 =
            childCode := by
        exact congrArg Prod.fst hsuccessor
      have hsuccessorAnnotation :
          (selection.successor A strategy hwin state childCode).2.1.2 =
            profiledRawJointHybridPhysicalAnnotationOf A strategy hwin
              source.family actual.direction := by
        exact (congrArg Prod.snd hsuccessorData).trans hchildAnnotation
      refine ⟨move, ?_⟩
      change
        (selection.successor A strategy hwin state childCode).2.1.2.2 =
          some move
      rw [hsuccessorAnnotation]
      exact hannotation

/-- Mirrored fact for a live right slot. -/
theorem resolvePacket_rightMove_exists
    (state : BankControl A strategy hwin)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (hrealizes : selection.ChildRealizes A strategy hwin state target
      (selection.resolveTarget A strategy hwin state target))
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .right target () =
      some root) :
    let packet := selection.resolvePacket A strategy hwin state target
    ∃ move : ProfiledRawJointRightPhysicalSiblingMove A,
      packet.successor.2.1.2.1 = some move := by
  dsimp only
  let childCode := selection.resolveTarget A strategy hwin state target
  rcases hrealizes with
    ⟨linkedMove, source, actual, hcode, hsourceMove, _hcompatible,
      hchildren, hchildCode, hbare, hsuccessor⟩
  change childCode = sourceFreeBeliefParentLinkedNext
    (profiledRawJointOneSidedNext A) state.2.1 linkedMove actual at hchildCode
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
      have hsuccessorData :
          (selection.successor A strategy hwin state childCode).2.1 =
            childCode := by
        exact congrArg Prod.fst hsuccessor
      have hsuccessorAnnotation :
          (selection.successor A strategy hwin state childCode).2.1.2 =
            profiledRawJointHybridPhysicalAnnotationOf A strategy hwin
              source.family actual.direction := by
        exact (congrArg Prod.snd hsuccessorData).trans hchildAnnotation
      refine ⟨move, ?_⟩
      change
        (selection.successor A strategy hwin state childCode).2.1.2.1 =
          some move
      rw [hsuccessorAnnotation]
      exact hannotation

/-! ## Regression bridge to the legacy bank -/

@[simp] theorem default_resolvePacket
    (state : BankControl A strategy hwin)
    (target : ProfiledRawJointIncidenceCode A (I := Unit)) :
    (profiledRawJointOneSidedPhysicalCompatibleDefaultPolicySelection A
      strategy hwin).resolvePacket A strategy hwin state target =
      profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
        hwin state target :=
  rfl

@[simp] theorem default_resolveRightRecord
    (state : BankControl A strategy hwin)
    (record : ProfiledRawJointTargetRightReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂)
      (ProfiledRawJointIncidenceCode A (I := Unit)))
    (row : PairedEntryRow) :
    (profiledRawJointOneSidedPhysicalCompatibleDefaultPolicySelection A
      strategy hwin).resolveRightRecord A strategy hwin state record row =
      profiledRawJointOneSidedPhysicalCompatibleBankResolveRightRecord A
        strategy hwin state record row :=
  rfl

@[simp] theorem default_resolveLeftRecord
    (state : BankControl A strategy hwin)
    (record : ProfiledRawJointTargetLeftReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂)
      (ProfiledRawJointIncidenceCode A (I := Unit)))
    (row : PairedEntryRow) :
    (profiledRawJointOneSidedPhysicalCompatibleDefaultPolicySelection A
      strategy hwin).resolveLeftRecord A strategy hwin state record row =
      profiledRawJointOneSidedPhysicalCompatibleBankResolveLeftRecord A
        strategy hwin state record row :=
  rfl

end ProfiledRawJointOneSidedPhysicalCompatiblePolicySelection

end

end DetParityAutomaton

end DistributedSynthesis
