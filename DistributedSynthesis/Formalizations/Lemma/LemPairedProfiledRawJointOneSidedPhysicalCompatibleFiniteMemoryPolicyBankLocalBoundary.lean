/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyBank
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointFinitePhysicalSiblingTargetSynchronization

/-!
# Finite-memory recurrent-bank boundary packets

The recurrent endpoint construction communicates a resolved target as a
finite packet containing the requested public target, its parent-linked
child, and the bank successor installed by that child.  This file lifts that
packet seam to a selected physical-compatible policy with explicit finite
memory.

The policy memory remains inside the bank successor.  In particular, packet
formation neither projects it away nor centralizes it: copying a packet
copies the memory of that bank lineage, and installing its successor installs
the memory update chosen by the same policy transition.
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

private abbrev BankControl :=
  ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankControl
    (Memory := Memory) A strategy

private abbrev LinkedCode :=
  SourceFreeBeliefParentLinkedCode
    (BeliefCode := ProfiledRawJointIncidenceCode A (I := Unit))
    (Annotation := ProfiledRawJointHybridPhysicalEdgeAnnotation A)

/-- Runtime result of resolving one locally computed closing target in an
augmented bank.  Its successor contains the policy memory after the selected
child transition. -/
structure
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankResolvedTarget
    where
  target : ProfiledRawJointIncidenceCode A (I := Unit)
  childCode : LinkedCode A
  successor : BankControl (Memory := Memory) A strategy

noncomputable instance :
    Fintype
      (ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankResolvedTarget
        (Memory := Memory) A strategy) := by
  classical
  let Rep :=
    ProfiledRawJointIncidenceCode A (I := Unit) × LinkedCode A ×
      BankControl (Memory := Memory) A strategy
  let equiv :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankResolvedTarget
          (Memory := Memory) A strategy ≃ Rep := {
    toFun := fun packet ↦
      (packet.target, packet.childCode, packet.successor)
    invFun := fun packet ↦ ⟨packet.1, packet.2.1, packet.2.2⟩
    left_inv := by intro packet; cases packet; rfl
    right_inv := by intro packet; cases packet; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

namespace
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection

variable
  (initialMemory : RootKey A strategy → Memory)
  (selection :
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection
      (Memory := Memory) A strategy hwin initialMemory)

/-- Resolve a bare target and retain the selected augmented successor in one
finite endpoint packet. -/
noncomputable def resolvePacket
    (state : BankControl (Memory := Memory) A strategy)
    (target : ProfiledRawJointIncidenceCode A (I := Unit)) :
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankResolvedTarget
      (Memory := Memory) A strategy :=
  let childCode :=
    selection.resolveTarget A strategy hwin initialMemory state target
  ⟨target, childCode,
    selection.successor A strategy hwin initialMemory state childCode⟩

/-- Resolve a target read from the informed right receiver's finite record. -/
noncomputable def resolveRightRecord
    (state : BankControl (Memory := Memory) A strategy)
    (record : ProfiledRawJointTargetRightReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂)
      (ProfiledRawJointIncidenceCode A (I := Unit)))
    (row : PairedEntryRow) :
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankResolvedTarget
      (Memory := Memory) A strategy :=
  selection.resolvePacket A strategy hwin initialMemory state
    (record.target row)

/-- Left-orientation mirror. -/
noncomputable def resolveLeftRecord
    (state : BankControl (Memory := Memory) A strategy)
    (record : ProfiledRawJointTargetLeftReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂)
      (ProfiledRawJointIncidenceCode A (I := Unit)))
    (row : PairedEntryRow) :
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankResolvedTarget
      (Memory := Memory) A strategy :=
  selection.resolvePacket A strategy hwin initialMemory state
    (record.target row)

@[simp] theorem resolvePacket_target
    (state : BankControl (Memory := Memory) A strategy)
    (target : ProfiledRawJointIncidenceCode A (I := Unit)) :
    (selection.resolvePacket A strategy hwin initialMemory state target).target =
      target :=
  rfl

@[simp] theorem resolvePacket_childCode
    (state : BankControl (Memory := Memory) A strategy)
    (target : ProfiledRawJointIncidenceCode A (I := Unit)) :
    (selection.resolvePacket A strategy hwin initialMemory state
        target).childCode =
      selection.resolveTarget A strategy hwin initialMemory state target :=
  rfl

@[simp] theorem resolvePacket_successor
    (state : BankControl (Memory := Memory) A strategy)
    (target : ProfiledRawJointIncidenceCode A (I := Unit)) :
    (selection.resolvePacket A strategy hwin initialMemory state
        target).successor =
      selection.successor A strategy hwin initialMemory state
        (selection.resolveTarget A strategy hwin initialMemory state target) :=
  rfl

@[simp] theorem resolveRightRecord_target
    (state : BankControl (Memory := Memory) A strategy)
    (record : ProfiledRawJointTargetRightReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂)
      (ProfiledRawJointIncidenceCode A (I := Unit)))
    (row : PairedEntryRow) :
    (selection.resolveRightRecord A strategy hwin initialMemory state record
      row).target = record.target row :=
  rfl

@[simp] theorem resolveLeftRecord_target
    (state : BankControl (Memory := Memory) A strategy)
    (record : ProfiledRawJointTargetLeftReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂)
      (ProfiledRawJointIncidenceCode A (I := Unit)))
    (row : PairedEntryRow) :
    (selection.resolveLeftRecord A strategy hwin initialMemory state record
      row).target = record.target row :=
  rfl

/-- On a legal installed-right-table target, the packet is the exact selected
policy edge, retains the root key, and carries a reachable augmented
successor. -/
theorem resolveRightPacket_spec
    (state : BankControl (Memory := Memory) A strategy)
    (hreachable :
      selection.Reachable A strategy hwin initialMemory state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcurrentCode : state.2.1.1.1 = currentCode)
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .right currentCode () =
      some root)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (hmove : state.2.1.1.2.1 = some move)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : profiledRawJointRightPhysicalSiblingAllowed A move.1 target) :
    let packet :=
      selection.resolvePacket A strategy hwin initialMemory state target
    packet.childCode.1 = target ∧
      selection.ChildRealizes A strategy hwin initialMemory state target
        packet.childCode ∧
      packet.successor.1 = state.1 ∧
      selection.Reachable A strategy hwin initialMemory packet.successor := by
  dsimp only
  exact selection.resolveRightTarget_spec A strategy hwin initialMemory state
    hreachable currentCode hcurrentCode root hroot move hmove target htarget

/-- Left-orientation mirror of `resolveRightPacket_spec`. -/
theorem resolveLeftPacket_spec
    (state : BankControl (Memory := Memory) A strategy)
    (hreachable :
      selection.Reachable A strategy hwin initialMemory state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcurrentCode : state.2.1.1.1 = currentCode)
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .left currentCode () =
      some root)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hmove : state.2.1.1.2.2 = some move)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : profiledRawJointLeftPhysicalSiblingAllowed A move.1 target) :
    let packet :=
      selection.resolvePacket A strategy hwin initialMemory state target
    packet.childCode.1 = target ∧
      selection.ChildRealizes A strategy hwin initialMemory state target
        packet.childCode ∧
      packet.successor.1 = state.1 ∧
      selection.Reachable A strategy hwin initialMemory packet.successor := by
  dsimp only
  exact selection.resolveLeftTarget_spec A strategy hwin initialMemory state
    hreachable currentCode hcurrentCode root hroot move hmove target htarget

/-- Packet construction, including the successor memory, depends only on the
augmented policy selected at the packet source's root key. -/
theorem resolvePacket_congr_at
    (other :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection
        (Memory := Memory) A strategy hwin initialMemory)
    (key : RootKey A strategy)
    (state : BankControl (Memory := Memory) A strategy)
    (hkey : state.1 = key)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (hagrees : selection.AgreeAt A strategy hwin initialMemory other key) :
    selection.resolvePacket A strategy hwin initialMemory state target =
      other.resolvePacket A strategy hwin initialMemory state target := by
  dsimp only [resolvePacket]
  rw [selection.resolveTarget_congr_at A strategy hwin initialMemory other key
    state hkey target hagrees]
  rw [selection.successor_congr_at A strategy hwin initialMemory other key
    state hkey
    (other.resolveTarget A strategy hwin initialMemory state target) hagrees]

/-- A realized packet whose public target has a live left slot installs an
actual left physical move.  The proof uses only the public part of the
augmented successor; the memory update is retained unchanged. -/
theorem resolvePacket_leftMove_exists
    (state : BankControl (Memory := Memory) A strategy)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (hrealizes :
      selection.ChildRealizes A strategy hwin initialMemory state target
        (selection.resolveTarget A strategy hwin initialMemory state target))
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .left target () =
      some root) :
    let packet :=
      selection.resolvePacket A strategy hwin initialMemory state target
    ∃ move : ProfiledRawJointLeftPhysicalSiblingMove A,
      packet.successor.2.1.1.2.2 = some move := by
  dsimp only
  let childCode :=
    selection.resolveTarget A strategy hwin initialMemory state target
  rcases hrealizes with
    ⟨linkedMove, source, actual, hcode, hsourceMove, _hcompatible,
      hchildren, hchildCode, hbare, hsuccessor⟩
  change childCode = sourceFreeBeliefParentLinkedNext
    (profiledRawJointOneSidedNext A) state.2.1.1 linkedMove actual at hchildCode
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
          (selection.successor A strategy hwin initialMemory state
            childCode).2.1.1.2 =
              profiledRawJointHybridPhysicalAnnotationOf A strategy hwin
                source.family actual.direction := by
        exact (congrArg (fun publicState ↦ publicState.1.2)
          hsuccessor).trans hchildAnnotation
      refine ⟨move, ?_⟩
      change
        (selection.successor A strategy hwin initialMemory state
          childCode).2.1.1.2.2 = some move
      rw [hsuccessorAnnotation]
      exact hannotation

/-- Mirrored live-right-slot fact. -/
theorem resolvePacket_rightMove_exists
    (state : BankControl (Memory := Memory) A strategy)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (hrealizes :
      selection.ChildRealizes A strategy hwin initialMemory state target
        (selection.resolveTarget A strategy hwin initialMemory state target))
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .right target () =
      some root) :
    let packet :=
      selection.resolvePacket A strategy hwin initialMemory state target
    ∃ move : ProfiledRawJointRightPhysicalSiblingMove A,
      packet.successor.2.1.1.2.1 = some move := by
  dsimp only
  let childCode :=
    selection.resolveTarget A strategy hwin initialMemory state target
  rcases hrealizes with
    ⟨linkedMove, source, actual, hcode, hsourceMove, _hcompatible,
      hchildren, hchildCode, hbare, hsuccessor⟩
  change childCode = sourceFreeBeliefParentLinkedNext
    (profiledRawJointOneSidedNext A) state.2.1.1 linkedMove actual at hchildCode
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
          (selection.successor A strategy hwin initialMemory state
            childCode).2.1.1.2 =
              profiledRawJointHybridPhysicalAnnotationOf A strategy hwin
                source.family actual.direction := by
        exact (congrArg (fun publicState ↦ publicState.1.2)
          hsuccessor).trans hchildAnnotation
      refine ⟨move, ?_⟩
      change
        (selection.successor A strategy hwin initialMemory state
          childCode).2.1.1.2.1 = some move
      rw [hsuccessorAnnotation]
      exact hannotation

end
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection

end

end DetParityAutomaton

end DistributedSynthesis
