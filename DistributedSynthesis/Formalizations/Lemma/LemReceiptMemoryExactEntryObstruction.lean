/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemReceiptMemoryOwnerObstruction

/-!
# A nonempty exact-bank instance of the receipt-memory obstruction

The source histories are generated, the root annotation is the semantic
annotation, and the packet is produced by the actual exact-cell resolver.
The entry uses the repository's installed/staged honest-entry constructor.
This is not an arbitrary inconsistent packet or a detached block composition.
Reachability of this entry from the complete guarded front is a separate
question; the theorem below does not assume or establish it.
-/

namespace DistributedSynthesis
namespace ReceiptMemoryOwnerObstruction
namespace ExactEntry
open DetParityAutomaton
open ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTable

noncomputable section

def initialWorld : ProfiledRawJointCommonBaseWorld objective source :=
  ⟨[], .empty, (), (), objective.initial⟩
def family := profiledRawJointCommonWorldFamily objective initialWorld
def direction := profiledRawJointBothRestartDirection ((), ())
def world := profiledRawJointCommonWorldAfterBoth objective initialWorld ((), ())

theorem right_member : (family.semanticChild objective direction).right () =
    some (world.procOneMember objective) :=
  profiledRawJointCommonWorld_semanticChild_right_bothRestart objective initialWorld ((), ())

theorem left_member : (family.semanticChild objective direction).left () =
    some (world.procTwoMember objective) :=
  profiledRawJointCommonWorld_semanticChild_left_bothRestart objective initialWorld ((), ())

def semanticState : ProfiledRawJointOneSidedSemanticState objective source (I := Unit) where
  family := family.leftActualChild objective direction
  exactFibre := family.leftActualChild_exactFibreAt objective direction

def annotation := profiledRawJointHybridPhysicalAnnotationOf objective source source_wins
  family direction

def key : ProfiledRawJointOneSidedPhysicalCompatibleRootKey objective source :=
  profiledRawJointOneSidedPhysicalCompatibleRootKeyOf objective source semanticState annotation
    (profiledRawJointHybridPhysicalAnnotationOf_leftActual_compatible
      objective source source_wins family direction)

abbrev Memory := ProfiledRawJointOneSidedPhysicalExactCommonActionMemory objective source

def tables := (exactEffectTable objective source source_wins key).family objective source key

def bank :=
  ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.root
    objective source (exactInitialMemory objective source) key

theorem installed_right_exists : ∃ move : ProfiledRawJointRightPhysicalSiblingMove objective,
    annotation.1 = some move := by
  unfold annotation profiledRawJointHybridPhysicalAnnotationOf
    profiledRawJointRightPhysicalSiblingMoveOption
  split
  · exact ⟨_, rfl⟩
  · rename_i h
    exact False.elim (h ⟨_, right_member⟩)

def template : ProfiledRawJointLeftPhysicalSiblingReceiver objective :=
  initialProfiledRawJointLeftPhysicalSiblingReceiver objective
    (profiledRawJointLeftPhysicalSiblingMoveOf objective source_wins family direction
      (world.procTwoMember objective) left_member) .first

theorem current_right (move : ProfiledRawJointRightPhysicalSiblingMove objective)
    (member : ProcOnePairedEntryRep source × objective.State)
    (hmember : (family.semanticChild objective direction).right () = some member)
    (hdescriptor : move.1 = profiledRawJointRightPhysicalSiblingDescriptorOf
      objective family direction member) :
    profiledRawJointOneSidedCurrentSlots objective .right key.1.1 () =
      some (.inl move.1.source) := by
  rw [hdescriptor]
  simp only [key, profiledRawJointOneSidedPhysicalCompatibleRootKeyOf,
    ProfiledRawJointOneSidedSemanticState.code, semanticState,
    profiledRawJointOneSidedCurrentSlots, ProfiledRawJointSemanticFamily.incidenceCode,
    ProfiledRawJointSemanticFamily.code, ProfiledRawJointSemanticFamily.leftActualChild]
  change Option.map Sum.inl
    (Option.map (profiledRawRightSlotOfSemanticPair objective)
      ((family.semanticChild objective direction).right ())) = _
  rw [hmember]
  rfl

theorem allowed_target_left_live
    (member : ProcOnePairedEntryRep source × objective.State)
    (hmember : (family.semanticChild objective direction).right () = some member)
    (target : ProfiledRawJointUnitTarget objective)
    (hallowed : ProfiledRawJointRightSiblingSharedAllowedTarget objective family direction target) :
    ∃ slot : ProfiledRawLeftSlot objective,
      profiledRawJointOneSidedCurrentSlots objective .left target () = some (.inr slot) := by
  obtain ⟨row, past, input, rfl⟩ := hallowed
  have ht := (profiledRawJointRightSiblingActivation objective source_wins
    family direction member hmember false).target_state row past input
  dsimp only [profiledRawJointRightSiblingActivation] at ht
  unfold profiledRawJointUnitRightTargetProjection at ht
  split at ht
  · rename_i slot hs
    exact ⟨slot, by simp only [profiledRawJointOneSidedCurrentSlots, hs, Option.map_some]⟩
  · cases ht

theorem key_annotation : key.1.2 = annotation := rfl

attribute [irreducible] initialWorld family direction world semanticState annotation key tables bank

def packetFor (move : ProfiledRawJointRightPhysicalSiblingMove objective) :=
  tables.resolvePacket objective source source_wins bank
    ((((move.memberController objective false).labelOf
      (move.memberController objective false).initial).2
      (profiledRawJointRightPhysicalSiblingMonitor objective move.1 false).initial
      ((), ())).target .first)

theorem packetFor_eq (move : ProfiledRawJointRightPhysicalSiblingMove objective) :
    packetFor move = tables.resolvePacket objective source source_wins bank
      ((((move.memberController objective false).labelOf
        (move.memberController objective false).initial).2
        (profiledRawJointRightPhysicalSiblingMonitor objective move.1 false).initial
        ((), ())).target .first) := rfl

attribute [irreducible] packetFor

/-- Non-vacuity with the exact resolver: there is an installed/staged entry
at this concrete admissible key whose actual `left,right,...` tail rejects.
Its objective coordinate is the one reconstructed from the installed left
move, as in the existing honest-entry interface. -/
theorem exact_entry_rejects :
    ∃ (rightMove : ProfiledRawJointRightPhysicalSiblingMove objective)
      (packet : ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankResolvedTarget
        (Memory := Memory) objective source)
      (leftMove : ProfiledRawJointLeftPhysicalSiblingMove objective),
      key.1.2.1 = some rightMove ∧
      profiledRawJointOneSidedCurrentSlots objective .right key.1.1 () =
        some (.inl rightMove.1.source) ∧
      packet = tables.resolvePacket objective source source_wins bank
        ((((rightMove.memberController objective false).labelOf
          (rightMove.memberController objective false).initial).2
          (profiledRawJointRightPhysicalSiblingMonitor objective rightMove.1 false).initial
          ((), ())).target .first) ∧
      packet.successor.2.1.1.2.2 = some leftMove ∧
      let receiver := initialProfiledRawJointRightPhysicalSiblingReceiver objective rightMove .first
      let entry :=
        ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.ownerFibreRightEntryLiveState
          objective source bank receiver (rightMove.memberController objective false).initial
          template packet leftMove
      ∀ graphs : Nat → Graph, graphs 0 = .left → graphs 1 = .right →
        ¬ objective.AcceptsFrom entry.2 (ownerWord tables entry.1 graphs) := by
  obtain ⟨rightMove, hr⟩ := installed_right_exists
  have hrkey : key.1.2.1 = some rightMove := by rw [key_annotation]; exact hr
  have hroption : profiledRawJointRightPhysicalSiblingMoveOption objective source source_wins
      family direction = some rightMove := by
    unfold annotation at hr
    exact hr
  obtain ⟨member, hmember, hm⟩ := profiledRawJointRightPhysicalSiblingMoveOption_spec
    objective source source_wins family direction rightMove hroption
  have hd : rightMove.1 = profiledRawJointRightPhysicalSiblingDescriptorOf
      objective family direction member := by rw [hm]; rfl
  have hroot := current_right rightMove member hmember hd
  let target := (((rightMove.memberController objective false).labelOf
    (rightMove.memberController objective false).initial).2
    (profiledRawJointRightPhysicalSiblingMonitor objective rightMove.1 false).initial
    ((), ())).target .first
  have ha : profiledRawJointRightPhysicalSiblingAllowed objective rightMove.1 target :=
    (rightMove.memberController_targetSafe objective false (fun _ ↦ ((), ())) 0 .first).2
  have hsemantic : ProfiledRawJointRightSiblingSharedAllowedTarget objective family direction target := by
    rw [hd, profiledRawJointRightPhysicalSiblingDescriptorOf_allowed_iff] at ha
    exact ha
  obtain ⟨slot, hslot⟩ := allowed_target_left_live member hmember target hsemantic
  have hrealizes : tables.ChildRealizes objective source source_wins bank target
      (tables.resolveTarget objective source source_wins bank target) := by
    unfold tables bank
    exact (exactEffectTable_root_aligned objective source key).resolveTarget_realizes_right
      objective source source_wins key _ key.1.1 rfl
      (.inl rightMove.1.source) hroot rightMove hrkey target ha
  obtain ⟨leftMove, hl⟩ := childRealizes_resolvePacket_leftMove_exists
    objective source source_wins tables bank target hrealizes (.inr slot) hslot
  have hlpacket : (packetFor rightMove).successor.2.1.1.2.2 = some leftMove := by
    rw [packetFor_eq]
    exact hl
  refine ⟨rightMove, packetFor rightMove,
    leftMove, hrkey, hroot, packetFor_eq rightMove, hlpacket, ?_⟩
  dsimp only
  intro graphs hzero hone
  exact installed_entry_left_right_rejects tables bank
    (initialProfiledRawJointRightPhysicalSiblingReceiver objective rightMove .first)
    (rightMove.memberController objective false).initial
    (profiledRawJointRightPhysicalSiblingOwnerReachable_initial objective rightMove)
    template (packetFor rightMove) family direction member hmember hd leftMove hlpacket
    graphs hzero hone
    (ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.ownerFibreRightEntryDPAState
      objective leftMove)

end
end ExactEntry
end ReceiptMemoryOwnerObstruction
end DistributedSynthesis
