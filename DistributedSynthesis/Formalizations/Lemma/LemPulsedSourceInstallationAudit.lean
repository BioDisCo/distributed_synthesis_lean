/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPulsedSourceBlockFlexibility
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatibleExactEffectTable

/-!
# Target-conditioned installation in the pulsed-source stress test

The opposite move installed at a realized target must have that target's
source slot. In particular, the two same-source schedules in the block test
cannot simply be installed as a parent and its successor. This file checks
the source-sensitive first-round obligation as well as the packet seam.
-/

namespace DistributedSynthesis
namespace PulsedSourceInstallationAudit

open DetParityAutomaton TwoProcessNoResetReversalObstruction
open TwoProcessPhysicalTargetAudit (pulsedSource pulsedSource_wins strictState)

noncomputable section

def minimumState : PairedEntryTreeState objective → Bool
  | .inl _ => true
  | .inr (.inl slot) => slot.2
  | .inr (.inr slot) => slot.2

def nonGrantingTargetSlot : ProfiledRawLeftSlot objective :=
  (((false, true), true), fun _ ↦ true)

/-- Pulsed outputs do not depend on receipt; both endpoints see the same
round count at the initial strict letter of a semantic left entry. -/
theorem pulsed_left_initial_outputs_eq (entry : ProcTwoPairedEntryRep pulsedSource) :
    entry.lambdaOfStrategy.blind [] () =
      entry.lambdaOfStrategy.informedRight [] ((), ()) := by
  have hone := StarReadback.viewRounds_currentView .one entry.rightHistory
  have htwo := StarReadback.viewRounds_currentView .two entry.rightHistory
  change clock (nextView .two entry.rightHistory (leftEnvironment ((), ()))) =
    clock (nextView .one entry.rightHistory (leftEnvironment ((), ())))
  simpa [clock, nextView, advanceViewsWithEnvironment, leftEnvironment,
    StarReadback.viewRounds, currentView] using congrArg
      (fun n ↦ decide ((n + 1) % 2 = 0)) (htwo.trans hone.symm)

theorem blockMin_cons_grant (record : RoundRecord Unit Unit Graph Bool Bool)
    (hgrant : grant record = true)
    (rest : List (RoundRecord Unit Unit Graph Bool Bool)) :
    blockMinState objective false (record :: rest) = true := by
  simpa [blockMinState, blockEndAndMin, objective, minPriorityState, hgrant]
    using PulsedSourceBlockFlexibility.blockMin_true rest

/-- From a rejecting strict source with next informed profile `true`, an
allowed semantic target cannot both retain an odd minimum and reject again. -/
theorem left_allowed_oddMinimum_forces_grant
    {sourceMinimum : Bool}
    (family : ProfiledRawJointSemanticFamily objective pulsedSource (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := Unit) (In₂ := Unit))
    (member : ProcTwoPairedEntryRep pulsedSource × objective.State)
    (hmember : (family.semanticChild objective direction).left () = some member)
    (hsource : profiledRawLeftSlotOfSemanticPair objective member =
      (((false, true), sourceMinimum), fun _ ↦ true))
    (target : ProfiledRawJointUnitTarget objective)
    (hallowed : ProfiledRawJointLeftSiblingSharedAllowedTarget objective
      family direction target)
    (hmin : minimumState (erasePairedProfiledState objective
      (profiledRawJointUnitLeftTargetProjection objective target)) = false) :
    strictState (erasePairedProfiledState objective
      (profiledRawJointUnitLeftTargetProjection objective target)) = true := by
  have hinformed : member.1.lambdaOfStrategy.informedRight [] ((), ()) = true :=
    congrArg (fun slot : ProfiledRawLeftSlot objective ↦ slot.2 ((), ())) hsource
  have hblind : member.1.lambdaOfStrategy.blind [] () = true :=
    (pulsed_left_initial_outputs_eq member.1).trans hinformed
  obtain ⟨row, past, input, rfl⟩ := hallowed
  have h := (profiledRawJointLeftSiblingActivation objective pulsedSource_wins
    family direction member hmember false).target_state row past input
  dsimp only [profiledRawJointLeftSiblingActivation] at h
  rw [h] at hmin ⊢
  rw [hsource] at hmin ⊢
  cases row with
  | both =>
    change blockMinState objective true (member.1.lambdaOfStrategy.bothWord past) =
      false at hmin
    rw [PulsedSourceBlockFlexibility.blockMin_true] at hmin
    cases hmin
  | first =>
    cases past with
    | nil =>
      rcases input with ⟨⟨⟩, ⟨⟩⟩
      change (member.1.lambdaOfStrategy.informedRight [] ((), ()) &&
        member.1.lambdaOfStrategy.blind [] ()) = true
      rw [hinformed, hblind]
      rfl
    | cons input rest =>
      rcases input with ⟨⟨⟩, ⟨⟩⟩
      change blockMinState objective false
        (leftRoundRecord ((), ()) (member.1.lambdaOfStrategy.informedRight [] ((), ()))
          (member.1.lambdaOfStrategy.blind [] ()) :: _) = false at hmin
      rw [blockMin_cons_grant _ (by simp [grant, leftRoundRecord, hinformed, hblind])]
        at hmin
      cases hmin

/-- Every accepted table for such a semantic descriptor must make its first
strict-left letter grant. In particular its first blind sender output is
`true`, regardless of which accepted finite table is selected. -/
theorem left_first_outputs_grant
    {sourceMinimum : Bool}
    (family : ProfiledRawJointSemanticFamily objective pulsedSource (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := Unit) (In₂ := Unit))
    (member : ProcTwoPairedEntryRep pulsedSource × objective.State)
    (hmember : (family.semanticChild objective direction).left () = some member)
    (hsource : profiledRawLeftSlotOfSemanticPair objective member =
      (((false, true), sourceMinimum), fun _ ↦ true))
    (move : ProfiledRawJointLeftPhysicalSiblingMove objective)
    (hdescriptor : move.1 = profiledRawJointLeftPhysicalSiblingDescriptorOf
      objective family direction member) :
    ((stepProfiledRawJointLeftPhysicalSiblingReceiverFor objective move
      (move.memberController objective false).initial .first
      (profiledRawJointLeftPhysicalSiblingMonitor objective move.1 false).initial
      ((), ())).1 &&
      (((move.memberController objective false).labelOf
        (move.memberController objective false).initial).1 ())) = true := by
  obtain ⟨hclose, hallowed⟩ := move.memberController_targetSafe objective false
    (fun _ ↦ ((), ())) 0 .first
  let play := treePlay (narrowedInducedTree
    (profiledRawJointLeftPhysicalSiblingMonitor objective move.1 false)
    (move.memberController objective false).labeledTree) (fun _ ↦ ((), ()))
  have hmin : minimumState (erasePairedProfiledState objective
      (profiledRawJointUnitLeftTargetProjection objective
        ((play 0).2.1.target .first))) = false := by
    rw [hclose]
    change move.1.source.1.1.1 = false
    rw [hdescriptor]
    exact congrArg (fun slot : ProfiledRawLeftSlot objective ↦ slot.1.1.1) hsource
  nth_rw 1 [hdescriptor] at hallowed
  rw [profiledRawJointLeftPhysicalSiblingDescriptorOf_allowed_iff] at hallowed
  have hgrant := left_allowed_oddMinimum_forces_grant family direction member
    hmember hsource _ hallowed hmin
  rw [hclose, TwoProcessPhysicalTargetAudit.strictState_leftClose] at hgrant
  exact hgrant

theorem left_first_sender_true
    (family : ProfiledRawJointSemanticFamily objective pulsedSource (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := Unit) (In₂ := Unit))
    (member : ProcTwoPairedEntryRep pulsedSource × objective.State)
    (hmember : (family.semanticChild objective direction).left () = some member)
    (hsource : profiledRawLeftSlotOfSemanticPair objective member =
      nonGrantingTargetSlot)
    (move : ProfiledRawJointLeftPhysicalSiblingMove objective)
    (hdescriptor : move.1 = profiledRawJointLeftPhysicalSiblingDescriptorOf
      objective family direction member) :
    (((move.memberController objective false).labelOf
      (move.memberController objective false).initial).1 ()) = true :=
  (Bool.and_eq_true_iff.mp
    (left_first_outputs_grant family direction member hmember hsource move
      hdescriptor)).2

/-- The first non-granting target in the explicit stress test has a different
source slot from the independently chosen original left schedule. -/
theorem rightTarget_false_leftSlot :
    (PulsedSourceBlockFlexibility.rightTarget false).family.left () =
      some nonGrantingTargetSlot := by
  have h := PulsedSourceBlockFlexibility.rightTarget_projection false
  unfold profiledRawJointUnitRightTargetProjection at h
  cases hs : (PulsedSourceBlockFlexibility.rightTarget false).family.left () with
  | none => simp [hs] at h
  | some slot =>
    simp only [hs, Sum.inr.injEq] at h
    exact congrArg some h

theorem rightTarget_false_currentSlot :
    profiledRawJointOneSidedCurrentSlots objective .left
      (PulsedSourceBlockFlexibility.rightTarget false) () =
        some (.inr nonGrantingTargetSlot) := by
  simp [profiledRawJointOneSidedCurrentSlots, rightTarget_false_leftSlot]

theorem installed_source_ne_original :
    nonGrantingTargetSlot ≠ PulsedSourceBlockFlexibility.source := by
  intro h
  have hstates := congrArg (fun slot : ProfiledRawLeftSlot objective ↦ slot.1.1.1) h
  cases hstates

section Packet

universe m
variable {Memory : Type m}

private abbrev Tables :=
  ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection
    (Memory := Memory) objective pulsedSource

private abbrev Bank :=
  ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankControl
    (Memory := Memory) objective pulsedSource

/-- Source-sensitive provenance of the move actually installed by a raw-table
packet. No global acceptance or finite-memory hypothesis is assumed. -/
theorem realized_packet_left_provenance_at
    (tables : Tables (Memory := Memory)) (state : Bank (Memory := Memory))
    (target : ProfiledRawJointUnitTarget objective)
    (slot : ProfiledRawLeftSlot objective)
    (hslotAt : profiledRawJointOneSidedCurrentSlots objective .left target () =
      some (.inr slot))
    (hrealizes : tables.ChildRealizes objective pulsedSource pulsedSource_wins
      state target
      (tables.resolveTarget objective pulsedSource pulsedSource_wins state target))
    (move : ProfiledRawJointLeftPhysicalSiblingMove objective)
    (hmove : (tables.resolvePacket objective pulsedSource pulsedSource_wins
      state target).successor.2.1.1.2.2 =
        some move) :
    ∃ (family : ProfiledRawJointSemanticFamily objective pulsedSource (I := Unit))
      (direction : ProfiledRawJointFamilyDirection
        (I := Unit) (In₁ := Unit) (In₂ := Unit))
      (member : ProcTwoPairedEntryRep pulsedSource × objective.State),
      (family.semanticChild objective direction).left () = some member ∧
      profiledRawLeftSlotOfSemanticPair objective member = slot ∧
      move.1 = profiledRawJointLeftPhysicalSiblingDescriptorOf objective
        family direction member := by
  let childCode := tables.resolveTarget objective pulsedSource pulsedSource_wins
    state target
  obtain ⟨source, actual, hcode, hannotation, _⟩ :=
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTable.childRealizes_exists_child
      objective pulsedSource pulsedSource_wins tables state _ childCode hrealizes
  have hroot : profiledRawJointOneSidedCurrentSlots objective .left
      ((source.step objective actual).code objective) () =
        some (.inr slot) := by
    rw [hcode]
    exact hslotAt
  obtain ⟨member, hmember, hslot, _⟩ :=
    (source.step objective actual).exists_left_member_of_currentSlot objective ()
      (.inr slot) hroot
  have hsource : profiledRawLeftSlotOfSemanticPair objective member =
      slot := (Sum.inr.inj hslot).symm
  have hsuccessor :
      (tables.successor objective pulsedSource state childCode).2.1.1.2 =
        childCode.2 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, hsuccessor⟩ := hrealizes
    exact congrArg (fun publicState ↦ publicState.1.2) hsuccessor
  change (tables.successor objective pulsedSource state childCode).2.1.1.2.2 =
    some move at hmove
  rw [hsuccessor, hannotation] at hmove
  cases hside : actual.side with
  | left =>
    simp [ProfiledRawJointOneSidedSemanticState.step, hside,
      ProfiledRawJointSemanticFamily.leftActualChild] at hmember
  | right =>
    have hsemantic : (source.family.semanticChild objective actual.direction).left () =
        some member := by
      simpa [ProfiledRawJointOneSidedSemanticState.step, hside,
        ProfiledRawJointSemanticFamily.rightActualChild] using hmember
    change (profiledRawJointHybridPhysicalAnnotationOf objective pulsedSource
      pulsedSource_wins source.family actual.direction).2 = some move at hmove
    obtain ⟨other, hother, hselected⟩ :=
      profiledRawJointLeftPhysicalSiblingMoveOption_spec objective pulsedSource
        pulsedSource_wins source.family actual.direction move hmove
    have heq : other = member := Option.some.inj (hother.symm.trans hsemantic)
    subst other
    refine ⟨source.family, actual.direction, member, hsemantic, hsource, ?_⟩
    rw [hselected]
    rfl

theorem realized_packet_left_provenance
    (tables : Tables (Memory := Memory)) (state : Bank (Memory := Memory))
    (hrealizes : tables.ChildRealizes objective pulsedSource pulsedSource_wins
      state (PulsedSourceBlockFlexibility.rightTarget false)
      (tables.resolveTarget objective pulsedSource pulsedSource_wins state
        (PulsedSourceBlockFlexibility.rightTarget false)))
    (move : ProfiledRawJointLeftPhysicalSiblingMove objective)
    (hmove : (tables.resolvePacket objective pulsedSource pulsedSource_wins
      state (PulsedSourceBlockFlexibility.rightTarget false)).successor.2.1.1.2.2 =
        some move) :
    ∃ (family : ProfiledRawJointSemanticFamily objective pulsedSource (I := Unit))
      (direction : ProfiledRawJointFamilyDirection
        (I := Unit) (In₁ := Unit) (In₂ := Unit))
      (member : ProcTwoPairedEntryRep pulsedSource × objective.State),
      (family.semanticChild objective direction).left () = some member ∧
      profiledRawLeftSlotOfSemanticPair objective member = nonGrantingTargetSlot ∧
      move.1 = profiledRawJointLeftPhysicalSiblingDescriptorOf objective
        family direction member :=
  realized_packet_left_provenance_at tables state _ _ rightTarget_false_currentSlot
    hrealizes move hmove

theorem realized_packet_left_first_sender_true
    (tables : Tables (Memory := Memory)) (state : Bank (Memory := Memory))
    (hrealizes : tables.ChildRealizes objective pulsedSource pulsedSource_wins
      state (PulsedSourceBlockFlexibility.rightTarget false)
      (tables.resolveTarget objective pulsedSource pulsedSource_wins state
        (PulsedSourceBlockFlexibility.rightTarget false)))
    (move : ProfiledRawJointLeftPhysicalSiblingMove objective)
    (hmove : (tables.resolvePacket objective pulsedSource pulsedSource_wins
      state (PulsedSourceBlockFlexibility.rightTarget false)).successor.2.1.1.2.2 =
        some move) :
    (((move.memberController objective false).labelOf
      (move.memberController objective false).initial).1 ()) = true := by
  obtain ⟨family, direction, member, hmember, hsource, hdescriptor⟩ :=
    realized_packet_left_provenance tables state hrealizes move hmove
  exact left_first_sender_true family direction member hmember hsource move hdescriptor

/-- The literal staged bridge consumes the target's new owner on its first
blind step. It cannot substitute the old same-source left schedule. -/
theorem staged_bridge_first_output_true
    (tables : Tables (Memory := Memory)) (state : Bank (Memory := Memory))
    (hrealizes : tables.ChildRealizes objective pulsedSource pulsedSource_wins
      state (PulsedSourceBlockFlexibility.rightTarget false)
      (tables.resolveTarget objective pulsedSource pulsedSource_wins state
        (PulsedSourceBlockFlexibility.rightTarget false)))
    (receiver : ProfiledRawJointRightPhysicalSiblingReceiver objective) :
    let packet := tables.resolvePacket objective pulsedSource pulsedSource_wins
      state (PulsedSourceBlockFlexibility.rightTarget false)
    (profiledRawJointRecurrentFiniteMemoryRightToLeftBridgeNoRecv objective
      pulsedSource (.inl (state, receiver, some packet)) ()).2 = true := by
  obtain ⟨move, hmove⟩ :=
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTable.childRealizes_resolvePacket_leftMove_exists
      objective pulsedSource pulsedSource_wins tables state _ hrealizes
      (.inr nonGrantingTargetSlot) rightTarget_false_currentSlot
  dsimp only
  simp only [profiledRawJointRecurrentFiniteMemoryRightToLeftBridgeNoRecv, hmove]
  exact realized_packet_left_first_sender_true tables state hrealizes move hmove

/-- After an actual informed right receive producing the candidate's first
target, the strict open bridge's next blind output is forced to `true`.
This is an equation of the implemented bridge, not a new composition model. -/
theorem right_receive_then_blind_output_true
    (tables : Tables (Memory := Memory)) (state : Bank (Memory := Memory))
    (receiver : ProfiledRawJointRightPhysicalSiblingReceiver objective)
    (owner : (receiver.1.memberController objective false).Control)
    (htarget : (((receiver.1.memberController objective false).labelOf owner).2
      receiver.2.2.1 ((), ()) |>.target receiver.2.1) =
        PulsedSourceBlockFlexibility.rightTarget false)
    (hrealizes : tables.ChildRealizes objective pulsedSource pulsedSource_wins
      state (PulsedSourceBlockFlexibility.rightTarget false)
      (tables.resolveTarget objective pulsedSource pulsedSource_wins state
        (PulsedSourceBlockFlexibility.rightTarget false))) :
    let fork := tables.rightToLeftBridgeForkTwo objective pulsedSource
      pulsedSource_wins state receiver owner ((), ())
    (profiledRawJointRecurrentFiniteMemoryRightToLeftBridgeNoRecv objective
      pulsedSource fork.1.openControl ()).2 = true := by
  have hopen : (tables.rightToLeftBridgeForkTwo objective pulsedSource
      pulsedSource_wins state receiver owner ((), ())).1.openControl =
      .inl (tables.rightReceiveFor objective pulsedSource pulsedSource_wins
        state receiver owner ((), ())).1 := by
    unfold
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.rightToLeftBridgeForkTwo
    dsimp only
    split <;> rfl
  dsimp only
  rw [hopen]
  simpa only [
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.rightReceiveFor,
    stepProfiledRawJointRightPhysicalSiblingReceiverFor, htarget] using
    staged_bridge_first_output_true tables state hrealizes
      (stepProfiledRawJointRightPhysicalSiblingReceiverFor objective receiver.1
        owner receiver.2.1 receiver.2.2.1 ((), ())).2

/-- The candidate asks the newly blind endpoint for `false` at its first
reversal; the implemented bridge proved above instead emits `true`. -/
theorem candidate_first_reversal_output :
    (execution PulsedSourceBlockFlexibility.scheduledStrategy
      PulsedSourceBlockFlexibility.spoilingEnvironment 3).outputTwo = false := by
  decide

theorem owner_first_reversal_differs_from_candidate
    (tables : Tables (Memory := Memory)) (state : Bank (Memory := Memory))
    (receiver : ProfiledRawJointRightPhysicalSiblingReceiver objective)
    (owner : (receiver.1.memberController objective false).Control)
    (htarget : (((receiver.1.memberController objective false).labelOf owner).2
      receiver.2.2.1 ((), ()) |>.target receiver.2.1) =
        PulsedSourceBlockFlexibility.rightTarget false)
    (hrealizes : tables.ChildRealizes objective pulsedSource pulsedSource_wins
      state (PulsedSourceBlockFlexibility.rightTarget false)
      (tables.resolveTarget objective pulsedSource pulsedSource_wins state
        (PulsedSourceBlockFlexibility.rightTarget false)))
    (one : ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
      (Memory := Memory) objective pulsedSource)
    (coordinates : ProfiledRawJointRecurrentFiniteMemoryBoundaryBankCoordinates
      (Memory := Memory) objective pulsedSource) :
    let fork := tables.rightToLeftBridgeForkTwo objective pulsedSource
      pulsedSource_wins state receiver owner ((), ())
    let two : ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
        (Memory := Memory) objective pulsedSource :=
      (.inl fork.1.openControl, coordinates)
    (tables.ownerFibreRound objective pulsedSource pulsedSource_wins
      (one, two) ((), ()) .left).2.2 ≠
        (execution PulsedSourceBlockFlexibility.scheduledStrategy
          PulsedSourceBlockFlexibility.spoilingEnvironment 3).outputTwo := by
  change (profiledRawJointRecurrentFiniteMemoryRightToLeftBridgeNoRecv objective
      pulsedSource (tables.rightToLeftBridgeForkTwo objective pulsedSource
        pulsedSource_wins state receiver owner ((), ())).1.openControl ()).2 ≠ _
  rw [right_receive_then_blind_output_true tables state receiver owner htarget hrealizes,
    candidate_first_reversal_output]
  decide

end Packet

end
end PulsedSourceInstallationAudit
end DistributedSynthesis
