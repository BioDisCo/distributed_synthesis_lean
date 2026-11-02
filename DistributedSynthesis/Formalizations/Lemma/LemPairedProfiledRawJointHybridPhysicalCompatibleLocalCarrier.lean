/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingDeferredMemberControl
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointFinitePhysicalSiblingLocalInstallation
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatiblePath

/-!
# Local carriers for compatible physical sibling tables

This file closes the recurrent controller-side seam at exactly the level at
which it is true.  A carried finite physical sibling move has two local
projections:

* the nonreceiver stores the move's finite owner control and advances it from
  its own input only;
* the receiver stores the same move, its finite monitor state, and the latest
  emitted finite target.

The hidden common/strict member can remain unresolved in an acknowledged
delayed carrier.  Both member projections have literally the same owner
output and next owner control, so the generic deferred-member carrier applies
without a hierarchy signal.

At a physical cut, target safety of that *same installed move*, together with
its proof-side equality to the corresponding component of the current
compatible annotation, produces
`ProfiledRawJointHybridPhysicalCompatibleTableTargetAt`.  The existing
compatible-path theorem then selects a child of the same outer policy.
Runtime controls contain only finite moves, finite local controller states,
and finite retained payloads.  No executable definition below accepts a
graph, orientation, side, leader bit, strict-leader bit, policy state,
history, or view.

This is deliberately the recurrent one-sided seam.  The initial common root
has no recurrent table component; its first exact strict exit is a separate
finite prefix.  In particular, none of the theorems below is claimed for the
`n = 0` common-root transition of a compatible target path.
-/

namespace DistributedSynthesis

universe u v x y s p

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

private abbrev CompatiblePolicy
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleRationalPolicy A strategy hwin
    initial

private abbrev CompatibleState
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatiblePolicyState A strategy hwin initial

/-! ## The finite sibling moves satisfy the delayed-member laws -/

/-- State-first owner step for one right physical move.  The Boolean is the
unresolved proof-side member, not an observed hierarchy bit. -/
noncomputable def profiledRawJointRightPhysicalSiblingDeferredStep
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (member : Bool)
    (control : (move.memberController A false).Control)
    (input : In₁) :
    (move.memberController A false).Control × Out₁ :=
  let controller := move.memberController A member
  (controller.step control input, (controller.labelOf control).1 input)

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- The unresolved right common/strict pair has one blind output and one
shared successor owner control at every already-reached table control. -/
theorem profiledRawJointRightPhysicalSiblingDeferredStep_laws
    (move : ProfiledRawJointRightPhysicalSiblingMove A) :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberStepLaws
      (profiledRawJointRightPhysicalSiblingDeferredStep A move) := by
  refine { outputEq := ?_, stateEq := ?_ }
  · intro control input
    rfl
  · intro control input
    rfl

/-- Left mirror of the shared owner step. -/
noncomputable def profiledRawJointLeftPhysicalSiblingDeferredStep
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (member : Bool)
    (control : (move.memberController A false).Control)
    (input : In₂) :
    (move.memberController A false).Control × Out₂ :=
  let controller := move.memberController A member
  (controller.step control input, (controller.labelOf control).1 input)

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointLeftPhysicalSiblingDeferredStep_laws
    (move : ProfiledRawJointLeftPhysicalSiblingMove A) :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberStepLaws
      (profiledRawJointLeftPhysicalSiblingDeferredStep A move) := by
  refine { outputEq := ?_, stateEq := ?_ }
  · intro control input
    rfl
  · intro control input
    rfl

/-! ## Finite move-keyed pending carriers -/

/-- A right pending owner occurrence.  The installed table is the finite key;
the only hidden bit is the unresolved common/strict member. -/
noncomputable abbrev ProfiledRawJointRightPhysicalSiblingDeferredOwner
    (Payload : Type p) :=
  FiniteAcknowledgedDelayedCarrier.KeyedDeferredMemberControl
    (ProfiledRawJointRightPhysicalSiblingMove A)
    (fun move ↦ (move.memberController A false).Control) Payload

noncomputable instance {Payload : Type p} [Fintype Payload] :
    Fintype (ProfiledRawJointRightPhysicalSiblingDeferredOwner A Payload) := by
  classical
  infer_instance

/-- A left pending owner occurrence. -/
noncomputable abbrev ProfiledRawJointLeftPhysicalSiblingDeferredOwner
    (Payload : Type p) :=
  FiniteAcknowledgedDelayedCarrier.KeyedDeferredMemberControl
    (ProfiledRawJointLeftPhysicalSiblingMove A)
    (fun move ↦ (move.memberController A false).Control) Payload

noncomputable instance {Payload : Type p} [Fintype Payload] :
    Fintype (ProfiledRawJointLeftPhysicalSiblingDeferredOwner A Payload) := by
  classical
  infer_instance

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- The whole finite right move family, after sigma packing, satisfies the
generic delayed-member law expected by the acknowledged carrier. -/
theorem profiledRawJointRightPhysicalSiblingKeyedDeferredStep_laws :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberStepLaws
      (FiniteAcknowledgedDelayedCarrier.keyedDeferredSharedStep
        (fun move ↦
          profiledRawJointRightPhysicalSiblingDeferredStep A move)) := by
  exact FiniteAcknowledgedDelayedCarrier.keyedDeferredSharedStep_laws
    (fun move ↦ profiledRawJointRightPhysicalSiblingDeferredStep A move)
    (fun move ↦
      profiledRawJointRightPhysicalSiblingDeferredStep_laws A move)

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Left-family mirror. -/
theorem profiledRawJointLeftPhysicalSiblingKeyedDeferredStep_laws :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberStepLaws
      (FiniteAcknowledgedDelayedCarrier.keyedDeferredSharedStep
        (fun move ↦
          profiledRawJointLeftPhysicalSiblingDeferredStep A move)) := by
  exact FiniteAcknowledgedDelayedCarrier.keyedDeferredSharedStep_laws
    (fun move ↦ profiledRawJointLeftPhysicalSiblingDeferredStep A move)
    (fun move ↦
      profiledRawJointLeftPhysicalSiblingDeferredStep_laws A move)

/-! ## A literal local physical cut supplies the compatible target -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- A checked right physical close cannot carry a target with an empty left
lane.  This is the bare-code version of the standard policy-state target
shape inversion. -/
theorem exists_profiledRawJointLeftSlot_of_rightPhysicalTargetSafe
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (scan : PairedRightScanState A) (row : PairedEntryRow)
    (physical : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hclose : erasePairedProfiledState A
        (profiledRawJointUnitRightTargetProjection A target) =
      pairedRightCloseTarget A scan row physical) :
    ∃ slot : ProfiledRawLeftSlot A,
      target.family.left () = some slot := by
  cases hslot : target.family.left () with
  | none =>
      simp [profiledRawJointUnitRightTargetProjection, hslot,
        erasePairedProfiledState, pairedRightCloseTarget] at hclose
  | some slot => exact ⟨slot, rfl⟩

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Left-close mirror. -/
theorem exists_profiledRawJointRightSlot_of_leftPhysicalTargetSafe
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (scan : PairedLeftScanState A) (row : PairedEntryRow)
    (physical : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hclose : erasePairedProfiledState A
        (profiledRawJointUnitLeftTargetProjection A target) =
      pairedLeftCloseTarget A scan row physical) :
    ∃ slot : ProfiledRawRightSlot A,
      target.family.right () = some slot := by
  cases hslot : target.family.right () with
  | none =>
      simp [profiledRawJointUnitLeftTargetProjection, hslot,
        erasePairedProfiledState, pairedLeftCloseTarget] at hclose
  | some slot => exact ⟨slot, rfl⟩

/-- Right recurrent cut.  The `play` is induced by the exact finite owner
controller stored at the nonreceiver; its receiver component is exactly the
finite table advanced by the local receive function.  Target safety supplies
the only non-structural constructor field. -/
theorem
    profiledRawJointHybridPhysicalCompatibleRightTableTargetAt_of_localCut
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (state : CompatibleState A strategy hwin initial)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (current_code : state.1.1 = .oneSided currentCode)
    (currentRoot : ProfiledRawJointThreadRoot A)
    (current_live :
      profiledRawJointHybridCurrentSlots A .right state.1.1 () =
        some currentRoot)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (move_eq : state.1.2.1 = some move)
    (member : Bool) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow) (slot : ProfiledRawLeftSlot A)
    (target_live :
      let monitor := profiledRawJointRightPhysicalSiblingMonitor A move.1
        member
      let controller := move.memberController A member
      let play := treePlay
        (narrowedInducedTree monitor controller.labeledTree) env
      ((play n).2.1.target row).family.left () = some slot) :
    ProfiledRawJointHybridPhysicalCompatibleTableTargetAt A strategy hwin
      state .left (.inr slot) := by
  let monitor := profiledRawJointRightPhysicalSiblingMonitor A move.1 member
  let controller := move.memberController A member
  let play := treePlay
    (narrowedInducedTree monitor controller.labeledTree) env
  let target := (play n).2.1.target row
  have hsafe := move.memberController_targetSafe A member env n row
  dsimp only at hsafe target_live
  exact
    .right currentCode current_code currentRoot current_live move move_eq
      target hsafe.2 slot target_live

/-- Left recurrent cut mirror. -/
theorem
    profiledRawJointHybridPhysicalCompatibleLeftTableTargetAt_of_localCut
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (state : CompatibleState A strategy hwin initial)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (current_code : state.1.1 = .oneSided currentCode)
    (currentRoot : ProfiledRawJointThreadRoot A)
    (current_live :
      profiledRawJointHybridCurrentSlots A .left state.1.1 () =
        some currentRoot)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (move_eq : state.1.2.2 = some move)
    (member : Bool) (env : Nat → In₁ × In₂) (n : Nat)
    (row : PairedEntryRow) (slot : ProfiledRawRightSlot A)
    (target_live :
      let monitor := profiledRawJointLeftPhysicalSiblingMonitor A move.1
        member
      let controller := move.memberController A member
      let play := treePlay
        (narrowedInducedTree monitor controller.labeledTree) env
      ((play n).2.1.target row).family.right () = some slot) :
    ProfiledRawJointHybridPhysicalCompatibleTableTargetAt A strategy hwin
      state .right (.inl slot) := by
  let monitor := profiledRawJointLeftPhysicalSiblingMonitor A move.1 member
  let controller := move.memberController A member
  let play := treePlay
    (narrowedInducedTree monitor controller.labeledTree) env
  let target := (play n).2.1.target row
  have hsafe := move.memberController_targetSafe A member env n row
  dsimp only at hsafe target_live
  exact
    .left currentCode current_code currentRoot current_live move move_eq
      target hsafe.2 slot target_live

/-- A right local controller cut supplies its crossed live slot and the full
compatible table-target predicate; target liveness is not an extra model
hypothesis. -/
theorem
    exists_profiledRawJointHybridPhysicalCompatibleRightTableTargetAt_of_localCut
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (state : CompatibleState A strategy hwin initial)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (current_code : state.1.1 = .oneSided currentCode)
    (currentRoot : ProfiledRawJointThreadRoot A)
    (current_live :
      profiledRawJointHybridCurrentSlots A .right state.1.1 () =
        some currentRoot)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (move_eq : state.1.2.1 = some move)
    (member : Bool) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow) :
    ∃ slot : ProfiledRawLeftSlot A,
      ProfiledRawJointHybridPhysicalCompatibleTableTargetAt A strategy hwin
        state .left (.inr slot) := by
  let monitor := profiledRawJointRightPhysicalSiblingMonitor A move.1 member
  let controller := move.memberController A member
  let play := treePlay
    (narrowedInducedTree monitor controller.labeledTree) env
  let target := (play n).2.1.target row
  have hsafe := move.memberController_targetSafe A member env n row
  dsimp only at hsafe
  obtain ⟨slot, hslot⟩ :=
    exists_profiledRawJointLeftSlot_of_rightPhysicalTargetSafe A target
      ((monitor.run play n).2.1) row
      (profiledRawJointTargetRightPhysicalLetter A (play n)) hsafe.1
  refine ⟨slot, ?_⟩
  exact
    profiledRawJointHybridPhysicalCompatibleRightTableTargetAt_of_localCut A
      strategy hwin state currentCode current_code currentRoot current_live
      move move_eq member env n row slot hslot

/-- Left local-cut mirror. -/
theorem
    exists_profiledRawJointHybridPhysicalCompatibleLeftTableTargetAt_of_localCut
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (state : CompatibleState A strategy hwin initial)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (current_code : state.1.1 = .oneSided currentCode)
    (currentRoot : ProfiledRawJointThreadRoot A)
    (current_live :
      profiledRawJointHybridCurrentSlots A .left state.1.1 () =
        some currentRoot)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (move_eq : state.1.2.2 = some move)
    (member : Bool) (env : Nat → In₁ × In₂) (n : Nat)
    (row : PairedEntryRow) :
    ∃ slot : ProfiledRawRightSlot A,
      ProfiledRawJointHybridPhysicalCompatibleTableTargetAt A strategy hwin
        state .right (.inl slot) := by
  let monitor := profiledRawJointLeftPhysicalSiblingMonitor A move.1 member
  let controller := move.memberController A member
  let play := treePlay
    (narrowedInducedTree monitor controller.labeledTree) env
  let target := (play n).2.1.target row
  have hsafe := move.memberController_targetSafe A member env n row
  dsimp only at hsafe
  obtain ⟨slot, hslot⟩ :=
    exists_profiledRawJointRightSlot_of_leftPhysicalTargetSafe A target
      ((monitor.run play n).2.1) row
      (profiledRawJointTargetLeftPhysicalLetter A (play n)) hsafe.1
  refine ⟨slot, ?_⟩
  exact
    profiledRawJointHybridPhysicalCompatibleLeftTableTargetAt_of_localCut A
      strategy hwin state currentCode current_code currentRoot current_live
      move move_eq member env n row slot hslot

/-! ## Same-policy successor in one arrow -/

/-- A right local cut of the literally installed table advances the same
compatible policy.  The outer policy and reachability remain proof-side and
are absent from every executable carrier above. -/
theorem
    exists_profiledRawJointHybridPhysicalCompatibleRightTransition_of_localCut_atSlot
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (hreachable : ProfiledRawJointHybridPhysicalCompatibleReachable A
      strategy hwin initial policy state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (current_code : state.1.1 = .oneSided currentCode)
    (currentRoot : ProfiledRawJointThreadRoot A)
    (current_live :
      profiledRawJointHybridCurrentSlots A .right state.1.1 () =
        some currentRoot)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (move_eq : state.1.2.1 = some move)
    (member : Bool) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow) (slot : ProfiledRawLeftSlot A)
    (target_live :
      let monitor := profiledRawJointRightPhysicalSiblingMonitor A move.1
        member
      let controller := move.memberController A member
      let play := treePlay
        (narrowedInducedTree monitor controller.labeledTree) env
      ((play n).2.1.target row).family.left () = some slot) :
    ∃ next : CompatibleState A strategy hwin initial,
      Nonempty
        (ProfiledRawJointHybridPhysicalCompatibleTargetTransitionAt A
          strategy hwin policy state next .left (.inr slot)) := by
  let targetAt :=
    profiledRawJointHybridPhysicalCompatibleRightTableTargetAt_of_localCut A
      strategy hwin state currentCode current_code currentRoot current_live
      move move_eq member env n row slot target_live
  exact targetAt.exists_transition A strategy hwin policy state hreachable

/-- Left local-cut mirror. -/
theorem
    exists_profiledRawJointHybridPhysicalCompatibleLeftTransition_of_localCut_atSlot
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (hreachable : ProfiledRawJointHybridPhysicalCompatibleReachable A
      strategy hwin initial policy state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (current_code : state.1.1 = .oneSided currentCode)
    (currentRoot : ProfiledRawJointThreadRoot A)
    (current_live :
      profiledRawJointHybridCurrentSlots A .left state.1.1 () =
        some currentRoot)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (move_eq : state.1.2.2 = some move)
    (member : Bool) (env : Nat → In₁ × In₂) (n : Nat)
    (row : PairedEntryRow) (slot : ProfiledRawRightSlot A)
    (target_live :
      let monitor := profiledRawJointLeftPhysicalSiblingMonitor A move.1
        member
      let controller := move.memberController A member
      let play := treePlay
        (narrowedInducedTree monitor controller.labeledTree) env
      ((play n).2.1.target row).family.right () = some slot) :
    ∃ next : CompatibleState A strategy hwin initial,
      Nonempty
        (ProfiledRawJointHybridPhysicalCompatibleTargetTransitionAt A
          strategy hwin policy state next .right (.inl slot)) := by
  let targetAt :=
    profiledRawJointHybridPhysicalCompatibleLeftTableTargetAt_of_localCut A
      strategy hwin state currentCode current_code currentRoot current_live
      move move_eq member env n row slot target_live
  exact targetAt.exists_transition A strategy hwin policy state hreachable

/-- Complete recurrent right seam: an actual local cut of the installed
finite table automatically exposes the crossed live slot and advances one
fixed compatible policy. -/
theorem
    exists_profiledRawJointHybridPhysicalCompatibleRightTransition_of_localCut
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (hreachable : ProfiledRawJointHybridPhysicalCompatibleReachable A
      strategy hwin initial policy state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (current_code : state.1.1 = .oneSided currentCode)
    (currentRoot : ProfiledRawJointThreadRoot A)
    (current_live :
      profiledRawJointHybridCurrentSlots A .right state.1.1 () =
        some currentRoot)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (move_eq : state.1.2.1 = some move)
    (member : Bool) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow) :
    ∃ slot : ProfiledRawLeftSlot A,
      ∃ next : CompatibleState A strategy hwin initial,
        Nonempty
          (ProfiledRawJointHybridPhysicalCompatibleTargetTransitionAt A
            strategy hwin policy state next .left (.inr slot)) := by
  obtain ⟨slot, targetAt⟩ :=
    exists_profiledRawJointHybridPhysicalCompatibleRightTableTargetAt_of_localCut
      A strategy hwin state currentCode current_code currentRoot current_live
        move move_eq member env n row
  obtain ⟨next, transition⟩ :=
    targetAt.exists_transition A strategy hwin policy state hreachable
  exact ⟨slot, next, transition⟩

/-- Complete recurrent left seam. -/
theorem
    exists_profiledRawJointHybridPhysicalCompatibleLeftTransition_of_localCut
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (hreachable : ProfiledRawJointHybridPhysicalCompatibleReachable A
      strategy hwin initial policy state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (current_code : state.1.1 = .oneSided currentCode)
    (currentRoot : ProfiledRawJointThreadRoot A)
    (current_live :
      profiledRawJointHybridCurrentSlots A .left state.1.1 () =
        some currentRoot)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (move_eq : state.1.2.2 = some move)
    (member : Bool) (env : Nat → In₁ × In₂) (n : Nat)
    (row : PairedEntryRow) :
    ∃ slot : ProfiledRawRightSlot A,
      ∃ next : CompatibleState A strategy hwin initial,
        Nonempty
          (ProfiledRawJointHybridPhysicalCompatibleTargetTransitionAt A
            strategy hwin policy state next .right (.inl slot)) := by
  obtain ⟨slot, targetAt⟩ :=
    exists_profiledRawJointHybridPhysicalCompatibleLeftTableTargetAt_of_localCut
      A strategy hwin state currentCode current_code currentRoot current_live
        move move_eq member env n row
  obtain ⟨next, transition⟩ :=
    targetAt.exists_transition A strategy hwin policy state hreachable
  exact ⟨slot, next, transition⟩

end

end DetParityAutomaton

end DistributedSynthesis
