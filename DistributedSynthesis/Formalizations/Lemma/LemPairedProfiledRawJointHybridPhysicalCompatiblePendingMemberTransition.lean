/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorOperationalClose

/-!
# Compatible transition selected by a resolved pending member

The unresolved operational payload stores one target selected by the already
acknowledged table member and two possible next-receiver rows.  Once the fresh
open/close acknowledgement resolves, installation must
preserve two facts simultaneously:

* the installed crossed control has the selected target's compatible-policy
  key; and
* that key is an exact transition of the same fixed compatible policy.

This file packages that bridge.  The old entry member and fresh closing member
are independent: the former selects the target/key, while the latter selects
only the next receiver row.  Neither is a runtime strict-leader test.
-/

namespace DistributedSynthesis

universe u v x y s c

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

private abbrev RightOutput
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleSuccessorRightReceiverOutput A
    strategy hwin initial

private abbrev LeftOutput
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleSuccessorLeftReceiverOutput A
    strategy hwin initial

/-! ## Generic row-selected installation -/

/-- Resolving a right pending output installs a left control whose key and
selected target form one exact compatible transition. -/
theorem
    exists_profiledRawJointHybridPhysicalCompatibleTargetAt_of_installLeftPendingOutput
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    {ParentShared : Type c} (shared : ParentShared)
    (output : RightOutput A strategy hwin initial)
    (entryRow : PairedEntryRow) (closeMember : Bool)
    (hkey :
      let target := (output.target entryRow).1
      ProfiledRawJointHybridPhysicalCompatibleRightSuccessorKeyAt A strategy
        hwin policy state
          (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A
            strategy hwin target)
          target.1) :
    let pending :=
      profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfOutput A
        strategy hwin output entryRow
    let target :=
      profiledRawJointHybridPhysicalCompatibleRightPendingPayloadTarget A
        strategy hwin pending closeMember
    let installed :=
      profiledRawJointHybridPhysicalCompatibleInstallLeftPendingMember A
        strategy hwin policy (closeMember, shared, pending)
    ∃ slot : ProfiledRawLeftSlot A,
      installed.1.1 =
          profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
            hwin target ∧
        ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetAt A strategy
          hwin policy state target .left (.inr slot) := by
  dsimp only
  have hkey' :
      ProfiledRawJointHybridPhysicalCompatibleRightSuccessorKeyAt A strategy
        hwin policy state
          (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A
            strategy hwin
            (profiledRawJointHybridPhysicalCompatibleRightPendingPayloadTarget A
              strategy hwin
              (profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfOutput
                A strategy hwin output entryRow) closeMember))
          (profiledRawJointHybridPhysicalCompatibleRightPendingPayloadTarget A
            strategy hwin
            (profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfOutput
              A strategy hwin output entryRow) closeMember).1 := by
    simpa using hkey
  obtain ⟨slot, htargetAt⟩ :=
    exists_profiledRawJointHybridPhysicalCompatibleSuccessorTargetAt_of_rightKeyAt
      A strategy hwin policy state
        (profiledRawJointHybridPhysicalCompatibleRightPendingPayloadTarget A
          strategy hwin
          (profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfOutput
            A strategy hwin output entryRow) closeMember)
        hkey'
  exact ⟨slot, rfl, htargetAt⟩

/-- Left-close mirror. -/
theorem
    exists_profiledRawJointHybridPhysicalCompatibleTargetAt_of_installRightPendingOutput
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    {ParentShared : Type c} (shared : ParentShared)
    (output : LeftOutput A strategy hwin initial)
    (entryRow : PairedEntryRow) (closeMember : Bool)
    (hkey :
      let target := (output.target entryRow).1
      ProfiledRawJointHybridPhysicalCompatibleLeftSuccessorKeyAt A strategy
        hwin policy state
          (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A
            strategy hwin target)
          target.1) :
    let pending :=
      profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfOutput A
        strategy hwin output entryRow
    let target :=
      profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadTarget A
        strategy hwin pending closeMember
    let installed :=
      profiledRawJointHybridPhysicalCompatibleInstallRightPendingMember A
        strategy hwin policy (closeMember, shared, pending)
    ∃ slot : ProfiledRawRightSlot A,
      installed.1.1 =
          profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
            hwin target ∧
        ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetAt A strategy
          hwin policy state target .right (.inl slot) := by
  dsimp only
  have hkey' :
      ProfiledRawJointHybridPhysicalCompatibleLeftSuccessorKeyAt A strategy
        hwin policy state
          (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A
            strategy hwin
            (profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadTarget A
              strategy hwin
              (profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfOutput
                A strategy hwin output entryRow) closeMember))
          (profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadTarget A
            strategy hwin
            (profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfOutput
              A strategy hwin output entryRow) closeMember).1 := by
    simpa using hkey
  obtain ⟨slot, htargetAt⟩ :=
    exists_profiledRawJointHybridPhysicalCompatibleSuccessorTargetAt_of_leftKeyAt
      A strategy hwin policy state
        (profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadTarget A
          strategy hwin
          (profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfOutput A
            strategy hwin output entryRow) closeMember)
        hkey'
  exact ⟨slot, rfl, htargetAt⟩

/-! ## Discharge from the actual decorated finite tables -/

/-- The arbitrary-row key theorem of a live decorated right table discharges
the generic pending-install premise.  `tableMember` is the member whose table
produced the output; `closeMember` is the later acknowledgement selecting only
the next receiver row `.first` or `.both`. -/
theorem
    exists_profiledRawJointHybridPhysicalCompatibleTargetAt_of_installLeftDecoratedOutput
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
    (tableMember : Bool) (word : List In₁)
    (monitorState :
      (profiledRawJointRightPhysicalSiblingMonitor A move.1
        tableMember).State)
    (input : In₂ × In₁) {ParentShared : Type c} (shared : ParentShared)
    (closeMember : Bool)
    (target_allowed :
      profiledRawJointRightPhysicalSiblingAllowed A move.1
        (((move.memberController A tableMember).labeledTree word).2
          monitorState input |>.target
            (profiledRawJointHybridPhysicalCompatiblePendingRow tableMember)))
    (slot : ProfiledRawLeftSlot A)
    (target_live :
      (((move.memberController A tableMember).labeledTree word).2
          monitorState input |>.target
            (profiledRawJointHybridPhysicalCompatiblePendingRow tableMember)
        ).family.left () = some slot) :
    let decorated :=
      profiledRawJointHybridPhysicalCompatibleDecoratedRightMemberController A
        strategy hwin policy state move tableMember
    let output := (decorated.labeledTree word).2 monitorState input
    let pending :=
      profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfOutput A
        strategy hwin output
          (profiledRawJointHybridPhysicalCompatiblePendingRow tableMember)
    let target :=
      profiledRawJointHybridPhysicalCompatibleRightPendingPayloadTarget A
        strategy hwin pending closeMember
    let installed :=
      profiledRawJointHybridPhysicalCompatibleInstallLeftPendingMember A
        strategy hwin policy (closeMember, shared, pending)
    ∃ selectedSlot : ProfiledRawLeftSlot A,
      installed.1.1 =
          profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
            hwin target ∧
        ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetAt A strategy
          hwin policy state target .left (.inr selectedSlot) := by
  dsimp only
  apply
    exists_profiledRawJointHybridPhysicalCompatibleTargetAt_of_installLeftPendingOutput
      A strategy hwin policy state shared _
        (profiledRawJointHybridPhysicalCompatiblePendingRow tableMember)
        closeMember
  exact
    profiledRawJointHybridPhysicalCompatibleDecoratedRightMemberController_key
      A strategy hwin policy state hreachable currentCode current_code
      currentRoot current_live move move_eq tableMember word monitorState input
      (profiledRawJointHybridPhysicalCompatiblePendingRow tableMember)
      target_allowed slot target_live

/-- Left-table mirror. -/
theorem
    exists_profiledRawJointHybridPhysicalCompatibleTargetAt_of_installRightDecoratedOutput
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
    (tableMember : Bool) (word : List In₂)
    (monitorState :
      (profiledRawJointLeftPhysicalSiblingMonitor A move.1 tableMember).State)
    (input : In₁ × In₂) {ParentShared : Type c} (shared : ParentShared)
    (closeMember : Bool)
    (target_allowed :
      profiledRawJointLeftPhysicalSiblingAllowed A move.1
        (((move.memberController A tableMember).labeledTree word).2
          monitorState input |>.target
            (profiledRawJointHybridPhysicalCompatiblePendingRow tableMember)))
    (slot : ProfiledRawRightSlot A)
    (target_live :
      (((move.memberController A tableMember).labeledTree word).2
          monitorState input |>.target
            (profiledRawJointHybridPhysicalCompatiblePendingRow tableMember)
        ).family.right () = some slot) :
    let decorated :=
      profiledRawJointHybridPhysicalCompatibleDecoratedLeftMemberController A
        strategy hwin policy state move tableMember
    let output := (decorated.labeledTree word).2 monitorState input
    let pending :=
      profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfOutput A
        strategy hwin output
          (profiledRawJointHybridPhysicalCompatiblePendingRow tableMember)
    let target :=
      profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadTarget A
        strategy hwin pending closeMember
    let installed :=
      profiledRawJointHybridPhysicalCompatibleInstallRightPendingMember A
        strategy hwin policy (closeMember, shared, pending)
    ∃ selectedSlot : ProfiledRawRightSlot A,
      installed.1.1 =
          profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
            hwin target ∧
        ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetAt A strategy
          hwin policy state target .right (.inl selectedSlot) := by
  dsimp only
  apply
    exists_profiledRawJointHybridPhysicalCompatibleTargetAt_of_installRightPendingOutput
      A strategy hwin policy state shared _
        (profiledRawJointHybridPhysicalCompatiblePendingRow tableMember)
        closeMember
  exact
    profiledRawJointHybridPhysicalCompatibleDecoratedLeftMemberController_key
      A strategy hwin policy state hreachable currentCode current_code
      currentRoot current_live move move_eq tableMember word monitorState input
      (profiledRawJointHybridPhysicalCompatiblePendingRow tableMember)
      target_allowed slot target_live

end

end DetParityAutomaton

end DistributedSynthesis
