/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatiblePendingMemberTransition

/-!
# Physical cut packets for the two-row compatible successor frontier

The operational close retains the two exact target cells of one row-exact
receiver output in a common pending payload.  The acknowledged member selects
`.first` in the open/strict case and `.both` in the closed/simultaneous case.

This file connects that finite frontier to the literal DPA cut equations.  It
projects the decorated finite-controller play to the old checked physical
monitor, obtains its winning proof from the controller's universal guarantee,
and applies the member-indexed cut packet.  The member is proof-side carried
data; no executable map tests the graph or learns a strict leader.
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

/-! ## The two row conventions coincide -/

/-- The operational pending payload and the physical cut packet use the same
false/true row convention. -/
@[simp] theorem
    profiledRawJointHybridPhysicalCompatiblePendingRow_eq_closeRowOfMember
    (member : Bool) :
    profiledRawJointHybridPhysicalCompatiblePendingRow member =
      profiledRawJointCloseRowOfMember member := by
  cases member <;> rfl

/-! ## Exact decorated plays and their physical projections -/

/-- The row-exact play of one installed right finite table. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleRightDecoratedPlay
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointRightPhysicalSiblingMove A) (member : Bool)
    (env : Nat → In₂ × In₁) :=
  let monitor :=
    profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A strategy
      hwin (initial := initial) move member
  let controller :=
    profiledRawJointHybridPhysicalCompatibleDecoratedRightMemberController A
      strategy hwin policy state move member
  treePlay (narrowedInducedTree monitor controller.labeledTree) env

/-- Forget successor-key and row proofs, retaining the exact old physical
table play. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointRightPhysicalSiblingMove A) (member : Bool)
    (env : Nat → In₂ × In₁) :=
  BlockRecordMonitor.projectReceiverPlay
    (profiledRawJointHybridPhysicalCompatibleSuccessorRightReceiverProjection
      A strategy hwin)
    (profiledRawJointHybridPhysicalCompatibleRightDecoratedPlay A strategy hwin
      policy state move member env)

/-- The projected right play wins the original target monitor. -/
theorem
    profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay_wins
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointRightPhysicalSiblingMove A) (member : Bool)
    (env : Nat → In₂ × In₁) :
    (profiledRawJointRightPhysicalSiblingMonitor A move.1 member).WinsPlay
      (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A strategy
        hwin policy state move member env) := by
  let monitor :=
    profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A strategy
      hwin (initial := initial) move member
  let controller :=
    profiledRawJointHybridPhysicalCompatibleDecoratedRightMemberController A
      strategy hwin policy state move member
  let play := treePlay
    (narrowedInducedTree monitor controller.labeledTree) env
  have htree : monitor.lift.WinningTree
      (narrowedInducedTree monitor controller.labeledTree) :=
    narrowedInducedTree_winningTree_of_allThreadsWin monitor
      (profiledRawJointHybridPhysicalCompatibleDecoratedRightMemberController_wins
        A strategy hwin policy state move member)
  have hplay : monitor.WinsPlay play :=
    (monitor.lift_winningTree_iff
      (narrowedInducedTree monitor controller.labeledTree)).mp htree env
  exact (BlockRecordMonitor.comapReceiverOutput_wins_iff
    (profiledRawJointRightPhysicalSiblingMonitor A move.1 member)
    (profiledRawJointHybridPhysicalCompatibleSuccessorRightReceiverProjection
      A strategy hwin) play).mp hplay

/-! ## Three-parameter right cut -/

/-- Exact right-table physical packet with all three finite choices exposed.

`tableMember` selects the already installed finite controller.  `entryRow`
is the row carried by its receiver and selects the target cell of the current
output.  `closeMember` is the newly delivered acknowledgement and selects
only the closing record and the next entry row.  In particular no equality
between the old and new members is assumed. -/
theorem
    profiledRawJointHybridPhysicalCompatibleRight_memberCutPacket
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (tableMember : Bool) (entryRow : PairedEntryRow) (closeMember : Bool)
    (env : Nat → In₂ × In₁) (n : Nat) (slot : ProfiledRawLeftSlot A)
    (htarget :
      profiledRawJointHybridPhysicalCompatibleSuccessorRightTargetProjection A
          strategy hwin
          ((profiledRawJointHybridPhysicalCompatibleRightDecoratedPlay A
            strategy hwin policy state move tableMember env n).2.1.target
              entryRow).1 =
        .inr (.inr slot))
    (physicalState : A.State)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (cuts : Nat → Nat) (k : Nat)
    (hcut : cuts k < cuts (k + 1))
    (hstate : A.runFrom physicalState word (cuts k) =
      pairedCodeStateForRow A entryRow move.1.source.1.1)
    (hlength :
      (profiledRawJointTargetRightPhysicalPrefixRecords A entryRow
          (omegaPrefix
            (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A
              strategy hwin policy state move tableMember env) n)).length =
        cuts (k + 1) - cuts k - 1)
    (hslice : omegaPrefix (OmegaWord.drop word (cuts k))
        (profiledRawJointTargetRightPhysicalPrefixRecords A entryRow
          (omegaPrefix
            (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A
              strategy hwin policy state move tableMember env) n)).length =
      profiledRawJointTargetRightPhysicalPrefixRecords A entryRow
        (omegaPrefix
          (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A strategy
            hwin policy state move tableMember env) n))
    (hclosing : OmegaWord.drop word (cuts k)
        (profiledRawJointTargetRightPhysicalPrefixRecords A entryRow
          (omegaPrefix
            (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A
              strategy hwin policy state move tableMember env) n)).length =
      profiledRawJointTargetRightClosingRecordForMember closeMember entryRow
        (profiledRawJointTargetRightPhysicalLetter A
          (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A strategy
            hwin policy state move tableMember env n))) :
    cutBlockMin
        (fun j ↦ A.priority (A.runFrom physicalState word j)) cuts k =
        profiledRawJointThreadRootPriority A (.inr slot) ∧
      A.runFrom physicalState word (cuts (k + 1)) =
        pairedCodeStateForRow A
          (profiledRawJointCloseRowOfMember closeMember) slot.1.1 := by
  let decoratedPlay :=
    profiledRawJointHybridPhysicalCompatibleRightDecoratedPlay A strategy hwin
      policy state move tableMember env
  let play :=
    profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A strategy hwin
      policy state move tableMember env
  have hwins :=
    profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay_wins A strategy
      hwin policy state move tableMember env
  have htarget' :
      profiledRawJointUnitRightTargetProjection A
          ((play n).2.1.target entryRow) = .inr (.inr slot) := by
    simpa [play, decoratedPlay,
      profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay,
      profiledRawJointHybridPhysicalCompatibleRightDecoratedPlay,
      BlockRecordMonitor.projectReceiverPlay,
      profiledRawJointHybridPhysicalCompatibleSuccessorRightReceiverProjection,
      profiledRawJointHybridPhysicalCompatibleSuccessorRightTargetProjection]
      using htarget
  exact
    profiledRawJointTargetRight_memberCutPacket_of_wins A
      (profiledRawJointUnitRightTargetProjection A)
      (profiledRawJointRightPhysicalSiblingAllowed A move.1)
      move.1.source play hwins n entryRow slot htarget' closeMember
      physicalState word cuts k hcut hstate hlength hslice hclosing

/-! ## Installed right boundary packet -/

/-- One resolved right boundary in the exact form needed by a recurrent
carrier audit.  It combines the acknowledged installation theorem with the
literal physical cut theorem above.

The installed table member, current entry row, and fresh closing member are
independent parameters.  Consequently this statement covers every alternating
pair; none of the three is observable by an endpoint. -/
theorem
    profiledRawJointHybridPhysicalCompatibleRight_memberTransitionCutPacket
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    {ParentShared : Type c} (shared : ParentShared)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (tableMember : Bool) (entryRow : PairedEntryRow) (closeMember : Bool)
    (env : Nat → In₂ × In₁) (n : Nat)
    (hkey :
      let output :=
        (profiledRawJointHybridPhysicalCompatibleRightDecoratedPlay A strategy
          hwin policy state move tableMember env n).2.1
      let target := (output.target entryRow).1
      ProfiledRawJointHybridPhysicalCompatibleRightSuccessorKeyAt A strategy
        hwin policy state
          (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A
            strategy hwin target)
          target.1)
    (physicalState : A.State)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (cuts : Nat → Nat) (k : Nat)
    (hcut : cuts k < cuts (k + 1))
    (hstate : A.runFrom physicalState word (cuts k) =
      pairedCodeStateForRow A entryRow move.1.source.1.1)
    (hlength :
      (profiledRawJointTargetRightPhysicalPrefixRecords A entryRow
          (omegaPrefix
            (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A
              strategy hwin policy state move tableMember env) n)).length =
        cuts (k + 1) - cuts k - 1)
    (hslice : omegaPrefix (OmegaWord.drop word (cuts k))
        (profiledRawJointTargetRightPhysicalPrefixRecords A entryRow
          (omegaPrefix
            (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A
              strategy hwin policy state move tableMember env) n)).length =
      profiledRawJointTargetRightPhysicalPrefixRecords A entryRow
        (omegaPrefix
          (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A strategy
            hwin policy state move tableMember env) n))
    (hclosing : OmegaWord.drop word (cuts k)
        (profiledRawJointTargetRightPhysicalPrefixRecords A entryRow
          (omegaPrefix
            (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A
              strategy hwin policy state move tableMember env) n)).length =
      profiledRawJointTargetRightClosingRecordForMember closeMember entryRow
        (profiledRawJointTargetRightPhysicalLetter A
          (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A strategy
            hwin policy state move tableMember env n))) :
    let output :=
      (profiledRawJointHybridPhysicalCompatibleRightDecoratedPlay A strategy
        hwin policy state move tableMember env n).2.1
    let pending :=
      profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfOutput A
        strategy hwin output entryRow
    let target :=
      profiledRawJointHybridPhysicalCompatibleRightPendingPayloadTarget A
        strategy hwin pending closeMember
    let installed :=
      profiledRawJointHybridPhysicalCompatibleInstallLeftPendingMember.{u, v,
        x, y, s, c, max u v x y s} A strategy hwin policy
          (closeMember, shared, pending)
    ∃ slot : ProfiledRawLeftSlot A,
      installed.1.1 =
          profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
            hwin target ∧
        ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetAt A strategy
          hwin policy state target .left (.inr slot) ∧
        cutBlockMin
            (fun j ↦ A.priority (A.runFrom physicalState word j)) cuts k =
          profiledRawJointThreadRootPriority A (.inr slot) ∧
        A.runFrom physicalState word (cuts (k + 1)) =
          pairedCodeStateForRow A
            (profiledRawJointCloseRowOfMember closeMember) slot.1.1 := by
  dsimp only at hkey ⊢
  let output :=
    (profiledRawJointHybridPhysicalCompatibleRightDecoratedPlay A strategy hwin
      policy state move tableMember env n).2.1
  obtain ⟨slot, hinstalled, htargetAt⟩ :=
    exists_profiledRawJointHybridPhysicalCompatibleTargetAt_of_installLeftPendingOutput.{
      u, v, x, y, s, c, max u v x y s}
      A strategy hwin policy state shared output entryRow closeMember (by
        simpa [output] using hkey)
  have htarget :=
    ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetRootAt.right_projection_eq
      A strategy hwin htargetAt.root_at
  have hphysical :=
    profiledRawJointHybridPhysicalCompatibleRight_memberCutPacket A strategy
      hwin policy state move tableMember entryRow closeMember env n slot (by
        simpa [output] using htarget) physicalState word cuts k hcut hstate
          hlength hslice hclosing
  exact ⟨slot, hinstalled, htargetAt, hphysical.1, hphysical.2⟩

/-! ## Left mirror -/

/-- The row-exact play of one installed left finite table. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleLeftDecoratedPlay
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A) (member : Bool)
    (env : Nat → In₁ × In₂) :=
  let monitor :=
    profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A strategy
      hwin (initial := initial) move member
  let controller :=
    profiledRawJointHybridPhysicalCompatibleDecoratedLeftMemberController A
      strategy hwin policy state move member
  treePlay (narrowedInducedTree monitor controller.labeledTree) env

/-- Left physical projection. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A) (member : Bool)
    (env : Nat → In₁ × In₂) :=
  BlockRecordMonitor.projectReceiverPlay
    (profiledRawJointHybridPhysicalCompatibleSuccessorLeftReceiverProjection
      A strategy hwin)
    (profiledRawJointHybridPhysicalCompatibleLeftDecoratedPlay A strategy hwin
      policy state move member env)

/-- The projected left play wins its original target monitor. -/
theorem
    profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay_wins
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A) (member : Bool)
    (env : Nat → In₁ × In₂) :
    (profiledRawJointLeftPhysicalSiblingMonitor A move.1 member).WinsPlay
      (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A strategy
        hwin policy state move member env) := by
  let monitor :=
    profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A strategy
      hwin (initial := initial) move member
  let controller :=
    profiledRawJointHybridPhysicalCompatibleDecoratedLeftMemberController A
      strategy hwin policy state move member
  let play := treePlay
    (narrowedInducedTree monitor controller.labeledTree) env
  have htree : monitor.lift.WinningTree
      (narrowedInducedTree monitor controller.labeledTree) :=
    narrowedInducedTree_winningTree_of_allThreadsWin monitor
      (profiledRawJointHybridPhysicalCompatibleDecoratedLeftMemberController_wins
        A strategy hwin policy state move member)
  have hplay : monitor.WinsPlay play :=
    (monitor.lift_winningTree_iff
      (narrowedInducedTree monitor controller.labeledTree)).mp htree env
  exact (BlockRecordMonitor.comapReceiverOutput_wins_iff
    (profiledRawJointLeftPhysicalSiblingMonitor A move.1 member)
    (profiledRawJointHybridPhysicalCompatibleSuccessorLeftReceiverProjection
      A strategy hwin) play).mp hplay

/-- Left mirror of the three-parameter packet.  The installed table member,
current entry row, and new closing member remain independent. -/
theorem
    profiledRawJointHybridPhysicalCompatibleLeft_memberCutPacket
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (tableMember : Bool) (entryRow : PairedEntryRow) (closeMember : Bool)
    (env : Nat → In₁ × In₂) (n : Nat) (slot : ProfiledRawRightSlot A)
    (htarget :
      profiledRawJointHybridPhysicalCompatibleSuccessorLeftTargetProjection A
          strategy hwin
          ((profiledRawJointHybridPhysicalCompatibleLeftDecoratedPlay A
            strategy hwin policy state move tableMember env n).2.1.target
              entryRow).1 =
        .inr (.inl slot))
    (physicalState : A.State)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (cuts : Nat → Nat) (k : Nat)
    (hcut : cuts k < cuts (k + 1))
    (hstate : A.runFrom physicalState word (cuts k) =
      pairedCodeStateForRow A entryRow move.1.source.1.1)
    (hlength :
      (profiledRawJointTargetLeftPhysicalPrefixRecords A entryRow
          (omegaPrefix
            (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A
              strategy hwin policy state move tableMember env) n)).length =
        cuts (k + 1) - cuts k - 1)
    (hslice : omegaPrefix (OmegaWord.drop word (cuts k))
        (profiledRawJointTargetLeftPhysicalPrefixRecords A entryRow
          (omegaPrefix
            (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A
              strategy hwin policy state move tableMember env) n)).length =
      profiledRawJointTargetLeftPhysicalPrefixRecords A entryRow
        (omegaPrefix
          (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A strategy
            hwin policy state move tableMember env) n))
    (hclosing : OmegaWord.drop word (cuts k)
        (profiledRawJointTargetLeftPhysicalPrefixRecords A entryRow
          (omegaPrefix
            (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A
              strategy hwin policy state move tableMember env) n)).length =
      profiledRawJointTargetLeftClosingRecordForMember closeMember entryRow
        (profiledRawJointTargetLeftPhysicalLetter A
          (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A strategy
            hwin policy state move tableMember env n))) :
    cutBlockMin
        (fun j ↦ A.priority (A.runFrom physicalState word j)) cuts k =
        profiledRawJointThreadRootPriority A (.inl slot) ∧
      A.runFrom physicalState word (cuts (k + 1)) =
        pairedCodeStateForRow A
          (profiledRawJointCloseRowOfMember closeMember) slot.1.1 := by
  let decoratedPlay :=
    profiledRawJointHybridPhysicalCompatibleLeftDecoratedPlay A strategy hwin
      policy state move tableMember env
  let play :=
    profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A strategy hwin
      policy state move tableMember env
  have hwins :=
    profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay_wins A strategy
      hwin policy state move tableMember env
  have htarget' :
      profiledRawJointUnitLeftTargetProjection A
          ((play n).2.1.target entryRow) =
        .inr (.inl slot) := by
    simpa [play, decoratedPlay,
      profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay,
      profiledRawJointHybridPhysicalCompatibleLeftDecoratedPlay,
      BlockRecordMonitor.projectReceiverPlay,
      profiledRawJointHybridPhysicalCompatibleSuccessorLeftReceiverProjection,
      profiledRawJointHybridPhysicalCompatibleSuccessorLeftTargetProjection]
      using htarget
  exact profiledRawJointTargetLeft_memberCutPacket_of_wins A
      (profiledRawJointUnitLeftTargetProjection A)
      (profiledRawJointLeftPhysicalSiblingAllowed A move.1)
      move.1.source play hwins n entryRow slot htarget' closeMember
      physicalState word cuts k hcut hstate hlength hslice hclosing

/-! ## Installed left boundary packet -/

/-- Left mirror of the complete resolved-boundary packet. -/
theorem
    profiledRawJointHybridPhysicalCompatibleLeft_memberTransitionCutPacket
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    {ParentShared : Type c} (shared : ParentShared)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (tableMember : Bool) (entryRow : PairedEntryRow) (closeMember : Bool)
    (env : Nat → In₁ × In₂) (n : Nat)
    (hkey :
      let output :=
        (profiledRawJointHybridPhysicalCompatibleLeftDecoratedPlay A strategy
          hwin policy state move tableMember env n).2.1
      let target := (output.target entryRow).1
      ProfiledRawJointHybridPhysicalCompatibleLeftSuccessorKeyAt A strategy
        hwin policy state
          (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A
            strategy hwin target)
          target.1)
    (physicalState : A.State)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (cuts : Nat → Nat) (k : Nat)
    (hcut : cuts k < cuts (k + 1))
    (hstate : A.runFrom physicalState word (cuts k) =
      pairedCodeStateForRow A entryRow move.1.source.1.1)
    (hlength :
      (profiledRawJointTargetLeftPhysicalPrefixRecords A entryRow
          (omegaPrefix
            (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A
              strategy hwin policy state move tableMember env) n)).length =
        cuts (k + 1) - cuts k - 1)
    (hslice : omegaPrefix (OmegaWord.drop word (cuts k))
        (profiledRawJointTargetLeftPhysicalPrefixRecords A entryRow
          (omegaPrefix
            (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A
              strategy hwin policy state move tableMember env) n)).length =
      profiledRawJointTargetLeftPhysicalPrefixRecords A entryRow
        (omegaPrefix
          (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A strategy
            hwin policy state move tableMember env) n))
    (hclosing : OmegaWord.drop word (cuts k)
        (profiledRawJointTargetLeftPhysicalPrefixRecords A entryRow
          (omegaPrefix
            (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A
              strategy hwin policy state move tableMember env) n)).length =
      profiledRawJointTargetLeftClosingRecordForMember closeMember entryRow
        (profiledRawJointTargetLeftPhysicalLetter A
          (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A strategy
            hwin policy state move tableMember env n))) :
    let output :=
      (profiledRawJointHybridPhysicalCompatibleLeftDecoratedPlay A strategy
        hwin policy state move tableMember env n).2.1
    let pending :=
      profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfOutput A
        strategy hwin output entryRow
    let target :=
      profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadTarget A
        strategy hwin pending closeMember
    let installed :=
      profiledRawJointHybridPhysicalCompatibleInstallRightPendingMember.{u, v,
        x, y, s, c, max u v x y s} A strategy hwin policy
          (closeMember, shared, pending)
    ∃ slot : ProfiledRawRightSlot A,
      installed.1.1 =
          profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
            hwin target ∧
        ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetAt A strategy
          hwin policy state target .right (.inl slot) ∧
        cutBlockMin
            (fun j ↦ A.priority (A.runFrom physicalState word j)) cuts k =
          profiledRawJointThreadRootPriority A (.inl slot) ∧
        A.runFrom physicalState word (cuts (k + 1)) =
          pairedCodeStateForRow A
            (profiledRawJointCloseRowOfMember closeMember) slot.1.1 := by
  dsimp only at hkey ⊢
  let output :=
    (profiledRawJointHybridPhysicalCompatibleLeftDecoratedPlay A strategy hwin
      policy state move tableMember env n).2.1
  obtain ⟨slot, hinstalled, htargetAt⟩ :=
    exists_profiledRawJointHybridPhysicalCompatibleTargetAt_of_installRightPendingOutput.{
      u, v, x, y, s, c, max u v x y s}
      A strategy hwin policy state shared output entryRow closeMember (by
        simpa [output] using hkey)
  have htarget :=
    ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetRootAt.left_projection_eq
      A strategy hwin htargetAt.root_at
  have hphysical :=
    profiledRawJointHybridPhysicalCompatibleLeft_memberCutPacket A strategy hwin
      policy state move tableMember entryRow closeMember env n slot (by
        simpa [output] using htarget) physicalState word cuts k hcut hstate
          hlength hslice hclosing
  exact ⟨slot, hinstalled, htargetAt, hphysical.1, hphysical.2⟩

end

end DetParityAutomaton

end DistributedSynthesis
