/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyBankLocalBoundary
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatiblePolicyBankLocalPhaseLive

/-!
# Finite-memory informed reversal bridges

At a strict receive, the informed endpoint advances its installed receiver,
resolves the target in the selected finite-memory bank, and stages the exact
resulting packet.  The simultaneous branch installs the opposite owner at the
packet successor.  One further blind step starts that same owner in the staged
branch, so the two candidates have equal output and coalesce literally.

The old bank coordinate and the packet-successor coordinate may contain
different policy memories.  They are retained in different bridge fields;
none of the proofs below identifies them.
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

private abbrev Packet :=
  ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankResolvedTarget
    (Memory := Memory) A strategy

/-! ## Right-to-left bridge on process two -/

abbrev ProfiledRawJointRecurrentFiniteMemoryRightToLeftStagedReceiver :=
  BankControl (Memory := Memory) A strategy ×
    ProfiledRawJointRightPhysicalSiblingReceiver A ×
      Option (Packet (Memory := Memory) A strategy)

/-- Installed left-owner mode.  It retains the augmented successor and the
right receiver which becomes dormant at the reversal. -/
abbrev ProfiledRawJointRecurrentFiniteMemoryRightToLeftInstalledOwner :=
  BankControl (Memory := Memory) A strategy ×
    ProfiledRawJointLeftPhysicalSiblingExceptional A ×
      ProfiledRawJointRightPhysicalSiblingReceiver A

abbrev ProfiledRawJointRecurrentFiniteMemoryRightToLeftBridgeControl :=
  ProfiledRawJointRecurrentFiniteMemoryRightToLeftStagedReceiver
      (Memory := Memory) A strategy ⊕
    ProfiledRawJointRecurrentFiniteMemoryRightToLeftInstalledOwner
      (Memory := Memory) A strategy

noncomputable instance :
    Fintype
      (ProfiledRawJointRecurrentFiniteMemoryRightToLeftStagedReceiver
        (Memory := Memory) A strategy) := by
  classical
  infer_instance

noncomputable instance :
    Fintype
      (ProfiledRawJointRecurrentFiniteMemoryRightToLeftInstalledOwner
        (Memory := Memory) A strategy) := by
  classical
  infer_instance

noncomputable instance :
    Fintype
      (ProfiledRawJointRecurrentFiniteMemoryRightToLeftBridgeControl
        (Memory := Memory) A strategy) := by
  classical
  infer_instance

def profiledRawJointRecurrentFiniteMemoryRightToLeftStagePacket
    (state : BankControl (Memory := Memory) A strategy)
    (receiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (packet : Packet (Memory := Memory) A strategy) :
    ProfiledRawJointRecurrentFiniteMemoryRightToLeftStagedReceiver
      (Memory := Memory) A strategy :=
  (state, receiver, some packet)

/-- Total no-receive step.  The missing-packet and missing-lane cases only
totalize malformed bridge states. -/
noncomputable def
    profiledRawJointRecurrentFiniteMemoryRightToLeftBridgeNoRecv
    (control :
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftBridgeControl
        (Memory := Memory) A strategy)
    (input : In₂) :
    ProfiledRawJointRecurrentFiniteMemoryRightToLeftBridgeControl
        (Memory := Memory) A strategy × Out₂ :=
  match control with
  | .inl staged =>
      match staged.2.2 with
      | none => (.inl staged, default)
      | some packet =>
          match packet.successor.2.1.1.2.2 with
          | none => (.inl staged, default)
          | some move =>
              let next := profiledRawJointLeftPhysicalSiblingMemberNoRecvStep
                A move false (move.memberController A false).initial input
              (.inr
                (packet.successor, ⟨move, next.2⟩, staged.2.1), next.1)
  | .inr installed =>
      let owner := installed.2.1
      let next := profiledRawJointLeftPhysicalSiblingMemberNoRecvStep A
        owner.1 false owner.2 input
      (.inr (installed.1, ⟨owner.1, next.2⟩, installed.2.2), next.1)

/-- The precise open/closed relation created by a right-to-left receive. -/
inductive ProfiledRawJointRecurrentFiniteMemoryRightToLeftBridgeBlind :
    ProfiledRawJointRecurrentFiniteMemoryRightToLeftBridgeControl
        (Memory := Memory) A strategy →
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftBridgeControl
        (Memory := Memory) A strategy → Prop
  | staged
      (state : BankControl (Memory := Memory) A strategy)
      (receiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
      (packet : Packet (Memory := Memory) A strategy)
      (move : ProfiledRawJointLeftPhysicalSiblingMove A)
      (hmove : packet.successor.2.1.1.2.2 = some move) :
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftBridgeBlind
        (.inl
          (profiledRawJointRecurrentFiniteMemoryRightToLeftStagePacket
            (Memory := Memory) A strategy state receiver packet))
        (.inr
          (packet.successor,
            ⟨move, (move.memberController A false).initial⟩, receiver))
  | recurrent
      (installed :
        ProfiledRawJointRecurrentFiniteMemoryRightToLeftInstalledOwner
          (Memory := Memory) A strategy) :
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftBridgeBlind
        (.inr installed) (.inr installed)

omit [Inhabited Out₁] [Fintype Memory] in
theorem profiledRawJointRecurrentFiniteMemoryRightToLeftBridgeBlind_noRecv
    (left right :
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftBridgeControl
        (Memory := Memory) A strategy)
    (input : In₂)
    (hblind :
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftBridgeBlind
        (Memory := Memory) A strategy left right) :
    (profiledRawJointRecurrentFiniteMemoryRightToLeftBridgeNoRecv
        (Memory := Memory) A strategy left input).2 =
        (profiledRawJointRecurrentFiniteMemoryRightToLeftBridgeNoRecv
          (Memory := Memory) A strategy right input).2 ∧
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftBridgeBlind
        (Memory := Memory) A strategy
        (profiledRawJointRecurrentFiniteMemoryRightToLeftBridgeNoRecv
          (Memory := Memory) A strategy left input).1
        (profiledRawJointRecurrentFiniteMemoryRightToLeftBridgeNoRecv
          (Memory := Memory) A strategy right input).1 := by
  cases hblind with
  | staged state receiver packet move hmove =>
      simp only [
        profiledRawJointRecurrentFiniteMemoryRightToLeftBridgeNoRecv,
        profiledRawJointRecurrentFiniteMemoryRightToLeftStagePacket, hmove]
      exact ⟨trivial, .recurrent _⟩
  | recurrent installed =>
      exact ⟨rfl, .recurrent _⟩

/-- A delivered staged branch selects the old receiver; an installed branch
creates the fresh receiver belonging to its new owner. -/
noncomputable def
    profiledRawJointRecurrentFiniteMemoryRightToLeftDeliveredReceiver
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (delivered :
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftBridgeControl
        (Memory := Memory) A strategy) :
    ProfiledRawJointLeftPhysicalSiblingReceiver A :=
  match delivered with
  | .inl _ => oldReceiver
  | .inr installed =>
      initialProfiledRawJointLeftPhysicalSiblingReceiver A
        installed.2.1.1 .both

/-- Augmented bank coordinate currently exposed by a process-two bridge. -/
def profiledRawJointRecurrentFiniteMemoryRightToLeftBridgeState
    (control :
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftBridgeControl
        (Memory := Memory) A strategy) :
    BankControl (Memory := Memory) A strategy :=
  match control with
  | .inl staged => staged.1
  | .inr installed => installed.1

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype Memory] in
@[simp] theorem
    profiledRawJointRecurrentFiniteMemoryRightToLeftDeliveredReceiver_open
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (staged :
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftStagedReceiver
        (Memory := Memory) A strategy) :
    profiledRawJointRecurrentFiniteMemoryRightToLeftDeliveredReceiver
      (Memory := Memory) A strategy oldReceiver (.inl staged) = oldReceiver :=
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype Memory] in
@[simp] theorem
    profiledRawJointRecurrentFiniteMemoryRightToLeftDeliveredReceiver_closed
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (installed :
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftInstalledOwner
        (Memory := Memory) A strategy) :
    profiledRawJointRecurrentFiniteMemoryRightToLeftDeliveredReceiver
        (Memory := Memory) A strategy oldReceiver (.inr installed) =
      initialProfiledRawJointLeftPhysicalSiblingReceiver A
        installed.2.1.1 .both :=
  rfl

omit [Inhabited Out₁] [Fintype Memory] in
theorem
    profiledRawJointRecurrentFiniteMemoryRightToLeftDeliveredReceiver_eq_after_noRecv
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (left right :
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftBridgeControl
        (Memory := Memory) A strategy)
    (input : In₂)
    (hblind :
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftBridgeBlind
        (Memory := Memory) A strategy left right) :
    profiledRawJointRecurrentFiniteMemoryRightToLeftDeliveredReceiver
        (Memory := Memory) A strategy oldReceiver
        (profiledRawJointRecurrentFiniteMemoryRightToLeftBridgeNoRecv
          (Memory := Memory) A strategy left input).1 =
      profiledRawJointRecurrentFiniteMemoryRightToLeftDeliveredReceiver
        (Memory := Memory) A strategy oldReceiver
        (profiledRawJointRecurrentFiniteMemoryRightToLeftBridgeNoRecv
          (Memory := Memory) A strategy right input).1 := by
  cases hblind with
  | staged state receiver packet move hmove =>
      simp [profiledRawJointRecurrentFiniteMemoryRightToLeftBridgeNoRecv,
        profiledRawJointRecurrentFiniteMemoryRightToLeftStagePacket, hmove]
  | recurrent installed => rfl

/-! ## Left-to-right bridge on process one -/

abbrev ProfiledRawJointRecurrentFiniteMemoryLeftToRightStagedReceiver :=
  BankControl (Memory := Memory) A strategy ×
    ProfiledRawJointLeftPhysicalSiblingReceiver A ×
      Option (Packet (Memory := Memory) A strategy)

abbrev ProfiledRawJointRecurrentFiniteMemoryLeftToRightInstalledOwner :=
  BankControl (Memory := Memory) A strategy ×
    ProfiledRawJointRightPhysicalSiblingExceptional A ×
      ProfiledRawJointLeftPhysicalSiblingReceiver A

abbrev ProfiledRawJointRecurrentFiniteMemoryLeftToRightBridgeControl :=
  ProfiledRawJointRecurrentFiniteMemoryLeftToRightStagedReceiver
      (Memory := Memory) A strategy ⊕
    ProfiledRawJointRecurrentFiniteMemoryLeftToRightInstalledOwner
      (Memory := Memory) A strategy

noncomputable instance :
    Fintype
      (ProfiledRawJointRecurrentFiniteMemoryLeftToRightStagedReceiver
        (Memory := Memory) A strategy) := by
  classical
  infer_instance

noncomputable instance :
    Fintype
      (ProfiledRawJointRecurrentFiniteMemoryLeftToRightInstalledOwner
        (Memory := Memory) A strategy) := by
  classical
  infer_instance

noncomputable instance :
    Fintype
      (ProfiledRawJointRecurrentFiniteMemoryLeftToRightBridgeControl
        (Memory := Memory) A strategy) := by
  classical
  infer_instance

def profiledRawJointRecurrentFiniteMemoryLeftToRightStagePacket
    (state : BankControl (Memory := Memory) A strategy)
    (receiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (packet : Packet (Memory := Memory) A strategy) :
    ProfiledRawJointRecurrentFiniteMemoryLeftToRightStagedReceiver
      (Memory := Memory) A strategy :=
  (state, receiver, some packet)

noncomputable def
    profiledRawJointRecurrentFiniteMemoryLeftToRightBridgeNoRecv
    (control :
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightBridgeControl
        (Memory := Memory) A strategy)
    (input : In₁) :
    ProfiledRawJointRecurrentFiniteMemoryLeftToRightBridgeControl
        (Memory := Memory) A strategy × Out₁ :=
  match control with
  | .inl staged =>
      match staged.2.2 with
      | none => (.inl staged, default)
      | some packet =>
          match packet.successor.2.1.1.2.1 with
          | none => (.inl staged, default)
          | some move =>
              let next := profiledRawJointRightPhysicalSiblingMemberNoRecvStep
                A move false (move.memberController A false).initial input
              (.inr
                (packet.successor, ⟨move, next.2⟩, staged.2.1), next.1)
  | .inr installed =>
      let owner := installed.2.1
      let next := profiledRawJointRightPhysicalSiblingMemberNoRecvStep A
        owner.1 false owner.2 input
      (.inr (installed.1, ⟨owner.1, next.2⟩, installed.2.2), next.1)

inductive ProfiledRawJointRecurrentFiniteMemoryLeftToRightBridgeBlind :
    ProfiledRawJointRecurrentFiniteMemoryLeftToRightBridgeControl
        (Memory := Memory) A strategy →
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightBridgeControl
        (Memory := Memory) A strategy → Prop
  | staged
      (state : BankControl (Memory := Memory) A strategy)
      (receiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
      (packet : Packet (Memory := Memory) A strategy)
      (move : ProfiledRawJointRightPhysicalSiblingMove A)
      (hmove : packet.successor.2.1.1.2.1 = some move) :
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightBridgeBlind
        (.inl
          (profiledRawJointRecurrentFiniteMemoryLeftToRightStagePacket
            (Memory := Memory) A strategy state receiver packet))
        (.inr
          (packet.successor,
            ⟨move, (move.memberController A false).initial⟩, receiver))
  | recurrent
      (installed :
        ProfiledRawJointRecurrentFiniteMemoryLeftToRightInstalledOwner
          (Memory := Memory) A strategy) :
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightBridgeBlind
        (.inr installed) (.inr installed)

omit [Inhabited Out₂] [Fintype Memory] in
theorem profiledRawJointRecurrentFiniteMemoryLeftToRightBridgeBlind_noRecv
    (left right :
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightBridgeControl
        (Memory := Memory) A strategy)
    (input : In₁)
    (hblind :
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightBridgeBlind
        (Memory := Memory) A strategy left right) :
    (profiledRawJointRecurrentFiniteMemoryLeftToRightBridgeNoRecv
        (Memory := Memory) A strategy left input).2 =
        (profiledRawJointRecurrentFiniteMemoryLeftToRightBridgeNoRecv
          (Memory := Memory) A strategy right input).2 ∧
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightBridgeBlind
        (Memory := Memory) A strategy
        (profiledRawJointRecurrentFiniteMemoryLeftToRightBridgeNoRecv
          (Memory := Memory) A strategy left input).1
        (profiledRawJointRecurrentFiniteMemoryLeftToRightBridgeNoRecv
          (Memory := Memory) A strategy right input).1 := by
  cases hblind with
  | staged state receiver packet move hmove =>
      simp only [
        profiledRawJointRecurrentFiniteMemoryLeftToRightBridgeNoRecv,
        profiledRawJointRecurrentFiniteMemoryLeftToRightStagePacket, hmove]
      exact ⟨trivial, .recurrent _⟩
  | recurrent installed =>
      exact ⟨rfl, .recurrent _⟩

noncomputable def
    profiledRawJointRecurrentFiniteMemoryLeftToRightDeliveredReceiver
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (delivered :
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightBridgeControl
        (Memory := Memory) A strategy) :
    ProfiledRawJointRightPhysicalSiblingReceiver A :=
  match delivered with
  | .inl _ => oldReceiver
  | .inr installed =>
      initialProfiledRawJointRightPhysicalSiblingReceiver A
        installed.2.1.1 .both

/-- Augmented bank coordinate currently exposed by a process-one bridge. -/
def profiledRawJointRecurrentFiniteMemoryLeftToRightBridgeState
    (control :
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightBridgeControl
        (Memory := Memory) A strategy) :
    BankControl (Memory := Memory) A strategy :=
  match control with
  | .inl staged => staged.1
  | .inr installed => installed.1

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype Memory] in
@[simp] theorem
    profiledRawJointRecurrentFiniteMemoryLeftToRightDeliveredReceiver_open
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (staged :
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightStagedReceiver
        (Memory := Memory) A strategy) :
    profiledRawJointRecurrentFiniteMemoryLeftToRightDeliveredReceiver
      (Memory := Memory) A strategy oldReceiver (.inl staged) = oldReceiver :=
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype Memory] in
@[simp] theorem
    profiledRawJointRecurrentFiniteMemoryLeftToRightDeliveredReceiver_closed
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (installed :
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightInstalledOwner
        (Memory := Memory) A strategy) :
    profiledRawJointRecurrentFiniteMemoryLeftToRightDeliveredReceiver
        (Memory := Memory) A strategy oldReceiver (.inr installed) =
      initialProfiledRawJointRightPhysicalSiblingReceiver A
        installed.2.1.1 .both :=
  rfl

omit [Inhabited Out₂] [Fintype Memory] in
theorem
    profiledRawJointRecurrentFiniteMemoryLeftToRightDeliveredReceiver_eq_after_noRecv
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (left right :
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightBridgeControl
        (Memory := Memory) A strategy)
    (input : In₁)
    (hblind :
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightBridgeBlind
        (Memory := Memory) A strategy left right) :
    profiledRawJointRecurrentFiniteMemoryLeftToRightDeliveredReceiver
        (Memory := Memory) A strategy oldReceiver
        (profiledRawJointRecurrentFiniteMemoryLeftToRightBridgeNoRecv
          (Memory := Memory) A strategy left input).1 =
      profiledRawJointRecurrentFiniteMemoryLeftToRightDeliveredReceiver
        (Memory := Memory) A strategy oldReceiver
        (profiledRawJointRecurrentFiniteMemoryLeftToRightBridgeNoRecv
          (Memory := Memory) A strategy right input).1 := by
  cases hblind with
  | staged state receiver packet move hmove =>
      simp [profiledRawJointRecurrentFiniteMemoryLeftToRightBridgeNoRecv,
        profiledRawJointRecurrentFiniteMemoryLeftToRightStagePacket, hmove]
  | recurrent installed => rfl

/-! ## Selection-relative informed receives -/

namespace
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection

variable
  (initialMemory : RootKey A strategy → Memory)
  (selection :
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection
      (Memory := Memory) A strategy hwin initialMemory)

noncomputable def rightToLeftStageRecord
    (state : BankControl (Memory := Memory) A strategy)
    (receiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (record : ProfiledRawJointTargetRightReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂)
      (ProfiledRawJointIncidenceCode A (I := Unit)))
    (row : PairedEntryRow) :
    ProfiledRawJointRecurrentFiniteMemoryRightToLeftStagedReceiver
      (Memory := Memory) A strategy :=
  profiledRawJointRecurrentFiniteMemoryRightToLeftStagePacket
    (Memory := Memory) A strategy state receiver
      (selection.resolveRightRecord A strategy hwin initialMemory state record
        row)

/-- Advance the installed right receiver and stage the packet resolved from
the target emitted in that same record. -/
noncomputable def rightReceiveFor
    (state : BankControl (Memory := Memory) A strategy)
    (receiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₂ × In₁) :
    ProfiledRawJointRecurrentFiniteMemoryRightToLeftStagedReceiver
        (Memory := Memory) A strategy × Out₂ :=
  let next := stepProfiledRawJointRightPhysicalSiblingReceiverFor A receiver.1
    owner receiver.2.1 receiver.2.2.1 input
  match next.2.2.2.2 with
  | none => ((state, next.2, none), next.1)
  | some target =>
      ((state, next.2,
        some (selection.resolvePacket A strategy hwin initialMemory state
          target)), next.1)

@[simp] theorem rightReceiveFor_packet
    (state : BankControl (Memory := Memory) A strategy)
    (receiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₂ × In₁) :
    (selection.rightReceiveFor A strategy hwin initialMemory state receiver
      owner input).1.2.2 =
      some
        (selection.resolvePacket A strategy hwin initialMemory state
          (((receiver.1.memberController A false).labelOf owner).2
            receiver.2.2.1 input |>.target receiver.2.1)) :=
  rfl

@[simp] theorem rightReceiveFor_receiver
    (state : BankControl (Memory := Memory) A strategy)
    (receiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₂ × In₁) :
    (selection.rightReceiveFor A strategy hwin initialMemory state receiver
      owner input).1.2.1 =
      (stepProfiledRawJointRightPhysicalSiblingReceiverFor A receiver.1 owner
        receiver.2.1 receiver.2.2.1 input).2 :=
  rfl

@[simp] theorem rightReceiveFor_output
    (state : BankControl (Memory := Memory) A strategy)
    (receiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₂ × In₁) :
    (selection.rightReceiveFor A strategy hwin initialMemory state receiver
      owner input).2 =
      (stepProfiledRawJointRightPhysicalSiblingReceiverFor A receiver.1 owner
        receiver.2.1 receiver.2.2.1 input).1 :=
  rfl

/-- The actual informed process-two fork.  Its strict member keeps the
advanced receiver at the old augmented state; its simultaneous member installs
the opposite owner at the packet successor. -/
noncomputable def rightToLeftBridgeForkTwo
    (state : BankControl (Memory := Memory) A strategy)
    (receiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₂ × In₁) :
    FiniteDelayedFork
        (ProfiledRawJointRecurrentFiniteMemoryRightToLeftBridgeControl
          (Memory := Memory) A strategy) × Out₂ :=
  let next := selection.rightReceiveFor A strategy hwin initialMemory state
    receiver owner input
  let target := (((receiver.1.memberController A false).labelOf owner).2
    receiver.2.2.1 input |>.target receiver.2.1)
  let packet :=
    selection.resolvePacket A strategy hwin initialMemory state target
  let openControl :
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftBridgeControl
        (Memory := Memory) A strategy :=
    .inl next.1
  match packet.successor.2.1.1.2.2 with
  | none => (⟨openControl, openControl⟩, next.2)
  | some move =>
      (⟨openControl,
        .inr
          (packet.successor,
            ⟨move, (move.memberController A false).initial⟩,
            next.1.2.1)⟩,
        next.2)

theorem rightToLeftStagePacket_blind
    (state : BankControl (Memory := Memory) A strategy)
    (receiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
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
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftBridgeBlind
        (Memory := Memory) A strategy
        (.inl
          (profiledRawJointRecurrentFiniteMemoryRightToLeftStagePacket
            (Memory := Memory) A strategy state receiver packet))
        (.inr
          (packet.successor,
            ⟨move, (move.memberController A false).initial⟩, receiver)) := by
  dsimp only
  obtain ⟨move, hmove⟩ :=
    selection.resolvePacket_leftMove_exists A strategy hwin initialMemory
      state target hrealizes root hroot
  exact ⟨move, .staged state receiver _ move hmove⟩

theorem rightToLeftStageRecord_blind
    (state : BankControl (Memory := Memory) A strategy)
    (receiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (record : ProfiledRawJointTargetRightReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂)
      (ProfiledRawJointIncidenceCode A (I := Unit)))
    (row : PairedEntryRow)
    (hrealizes :
      selection.ChildRealizes A strategy hwin initialMemory state
        (record.target row)
        (selection.resolveTarget A strategy hwin initialMemory state
          (record.target row)))
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .left
      (record.target row) () = some root) :
    ∃ move : ProfiledRawJointLeftPhysicalSiblingMove A,
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftBridgeBlind
        (Memory := Memory) A strategy
        (.inl
          (selection.rightToLeftStageRecord A strategy hwin initialMemory
            state receiver record row))
        (.inr
          ((selection.resolveRightRecord A strategy hwin initialMemory state
              record row).successor,
            ⟨move, (move.memberController A false).initial⟩, receiver)) := by
  simpa [rightToLeftStageRecord, resolveRightRecord] using
    (selection.rightToLeftStagePacket_blind A strategy hwin initialMemory
      state receiver (record.target row) hrealizes root hroot)

theorem rightReceiveFor_blind
    (state : BankControl (Memory := Memory) A strategy)
    (receiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₂ × In₁)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : target =
      (((receiver.1.memberController A false).labelOf owner).2
        receiver.2.2.1 input |>.target receiver.2.1))
    (hrealizes :
      selection.ChildRealizes A strategy hwin initialMemory state target
        (selection.resolveTarget A strategy hwin initialMemory state target))
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .left target () =
      some root) :
    ∃ move : ProfiledRawJointLeftPhysicalSiblingMove A,
      let next := selection.rightReceiveFor A strategy hwin initialMemory
        state receiver owner input
      let packet :=
        selection.resolvePacket A strategy hwin initialMemory state target
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftBridgeBlind
        (Memory := Memory) A strategy
        (.inl next.1)
        (.inr
          (packet.successor,
            ⟨move, (move.memberController A false).initial⟩,
              next.1.2.1)) := by
  subst target
  let next := stepProfiledRawJointRightPhysicalSiblingReceiverFor A receiver.1
    owner receiver.2.1 receiver.2.2.1 input
  simpa [rightReceiveFor, next] using
    (selection.rightToLeftStagePacket_blind A strategy hwin initialMemory
      state next.2
      ((((receiver.1.memberController A false).labelOf owner).2
        receiver.2.2.1 input).target receiver.2.1) hrealizes root hroot)

/-- A legal informed right receive produces the exact blind bridge pair. -/
theorem rightToLeftBridgeForkTwo_blind
    (state : BankControl (Memory := Memory) A strategy)
    (receiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₂ × In₁)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : target =
      (((receiver.1.memberController A false).labelOf owner).2
        receiver.2.2.1 input |>.target receiver.2.1))
    (hrealizes :
      selection.ChildRealizes A strategy hwin initialMemory state target
        (selection.resolveTarget A strategy hwin initialMemory state target))
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .left target () =
      some root) :
    let fork :=
      (selection.rightToLeftBridgeForkTwo A strategy hwin initialMemory state
        receiver owner input).1
    ProfiledRawJointRecurrentFiniteMemoryRightToLeftBridgeBlind
      (Memory := Memory) A strategy fork.openControl fork.closedControl := by
  subst target
  let target := (((receiver.1.memberController A false).labelOf owner).2
    receiver.2.2.1 input |>.target receiver.2.1)
  let packet :=
    selection.resolvePacket A strategy hwin initialMemory state target
  obtain ⟨move, hmove⟩ :=
    selection.resolvePacket_leftMove_exists A strategy hwin initialMemory
      state target hrealizes root hroot
  simp only [rightToLeftBridgeForkTwo, target, packet, hmove]
  exact .staged state
    (selection.rightReceiveFor A strategy hwin initialMemory state receiver
      owner input).1.2.1 packet move hmove

/-- Under the same live-lane fact used by the blind proof, the two fork
members expose exactly the old and successor memories. -/
theorem rightToLeftBridgeForkTwo_coordinates_of_move
    (state : BankControl (Memory := Memory) A strategy)
    (receiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₂ × In₁)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hmove :
      (selection.resolvePacket A strategy hwin initialMemory state
        ((((receiver.1.memberController A false).labelOf owner).2
          receiver.2.2.1 input).target receiver.2.1)).successor.2.1.1.2.2 =
        some move) :
    let fork :=
      (selection.rightToLeftBridgeForkTwo A strategy hwin initialMemory state
        receiver owner input).1
    profiledRawJointRecurrentFiniteMemoryRightToLeftBridgeState
        (Memory := Memory) A strategy fork.openControl = state ∧
      profiledRawJointRecurrentFiniteMemoryRightToLeftBridgeState
        (Memory := Memory) A strategy fork.closedControl =
          (selection.resolvePacket A strategy hwin initialMemory state
            ((((receiver.1.memberController A false).labelOf owner).2
              receiver.2.2.1 input).target receiver.2.1)).successor := by
  simp only [rightToLeftBridgeForkTwo, rightReceiveFor, hmove,
    profiledRawJointRecurrentFiniteMemoryRightToLeftBridgeState]
  constructor
  · trivial
  · simp [rightReceiveFor]

noncomputable def leftToRightStageRecord
    (state : BankControl (Memory := Memory) A strategy)
    (receiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (record : ProfiledRawJointTargetLeftReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂)
      (ProfiledRawJointIncidenceCode A (I := Unit)))
    (row : PairedEntryRow) :
    ProfiledRawJointRecurrentFiniteMemoryLeftToRightStagedReceiver
      (Memory := Memory) A strategy :=
  profiledRawJointRecurrentFiniteMemoryLeftToRightStagePacket
    (Memory := Memory) A strategy state receiver
      (selection.resolveLeftRecord A strategy hwin initialMemory state record
        row)

noncomputable def leftReceiveFor
    (state : BankControl (Memory := Memory) A strategy)
    (receiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₁ × In₂) :
    ProfiledRawJointRecurrentFiniteMemoryLeftToRightStagedReceiver
        (Memory := Memory) A strategy × Out₁ :=
  let next := stepProfiledRawJointLeftPhysicalSiblingReceiverFor A receiver.1
    owner receiver.2.1 receiver.2.2.1 input
  match next.2.2.2.2 with
  | none => ((state, next.2, none), next.1)
  | some target =>
      ((state, next.2,
        some (selection.resolvePacket A strategy hwin initialMemory state
          target)), next.1)

@[simp] theorem leftReceiveFor_packet
    (state : BankControl (Memory := Memory) A strategy)
    (receiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₁ × In₂) :
    (selection.leftReceiveFor A strategy hwin initialMemory state receiver
      owner input).1.2.2 =
      some
        (selection.resolvePacket A strategy hwin initialMemory state
          (((receiver.1.memberController A false).labelOf owner).2
            receiver.2.2.1 input |>.target receiver.2.1)) :=
  rfl

@[simp] theorem leftReceiveFor_receiver
    (state : BankControl (Memory := Memory) A strategy)
    (receiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₁ × In₂) :
    (selection.leftReceiveFor A strategy hwin initialMemory state receiver
      owner input).1.2.1 =
      (stepProfiledRawJointLeftPhysicalSiblingReceiverFor A receiver.1 owner
        receiver.2.1 receiver.2.2.1 input).2 :=
  rfl

@[simp] theorem leftReceiveFor_output
    (state : BankControl (Memory := Memory) A strategy)
    (receiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₁ × In₂) :
    (selection.leftReceiveFor A strategy hwin initialMemory state receiver
      owner input).2 =
      (stepProfiledRawJointLeftPhysicalSiblingReceiverFor A receiver.1 owner
        receiver.2.1 receiver.2.2.1 input).1 :=
  rfl

/-- Mirrored informed process-one fork. -/
noncomputable def leftToRightBridgeForkOne
    (state : BankControl (Memory := Memory) A strategy)
    (receiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₁ × In₂) :
    FiniteDelayedFork
        (ProfiledRawJointRecurrentFiniteMemoryLeftToRightBridgeControl
          (Memory := Memory) A strategy) × Out₁ :=
  let next := selection.leftReceiveFor A strategy hwin initialMemory state
    receiver owner input
  let target := (((receiver.1.memberController A false).labelOf owner).2
    receiver.2.2.1 input |>.target receiver.2.1)
  let packet :=
    selection.resolvePacket A strategy hwin initialMemory state target
  let openControl :
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightBridgeControl
        (Memory := Memory) A strategy :=
    .inl next.1
  match packet.successor.2.1.1.2.1 with
  | none => (⟨openControl, openControl⟩, next.2)
  | some move =>
      (⟨openControl,
        .inr
          (packet.successor,
            ⟨move, (move.memberController A false).initial⟩,
            next.1.2.1)⟩,
        next.2)

theorem leftToRightStagePacket_blind
    (state : BankControl (Memory := Memory) A strategy)
    (receiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
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
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightBridgeBlind
        (Memory := Memory) A strategy
        (.inl
          (profiledRawJointRecurrentFiniteMemoryLeftToRightStagePacket
            (Memory := Memory) A strategy state receiver packet))
        (.inr
          (packet.successor,
            ⟨move, (move.memberController A false).initial⟩, receiver)) := by
  dsimp only
  obtain ⟨move, hmove⟩ :=
    selection.resolvePacket_rightMove_exists A strategy hwin initialMemory
      state target hrealizes root hroot
  exact ⟨move, .staged state receiver _ move hmove⟩

theorem leftToRightStageRecord_blind
    (state : BankControl (Memory := Memory) A strategy)
    (receiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (record : ProfiledRawJointTargetLeftReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂)
      (ProfiledRawJointIncidenceCode A (I := Unit)))
    (row : PairedEntryRow)
    (hrealizes :
      selection.ChildRealizes A strategy hwin initialMemory state
        (record.target row)
        (selection.resolveTarget A strategy hwin initialMemory state
          (record.target row)))
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .right
      (record.target row) () = some root) :
    ∃ move : ProfiledRawJointRightPhysicalSiblingMove A,
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightBridgeBlind
        (Memory := Memory) A strategy
        (.inl
          (selection.leftToRightStageRecord A strategy hwin initialMemory
            state receiver record row))
        (.inr
          ((selection.resolveLeftRecord A strategy hwin initialMemory state
              record row).successor,
            ⟨move, (move.memberController A false).initial⟩, receiver)) := by
  simpa [leftToRightStageRecord, resolveLeftRecord] using
    (selection.leftToRightStagePacket_blind A strategy hwin initialMemory
      state receiver (record.target row) hrealizes root hroot)

theorem leftReceiveFor_blind
    (state : BankControl (Memory := Memory) A strategy)
    (receiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₁ × In₂)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : target =
      (((receiver.1.memberController A false).labelOf owner).2
        receiver.2.2.1 input |>.target receiver.2.1))
    (hrealizes :
      selection.ChildRealizes A strategy hwin initialMemory state target
        (selection.resolveTarget A strategy hwin initialMemory state target))
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .right target () =
      some root) :
    ∃ move : ProfiledRawJointRightPhysicalSiblingMove A,
      let next := selection.leftReceiveFor A strategy hwin initialMemory
        state receiver owner input
      let packet :=
        selection.resolvePacket A strategy hwin initialMemory state target
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightBridgeBlind
        (Memory := Memory) A strategy
        (.inl next.1)
        (.inr
          (packet.successor,
            ⟨move, (move.memberController A false).initial⟩,
              next.1.2.1)) := by
  subst target
  let next := stepProfiledRawJointLeftPhysicalSiblingReceiverFor A receiver.1
    owner receiver.2.1 receiver.2.2.1 input
  simpa [leftReceiveFor, next] using
    (selection.leftToRightStagePacket_blind A strategy hwin initialMemory
      state next.2
      ((((receiver.1.memberController A false).labelOf owner).2
        receiver.2.2.1 input).target receiver.2.1) hrealizes root hroot)

/-- A legal informed left receive produces the mirrored exact blind pair. -/
theorem leftToRightBridgeForkOne_blind
    (state : BankControl (Memory := Memory) A strategy)
    (receiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₁ × In₂)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : target =
      (((receiver.1.memberController A false).labelOf owner).2
        receiver.2.2.1 input |>.target receiver.2.1))
    (hrealizes :
      selection.ChildRealizes A strategy hwin initialMemory state target
        (selection.resolveTarget A strategy hwin initialMemory state target))
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .right target () =
      some root) :
    let fork :=
      (selection.leftToRightBridgeForkOne A strategy hwin initialMemory state
        receiver owner input).1
    ProfiledRawJointRecurrentFiniteMemoryLeftToRightBridgeBlind
      (Memory := Memory) A strategy fork.openControl fork.closedControl := by
  subst target
  let target := (((receiver.1.memberController A false).labelOf owner).2
    receiver.2.2.1 input |>.target receiver.2.1)
  let packet :=
    selection.resolvePacket A strategy hwin initialMemory state target
  obtain ⟨move, hmove⟩ :=
    selection.resolvePacket_rightMove_exists A strategy hwin initialMemory
      state target hrealizes root hroot
  simp only [leftToRightBridgeForkOne, target, packet, hmove]
  exact .staged state
    (selection.leftReceiveFor A strategy hwin initialMemory state receiver
      owner input).1.2.1 packet move hmove

/-- Mirrored old/successor coordinate equation. -/
theorem leftToRightBridgeForkOne_coordinates_of_move
    (state : BankControl (Memory := Memory) A strategy)
    (receiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₁ × In₂)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (hmove :
      (selection.resolvePacket A strategy hwin initialMemory state
        ((((receiver.1.memberController A false).labelOf owner).2
          receiver.2.2.1 input).target receiver.2.1)).successor.2.1.1.2.1 =
        some move) :
    let fork :=
      (selection.leftToRightBridgeForkOne A strategy hwin initialMemory state
        receiver owner input).1
    profiledRawJointRecurrentFiniteMemoryLeftToRightBridgeState
        (Memory := Memory) A strategy fork.openControl = state ∧
      profiledRawJointRecurrentFiniteMemoryLeftToRightBridgeState
        (Memory := Memory) A strategy fork.closedControl =
          (selection.resolvePacket A strategy hwin initialMemory state
            ((((receiver.1.memberController A false).labelOf owner).2
              receiver.2.2.1 input).target receiver.2.1)).successor := by
  simp only [leftToRightBridgeForkOne, leftReceiveFor, hmove,
    profiledRawJointRecurrentFiniteMemoryLeftToRightBridgeState]
  constructor
  · trivial
  · simp [leftReceiveFor]

end
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection

/-! ## Combined blind law -/

noncomputable def
    profiledRawJointRecurrentFiniteMemoryBridgeBlindNoRecvLaws :
    FiniteAcknowledgedDelayedCarrier.BlindNoRecvLaws
      (profiledRawJointRecurrentFiniteMemoryLeftToRightBridgeNoRecv
        (Memory := Memory) A strategy)
      (profiledRawJointRecurrentFiniteMemoryRightToLeftBridgeNoRecv
        (Memory := Memory) A strategy)
      (ProfiledRawJointRecurrentFiniteMemoryLeftToRightBridgeBlind
        (Memory := Memory) A strategy)
      (ProfiledRawJointRecurrentFiniteMemoryRightToLeftBridgeBlind
        (Memory := Memory) A strategy) where
  one :=
    profiledRawJointRecurrentFiniteMemoryLeftToRightBridgeBlind_noRecv
      (Memory := Memory) A strategy
  two :=
    profiledRawJointRecurrentFiniteMemoryRightToLeftBridgeBlind_noRecv
      (Memory := Memory) A strategy

end

end DetParityAutomaton

end DistributedSynthesis
