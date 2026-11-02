/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelectionOwnerFibreSafetyAutomaton

/-!
# Exact finite family of recurrent owner-fibre entries

For one fixed physical-compatible root key, a recurrent entry is not an
arbitrary pair of endpoint controls and an arbitrary objective state.  The
honest front fixes an orientation, an installed move at that key, a receiver
row and finite dormant template, and the input of the resolving front round.
The selected augmented policy then fixes the target packet.  Its opposite
installed move fixes the objective-DPA state at the recurrent seam.

This file records those two oriented constructors and filters the finite live
state space by their exact image.  In particular, the DPA coordinate is
definitionally reconstructed from the resolved opposite move; it is never
quantified independently over `A.State`.
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

private abbrev OneControl :=
  ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
    (Memory := Memory) A strategy

private abbrev TwoControl :=
  ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
    (Memory := Memory) A strategy

private abbrev LiveState :=
  ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyLiveState
    (Memory := Memory) A strategy

private abbrev PolicySelection
    (initialMemory : RootKey A strategy → Memory) :=
  ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection
    (Memory := Memory) A strategy hwin initialMemory

/-! ## Selection-free finite front contexts

The policy successor, and therefore the live DPA coordinate, cannot be part of
the context over which a future choice automaton branches: that successor is
produced only after the automaton has chosen the augmented policy action.  We
therefore separate the finite front data from its selection-dependent live
realization.
-/

structure ProfiledRawJointRecurrentFiniteMemoryOwnerFibreRightFrontParameter
    where
  installedMove : ProfiledRawJointRightPhysicalSiblingMove A
  row : PairedEntryRow
  dormantTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A
  closingInput : In₁ × In₂
  deriving Fintype

structure ProfiledRawJointRecurrentFiniteMemoryOwnerFibreLeftFrontParameter
    where
  installedMove : ProfiledRawJointLeftPhysicalSiblingMove A
  row : PairedEntryRow
  dormantTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A
  closingInput : In₁ × In₂
  deriving Fintype

def ProfiledRawJointRecurrentFiniteMemoryOwnerFibreRightFrontParameter.AtKey
    (key : RootKey A strategy)
    (context :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreRightFrontParameter A) :
    Prop :=
  key.1.2.1 = some context.installedMove ∧
    profiledRawJointOneSidedCurrentSlots A .right key.1.1 () =
      some (.inl context.installedMove.1.source)

def ProfiledRawJointRecurrentFiniteMemoryOwnerFibreLeftFrontParameter.AtKey
    (key : RootKey A strategy)
    (context :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreLeftFrontParameter A) :
    Prop :=
  key.1.2.2 = some context.installedMove ∧
    profiledRawJointOneSidedCurrentSlots A .left key.1.1 () =
      some (.inr context.installedMove.1.source)

/-- Finite, selection-independent contexts presented by the right-oriented
honest front at one root key. -/
abbrev ProfiledRawJointRecurrentFiniteMemoryOwnerFibreRightFrontContextAt
    (key : RootKey A strategy) :=
  { context :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreRightFrontParameter A //
    context.AtKey A strategy key }

/-- Mirrored selection-independent front contexts. -/
abbrev ProfiledRawJointRecurrentFiniteMemoryOwnerFibreLeftFrontContextAt
    (key : RootKey A strategy) :=
  { context :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreLeftFrontParameter A //
    context.AtKey A strategy key }

/-- The finite universal index used before an augmented policy has been
chosen. -/
abbrev ProfiledRawJointRecurrentFiniteMemoryOwnerFibreFrontContextAt
    (key : RootKey A strategy) :=
  ProfiledRawJointRecurrentFiniteMemoryOwnerFibreRightFrontContextAt A strategy
      key ⊕
    ProfiledRawJointRecurrentFiniteMemoryOwnerFibreLeftFrontContextAt A strategy
      key

noncomputable instance
    (key : RootKey A strategy) :
    Fintype
      (ProfiledRawJointRecurrentFiniteMemoryOwnerFibreFrontContextAt A strategy
        key) := by
  classical
  infer_instance

/-- The selection-free context family is literally the whole finite context
type.  In particular, it is available before any packet successor is chosen.
-/
noncomputable def
    profiledRawJointRecurrentFiniteMemoryOwnerFibreFrontContextsAt
    (key : RootKey A strategy) :
    Finset
      (ProfiledRawJointRecurrentFiniteMemoryOwnerFibreFrontContextAt A strategy
        key) := by
  classical
  exact Finset.univ

/-! ## Fixed-key predicates for the augmented endpoint space -/

def ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankControl.AtKey
    (key : RootKey A strategy)
    (state : BankControl (Memory := Memory) A strategy) : Prop :=
  state.1 = key

def ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankResolvedTarget.AtKey
    (key : RootKey A strategy)
    (packet : Packet (Memory := Memory) A strategy) : Prop :=
  packet.successor.1 = key

def ProfiledRawJointRecurrentFiniteMemoryRightToLeftBridgeAtKey
    (key : RootKey A strategy)
    (control :
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftBridgeControl
        (Memory := Memory) A strategy) : Prop :=
  match control with
  | .inl staged =>
      staged.1.AtKey A strategy key ∧
        ∀ packet, staged.2.2 = some packet → packet.AtKey A strategy key
  | .inr installed => installed.1.AtKey A strategy key

def ProfiledRawJointRecurrentFiniteMemoryLeftToRightBridgeAtKey
    (key : RootKey A strategy)
    (control :
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightBridgeControl
        (Memory := Memory) A strategy) : Prop :=
  match control with
  | .inl staged =>
      staged.1.AtKey A strategy key ∧
        ∀ packet, staged.2.2 = some packet → packet.AtKey A strategy key
  | .inr installed => installed.1.AtKey A strategy key

def ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreAtKey
    (key : RootKey A strategy)
    (control :
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibrePending
        (Memory := Memory) A strategy) : Prop :=
  (profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreReceiver
      (Memory := Memory) A strategy
      ⟨false, control.2.1, control.2.2⟩).1.AtKey A strategy key ∧
    (profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreReceiver
      (Memory := Memory) A strategy
      ⟨true, control.2.1, control.2.2⟩).1.AtKey A strategy key

def ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreAtKey
    (key : RootKey A strategy)
    (control :
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibrePending
        (Memory := Memory) A strategy) : Prop :=
  (profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreReceiver
      (Memory := Memory) A strategy
      ⟨false, control.2.1, control.2.2⟩).1.AtKey A strategy key ∧
    (profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreReceiver
      (Memory := Memory) A strategy
      ⟨true, control.2.1, control.2.2⟩).1.AtKey A strategy key

def ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneBaseAtKey
    (key : RootKey A strategy)
    (control :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneBase
        (Memory := Memory) A strategy) : Prop :=
  match control with
  | .inl bridge =>
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightBridgeAtKey
        (Memory := Memory) A strategy key bridge
  | .inr pending =>
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreAtKey
        (Memory := Memory) A strategy key pending

def ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoBaseAtKey
    (key : RootKey A strategy)
    (control :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoBase
        (Memory := Memory) A strategy) : Prop :=
  match control with
  | .inl bridge =>
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftBridgeAtKey
        (Memory := Memory) A strategy key bridge
  | .inr pending =>
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreAtKey
        (Memory := Memory) A strategy key pending

def ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneAtKey
    (key : RootKey A strategy)
    (control : OneControl (Memory := Memory) A strategy) : Prop :=
  ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneBaseAtKey
      (Memory := Memory) A strategy key control.1 ∧
    control.2.1.AtKey A strategy key ∧
    control.2.2.AtKey A strategy key

def ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoAtKey
    (key : RootKey A strategy)
    (control : TwoControl (Memory := Memory) A strategy) : Prop :=
  ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoBaseAtKey
      (Memory := Memory) A strategy key control.1 ∧
    control.2.1.AtKey A strategy key ∧
    control.2.2.AtKey A strategy key

def ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyLiveStateAtKey
    (key : RootKey A strategy)
    (state : LiveState (Memory := Memory) A strategy) : Prop :=
  ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneAtKey
      (Memory := Memory) A strategy key state.1.1 ∧
    ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoAtKey
      (Memory := Memory) A strategy key state.1.2

namespace
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection

variable
  (initialMemory : RootKey A strategy → Memory)
  (selection : PolicySelection (Memory := Memory) A strategy hwin
    initialMemory)

/-! ## The two exact oriented entry constructors -/

noncomputable def ownerFibreRightEntryOne
    (rightState : BankControl (Memory := Memory) A strategy)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightOwner : (rightReceiver.1.memberController A false).Control)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (packet : Packet (Memory := Memory) A strategy) :
    OneControl (Memory := Memory) A strategy :=
  (.inl
    (.inr (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
    (rightState, packet.successor))

noncomputable def ownerFibreRightEntryTwo
    (rightState : BankControl (Memory := Memory) A strategy)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (packet : Packet (Memory := Memory) A strategy) :
    TwoControl (Memory := Memory) A strategy :=
  (.inl (.inl (rightState, rightReceiver, some packet)),
    (rightState, packet.successor))

noncomputable def ownerFibreLeftEntryOne
    (leftState : BankControl (Memory := Memory) A strategy)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (packet : Packet (Memory := Memory) A strategy) :
    OneControl (Memory := Memory) A strategy :=
  (.inl (.inl (leftState, leftReceiver, some packet)),
    (packet.successor, leftState))

noncomputable def ownerFibreLeftEntryTwo
    (leftState : BankControl (Memory := Memory) A strategy)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (leftOwner : (leftReceiver.1.memberController A false).Control)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (packet : Packet (Memory := Memory) A strategy) :
    TwoControl (Memory := Memory) A strategy :=
  (.inl
    (.inr (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
    (packet.successor, leftState))

/-- The checker state after a right-oriented front close is the first-row
state of the newly installed dormant-left move. -/
def ownerFibreRightEntryDPAState
    (leftMove : ProfiledRawJointLeftPhysicalSiblingMove A) : A.State :=
  pairedCodeStateForRow A .first leftMove.1.source.1.1

/-- Mirrored exact checker coordinate. -/
def ownerFibreLeftEntryDPAState
    (rightMove : ProfiledRawJointRightPhysicalSiblingMove A) : A.State :=
  pairedCodeStateForRow A .first rightMove.1.source.1.1

noncomputable def ownerFibreRightEntryLiveState
    (rightState : BankControl (Memory := Memory) A strategy)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightOwner : (rightReceiver.1.memberController A false).Control)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (packet : Packet (Memory := Memory) A strategy)
    (leftMove : ProfiledRawJointLeftPhysicalSiblingMove A) :
    LiveState (Memory := Memory) A strategy :=
  ((ownerFibreRightEntryOne (Memory := Memory) A strategy
      rightState rightReceiver rightOwner leftTemplate packet,
    ownerFibreRightEntryTwo (Memory := Memory) A strategy
      rightState rightReceiver packet),
    ownerFibreRightEntryDPAState A leftMove)

noncomputable def ownerFibreLeftEntryLiveState
    (leftState : BankControl (Memory := Memory) A strategy)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (leftOwner : (leftReceiver.1.memberController A false).Control)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (packet : Packet (Memory := Memory) A strategy)
    (rightMove : ProfiledRawJointRightPhysicalSiblingMove A) :
    LiveState (Memory := Memory) A strategy :=
  ((ownerFibreLeftEntryOne (Memory := Memory) A strategy leftState
      leftReceiver packet,
    ownerFibreLeftEntryTwo (Memory := Memory) A strategy leftState
      leftReceiver leftOwner rightTemplate packet),
    ownerFibreLeftEntryDPAState A rightMove)

/-- Selection-dependent realization of one finite front context.  The context
contains no policy result.  Resolving it with `selection` produces the packet,
and the opposite move stored in that packet produces both the dormant endpoint
and the exact DPA coordinate. -/
def RealizesOwnerFibreFrontContextAt
    (key : RootKey A strategy)
    (context :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreFrontContextAt A strategy
        key)
    (state : LiveState (Memory := Memory) A strategy) : Prop :=
  match context with
  | .inl context =>
      let rightMove := context.1.installedMove
      let rightState := selection.root A strategy hwin initialMemory key
      let rightReceiver :=
        initialProfiledRawJointRightPhysicalSiblingReceiver A rightMove
          context.1.row
      let rightOwner := (rightMove.memberController A false).initial
      let data :
          ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData
            (Memory := Memory) A strategy :=
        (rightState, ⟨rightReceiver, rightOwner⟩,
          context.1.dormantTemplate)
      let packet := selection.resolvePacket A strategy hwin initialMemory
        rightState (data.target (Memory := Memory) A strategy
          context.1.closingInput)
      ∃ leftMove : ProfiledRawJointLeftPhysicalSiblingMove A,
        packet.successor.2.1.1.2.2 = some leftMove ∧
          state = ownerFibreRightEntryLiveState (Memory := Memory) A strategy
            rightState rightReceiver rightOwner context.1.dormantTemplate
              packet leftMove
  | .inr context =>
      let leftMove := context.1.installedMove
      let leftState := selection.root A strategy hwin initialMemory key
      let leftReceiver :=
        initialProfiledRawJointLeftPhysicalSiblingReceiver A leftMove
          context.1.row
      let leftOwner := (leftMove.memberController A false).initial
      let data :
          ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData
            (Memory := Memory) A strategy :=
        (leftState, ⟨leftReceiver, leftOwner⟩,
          context.1.dormantTemplate)
      let packet := selection.resolvePacket A strategy hwin initialMemory
        leftState (data.target (Memory := Memory) A strategy
          context.1.closingInput)
      ∃ rightMove : ProfiledRawJointRightPhysicalSiblingMove A,
        packet.successor.2.1.1.2.1 = some rightMove ∧
          state = ownerFibreLeftEntryLiveState (Memory := Memory) A strategy
            leftState leftReceiver leftOwner context.1.dormantTemplate
              packet rightMove

/-- No selection-free front context disappears after a valid augmented policy
is chosen.  Installed-table target closure supplies the opposite move in the
resolved packet, so every context has exactly shaped live realizations. -/
theorem ownerFibreFrontContext_realizes
    (key : RootKey A strategy)
    (context :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreFrontContextAt A strategy
        key) :
    ∃ state : LiveState (Memory := Memory) A strategy,
      selection.RealizesOwnerFibreFrontContextAt A strategy hwin initialMemory
        key context state := by
  rcases context with context | context
  · rcases context with ⟨parameter, hinstalled, hroot⟩
    rcases parameter with ⟨rightMove, row, leftTemplate, input⟩
    let rightState := selection.root A strategy hwin initialMemory key
    let rightReceiver :=
      initialProfiledRawJointRightPhysicalSiblingReceiver A rightMove row
    let rightOwner := (rightMove.memberController A false).initial
    let data :
        ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData
          (Memory := Memory) A strategy :=
      (rightState, ⟨rightReceiver, rightOwner⟩, leftTemplate)
    let target := data.target (Memory := Memory) A strategy input
    let blockInput : In₂ × In₁ := (input.2, input.1)
    let env : Nat → In₂ × In₁ := omegaOfList [blockInput]
    have hat := profiledRawJointRightPhysicalSibling_treePlay_at_prefix A
      rightMove [] blockInput
    have hsafe := rightMove.memberController_targetSafe A false env 0 row
    have hat' :
        treePlay
            (narrowedInducedTree
              (profiledRawJointRightPhysicalSiblingMonitor A rightMove.1
                false)
              (rightMove.memberController A false).labeledTree)
            env 0 =
          narrowedRecord
            (profiledRawJointRightPhysicalSiblingMonitor A rightMove.1 false)
            ((rightMove.memberController A false).labelOf
              (rightMove.memberController A false).initial)
            (profiledRawJointRightPhysicalSiblingMonitor A rightMove.1 false
              |>.initial)
            blockInput := by
      simpa [env] using hat
    dsimp only at hsafe
    rw [hat'] at hsafe
    dsimp only [narrowedRecord] at hsafe
    have hallowed :
        profiledRawJointRightPhysicalSiblingAllowed A rightMove.1 target := by
      simpa [target, data, rightReceiver, rightOwner, blockInput] using hsafe.2
    obtain ⟨freshSlot, hfreshSlot⟩ :=
      exists_profiledRawJointLeftSlot_of_rightPhysicalTargetSafe A _ _ _ _
        hsafe.1
    have htargetRoot :
        profiledRawJointOneSidedCurrentSlots A .left target () =
          some (.inr freshSlot) := by
      change Option.map Sum.inr (target.family.left ()) =
        some (.inr freshSlot)
      have hfreshSlot' : target.family.left () = some freshSlot := by
        simpa [target, data, rightReceiver, rightOwner, blockInput] using
          hfreshSlot
      simp [hfreshSlot']
    have hdata := selection.root_data A strategy hwin initialMemory key
    have hcurrentCode : rightState.2.1.1.1 = key.1.1 := by
      exact congrArg Prod.fst hdata
    have hcurrentMove : rightState.2.1.1.2.1 = some rightMove := by
      exact (congrArg (fun root ↦ root.2.1) hdata).trans hinstalled
    have hpacketSpec :=
      selection.resolveRightPacket_spec A strategy hwin initialMemory
        rightState
        (selection.root_reachable A strategy hwin initialMemory key)
        key.1.1 hcurrentCode (.inl rightMove.1.source) hroot rightMove
        hcurrentMove target hallowed
    obtain ⟨_bare, hrealizes, _key, _reachable⟩ := hpacketSpec
    obtain ⟨leftMove, hleftMove⟩ :=
      selection.resolvePacket_leftMove_exists A strategy hwin initialMemory
        rightState target hrealizes (.inr freshSlot) htargetRoot
    let packet := selection.resolvePacket A strategy hwin initialMemory
      rightState target
    refine ⟨ownerFibreRightEntryLiveState (Memory := Memory) A strategy
      rightState rightReceiver rightOwner leftTemplate packet leftMove, ?_⟩
    exact ⟨leftMove, hleftMove, rfl⟩
  · rcases context with ⟨parameter, hinstalled, hroot⟩
    rcases parameter with ⟨leftMove, row, rightTemplate, input⟩
    let leftState := selection.root A strategy hwin initialMemory key
    let leftReceiver :=
      initialProfiledRawJointLeftPhysicalSiblingReceiver A leftMove row
    let leftOwner := (leftMove.memberController A false).initial
    let data :
        ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData
          (Memory := Memory) A strategy :=
      (leftState, ⟨leftReceiver, leftOwner⟩, rightTemplate)
    let target := data.target (Memory := Memory) A strategy input
    let env : Nat → In₁ × In₂ := omegaOfList [input]
    have hat := profiledRawJointLeftPhysicalSibling_treePlay_at_prefix A
      leftMove [] input
    have hsafe := leftMove.memberController_targetSafe A false env 0 row
    have hat' :
        treePlay
            (narrowedInducedTree
              (profiledRawJointLeftPhysicalSiblingMonitor A leftMove.1 false)
              (leftMove.memberController A false).labeledTree)
            env 0 =
          narrowedRecord
            (profiledRawJointLeftPhysicalSiblingMonitor A leftMove.1 false)
            ((leftMove.memberController A false).labelOf
              (leftMove.memberController A false).initial)
            (profiledRawJointLeftPhysicalSiblingMonitor A leftMove.1 false
              |>.initial)
            input := by
      simpa [env] using hat
    dsimp only at hsafe
    rw [hat'] at hsafe
    dsimp only [narrowedRecord] at hsafe
    have hallowed :
        profiledRawJointLeftPhysicalSiblingAllowed A leftMove.1 target := by
      simpa [target, data, leftReceiver, leftOwner] using hsafe.2
    obtain ⟨freshSlot, hfreshSlot⟩ :=
      exists_profiledRawJointRightSlot_of_leftPhysicalTargetSafe A _ _ _ _
        hsafe.1
    have htargetRoot :
        profiledRawJointOneSidedCurrentSlots A .right target () =
          some (.inl freshSlot) := by
      change Option.map Sum.inl (target.family.right ()) =
        some (.inl freshSlot)
      have hfreshSlot' : target.family.right () = some freshSlot := by
        simpa [target, data, leftReceiver, leftOwner] using hfreshSlot
      simp [hfreshSlot']
    have hdata := selection.root_data A strategy hwin initialMemory key
    have hcurrentCode : leftState.2.1.1.1 = key.1.1 := by
      exact congrArg Prod.fst hdata
    have hcurrentMove : leftState.2.1.1.2.2 = some leftMove := by
      exact (congrArg (fun root ↦ root.2.2) hdata).trans hinstalled
    have hpacketSpec :=
      selection.resolveLeftPacket_spec A strategy hwin initialMemory leftState
        (selection.root_reachable A strategy hwin initialMemory key)
        key.1.1 hcurrentCode (.inr leftMove.1.source) hroot leftMove
        hcurrentMove target hallowed
    obtain ⟨_bare, hrealizes, _key, _reachable⟩ := hpacketSpec
    obtain ⟨rightMove, hrightMove⟩ :=
      selection.resolvePacket_rightMove_exists A strategy hwin initialMemory
        leftState target hrealizes (.inl freshSlot) htargetRoot
    let packet := selection.resolvePacket A strategy hwin initialMemory
      leftState target
    refine ⟨ownerFibreLeftEntryLiveState (Memory := Memory) A strategy
      leftState leftReceiver leftOwner rightTemplate packet rightMove, ?_⟩
    exact ⟨rightMove, hrightMove, rfl⟩

/-- Packet determinism makes the selected realization of a fixed context
unique. -/
theorem ownerFibreFrontContext_realization_unique
    (key : RootKey A strategy)
    (context :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreFrontContextAt A strategy
        key)
    (first second : LiveState (Memory := Memory) A strategy)
    (hfirst : selection.RealizesOwnerFibreFrontContextAt A strategy hwin
      initialMemory key context first)
    (hsecond : selection.RealizesOwnerFibreFrontContextAt A strategy hwin
      initialMemory key context second) :
    first = second := by
  rcases context with context | context
  · rcases hfirst with ⟨firstMove, hfirstMove, hfirstState⟩
    rcases hsecond with ⟨secondMove, hsecondMove, hsecondState⟩
    have hmove : firstMove = secondMove :=
      Option.some.inj (hfirstMove.symm.trans hsecondMove)
    subst secondMove
    exact hfirstState.trans hsecondState.symm
  · rcases hfirst with ⟨firstMove, hfirstMove, hfirstState⟩
    rcases hsecond with ⟨secondMove, hsecondMove, hsecondState⟩
    have hmove : firstMove = secondMove :=
      Option.some.inj (hfirstMove.symm.trans hsecondMove)
    subst secondMove
    exact hfirstState.trans hsecondState.symm

/-- The unique selected recurrent live state generated by a finite front
context. -/
noncomputable def ownerFibreFrontContextLiveState
    (key : RootKey A strategy)
    (context :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreFrontContextAt A strategy
        key) :
    LiveState (Memory := Memory) A strategy :=
  Classical.choose
    (selection.ownerFibreFrontContext_realizes A strategy hwin initialMemory
      key context)

theorem ownerFibreFrontContextLiveState_realizes
    (key : RootKey A strategy)
    (context :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreFrontContextAt A strategy
        key) :
    selection.RealizesOwnerFibreFrontContextAt A strategy hwin initialMemory
      key context
      (selection.ownerFibreFrontContextLiveState A strategy hwin initialMemory
        key context) :=
  Classical.choose_spec
    (selection.ownerFibreFrontContext_realizes A strategy hwin initialMemory
      key context)

theorem realizesOwnerFibreFrontContextAt_iff_eq_liveState
    (key : RootKey A strategy)
    (context :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreFrontContextAt A strategy
        key)
    (state : LiveState (Memory := Memory) A strategy) :
    selection.RealizesOwnerFibreFrontContextAt A strategy hwin initialMemory
        key context state ↔
      state = selection.ownerFibreFrontContextLiveState A strategy hwin
        initialMemory key context := by
  constructor
  · intro hstate
    exact selection.ownerFibreFrontContext_realization_unique A strategy hwin
      initialMemory key context state _ hstate
      (selection.ownerFibreFrontContextLiveState_realizes A strategy hwin
        initialMemory key context)
  · intro hstate
    subst state
    exact selection.ownerFibreFrontContextLiveState_realizes A strategy hwin
      initialMemory key context

/-! ## Structural correctness of the oriented constructors -/

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype Memory] in
theorem ownerFibreRightEntryLiveState_atKey
    (key : RootKey A strategy)
    (rightState : BankControl (Memory := Memory) A strategy)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightOwner : (rightReceiver.1.memberController A false).Control)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (packet : Packet (Memory := Memory) A strategy)
    (leftMove : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hstate : rightState.AtKey A strategy key)
    (hpacket : packet.AtKey A strategy key) :
    ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyLiveStateAtKey
      (Memory := Memory) A strategy key
      (ownerFibreRightEntryLiveState (Memory := Memory) A strategy rightState
        rightReceiver rightOwner leftTemplate packet leftMove) := by
  exact
    ⟨⟨hstate, hstate, hpacket⟩,
      ⟨⟨hstate, by
          intro candidate hc
          cases Option.some.inj hc
          exact hpacket⟩,
        hstate, hpacket⟩⟩

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype Memory] in
theorem ownerFibreLeftEntryLiveState_atKey
    (key : RootKey A strategy)
    (leftState : BankControl (Memory := Memory) A strategy)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (leftOwner : (leftReceiver.1.memberController A false).Control)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (packet : Packet (Memory := Memory) A strategy)
    (rightMove : ProfiledRawJointRightPhysicalSiblingMove A)
    (hstate : leftState.AtKey A strategy key)
    (hpacket : packet.AtKey A strategy key) :
    ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyLiveStateAtKey
      (Memory := Memory) A strategy key
      (ownerFibreLeftEntryLiveState (Memory := Memory) A strategy leftState
        leftReceiver leftOwner rightTemplate packet rightMove) := by
  exact
    ⟨⟨⟨hstate, by
          intro candidate hc
          cases Option.some.inj hc
          exact hpacket⟩,
        hpacket, hstate⟩,
      ⟨hstate, hpacket, hstate⟩⟩

omit [Fintype Memory] [Inhabited Out₁] [Inhabited Out₂] in
theorem ownerFibreRightEntryLiveState_decodes
    (rightState : BankControl (Memory := Memory) A strategy)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightOwner : (rightReceiver.1.memberController A false).Control)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (packet : Packet (Memory := Memory) A strategy)
    (leftMove : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hmove : packet.successor.2.1.1.2.2 = some leftMove) :
    ProfiledRawJointRecurrentFiniteMemoryOwnerFibreDecodes
      (Memory := Memory) A strategy
      (ownerFibreRightEntryLiveState (Memory := Memory) A strategy rightState
        rightReceiver rightOwner leftTemplate packet leftMove).1.1
      (ownerFibreRightEntryLiveState (Memory := Memory) A strategy rightState
        rightReceiver rightOwner leftTemplate packet leftMove).1.2 := by
  exact
    profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?_entry
      (Memory := Memory) A strategy rightState rightReceiver rightOwner
        leftTemplate packet leftMove hmove

omit [Fintype Memory] [Inhabited Out₁] [Inhabited Out₂] in
theorem ownerFibreLeftEntryLiveState_decodes
    (leftState : BankControl (Memory := Memory) A strategy)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (leftOwner : (leftReceiver.1.memberController A false).Control)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (packet : Packet (Memory := Memory) A strategy)
    (rightMove : ProfiledRawJointRightPhysicalSiblingMove A)
    (hmove : packet.successor.2.1.1.2.1 = some rightMove) :
    ProfiledRawJointRecurrentFiniteMemoryOwnerFibreDecodes
      (Memory := Memory) A strategy
      (ownerFibreLeftEntryLiveState (Memory := Memory) A strategy leftState
        leftReceiver leftOwner rightTemplate packet rightMove).1.1
      (ownerFibreLeftEntryLiveState (Memory := Memory) A strategy leftState
        leftReceiver leftOwner rightTemplate packet rightMove).1.2 := by
  exact
    profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?_entry
      (Memory := Memory) A strategy leftState leftReceiver leftOwner
        rightTemplate packet rightMove hmove

/-! ## Exact canonical-entry predicate and its finite image -/

/-- Exact right-oriented image of the honest finite front at one fixed key.
The opposite move is read from the selected packet successor and also fixes
the DPA coordinate. -/
def IsOwnerFibreRightHonestEntryAt
    (key : RootKey A strategy)
    (state : LiveState (Memory := Memory) A strategy) : Prop :=
  ∃ (rightMove : ProfiledRawJointRightPhysicalSiblingMove A)
      (row : PairedEntryRow)
      (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
      (input : In₁ × In₂)
      (leftMove : ProfiledRawJointLeftPhysicalSiblingMove A),
    key.1.2.1 = some rightMove ∧
      profiledRawJointOneSidedCurrentSlots A .right key.1.1 () =
        some (.inl rightMove.1.source) ∧
      let rightState := selection.root A strategy hwin initialMemory key
      let rightReceiver :=
        initialProfiledRawJointRightPhysicalSiblingReceiver A rightMove row
      let rightOwner := (rightMove.memberController A false).initial
      let data :
          ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData
            (Memory := Memory) A strategy :=
        (rightState, ⟨rightReceiver, rightOwner⟩, leftTemplate)
      let packet := selection.resolvePacket A strategy hwin initialMemory
        rightState
        (data.target (Memory := Memory) A strategy input)
      packet.successor.2.1.1.2.2 = some leftMove ∧
        state = ownerFibreRightEntryLiveState (Memory := Memory) A strategy
          rightState rightReceiver rightOwner leftTemplate
            packet leftMove

/-- Mirrored exact image. -/
def IsOwnerFibreLeftHonestEntryAt
    (key : RootKey A strategy)
    (state : LiveState (Memory := Memory) A strategy) : Prop :=
  ∃ (leftMove : ProfiledRawJointLeftPhysicalSiblingMove A)
      (row : PairedEntryRow)
      (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
      (input : In₁ × In₂)
      (rightMove : ProfiledRawJointRightPhysicalSiblingMove A),
    key.1.2.2 = some leftMove ∧
      profiledRawJointOneSidedCurrentSlots A .left key.1.1 () =
        some (.inr leftMove.1.source) ∧
      let leftState := selection.root A strategy hwin initialMemory key
      let leftReceiver :=
        initialProfiledRawJointLeftPhysicalSiblingReceiver A leftMove row
      let leftOwner := (leftMove.memberController A false).initial
      let data :
          ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData
            (Memory := Memory) A strategy :=
        (leftState, ⟨leftReceiver, leftOwner⟩, rightTemplate)
      let packet := selection.resolvePacket A strategy hwin initialMemory
        leftState
        (data.target (Memory := Memory) A strategy input)
      packet.successor.2.1.1.2.1 = some rightMove ∧
        state = ownerFibreLeftEntryLiveState (Memory := Memory) A strategy
          leftState leftReceiver leftOwner rightTemplate packet
            rightMove

def IsOwnerFibreHonestEntryAt
    (key : RootKey A strategy)
    (state : LiveState (Memory := Memory) A strategy) : Prop :=
  selection.IsOwnerFibreRightHonestEntryAt A strategy hwin initialMemory key
      state ∨
    selection.IsOwnerFibreLeftHonestEntryAt A strategy hwin initialMemory key
      state

/-- Quantifier-order interface for the future choice automaton: the universal
front context is selected from a finite type that does not mention
`selection`; only its realized live entry depends on the selected packet. -/
theorem isOwnerFibreHonestEntryAt_iff_exists_frontContext
    (key : RootKey A strategy)
    (state : LiveState (Memory := Memory) A strategy) :
    selection.IsOwnerFibreHonestEntryAt A strategy hwin initialMemory key
        state ↔
      ∃ context :
          ProfiledRawJointRecurrentFiniteMemoryOwnerFibreFrontContextAt A
            strategy key,
        selection.RealizesOwnerFibreFrontContextAt A strategy hwin
          initialMemory key context state := by
  constructor
  · rintro (hright | hleft)
    · rcases hright with
        ⟨rightMove, row, leftTemplate, input, leftMove, hinstalled,
          hroot, hpacket, hstate⟩
      let parameter :
          ProfiledRawJointRecurrentFiniteMemoryOwnerFibreRightFrontParameter
            A :=
        ⟨rightMove, row, leftTemplate, input⟩
      let context :
          ProfiledRawJointRecurrentFiniteMemoryOwnerFibreRightFrontContextAt
            A strategy key :=
        ⟨parameter, hinstalled, hroot⟩
      refine ⟨.inl context, ?_⟩
      exact ⟨leftMove, hpacket, hstate⟩
    · rcases hleft with
        ⟨leftMove, row, rightTemplate, input, rightMove, hinstalled,
          hroot, hpacket, hstate⟩
      let parameter :
          ProfiledRawJointRecurrentFiniteMemoryOwnerFibreLeftFrontParameter
            A :=
        ⟨leftMove, row, rightTemplate, input⟩
      let context :
          ProfiledRawJointRecurrentFiniteMemoryOwnerFibreLeftFrontContextAt
            A strategy key :=
        ⟨parameter, hinstalled, hroot⟩
      refine ⟨.inr context, ?_⟩
      exact ⟨rightMove, hpacket, hstate⟩
  · rintro ⟨context, hcontext⟩
    rcases context with context | context
    · rcases context with ⟨parameter, hinstalled, hroot⟩
      rcases parameter with ⟨rightMove, row, leftTemplate, input⟩
      rcases hcontext with ⟨leftMove, hpacket, hstate⟩
      exact Or.inl
        ⟨rightMove, row, leftTemplate, input, leftMove, hinstalled, hroot,
          hpacket, hstate⟩
    · rcases context with ⟨parameter, hinstalled, hroot⟩
      rcases parameter with ⟨leftMove, row, rightTemplate, input⟩
      rcases hcontext with ⟨rightMove, hpacket, hstate⟩
      exact Or.inr
        ⟨leftMove, row, rightTemplate, input, rightMove, hinstalled, hroot,
          hpacket, hstate⟩

/-- All and only canonical live entries at `key`.  Finiteness comes from the
runtime state space; the defining predicate retains the exact front image. -/
noncomputable def ownerFibreHonestEntriesAt
    (key : RootKey A strategy) :
    Finset (LiveState (Memory := Memory) A strategy) := by
  classical
  letI : Fintype A.State := A.stateFinite
  exact Finset.univ.filter fun state ↦
    selection.IsOwnerFibreHonestEntryAt A strategy hwin initialMemory key state

@[simp] theorem mem_ownerFibreHonestEntriesAt
    (key : RootKey A strategy)
    (state : LiveState (Memory := Memory) A strategy) :
    state ∈ selection.ownerFibreHonestEntriesAt A strategy hwin initialMemory
        key ↔
      selection.IsOwnerFibreHonestEntryAt A strategy hwin initialMemory key
        state := by
  classical
  letI : Fintype A.State := A.stateFinite
  constructor
  · intro hmem
    exact (Finset.mem_filter.mp hmem).2
  · intro hentry
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ state, hentry⟩

theorem mem_ownerFibreHonestEntriesAt_iff_exists_frontContext
    (key : RootKey A strategy)
    (state : LiveState (Memory := Memory) A strategy) :
    state ∈ selection.ownerFibreHonestEntriesAt A strategy hwin initialMemory
        key ↔
      ∃ context :
          ProfiledRawJointRecurrentFiniteMemoryOwnerFibreFrontContextAt A
            strategy key,
        selection.RealizesOwnerFibreFrontContextAt A strategy hwin
          initialMemory key context state := by
  rw [selection.mem_ownerFibreHonestEntriesAt A strategy hwin initialMemory
    key state]
  exact selection.isOwnerFibreHonestEntryAt_iff_exists_frontContext A strategy
    hwin initialMemory key state

theorem mem_ownerFibreHonestEntriesAt_iff_exists_eq_liveState
    (key : RootKey A strategy)
    (state : LiveState (Memory := Memory) A strategy) :
    state ∈ selection.ownerFibreHonestEntriesAt A strategy hwin initialMemory
        key ↔
      ∃ context :
          ProfiledRawJointRecurrentFiniteMemoryOwnerFibreFrontContextAt A
            strategy key,
        state = selection.ownerFibreFrontContextLiveState A strategy hwin
          initialMemory key context := by
  rw [selection.mem_ownerFibreHonestEntriesAt_iff_exists_frontContext A
    strategy hwin initialMemory key state]
  constructor
  · rintro ⟨context, hrealizes⟩
    exact ⟨context,
      (selection.realizesOwnerFibreFrontContextAt_iff_eq_liveState A strategy
        hwin initialMemory key context state).mp hrealizes⟩
  · rintro ⟨context, hstate⟩
    exact ⟨context,
      (selection.realizesOwnerFibreFrontContextAt_iff_eq_liveState A strategy
        hwin initialMemory key context state).mpr hstate⟩

/-- Exact emptiness audit.  The selected live-entry set is empty precisely
when the selection-free front-context type is empty.  The forward implication
uses the context witness stored by membership; the reverse implication uses
installed-table target closure, not a default packet or arbitrary DPA state.
-/
theorem ownerFibreHonestEntriesAt_nonempty_iff
    (key : RootKey A strategy) :
    (selection.ownerFibreHonestEntriesAt A strategy hwin initialMemory key
        ).Nonempty ↔
      Nonempty
        (ProfiledRawJointRecurrentFiniteMemoryOwnerFibreFrontContextAt A
          strategy key) := by
  constructor
  · rintro ⟨state, hmem⟩
    obtain ⟨context, _hrealizes⟩ :=
      (selection.mem_ownerFibreHonestEntriesAt_iff_exists_frontContext A
        strategy hwin initialMemory key state).mp hmem
    exact ⟨context⟩
  · rintro ⟨context⟩
    obtain ⟨state, hrealizes⟩ :=
      selection.ownerFibreFrontContext_realizes A strategy hwin initialMemory
        key context
    exact ⟨state,
      (selection.mem_ownerFibreHonestEntriesAt_iff_exists_frontContext A
        strategy hwin initialMemory key state).mpr ⟨context, hrealizes⟩⟩

/-- The exact safety obligation at one key.  This applies the already compiled
output-aware product to precisely the selected realizations of the
selection-free front contexts. -/
def OwnerFibreSafeOnHonestEntriesAt
    (key : RootKey A strategy) : Prop :=
  selection.OwnerFibreSafeOn A strategy hwin initialMemory
    (selection.ownerFibreHonestEntriesAt A strategy hwin initialMemory key)

theorem ownerFibreSafeOnHonestEntriesAt_iff
    (key : RootKey A strategy) :
    selection.OwnerFibreSafeOnHonestEntriesAt A strategy hwin initialMemory
        key ↔
      ∀ (context :
          ProfiledRawJointRecurrentFiniteMemoryOwnerFibreFrontContextAt A
            strategy key)
        (state : LiveState (Memory := Memory) A strategy),
        selection.RealizesOwnerFibreFrontContextAt A strategy hwin
            initialMemory key context state →
          selection.OwnerFibreSafe A strategy hwin initialMemory state := by
  constructor
  · intro hsafe context state hrealizes
    apply hsafe state
    exact
      (selection.mem_ownerFibreHonestEntriesAt_iff_exists_frontContext A
        strategy hwin initialMemory key state).mpr ⟨context, hrealizes⟩
  · intro hsafe state hmem
    obtain ⟨context, hrealizes⟩ :=
      (selection.mem_ownerFibreHonestEntriesAt_iff_exists_frontContext A
        strategy hwin initialMemory key state).mp hmem
    exact hsafe context state hrealizes

/-- Membership fixes every stored bank coordinate to the advertised key. -/
theorem ownerFibreHonestEntriesAt_liveStateAtKey
    (key : RootKey A strategy)
    (state : LiveState (Memory := Memory) A strategy)
    (hmem : state ∈
      selection.ownerFibreHonestEntriesAt A strategy hwin initialMemory key) :
    ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyLiveStateAtKey
      (Memory := Memory) A strategy key state := by
  have hentry :=
    (selection.mem_ownerFibreHonestEntriesAt A strategy hwin initialMemory key
      state).mp hmem
  rcases hentry with hright | hleft
  · rcases hright with
      ⟨rightMove, row, leftTemplate, input, leftMove, _hinstalled,
        _hroot, hmove, hstate⟩
    subst state
    apply ownerFibreRightEntryLiveState_atKey (Memory := Memory) A strategy
      key
    · rfl
    · rfl
  · rcases hleft with
      ⟨leftMove, row, rightTemplate, input, rightMove, _hinstalled,
        _hroot, hmove, hstate⟩
    subst state
    apply ownerFibreLeftEntryLiveState_atKey (Memory := Memory) A strategy key
    · rfl
    · rfl

/-- Every canonical entry starts in a genuinely decoded orientation. -/
theorem ownerFibreHonestEntriesAt_decodes
    (key : RootKey A strategy)
    (state : LiveState (Memory := Memory) A strategy)
    (hmem : state ∈
      selection.ownerFibreHonestEntriesAt A strategy hwin initialMemory key) :
    ProfiledRawJointRecurrentFiniteMemoryOwnerFibreDecodes
      (Memory := Memory) A strategy state.1.1 state.1.2 := by
  have hentry :=
    (selection.mem_ownerFibreHonestEntriesAt A strategy hwin initialMemory key
      state).mp hmem
  rcases hentry with hright | hleft
  · rcases hright with
      ⟨rightMove, row, leftTemplate, input, leftMove, _hinstalled,
        _hroot, hmove, hstate⟩
    subst state
    exact ownerFibreRightEntryLiveState_decodes (Memory := Memory) A strategy
      _ _ _ _ _ _ hmove
  · rcases hleft with
      ⟨leftMove, row, rightTemplate, input, rightMove, _hinstalled,
        _hroot, hmove, hstate⟩
    subst state
    exact ownerFibreLeftEntryLiveState_decodes (Memory := Memory) A strategy
      _ _ _ _ _ _ hmove

/-- The DPA coordinate of a canonical entry has an exact opposite-move
witness.  This rules out the unsound Cartesian product with all states of
`A`. -/
theorem ownerFibreHonestEntriesAt_dpa_exact
    (key : RootKey A strategy)
    (state : LiveState (Memory := Memory) A strategy)
    (hmem : state ∈
      selection.ownerFibreHonestEntriesAt A strategy hwin initialMemory key) :
    (∃ leftMove : ProfiledRawJointLeftPhysicalSiblingMove A,
        state.2 = ownerFibreRightEntryDPAState A leftMove) ∨
      ∃ rightMove : ProfiledRawJointRightPhysicalSiblingMove A,
        state.2 = ownerFibreLeftEntryDPAState A rightMove := by
  have hentry :=
    (selection.mem_ownerFibreHonestEntriesAt A strategy hwin initialMemory key
      state).mp hmem
  rcases hentry with hright | hleft
  · rcases hright with
      ⟨rightMove, row, leftTemplate, input, leftMove, _hinstalled,
        _hroot, hmove, hstate⟩
    subst state
    exact Or.inl ⟨leftMove, rfl⟩
  · rcases hleft with
      ⟨leftMove, row, rightTemplate, input, rightMove, _hinstalled,
        _hroot, hmove, hstate⟩
    subst state
    exact Or.inr ⟨rightMove, rfl⟩

end
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection

end

end DetParityAutomaton

end DistributedSynthesis
