/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatiblePolicyBankLocalBoundary
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointFinitePhysicalSiblingTargetSynchronization
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleLocalCarrier

/-!
# Total local controller for the recurrent physical policy bank

The endpoint controls at a recurrent block boundary have four reachable
selected shapes.  In the right orientation, process one has an installed
right owner and process two has either an explicit staged right receiver or a
deferred right receiver.  The left orientation is the mirror image.  This
file first decodes those shapes into aligned dependent owner/receiver data.
The decoder inspects only finite controls and equality of finite moves.

Semantic reachability will be imposed as a proposition on the decoded data;
it is not an argument to the executable decoder.
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

/-! ## Aligned finite boundary data -/

/-- All runtime data needed to execute one right-oriented boundary round.
The dependent pair stores a receiver together with an owner control for that
receiver's exact move, so no unchecked cast remains. -/
noncomputable abbrev ProfiledRawJointRecurrentRightBoundaryData :=
  BankControl A strategy hwin ×
    (Sigma fun receiver : ProfiledRawJointRightPhysicalSiblingReceiver A ↦
      (receiver.1.memberController A false).Control) ×
    ProfiledRawJointLeftPhysicalSiblingReceiver A

/-- Left-oriented mirror. -/
noncomputable abbrev ProfiledRawJointRecurrentLeftBoundaryData :=
  BankControl A strategy hwin ×
    (Sigma fun receiver : ProfiledRawJointLeftPhysicalSiblingReceiver A ↦
      (receiver.1.memberController A false).Control) ×
    ProfiledRawJointRightPhysicalSiblingReceiver A

noncomputable def ProfiledRawJointRecurrentRightBoundaryData.receiver
    (data : ProfiledRawJointRecurrentRightBoundaryData A strategy hwin) :
    ProfiledRawJointRightPhysicalSiblingReceiver A :=
  data.2.1.1

noncomputable def ProfiledRawJointRecurrentRightBoundaryData.owner
    (data : ProfiledRawJointRecurrentRightBoundaryData A strategy hwin) :
    ((data.receiver A strategy hwin).1.memberController A false).Control :=
  data.2.1.2

noncomputable def ProfiledRawJointRecurrentLeftBoundaryData.receiver
    (data : ProfiledRawJointRecurrentLeftBoundaryData A strategy hwin) :
    ProfiledRawJointLeftPhysicalSiblingReceiver A :=
  data.2.1.1

noncomputable def ProfiledRawJointRecurrentLeftBoundaryData.owner
    (data : ProfiledRawJointRecurrentLeftBoundaryData A strategy hwin) :
    ((data.receiver A strategy hwin).1.memberController A false).Control :=
  data.2.1.2

/-! ## Shape decoders -/

/-- Align an explicit right owner and right receiver. -/
private noncomputable def profiledRawJointRecurrentAlignRight?
    (state : BankControl A strategy hwin)
    (owner : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (receiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A) :
    Option (ProfiledRawJointRecurrentRightBoundaryData A strategy hwin) := by
  classical
  rcases owner with ⟨ownerMove, ownerControl⟩
  rcases receiver with ⟨receiverMove, row, receiverState, target⟩
  by_cases hmove : receiverMove = ownerMove
  · subst receiverMove
    exact some
      (state, ⟨⟨ownerMove, row, receiverState, target⟩, ownerControl⟩,
        oldReceiver)
  · exact none

/-- Align an explicit left owner and left receiver. -/
private noncomputable def profiledRawJointRecurrentAlignLeft?
    (state : BankControl A strategy hwin)
    (owner : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (receiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A) :
    Option (ProfiledRawJointRecurrentLeftBoundaryData A strategy hwin) := by
  classical
  rcases owner with ⟨ownerMove, ownerControl⟩
  rcases receiver with ⟨receiverMove, row, receiverState, target⟩
  by_cases hmove : receiverMove = ownerMove
  · subst receiverMove
    exact some
      (state, ⟨⟨ownerMove, row, receiverState, target⟩, ownerControl⟩,
        oldReceiver)
  · exact none

/-- Decode the two reachable right-oriented shapes.  In the explicit shape
the receiver-side bridge supplies the bank state.  In the deferred shape the
installed owner bridge supplies it, and the proof-side member selects the old
or fresh receiver exactly as prescribed by the acknowledged handoff. -/
noncomputable def profiledRawJointRecurrentRightBoundaryData?
    (one : ProfiledRawJointRecurrentBoundaryOneControl A strategy hwin)
    (two : ProfiledRawJointRecurrentBoundaryTwoControl A strategy hwin) :
    Option (ProfiledRawJointRecurrentRightBoundaryData A strategy hwin) :=
  match one, two with
  | .inl (.inr installed), .inl (.inl staged) =>
      profiledRawJointRecurrentAlignRight? A strategy hwin staged.1
        installed.2.1 staged.2.1 installed.2.2
  | .inl (.inr installed), .inr deferred =>
      let receiver := if deferred.1 then
          initialProfiledRawJointRightPhysicalSiblingReceiver A
            installed.2.1.1 .both
        else deferred.2.2
      profiledRawJointRecurrentAlignRight? A strategy hwin installed.1
        installed.2.1 receiver installed.2.2
  | _, _ => none

/-- Decode the two reachable left-oriented shapes. -/
noncomputable def profiledRawJointRecurrentLeftBoundaryData?
    (one : ProfiledRawJointRecurrentBoundaryOneControl A strategy hwin)
    (two : ProfiledRawJointRecurrentBoundaryTwoControl A strategy hwin) :
    Option (ProfiledRawJointRecurrentLeftBoundaryData A strategy hwin) :=
  match one, two with
  | .inl (.inl staged), .inl (.inr installed) =>
      profiledRawJointRecurrentAlignLeft? A strategy hwin staged.1
        installed.2.1 staged.2.1 installed.2.2
  | .inr deferred, .inl (.inr installed) =>
      let receiver := if deferred.1 then
          initialProfiledRawJointLeftPhysicalSiblingReceiver A
            installed.2.1.1 .both
        else deferred.2.2
      profiledRawJointRecurrentAlignLeft? A strategy hwin installed.1
        installed.2.1 receiver installed.2.2
  | _, _ => none

/-! ## Canonical decoder equations -/

@[simp] theorem profiledRawJointRecurrentRightBoundaryData?_explicit
    (stateOne stateTwo : BankControl A strategy hwin)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (row : PairedEntryRow)
    (receiverState :
      (profiledRawJointRightPhysicalSiblingMonitor A move.1 false).State)
    (target : Option (ProfiledRawJointUnitTarget A))
    (stagedPacket : Option
      (ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin))
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A) :
    profiledRawJointRecurrentRightBoundaryData? A strategy hwin
      (.inl (.inr
        (stateOne,
          (⟨move, owner⟩ : ProfiledRawJointRightPhysicalSiblingExceptional A),
          oldReceiver)))
      (.inl (.inl
        (stateTwo,
          (⟨move, row, receiverState, target⟩ :
            ProfiledRawJointRightPhysicalSiblingReceiver A), stagedPacket))) =
      some
        (stateTwo, ⟨⟨move, row, receiverState, target⟩, owner⟩,
          oldReceiver) :=
  by simp [profiledRawJointRecurrentRightBoundaryData?,
    profiledRawJointRecurrentAlignRight?]

@[simp] theorem profiledRawJointRecurrentRightBoundaryData?_deferred_false
    (state : BankControl A strategy hwin)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (row : PairedEntryRow)
    (receiverState :
      (profiledRawJointRightPhysicalSiblingMonitor A move.1 false).State)
    (target : Option (ProfiledRawJointUnitTarget A))
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (oldOwner : ProfiledRawJointLeftPhysicalSiblingExceptional A) :
    profiledRawJointRecurrentRightBoundaryData? A strategy hwin
      (.inl (.inr
        (state,
          (⟨move, owner⟩ : ProfiledRawJointRightPhysicalSiblingExceptional A),
          oldReceiver)))
      (.inr
        (false, oldOwner,
          (⟨move, row, receiverState, target⟩ :
            ProfiledRawJointRightPhysicalSiblingReceiver A))) =
      some
        (state, ⟨⟨move, row, receiverState, target⟩, owner⟩,
          oldReceiver) :=
  by simp [profiledRawJointRecurrentRightBoundaryData?,
    profiledRawJointRecurrentAlignRight?]

@[simp] theorem profiledRawJointRecurrentRightBoundaryData?_deferred_true
    (state : BankControl A strategy hwin)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (oldOwner : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (payload : ProfiledRawJointRightPhysicalSiblingReceiver A) :
    profiledRawJointRecurrentRightBoundaryData? A strategy hwin
      (.inl (.inr
        (state,
          (⟨move, owner⟩ : ProfiledRawJointRightPhysicalSiblingExceptional A),
          oldReceiver)))
      (.inr (true, oldOwner, payload)) =
      some
        (state,
          ⟨initialProfiledRawJointRightPhysicalSiblingReceiver A move .both,
            owner⟩,
          oldReceiver) :=
  by simp [profiledRawJointRecurrentRightBoundaryData?,
    profiledRawJointRecurrentAlignRight?,
    initialProfiledRawJointRightPhysicalSiblingReceiver]

@[simp] theorem profiledRawJointRecurrentLeftBoundaryData?_explicit
    (stateOne stateTwo : BankControl A strategy hwin)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (row : PairedEntryRow)
    (receiverState :
      (profiledRawJointLeftPhysicalSiblingMonitor A move.1 false).State)
    (target : Option (ProfiledRawJointUnitTarget A))
    (stagedPacket : Option
      (ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin))
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A) :
    profiledRawJointRecurrentLeftBoundaryData? A strategy hwin
      (.inl (.inl
        (stateOne,
          (⟨move, row, receiverState, target⟩ :
            ProfiledRawJointLeftPhysicalSiblingReceiver A), stagedPacket)))
      (.inl (.inr
        (stateTwo,
          (⟨move, owner⟩ : ProfiledRawJointLeftPhysicalSiblingExceptional A),
          oldReceiver))) =
      some
        (stateOne, ⟨⟨move, row, receiverState, target⟩, owner⟩,
          oldReceiver) :=
  by simp [profiledRawJointRecurrentLeftBoundaryData?,
    profiledRawJointRecurrentAlignLeft?]

@[simp] theorem profiledRawJointRecurrentLeftBoundaryData?_deferred_false
    (state : BankControl A strategy hwin)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (row : PairedEntryRow)
    (receiverState :
      (profiledRawJointLeftPhysicalSiblingMonitor A move.1 false).State)
    (target : Option (ProfiledRawJointUnitTarget A))
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (oldOwner : ProfiledRawJointRightPhysicalSiblingExceptional A) :
    profiledRawJointRecurrentLeftBoundaryData? A strategy hwin
      (.inr
        (false, oldOwner,
          (⟨move, row, receiverState, target⟩ :
            ProfiledRawJointLeftPhysicalSiblingReceiver A)))
      (.inl (.inr
        (state,
          (⟨move, owner⟩ : ProfiledRawJointLeftPhysicalSiblingExceptional A),
          oldReceiver))) =
      some
        (state, ⟨⟨move, row, receiverState, target⟩, owner⟩,
          oldReceiver) :=
  by simp [profiledRawJointRecurrentLeftBoundaryData?,
    profiledRawJointRecurrentAlignLeft?]

@[simp] theorem profiledRawJointRecurrentLeftBoundaryData?_deferred_true
    (state : BankControl A strategy hwin)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (oldOwner : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (payload : ProfiledRawJointLeftPhysicalSiblingReceiver A) :
    profiledRawJointRecurrentLeftBoundaryData? A strategy hwin
      (.inr (true, oldOwner, payload))
      (.inl (.inr
        (state,
          (⟨move, owner⟩ : ProfiledRawJointLeftPhysicalSiblingExceptional A),
          oldReceiver))) =
      some
        (state,
          ⟨initialProfiledRawJointLeftPhysicalSiblingReceiver A move .both,
            owner⟩,
          oldReceiver) :=
  by simp [profiledRawJointRecurrentLeftBoundaryData?,
    profiledRawJointRecurrentAlignLeft?,
    initialProfiledRawJointLeftPhysicalSiblingReceiver]

/-! ## Total receive and exact-close maps -/

noncomputable def ProfiledRawJointRecurrentRightBoundaryData.receive
    (data : ProfiledRawJointRecurrentRightBoundaryData A strategy hwin)
    (input : In₁ × In₂) :=
  profiledRawJointRecurrentRightToLeftBoundaryReceive A strategy hwin data.1
    (data.receiver A strategy hwin) (data.owner A strategy hwin) data.2.2 input

noncomputable def ProfiledRawJointRecurrentLeftBoundaryData.receive
    (data : ProfiledRawJointRecurrentLeftBoundaryData A strategy hwin)
    (input : In₁ × In₂) :=
  profiledRawJointRecurrentLeftToRightBoundaryReceive A strategy hwin data.1
    (data.receiver A strategy hwin) (data.owner A strategy hwin) data.2.2 input

/-- Decode one oriented boundary and execute both endpoint-local fork
constructions.  Right-oriented shapes have priority only in the impossible
totalization case where both decoders succeed. -/
noncomputable def profiledRawJointRecurrentBoundaryReceive?
    (one : ProfiledRawJointRecurrentBoundaryOneControl A strategy hwin)
    (two : ProfiledRawJointRecurrentBoundaryTwoControl A strategy hwin)
    (input : In₁ × In₂) :
    Option
      ((FiniteDelayedFork
          (ProfiledRawJointRecurrentBoundaryOneControl A strategy hwin) ×
            Out₁) ×
        (FiniteDelayedFork
          (ProfiledRawJointRecurrentBoundaryTwoControl A strategy hwin) ×
            Out₂)) :=
  match profiledRawJointRecurrentRightBoundaryData? A strategy hwin one two with
  | some data => some (data.receive A strategy hwin input)
  | none =>
      match profiledRawJointRecurrentLeftBoundaryData? A strategy hwin one two
          with
      | some data => some (data.receive A strategy hwin input)
      | none => none

/-- Total process-one open receive.  Outside the selected relation it falls
back to the ordinary local no-receive step; no correctness claim is made for
that unreachable branch. -/
noncomputable def profiledRawJointRecurrentBoundaryOpenRecvOne
    (one : ProfiledRawJointRecurrentBoundaryOneControl A strategy hwin)
    (inputOne : In₁)
    (two : ProfiledRawJointRecurrentBoundaryTwoControl A strategy hwin)
    (inputTwo : In₂) :
    ProfiledRawJointRecurrentBoundaryOneControl A strategy hwin × Out₁ :=
  match profiledRawJointRecurrentBoundaryReceive? A strategy hwin one two
      (inputOne, inputTwo) with
  | some result => (result.1.1.openControl, result.1.2)
  | none =>
      profiledRawJointRecurrentBoundaryNoRecvOne A strategy hwin one inputOne

/-- Total process-two open receive. -/
noncomputable def profiledRawJointRecurrentBoundaryOpenRecvTwo
    (two : ProfiledRawJointRecurrentBoundaryTwoControl A strategy hwin)
    (inputTwo : In₂)
    (one : ProfiledRawJointRecurrentBoundaryOneControl A strategy hwin)
    (inputOne : In₁) :
    ProfiledRawJointRecurrentBoundaryTwoControl A strategy hwin × Out₂ :=
  match profiledRawJointRecurrentBoundaryReceive? A strategy hwin one two
      (inputOne, inputTwo) with
  | some result => (result.2.1.openControl, result.2.2)
  | none =>
      profiledRawJointRecurrentBoundaryNoRecvTwo A strategy hwin two inputTwo

/-- The exact joint continuation selects the closed candidate of the same
two local forks used by the open maps. -/
noncomputable def profiledRawJointRecurrentBoundaryClose
    (one : ProfiledRawJointRecurrentBoundaryOneControl A strategy hwin)
    (inputOne : In₁)
    (two : ProfiledRawJointRecurrentBoundaryTwoControl A strategy hwin)
    (inputTwo : In₂) :
    ProfiledRawJointRecurrentBoundaryOneControl A strategy hwin ×
      ProfiledRawJointRecurrentBoundaryTwoControl A strategy hwin :=
  match profiledRawJointRecurrentBoundaryReceive? A strategy hwin one two
      (inputOne, inputTwo) with
  | some result =>
      (result.1.1.closedControl, result.2.1.closedControl)
  | none =>
      ((profiledRawJointRecurrentBoundaryNoRecvOne A strategy hwin one
        inputOne).1,
       (profiledRawJointRecurrentBoundaryNoRecvTwo A strategy hwin two
        inputTwo).1)

theorem profiledRawJointRecurrentBoundaryReceive?_of_right
    (one : ProfiledRawJointRecurrentBoundaryOneControl A strategy hwin)
    (two : ProfiledRawJointRecurrentBoundaryTwoControl A strategy hwin)
    (data : ProfiledRawJointRecurrentRightBoundaryData A strategy hwin)
    (hdata : profiledRawJointRecurrentRightBoundaryData? A strategy hwin one
      two = some data)
    (input : In₁ × In₂) :
    profiledRawJointRecurrentBoundaryReceive? A strategy hwin one two input =
      some (data.receive A strategy hwin input) := by
  simp [profiledRawJointRecurrentBoundaryReceive?, hdata]

theorem profiledRawJointRecurrentBoundaryReceive?_of_left
    (one : ProfiledRawJointRecurrentBoundaryOneControl A strategy hwin)
    (two : ProfiledRawJointRecurrentBoundaryTwoControl A strategy hwin)
    (data : ProfiledRawJointRecurrentLeftBoundaryData A strategy hwin)
    (hright : profiledRawJointRecurrentRightBoundaryData? A strategy hwin one
      two = none)
    (hdata : profiledRawJointRecurrentLeftBoundaryData? A strategy hwin one
      two = some data)
    (input : In₁ × In₂) :
    profiledRawJointRecurrentBoundaryReceive? A strategy hwin one two input =
      some (data.receive A strategy hwin input) := by
  simp [profiledRawJointRecurrentBoundaryReceive?, hright, hdata]

/-! ## Closure-shape audit -/

/-- Neither original oriented decoder accepts a pair in which both endpoints
are deferred.  Such a pair is produced by an immediate direction change
after a closed boundary, so this exact negative lemma prevents us from
mistaking the one-round receive laws below for a recurrent controller. -/
theorem profiledRawJointRecurrentBoundaryDecoder_deferredDeferred_gap
    (one : ProfiledRawJointRecurrentRightToLeftBlindControl A)
    (two : ProfiledRawJointRecurrentLeftToRightBlindControl A) :
    profiledRawJointRecurrentRightBoundaryData? A strategy hwin (.inr one)
          (.inr two) = none ∧
      profiledRawJointRecurrentLeftBoundaryData? A strategy hwin (.inr one)
          (.inr two) = none :=
  ⟨rfl, rfl⟩

/-! ## The non-vacuous selected relation for receive closure -/

/-- A right-oriented decoded boundary is genuinely reachable when its bank
state is reachable, its current code has a live right root and carries the
decoded physical move, and the delivered owner control and receiver monitor
state are the two folds of one finite input prefix.  The prefix is proof-side
data only. -/
def ProfiledRawJointRecurrentRightBoundaryInvariant
    (data : ProfiledRawJointRecurrentRightBoundaryData A strategy hwin) : Prop :=
  let receiver := data.receiver A strategy hwin
  let move := receiver.1
  let monitor := profiledRawJointRightPhysicalSiblingMonitor A move.1 false
  let controller := move.memberController A false
  ∃ currentCode : ProfiledRawJointIncidenceCode A (I := Unit),
    ∃ root : ProfiledRawJointThreadRoot A,
      ∃ past : List (In₂ × In₁),
        ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy
            hwin data.1 ∧
          data.1.2.1.1 = currentCode ∧
          profiledRawJointOneSidedCurrentSlots A .right currentCode () =
            some root ∧
          data.1.2.1.2.1 = some move ∧
          data.owner A strategy hwin =
            controller.controlAt (senderWord past) ∧
          receiver.2.2.1 =
            narrowedControl monitor controller.labeledTree past

/-- Left-oriented mirror of the matched-prefix bank invariant. -/
def ProfiledRawJointRecurrentLeftBoundaryInvariant
    (data : ProfiledRawJointRecurrentLeftBoundaryData A strategy hwin) : Prop :=
  let receiver := data.receiver A strategy hwin
  let move := receiver.1
  let monitor := profiledRawJointLeftPhysicalSiblingMonitor A move.1 false
  let controller := move.memberController A false
  ∃ currentCode : ProfiledRawJointIncidenceCode A (I := Unit),
    ∃ root : ProfiledRawJointThreadRoot A,
      ∃ past : List (In₁ × In₂),
        ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy
            hwin data.1 ∧
          data.1.2.1.1 = currentCode ∧
          profiledRawJointOneSidedCurrentSlots A .left currentCode () =
            some root ∧
          data.1.2.1.2.2 = some move ∧
          data.owner A strategy hwin =
            controller.controlAt (senderWord past) ∧
          receiver.2.2.1 =
            narrowedControl monitor controller.labeledTree past

/-- Every target which the aligned right receiver can emit is an exact live
left child of the retained bank state. -/
def ProfiledRawJointRecurrentRightBoundaryReady
    (data : ProfiledRawJointRecurrentRightBoundaryData A strategy hwin) : Prop :=
  ∀ input : In₁ × In₂,
    let receiver := data.receiver A strategy hwin
    let target := (((receiver.1.memberController A false).labelOf
      (data.owner A strategy hwin)).2 receiver.2.2.1
        (input.2, input.1) |>.target receiver.2.1)
    ProfiledRawJointOneSidedPhysicalCompatibleBankChildRealizes A strategy
        hwin data.1 target
          (profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A
            strategy hwin data.1 target) ∧
      ∃ root : ProfiledRawJointThreadRoot A,
        profiledRawJointOneSidedCurrentSlots A .left target () = some root

/-- Left-oriented mirror. -/
def ProfiledRawJointRecurrentLeftBoundaryReady
    (data : ProfiledRawJointRecurrentLeftBoundaryData A strategy hwin) : Prop :=
  ∀ input : In₁ × In₂,
    let receiver := data.receiver A strategy hwin
    let target := (((receiver.1.memberController A false).labelOf
      (data.owner A strategy hwin)).2 receiver.2.2.1 input |>.target
        receiver.2.1)
    ProfiledRawJointOneSidedPhysicalCompatibleBankChildRealizes A strategy
        hwin data.1 target
          (profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A
            strategy hwin data.1 target) ∧
      ∃ root : ProfiledRawJointThreadRoot A,
        profiledRawJointOneSidedCurrentSlots A .right target () = some root

/-- The right matched-prefix bank invariant discharges the one-round
readiness obligation.  The bank block theorem supplies the linked child;
the physical target equation supplies the crossed live slot. -/
theorem profiledRawJointRecurrentRightBoundaryInvariant_ready
    (data : ProfiledRawJointRecurrentRightBoundaryData A strategy hwin)
    (hinvariant : ProfiledRawJointRecurrentRightBoundaryInvariant A strategy
      hwin data) :
    ProfiledRawJointRecurrentRightBoundaryReady A strategy hwin data := by
  rcases data with ⟨state, ⟨⟨move, row, receiverState, lastTarget⟩,
    owner⟩, oldReceiver⟩
  dsimp only [ProfiledRawJointRecurrentRightBoundaryInvariant,
    ProfiledRawJointRecurrentRightBoundaryData.receiver,
    ProfiledRawJointRecurrentRightBoundaryData.owner] at hinvariant ⊢
  rcases hinvariant with
    ⟨currentCode, root, past, hreachable, hcurrentCode, hroot, hmove,
      howner, hreceiverState⟩
  intro input
  let blockInput : In₂ × In₁ := (input.2, input.1)
  let env : Nat → In₂ × In₁ := omegaOfList (past ++ [blockInput])
  have hat := profiledRawJointRightPhysicalSibling_treePlay_at_prefix A move
    past blockInput
  have hblock :=
    profiledRawJointOneSidedPhysicalCompatibleBankRightBlock_target A strategy
      hwin state hreachable currentCode hcurrentCode root hroot move hmove false
        env past.length row
  have hsafe := move.memberController_targetSafe A false env past.length row
  dsimp only at hat hblock hsafe
  rw [hat] at hblock hsafe
  dsimp only [narrowedRecord] at hblock hsafe
  rw [← howner, ← hreceiverState] at hblock hsafe
  obtain ⟨slot, hslot⟩ :=
    exists_profiledRawJointLeftSlot_of_rightPhysicalTargetSafe A _ _ _ _
      hsafe.1
  have hslot' :
      (((((move.memberController A false).labelOf owner).2 receiverState
        (input.2, input.1) |>.target row).family.left ())) = some slot := by
    simpa [blockInput] using hslot
  refine ⟨hblock.2.1, Sum.inr slot, ?_⟩
  change Option.map Sum.inr
      (((((move.memberController A false).labelOf owner).2 receiverState
        (input.2, input.1) |>.target row).family.left ())) =
    some (Sum.inr slot)
  simp [hslot']

/-- Left-oriented mirror of matched-prefix readiness. -/
theorem profiledRawJointRecurrentLeftBoundaryInvariant_ready
    (data : ProfiledRawJointRecurrentLeftBoundaryData A strategy hwin)
    (hinvariant : ProfiledRawJointRecurrentLeftBoundaryInvariant A strategy
      hwin data) :
    ProfiledRawJointRecurrentLeftBoundaryReady A strategy hwin data := by
  rcases data with ⟨state, ⟨⟨move, row, receiverState, lastTarget⟩,
    owner⟩, oldReceiver⟩
  dsimp only [ProfiledRawJointRecurrentLeftBoundaryInvariant,
    ProfiledRawJointRecurrentLeftBoundaryData.receiver,
    ProfiledRawJointRecurrentLeftBoundaryData.owner] at hinvariant ⊢
  rcases hinvariant with
    ⟨currentCode, root, past, hreachable, hcurrentCode, hroot, hmove,
      howner, hreceiverState⟩
  intro input
  let env : Nat → In₁ × In₂ := omegaOfList (past ++ [input])
  have hat := profiledRawJointLeftPhysicalSibling_treePlay_at_prefix A move
    past input
  have hblock :=
    profiledRawJointOneSidedPhysicalCompatibleBankLeftBlock_target A strategy
      hwin state hreachable currentCode hcurrentCode root hroot move hmove false
        env past.length row
  have hsafe := move.memberController_targetSafe A false env past.length row
  dsimp only at hat hblock hsafe
  rw [hat] at hblock hsafe
  dsimp only [narrowedRecord] at hblock hsafe
  rw [← howner, ← hreceiverState] at hblock hsafe
  obtain ⟨slot, hslot⟩ :=
    exists_profiledRawJointRightSlot_of_leftPhysicalTargetSafe A _ _ _ _
      hsafe.1
  refine ⟨hblock.2.1, Sum.inl slot, ?_⟩
  change Option.map Sum.inl
      (((((move.memberController A false).labelOf owner).2 receiverState
        input |>.target row).family.right ())) =
    some (Sum.inl slot)
  simp [hslot]

/-- Selected endpoint controls decode to one aligned live orientation.  This
relation is deliberately not `True`: it records the exact executable shape
and the matched-prefix bank invariant from which the semantic live-child
obligation follows. -/
inductive ProfiledRawJointRecurrentBoundarySelected :
    ProfiledRawJointRecurrentBoundaryOneControl A strategy hwin →
      ProfiledRawJointRecurrentBoundaryTwoControl A strategy hwin → Prop
  | right {one two}
      (data : ProfiledRawJointRecurrentRightBoundaryData A strategy hwin)
      (hdata : profiledRawJointRecurrentRightBoundaryData? A strategy hwin one
        two = some data)
      (invariant : ProfiledRawJointRecurrentRightBoundaryInvariant A strategy hwin
        data) :
      ProfiledRawJointRecurrentBoundarySelected one two
  | left {one two}
      (data : ProfiledRawJointRecurrentLeftBoundaryData A strategy hwin)
      (hright : profiledRawJointRecurrentRightBoundaryData? A strategy hwin one
        two = none)
      (hdata : profiledRawJointRecurrentLeftBoundaryData? A strategy hwin one
        two = some data)
      (invariant : ProfiledRawJointRecurrentLeftBoundaryInvariant A strategy hwin
        data) :
      ProfiledRawJointRecurrentBoundarySelected one two

/-- The total maps create exactly the two previously compiled blind pairs on
every selected receive. -/
theorem profiledRawJointRecurrentBoundaryBlindReceiveLaws :
    FiniteAcknowledgedDelayedCarrier.ExactClosingBlindReceiveLaws
      (profiledRawJointRecurrentBoundaryOpenRecvOne A strategy hwin)
      (profiledRawJointRecurrentBoundaryOpenRecvTwo A strategy hwin)
      (profiledRawJointRecurrentBoundaryClose A strategy hwin)
      (ProfiledRawJointRecurrentBoundarySelected A strategy hwin)
      (ProfiledRawJointRecurrentBoundaryOneBlind A strategy hwin)
      (ProfiledRawJointRecurrentBoundaryTwoBlind A strategy hwin) where
  one := by
    intro one inputOne two inputTwo hselected
    cases hselected with
    | right data hdata invariant =>
        have ready :=
          profiledRawJointRecurrentRightBoundaryInvariant_ready A strategy
            hwin data invariant
        obtain ⟨hrealizes, root, hroot⟩ := ready (inputOne, inputTwo)
        have hreceive :=
          profiledRawJointRecurrentBoundaryReceive?_of_right A strategy hwin
            one two data hdata (inputOne, inputTwo)
        have hspec :=
          profiledRawJointRecurrentRightToLeftBoundaryReceive_spec A strategy
            hwin data.1 (data.receiver A strategy hwin)
              (data.owner A strategy hwin) data.2.2 (inputOne, inputTwo) _ rfl
                hrealizes root hroot
        simp only [profiledRawJointRecurrentBoundaryOpenRecvOne,
          profiledRawJointRecurrentBoundaryClose, hreceive]
        exact hspec.2.2.1
    | left data hright hdata invariant =>
        have ready :=
          profiledRawJointRecurrentLeftBoundaryInvariant_ready A strategy
            hwin data invariant
        obtain ⟨hrealizes, root, hroot⟩ := ready (inputOne, inputTwo)
        have hreceive :=
          profiledRawJointRecurrentBoundaryReceive?_of_left A strategy hwin one
            two data hright hdata (inputOne, inputTwo)
        have hspec :=
          profiledRawJointRecurrentLeftToRightBoundaryReceive_spec A strategy
            hwin data.1 (data.receiver A strategy hwin)
              (data.owner A strategy hwin) data.2.2 (inputOne, inputTwo) _ rfl
                hrealizes root hroot
        simp only [profiledRawJointRecurrentBoundaryOpenRecvOne,
          profiledRawJointRecurrentBoundaryClose, hreceive]
        exact hspec.2.2.1
  two := by
    intro one inputOne two inputTwo hselected
    cases hselected with
    | right data hdata invariant =>
        have ready :=
          profiledRawJointRecurrentRightBoundaryInvariant_ready A strategy
            hwin data invariant
        obtain ⟨hrealizes, root, hroot⟩ := ready (inputOne, inputTwo)
        have hreceive :=
          profiledRawJointRecurrentBoundaryReceive?_of_right A strategy hwin
            one two data hdata (inputOne, inputTwo)
        have hspec :=
          profiledRawJointRecurrentRightToLeftBoundaryReceive_spec A strategy
            hwin data.1 (data.receiver A strategy hwin)
              (data.owner A strategy hwin) data.2.2 (inputOne, inputTwo) _ rfl
                hrealizes root hroot
        simp only [profiledRawJointRecurrentBoundaryOpenRecvTwo,
          profiledRawJointRecurrentBoundaryClose, hreceive]
        exact hspec.2.2.2
    | left data hright hdata invariant =>
        have ready :=
          profiledRawJointRecurrentLeftBoundaryInvariant_ready A strategy
            hwin data invariant
        obtain ⟨hrealizes, root, hroot⟩ := ready (inputOne, inputTwo)
        have hreceive :=
          profiledRawJointRecurrentBoundaryReceive?_of_left A strategy hwin one
            two data hright hdata (inputOne, inputTwo)
        have hspec :=
          profiledRawJointRecurrentLeftToRightBoundaryReceive_spec A strategy
            hwin data.1 (data.receiver A strategy hwin)
              (data.owner A strategy hwin) data.2.2 (inputOne, inputTwo) _ rfl
                hrealizes root hroot
        simp only [profiledRawJointRecurrentBoundaryOpenRecvTwo,
          profiledRawJointRecurrentBoundaryClose, hreceive]
        exact hspec.2.2.2

end

end DetParityAutomaton

end DistributedSynthesis
