/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemOwnerReversalOutputAudit

/-!
# Literal dynamics of the equal-open owner pair

Both delayed-branch bits are false. A strict-left round retains this shape;
a strict-right round stages a fresh packet. Blind steps preserve the bits,
so this is not a closed two-owner cycle under strict alternation.
-/

namespace DistributedSynthesis
namespace DetParityAutomaton

universe u v x y s m
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable {Memory : Type m}
variable (A : DetParityAutomaton.{max u v x y, s}
  (RoundRecord In₁ In₂ Graph Out₁ Out₂))
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
variable (hwin : ∀ env, A.Accepts (execution strategy env))

noncomputable section

omit [Inhabited In₁] [Inhabited Out₁] [Inhabited Out₂] in
theorem rightFibre_choice_after_step_valid
    (fibre : ProfiledRawJointRightOwnerFibreControl A)
    (hvalid : ProfiledRawJointRightOwnerFibreValid A fibre) (input : In₁) :
    ProfiledRawJointRightOwnerFibreValid A
      (profiledRawJointRightOwnerFibreControlOfOwner A
        ⟨fibre.1, (profiledRawJointRightPhysicalSiblingMemberNoRecvStep A fibre.1
          false fibre.2.1 input).2⟩) := by
  obtain ⟨past, howner, _⟩ := hvalid
  have hr : ProfiledRawJointRightPhysicalSiblingOwnerReachable A fibre.1 fibre.2.1 :=
    ⟨senderWord past, howner⟩
  exact profiledRawJointRightOwnerFibreChoiceControl_valid A fibre.1 _
    (hr.step A fibre.1 fibre.2.1 input)

structure OpenOwnerPair where
  right : ProfiledRawJointRightOwnerFibreControl A
  left : ProfiledRawJointLeftOwnerFibreControl A
  leftReceivers : FiniteDelayedFork
    (ProfiledRawJointRecurrentFiniteMemoryBankedLeftReceiver
      (Memory := Memory) A strategy)
  rightReceivers : FiniteDelayedFork
    (ProfiledRawJointRecurrentFiniteMemoryBankedRightReceiver
      (Memory := Memory) A strategy)
  oneCoordinates : ProfiledRawJointRecurrentFiniteMemoryBoundaryBankCoordinates
    (Memory := Memory) A strategy
  twoCoordinates : ProfiledRawJointRecurrentFiniteMemoryBoundaryBankCoordinates
    (Memory := Memory) A strategy

structure StagedRightOwnerPair where
  state : ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankControl
    (Memory := Memory) A strategy
  receiver : ProfiledRawJointRightPhysicalSiblingReceiver A
  right : ProfiledRawJointRightOwnerFibreControl A
  leftReceivers : FiniteDelayedFork
    (ProfiledRawJointRecurrentFiniteMemoryBankedLeftReceiver
      (Memory := Memory) A strategy)
  packet : ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankResolvedTarget
    (Memory := Memory) A strategy
  oneCoordinates : ProfiledRawJointRecurrentFiniteMemoryBoundaryBankCoordinates
    (Memory := Memory) A strategy
  twoCoordinates : ProfiledRawJointRecurrentFiniteMemoryBoundaryBankCoordinates
    (Memory := Memory) A strategy

structure InstalledLeftOwnerPair where
  data : ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData
    (Memory := Memory) A strategy
  right : ProfiledRawJointRightOwnerFibreControl A
  newLeft : ProfiledRawJointRecurrentFiniteMemoryBankedLeftReceiver
    (Memory := Memory) A strategy
  oneCoordinates : ProfiledRawJointRecurrentFiniteMemoryBoundaryBankCoordinates
    (Memory := Memory) A strategy
  twoCoordinates : ProfiledRawJointRecurrentFiniteMemoryBoundaryBankCoordinates
    (Memory := Memory) A strategy

abbrev InstalledLeftOwnerPair.state (pair : InstalledLeftOwnerPair (Memory := Memory) A strategy) :=
  pair.data.1
abbrev InstalledLeftOwnerPair.receiver (pair : InstalledLeftOwnerPair (Memory := Memory) A strategy) :=
  pair.data.receiver A strategy
abbrev InstalledLeftOwnerPair.owner (pair : InstalledLeftOwnerPair (Memory := Memory) A strategy) :=
  pair.data.owner A strategy
abbrev InstalledLeftOwnerPair.template (pair : InstalledLeftOwnerPair (Memory := Memory) A strategy) :=
  pair.data.2.2

def StagedRightOwnerPair.controls
    (pair : StagedRightOwnerPair (Memory := Memory) A strategy) :
    ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
      (Memory := Memory) A strategy ×
    ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
      (Memory := Memory) A strategy :=
  ((.inr (false, (pair.right, pair.leftReceivers), ()), pair.oneCoordinates),
   (.inl (.inl (pair.state, pair.receiver, some pair.packet)), pair.twoCoordinates))

def InstalledLeftOwnerPair.controls
    (pair : InstalledLeftOwnerPair (Memory := Memory) A strategy) :
    ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
      (Memory := Memory) A strategy ×
    ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
      (Memory := Memory) A strategy :=
  ((.inr (false, (pair.right, ⟨(pair.state A strategy, pair.receiver A strategy), pair.newLeft⟩), ()),
      pair.oneCoordinates),
   (.inl (.inr (pair.state A strategy, ⟨(pair.receiver A strategy).1, pair.owner A strategy⟩, pair.template A strategy)),
      pair.twoCoordinates))

namespace OpenOwnerPair

variable (pair : OpenOwnerPair (Memory := Memory) A strategy)
variable (tables : ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection
  (Memory := Memory) A strategy)

def controls :
    ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
      (Memory := Memory) A strategy ×
    ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
      (Memory := Memory) A strategy :=
  ((.inr (false, (pair.right, pair.leftReceivers), ()), pair.oneCoordinates),
   (.inr (false, (pair.left, pair.rightReceivers), ()), pair.twoCoordinates))

def rightPhaseData :
    ProfiledRawJointRecurrentFiniteMemoryRightPhaseLiveBoundaryData
      (Memory := Memory) A strategy :=
  ⟨(pair.rightReceivers.openControl.1,
    ⟨pair.right.finiteMemoryReceiverAt A pair.rightReceivers.openControl.2,
      pair.right.2.1⟩,
    pair.left.finiteMemoryReceiverAt A pair.leftReceivers.openControl.2),
    pair.leftReceivers.openControl.1, pair.left.2.1⟩

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem decode_right :
    profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?
      A strategy (pair.controls A strategy).1
        (pair.controls A strategy).2 = some (pair.rightPhaseData A strategy) := by
  exact profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?_openOpen
    A strategy _ _ _ _ _ _ _ _ _ _

/-- The right-to-left transition retains the right move in its advanced
owner fibre, and the left move in its no-receive fibre. -/
def stepLeft (input : In₁ × In₂) : OpenOwnerPair (Memory := Memory) A strategy :=
  let phase := pair.rightPhaseData A strategy
  let fork := tables.rightBoundaryOwnerFibreReceive A strategy hwin phase.1
    phase.2.1 phase.2.2 input
  { right := profiledRawJointRightOwnerFibreControlOfOwner A
      ⟨pair.right.1, (profiledRawJointRightPhysicalSiblingMemberNoRecvStep A pair.right.1
        false pair.right.2.1 input.1).2⟩
    left := (profiledRawJointLeftOwnerFibreNoRecv A pair.left input.2).1
    leftReceivers := fork.1.openControl.2.1.2
    rightReceivers := pair.rightReceivers
    oneCoordinates := (phase.1.1, phase.2.1)
    twoCoordinates := pair.twoCoordinates }

theorem stepLeft_right_valid
    (hvalid : ProfiledRawJointRightOwnerFibreValid A pair.right) (input : In₁ × In₂) :
    ProfiledRawJointRightOwnerFibreValid A
      (pair.stepLeft A strategy hwin tables input).right :=
  rightFibre_choice_after_step_valid A pair.right hvalid input.1

theorem round_left (input : In₁ × In₂) :
    tables.ownerFibreRound A strategy hwin (pair.controls A strategy) input .left =
    ((pair.stepLeft A strategy hwin tables input).controls A strategy,
     ((stepProfiledRawJointLeftPhysicalSiblingReceiverFor A pair.left.1
        pair.left.2.1 pair.leftReceivers.openControl.2.2.1 pair.left.2.2 input).1,
      ((pair.left.1.memberController A false).labelOf pair.left.2.1).1 input.2)) := by
  have hd := pair.decode_right A strategy
  simp only [ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreRound,
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryOpenRecvOne,
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryReceive?, hd]
  rfl

def stepRight (input : In₁ × In₂) : StagedRightOwnerPair (Memory := Memory) A strategy :=
  let phase := pair.rightPhaseData A strategy
  let data := phase.1
  let packet := tables.resolvePacket A strategy hwin data.1
    (data.target A strategy input)
  { state := data.1
    receiver := (stepProfiledRawJointRightPhysicalSiblingReceiverFor A pair.right.1
      pair.right.2.1 pair.rightReceivers.openControl.2.2.1 pair.right.2.2
        (input.2, input.1)).2
    right := (profiledRawJointRightOwnerFibreNoRecv A pair.right input.1).1
    leftReceivers := pair.leftReceivers
    packet := packet
    oneCoordinates := pair.oneCoordinates
    twoCoordinates := (data.1, packet.successor) }

theorem round_right (input : In₁ × In₂) :
    (tables.ownerFibreRound A strategy hwin (pair.controls A strategy) input .right).1 =
      (pair.stepRight A strategy hwin tables input).controls A strategy := by
  have hd := pair.decode_right A strategy
  simp only [ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreRound,
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryOpenRecvTwo,
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryReceive?, hd]
  simp only [ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.rightPhaseOwnerFibreReceive,
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.rightToLeftBridgeForkTwo]
  split <;> rfl

theorem round_right_outputs (input : In₁ × In₂) :
    (tables.ownerFibreRound A strategy hwin (pair.controls A strategy) input .right).2 =
      (((pair.right.1.memberController A false).labelOf pair.right.2.1).1 input.1,
       (stepProfiledRawJointRightPhysicalSiblingReceiverFor A pair.right.1
         pair.right.2.1 pair.rightReceivers.openControl.2.2.1 pair.right.2.2
         (input.2, input.1)).1) := by
  have hd := pair.decode_right A strategy
  simp only [ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreRound,
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryOpenRecvTwo,
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryReceive?, hd,
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.rightPhaseOwnerFibreReceive,
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.rightToLeftBridgeForkTwo]
  split <;> rfl

end OpenOwnerPair

namespace InstalledLeftOwnerPair
variable (pair : InstalledLeftOwnerPair (Memory := Memory) A strategy)
variable (tables : ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection
  (Memory := Memory) A strategy)

def phaseData : ProfiledRawJointRecurrentFiniteMemoryLeftPhaseLiveBoundaryData
    (Memory := Memory) A strategy :=
  ⟨(pair.state A strategy, ⟨pair.receiver A strategy, pair.owner A strategy⟩,
    pair.right.finiteMemoryReceiverAt A (pair.template A strategy)), pair.twoCoordinates.1,
    pair.right.2.1⟩

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem decode_left :
    profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData? A strategy
      (pair.controls A strategy).1 (pair.controls A strategy).2 =
      some (pair.phaseData A strategy) := by
  exact profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?_openFibreInstalled
    A strategy _ _ _ _ _ _ _ _

def stepRight (input : In₁ × In₂) : OpenOwnerPair (Memory := Memory) A strategy :=
  let phase := pair.phaseData A strategy
  let fork := tables.leftBoundaryOwnerFibreReceive A strategy hwin phase.1
    phase.2.1 phase.2.2 input
  { right := (profiledRawJointRightOwnerFibreNoRecv A pair.right input.1).1
    left := fork.1.openControl.2.1.1
    leftReceivers := ⟨(pair.state A strategy, pair.receiver A strategy), pair.newLeft⟩
    rightReceivers :=
      ⟨(phase.2.1, (stepProfiledRawJointRightPhysicalSiblingReceiverFor A pair.right.1
          pair.right.2.1 (pair.template A strategy).2.1 pair.right.2.2
          (input.2, input.1)).2), fork.1.openControl.2.1.2.closedControl⟩
    oneCoordinates := pair.oneCoordinates
    twoCoordinates := (phase.2.1, phase.1.1) }

theorem stepRight_right_valid
    (hvalid : ProfiledRawJointRightOwnerFibreValid A pair.right) (input : In₁ × In₂) :
    ProfiledRawJointRightOwnerFibreValid A
      (pair.stepRight A strategy hwin tables input).right :=
  hvalid.noRecv A pair.right input.1

theorem round_right (input : In₁ × In₂) :
    (tables.ownerFibreRound A strategy hwin (pair.controls A strategy) input .right).1 =
      (pair.stepRight A strategy hwin tables input).controls A strategy := by
  have hd := pair.decode_left A strategy
  have hr := profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?_none_of_left_some
    A strategy _ _ _ hd
  simp only [ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreRound,
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryOpenRecvTwo,
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryReceive?, hr, hd]
  rfl

end InstalledLeftOwnerPair

namespace StagedRightOwnerPair
variable (pair : StagedRightOwnerPair (Memory := Memory) A strategy)
variable (tables : ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection
  (Memory := Memory) A strategy)

def phaseData (move : ProfiledRawJointLeftPhysicalSiblingMove A) :
    ProfiledRawJointRecurrentFiniteMemoryRightPhaseLiveBoundaryData
      (Memory := Memory) A strategy :=
  ⟨(pair.state, ⟨pair.right.finiteMemoryReceiverAt A pair.receiver, pair.right.2.1⟩,
    initialProfiledRawJointLeftPhysicalSiblingReceiver A move .first),
    pair.packet.successor, (move.memberController A false).initial⟩

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem decode_right (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hmove : pair.packet.successor.2.1.1.2.2 = some move) :
    profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData? A strategy
      (pair.controls A strategy).1 (pair.controls A strategy).2 =
      some (pair.phaseData A strategy move) := by
  exact profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?_fibreStaged
    A strategy _ _ _ _ _ _ _ hmove _ _

def stepLeft (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (input : In₁ × In₂) : InstalledLeftOwnerPair (Memory := Memory) A strategy :=
  let phase := pair.phaseData A strategy move
  let fork := tables.rightBoundaryOwnerFibreReceive A strategy hwin phase.1
    phase.2.1 phase.2.2 input
  let receiver := (stepProfiledRawJointLeftPhysicalSiblingReceiverFor A move
    (move.memberController A false).initial .first
    (profiledRawJointLeftPhysicalSiblingMonitor A move.1 false).initial input).2
  { data := (pair.packet.successor,
      ⟨receiver, (profiledRawJointLeftPhysicalSiblingMemberNoRecvStep A move false
        (move.memberController A false).initial input.2).2⟩, pair.receiver)
    right := profiledRawJointRightOwnerFibreControlOfOwner A
      ⟨pair.right.1, (profiledRawJointRightPhysicalSiblingMemberNoRecvStep A pair.right.1
        false pair.right.2.1 input.1).2⟩
    newLeft := fork.1.openControl.2.1.2.closedControl
    oneCoordinates := (phase.1.1, phase.2.1)
    twoCoordinates := pair.twoCoordinates }

theorem stepLeft_right_valid
    (hvalid : ProfiledRawJointRightOwnerFibreValid A pair.right)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A) (input : In₁ × In₂) :
    ProfiledRawJointRightOwnerFibreValid A
      (pair.stepLeft A strategy hwin tables move input).right :=
  rightFibre_choice_after_step_valid A pair.right hvalid input.1

theorem round_left (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hmove : pair.packet.successor.2.1.1.2.2 = some move) (input : In₁ × In₂) :
    tables.ownerFibreRound A strategy hwin (pair.controls A strategy) input .left =
      ((pair.stepLeft A strategy hwin tables move input).controls A strategy,
       ((stepProfiledRawJointLeftPhysicalSiblingReceiverFor A move
          (move.memberController A false).initial .first
          (profiledRawJointLeftPhysicalSiblingMonitor A move.1 false).initial input).1,
        ((move.memberController A false).labelOf
          (move.memberController A false).initial).1 input.2)) := by
  have hd := pair.decode_right A strategy move hmove
  simp only [ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreRound,
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryOpenRecvOne,
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryReceive?, hd]
  simp only [controls, profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvTwo,
    profiledRawJointRecurrentFiniteMemoryRightToLeftBridgeNoRecv, hmove]
  rfl

/-- Four strict rounds return to a staged packet. In particular, the
equal-open pair cannot retain its two owners forever on this alternating
word. The returned packet is exactly the last right receive's packet. -/
def renew (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (inputs : Fin 4 → In₁ × In₂) : StagedRightOwnerPair (Memory := Memory) A strategy :=
  let installed := pair.stepLeft A strategy hwin tables move (inputs 0)
  let openPair := installed.stepRight A strategy hwin tables (inputs 1)
  let openPair' := openPair.stepLeft A strategy hwin tables (inputs 2)
  openPair'.stepRight A strategy hwin tables (inputs 3)

theorem renew_right_valid
    (hvalid : ProfiledRawJointRightOwnerFibreValid A pair.right)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A) (inputs : Fin 4 → In₁ × In₂) :
    ProfiledRawJointRightOwnerFibreValid A
      (pair.renew A strategy hwin tables move inputs).right := by
  apply ProfiledRawJointRightOwnerFibreValid.noRecv
  apply OpenOwnerPair.stepLeft_right_valid
  apply InstalledLeftOwnerPair.stepRight_right_valid
  exact pair.stepLeft_right_valid A strategy hwin tables hvalid move (inputs 0)

theorem renew_right_move (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (inputs : Fin 4 → In₁ × In₂) :
    (pair.renew A strategy hwin tables move inputs).right.1 = pair.right.1 := rfl

theorem renew_state (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (inputs : Fin 4 → In₁ × In₂) :
    (pair.renew A strategy hwin tables move inputs).state = pair.twoCoordinates.1 := rfl

theorem renew_anchor (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (inputs : Fin 4 → In₁ × In₂) :
    (pair.renew A strategy hwin tables move inputs).twoCoordinates.1 =
      (pair.renew A strategy hwin tables move inputs).state := rfl

theorem four_round_return (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hmove : pair.packet.successor.2.1.1.2.2 = some move)
    (inputs : Fin 4 → In₁ × In₂) :
    ([(inputs 0, Graph.left), (inputs 1, Graph.right),
      (inputs 2, Graph.left), (inputs 3, Graph.right)].foldl
      (fun controls direction ↦
        (tables.ownerFibreRound A strategy hwin controls direction.1 direction.2).1)
      (pair.controls A strategy)) =
      (pair.renew A strategy hwin tables move inputs).controls A strategy := by
  simp only [List.foldl_cons, List.foldl_nil, pair.round_left A strategy hwin tables move hmove,
    InstalledLeftOwnerPair.round_right, OpenOwnerPair.round_left, OpenOwnerPair.round_right]
  rfl

end StagedRightOwnerPair
end
end DetParityAutomaton
end DistributedSynthesis
