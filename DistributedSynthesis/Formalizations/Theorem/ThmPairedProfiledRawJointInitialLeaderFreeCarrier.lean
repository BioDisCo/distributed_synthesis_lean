/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointInitialRootControllers
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointInitialControllerBank
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointLeaderFreeControllerCarrier

/-!
# The leader-free root and first strict raw-joint handoff

This module defines the finite root controls and proves their first-step
output and strict-handoff properties.

At the physical root a receiving process cannot tell a strict receive from
`both`.  It therefore computes and retains both finite initial
contingencies.  A non-receiving process selects only its blind contingency.
The proof-side joint table consequently has the three exact shapes

```
left  : (root cross, initial-left owner)
right : (initial-right owner, root cross)
both  : (root cross, root cross).
```

The root cross is local finite data.  It contains no graph or leader bit: it
is the product of the two computations which a root receive makes possible.
The two crossed physical outputs agree by the root pin proved in
`ThmPairedProfiledRawJointInitialRootControllers`.

The second part gives the strict close maps.  The old receiving initial
control carries the delayed finite key.  On a strict reversal the
non-receiving side starts the guarded exceptional owner from that key, while
the receiving side reads the same key from the delivered old control and
starts the matching guarded exceptional receiver.  The common-key equations
are definitional. These results concern the root and the subsequent strict
handoff; they do not assert acceptance for arbitrary continuations.
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
  (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)

/-! ## The two finite initial controllers -/

abbrev ProfiledRawJointInitialLeftRootMonitor :=
  (profiledRawJointInitialLeftBlockMonitor A strategy).rootPinned
    (profiledRawJointInitialLeftRootRecord A strategy)

abbrev ProfiledRawJointInitialRightRootMonitor :=
  (profiledRawJointInitialRightBlockMonitor A strategy).rootPinned
    (profiledRawJointInitialRightRootRecord A strategy)

/-- Process one's finite receiving control for the initial-left
contingency. -/
abbrev ProfiledRawJointRootLeftReceiverControl :=
  (ProfiledRawJointInitialLeftRootMonitor A strategy).State

/-- Process two's blind control for the same contingency. -/
abbrev ProfiledRawJointRootLeftOwnerControl :=
  controllers.leftController.Control

/-- Process one's blind initial-right control. -/
abbrev ProfiledRawJointRootRightOwnerControl :=
  controllers.rightController.Control

/-- Process two's receiving initial-right control. -/
abbrev ProfiledRawJointRootRightReceiverControl :=
  (ProfiledRawJointInitialRightRootMonitor A strategy).State

noncomputable def profiledRawJointInitialLeftReceiverInitial :
    ProfiledRawJointRootLeftReceiverControl A strategy :=
  (ProfiledRawJointInitialLeftRootMonitor A strategy).initial

noncomputable def profiledRawJointInitialLeftOwnerInitial :
    ProfiledRawJointRootLeftOwnerControl A strategy controllers :=
  controllers.leftController.initial

noncomputable def profiledRawJointInitialRightOwnerInitial :
    ProfiledRawJointRootRightOwnerControl A strategy controllers :=
  controllers.rightController.initial

noncomputable def profiledRawJointInitialRightReceiverInitial :
    ProfiledRawJointRootRightReceiverControl A strategy :=
  (ProfiledRawJointInitialRightRootMonitor A strategy).initial

/-- One local receive step in the initial-left contingency.  The owner
control is delivered by the partner summary. -/
noncomputable def continueProfiledRawJointRootLeftReceiver
    (receiver : ProfiledRawJointRootLeftReceiverControl A strategy)
    (owner : ProfiledRawJointRootLeftOwnerControl A strategy controllers)
    (move : In₁ × In₂) :
    Out₁ × ProfiledRawJointRootLeftReceiverControl A strategy :=
  let monitor := ProfiledRawJointInitialLeftRootMonitor A strategy
  let label := controllers.leftController.labelOf owner
  let answer := label.2 receiver move
  (answer.1.informedOne,
    monitor.step receiver (move, answer, label.1 move.2))

/-- Blind initial-left owner step. -/
noncomputable def stepProfiledRawJointRootLeftOwner
    (owner : ProfiledRawJointRootLeftOwnerControl A strategy controllers)
    (input : In₂) :
    Out₂ × ProfiledRawJointRootLeftOwnerControl A strategy controllers :=
  let label := controllers.leftController.labelOf owner
  (label.1 input, controllers.leftController.step owner input)

/-- Blind initial-right owner step. -/
noncomputable def stepProfiledRawJointRootRightOwner
    (owner : ProfiledRawJointRootRightOwnerControl A strategy controllers)
    (input : In₁) :
    Out₁ × ProfiledRawJointRootRightOwnerControl A strategy controllers :=
  let label := controllers.rightController.labelOf owner
  (label.1 input, controllers.rightController.step owner input)

/-- Receiving initial-right mirror. -/
noncomputable def continueProfiledRawJointRootRightReceiver
    (receiver : ProfiledRawJointRootRightReceiverControl A strategy)
    (owner : ProfiledRawJointRootRightOwnerControl A strategy controllers)
    (move : In₂ × In₁) :
    Out₂ × ProfiledRawJointRootRightReceiverControl A strategy :=
  let monitor := ProfiledRawJointInitialRightRootMonitor A strategy
  let label := controllers.rightController.labelOf owner
  let answer := label.2 receiver move
  (answer.1.informedTwo,
    monitor.step receiver (move, answer, label.1 move.2))

/-! ## The finite root cross -/

/-- Both initial computations after one root receive.  This product contains
two contingencies, not a selected orientation. -/
structure ProfiledRawJointInitialRootCross where
  leftReceiver : ProfiledRawJointRootLeftReceiverControl A strategy
  leftOwner : ProfiledRawJointRootLeftOwnerControl A strategy controllers
  rightOwner : ProfiledRawJointRootRightOwnerControl A strategy controllers
  rightReceiver : ProfiledRawJointRootRightReceiverControl A strategy

noncomputable instance profiledRawJointInitialRootCrossFintype :
    Fintype (ProfiledRawJointInitialRootCross A strategy controllers) := by
  classical
  let Rep :=
    ProfiledRawJointRootLeftReceiverControl A strategy ×
    ProfiledRawJointRootLeftOwnerControl A strategy controllers ×
    ProfiledRawJointRootRightOwnerControl A strategy controllers ×
    ProfiledRawJointRootRightReceiverControl A strategy
  let equiv : ProfiledRawJointInitialRootCross A strategy controllers ≃
      Rep := {
    toFun := fun state =>
      (state.leftReceiver, state.leftOwner, state.rightOwner,
        state.rightReceiver)
    invFun := fun state => ⟨state.1, state.2.1, state.2.2.1, state.2.2.2⟩
    left_inv := by intro state; cases state; rfl
    right_inv := by intro state; rcases state with ⟨a, b, c, d⟩; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

/-- The literal four finite computations made by a root receive. -/
noncomputable def profiledRawJointInitialRootCrossStep
    (move : In₁ × In₂) :
    (Out₁ × Out₂) ×
      ProfiledRawJointInitialRootCross A strategy controllers :=
  let leftReceiver := continueProfiledRawJointRootLeftReceiver A strategy
    controllers (profiledRawJointInitialLeftReceiverInitial A strategy)
      (profiledRawJointInitialLeftOwnerInitial A strategy controllers) move
  let leftOwner := stepProfiledRawJointRootLeftOwner A strategy controllers
    (profiledRawJointInitialLeftOwnerInitial A strategy controllers) move.2
  let rightOwner := stepProfiledRawJointRootRightOwner A strategy
    controllers (profiledRawJointInitialRightOwnerInitial A strategy
      controllers) move.1
  let rightReceiver := continueProfiledRawJointRootRightReceiver A strategy
    controllers (profiledRawJointInitialRightReceiverInitial A strategy)
      (profiledRawJointInitialRightOwnerInitial A strategy controllers)
      (move.2, move.1)
  ((leftReceiver.1, rightReceiver.1),
    ⟨leftReceiver.2, leftOwner.2, rightOwner.2, rightReceiver.2⟩)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The process-one component selected by a root receive is simultaneously
the initial-left informed output and the initial-right reversing output. -/
theorem profiledRawJointInitialRootCrossStep_outputOne
    (move : In₁ × In₂) :
    (profiledRawJointInitialRootCrossStep A strategy controllers move).1.1 =
      ((controllers.rightController.labelOf
          controllers.rightController.initial).2
        (ProfiledRawJointInitialRightRootMonitor A strategy).initial
        (move.2, move.1)).1.reversingOne := by
  exact profiledRawJointInitialRoot_outputOne_compatible A strategy
    controllers move

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Process-two crossed root compatibility. -/
theorem profiledRawJointInitialRootCrossStep_outputTwo
    (move : In₁ × In₂) :
    (profiledRawJointInitialRootCrossStep A strategy controllers move).1.2 =
      ((controllers.leftController.labelOf
          controllers.leftController.initial).2
        (ProfiledRawJointInitialLeftRootMonitor A strategy).initial
        move).1.reversingTwo := by
  exact (profiledRawJointInitialRoot_outputTwo_compatible A strategy
    controllers move).symm

/-! ## Local root controls and the three first-step shapes -/

inductive ProfiledRawJointInitialRootOneControl where
  | root
  | rightOwner
      (state : ProfiledRawJointRootRightOwnerControl A strategy controllers)
  | cross (state : ProfiledRawJointInitialRootCross A strategy controllers)

inductive ProfiledRawJointInitialRootTwoControl where
  | root
  | leftOwner
      (state : ProfiledRawJointRootLeftOwnerControl A strategy controllers)
  | cross (state : ProfiledRawJointInitialRootCross A strategy controllers)

noncomputable instance profiledRawJointInitialRootOneControlFintype :
    Fintype
      (ProfiledRawJointInitialRootOneControl A strategy controllers) := by
  classical
  let Rep := Unit ⊕
    ProfiledRawJointRootRightOwnerControl A strategy controllers ⊕
    ProfiledRawJointInitialRootCross A strategy controllers
  let equiv : ProfiledRawJointInitialRootOneControl A strategy controllers ≃
      Rep := {
    toFun
      | .root => .inl ()
      | .rightOwner state => .inr (.inl state)
      | .cross state => .inr (.inr state)
    invFun
      | .inl _ => .root
      | .inr (.inl state) => .rightOwner state
      | .inr (.inr state) => .cross state
    left_inv := by intro state; cases state <;> rfl
    right_inv := by rintro (⟨⟩ | (state | state)) <;> rfl }
  exact Fintype.ofEquiv Rep equiv.symm

noncomputable instance profiledRawJointInitialRootTwoControlFintype :
    Fintype
      (ProfiledRawJointInitialRootTwoControl A strategy controllers) := by
  classical
  let Rep := Unit ⊕
    ProfiledRawJointRootLeftOwnerControl A strategy controllers ⊕
    ProfiledRawJointInitialRootCross A strategy controllers
  let equiv : ProfiledRawJointInitialRootTwoControl A strategy controllers ≃
      Rep := {
    toFun
      | .root => .inl ()
      | .leftOwner state => .inr (.inl state)
      | .cross state => .inr (.inr state)
    invFun
      | .inl _ => .root
      | .inr (.inl state) => .leftOwner state
      | .inr (.inr state) => .cross state
    left_inv := by intro state; cases state <;> rfl
    right_inv := by rintro (⟨⟩ | (state | state)) <;> rfl }
  exact Fintype.ofEquiv Rep equiv.symm

/-- Process one receives at the root.  This same local function is used for
`left` and `both`. -/
noncomputable def profiledRawJointInitialRootRecvOne
    (move : In₁ × In₂) :
    Out₁ × ProfiledRawJointInitialRootOneControl A strategy controllers :=
  let next := profiledRawJointInitialRootCrossStep A strategy controllers move
  (next.1.1, .cross next.2)

/-- Process two's root receive, shared by `right` and `both`. -/
noncomputable def profiledRawJointInitialRootRecvTwo
    (move : In₁ × In₂) :
    Out₂ × ProfiledRawJointInitialRootTwoControl A strategy controllers :=
  let next := profiledRawJointInitialRootCrossStep A strategy controllers move
  (next.1.2, .cross next.2)

/-- Process one's root non-receive selects its initial-right owner. -/
noncomputable def profiledRawJointInitialRootNoRecvOne
    (input : In₁) :
    Out₁ × ProfiledRawJointInitialRootOneControl A strategy controllers :=
  let next := stepProfiledRawJointRootRightOwner A strategy controllers
    (profiledRawJointInitialRightOwnerInitial A strategy controllers) input
  (next.1, .rightOwner next.2)

/-- Process two's root non-receive selects its initial-left owner. -/
noncomputable def profiledRawJointInitialRootNoRecvTwo
    (input : In₂) :
    Out₂ × ProfiledRawJointInitialRootTwoControl A strategy controllers :=
  let next := stepProfiledRawJointRootLeftOwner A strategy controllers
    (profiledRawJointInitialLeftOwnerInitial A strategy controllers) input
  (next.1, .leftOwner next.2)

def ProfiledRawJointInitialHasMatchedLeftRootShape
    (controls : ProfiledRawJointInitialRootOneControl A strategy controllers ×
      ProfiledRawJointInitialRootTwoControl A strategy controllers) : Prop :=
  ∃ cross owner,
    controls = (.cross cross, .leftOwner owner) ∧ owner = cross.leftOwner

def ProfiledRawJointInitialHasMatchedRightRootShape
    (controls : ProfiledRawJointInitialRootOneControl A strategy controllers ×
      ProfiledRawJointInitialRootTwoControl A strategy controllers) : Prop :=
  ∃ owner cross,
    controls = (.rightOwner owner, .cross cross) ∧ owner = cross.rightOwner

def ProfiledRawJointInitialHasImmediateBothRootShape
    (controls : ProfiledRawJointInitialRootOneControl A strategy controllers ×
      ProfiledRawJointInitialRootTwoControl A strategy controllers) : Prop :=
  ∃ cross,
    controls = (.cross cross, .cross cross)

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- The strict-left first round is a matched initial-left pair even though
process one retains both contingencies. -/
theorem profiledRawJointInitialRoot_left_hasMatchedShape
    (move : In₁ × In₂) :
    ProfiledRawJointInitialHasMatchedLeftRootShape A strategy controllers
      ((profiledRawJointInitialRootRecvOne A strategy controllers move).2,
        (profiledRawJointInitialRootNoRecvTwo A strategy controllers
          move.2).2) := by
  refine ⟨(profiledRawJointInitialRootCrossStep A strategy controllers
      move).2,
    (profiledRawJointInitialRootCrossStep A strategy controllers
      move).2.leftOwner, rfl, rfl⟩

/-- Strict-right mirror. -/
theorem profiledRawJointInitialRoot_right_hasMatchedShape
    (move : In₁ × In₂) :
    ProfiledRawJointInitialHasMatchedRightRootShape A strategy controllers
      ((profiledRawJointInitialRootNoRecvOne A strategy controllers
          move.1).2,
        (profiledRawJointInitialRootRecvTwo A strategy controllers move).2) := by
  refine ⟨(profiledRawJointInitialRootCrossStep A strategy controllers
      move).2.rightOwner,
    (profiledRawJointInitialRootCrossStep A strategy controllers move).2,
    rfl, rfl⟩

/-- Immediate `both` stores the literal same two-contingency product at both
processes; it does not select either strict leader. -/
theorem profiledRawJointInitialRoot_both_hasCrossShape
    (move : In₁ × In₂) :
    ProfiledRawJointInitialHasImmediateBothRootShape A strategy controllers
      ((profiledRawJointInitialRootRecvOne A strategy controllers move).2,
        (profiledRawJointInitialRootRecvTwo A strategy controllers move).2) :=
  ⟨(profiledRawJointInitialRootCrossStep A strategy controllers move).2,
    rfl⟩

end

/-! ## Delayed-key strict activation -/

/-- The finite exceptional-right key staged in an initial-left receiving
control. -/
def profiledRawJointInitialLeftStagedKey
    (receiver : ProfiledRawJointRootLeftReceiverControl A strategy) :
    Option (ProfiledRawJointInitialLeftGuardedKey A strategy) :=
  receiver.base.1.2

/-- Initial-right mirror. -/
def profiledRawJointInitialRightStagedKey
    (receiver : ProfiledRawJointRootRightReceiverControl A strategy) :
    Option (ProfiledRawJointInitialRightGuardedKey A strategy) :=
  receiver.base.1.2

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The first root receive really installs a left delayed key. -/
@[simp] theorem profiledRawJointInitialRootCrossStep_left_stagedKey
    (move : In₁ × In₂) :
    profiledRawJointInitialLeftStagedKey A strategy
        (profiledRawJointInitialRootCrossStep A strategy controllers
          move).2.leftReceiver =
      some (((controllers.leftController.labelOf
        controllers.leftController.initial).2
          (ProfiledRawJointInitialLeftRootMonitor A strategy).initial move).2) :=
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Initial-right mirror delayed key. -/
@[simp] theorem profiledRawJointInitialRootCrossStep_right_stagedKey
    (move : In₁ × In₂) :
    profiledRawJointInitialRightStagedKey A strategy
        (profiledRawJointInitialRootCrossStep A strategy controllers
          move).2.rightReceiver =
      some (((controllers.rightController.labelOf
        controllers.rightController.initial).2
          (ProfiledRawJointInitialRightRootMonitor A strategy).initial
            (move.2, move.1)).2) :=
  rfl

/-- Start and step the exceptional-right owner using only the old local
initial-left receiving control and the current non-received input. -/
noncomputable def startProfiledRawJointInitialLeftExceptionalOwner
    (bank : ProfiledRawJointInitialControllerBank A strategy)
    (receiver : ProfiledRawJointRootLeftReceiverControl A strategy)
    (input : In₁) :
    Out₁ × Option (ProfiledRawJointInitialLeftOwnerControl A strategy bank) :=
  match profiledRawJointInitialLeftStagedKey A strategy receiver with
  | none => (default, none)
  | some key =>
      let next := stepProfiledRawJointInitialLeftOwner A strategy bank
        (initialProfiledRawJointInitialLeftOwner A strategy bank key) input
      (next.1, some next.2)

/-- The matching exceptional-right receiver reads the same delayed key from
the delivered initial-left receiving control. -/
noncomputable def startProfiledRawJointInitialLeftExceptionalReceiver
    (bank : ProfiledRawJointInitialControllerBank A strategy)
    (partner : ProfiledRawJointRootLeftReceiverControl A strategy)
    (row : PairedEntryRow) (move : In₂ × In₁) :
    Out₂ × Option
      (ProfiledRawJointInitialLeftReceiverControl A strategy bank) :=
  match profiledRawJointInitialLeftStagedKey A strategy partner with
  | none => (default, none)
  | some key =>
      let initialOwner := initialProfiledRawJointInitialLeftOwner A strategy
        bank key
      let initialReceiver := initialProfiledRawJointInitialLeftReceiver A
        strategy bank key row
      let result := stepProfiledRawJointInitialLeftReceiverFor A strategy bank
        key initialOwner.2 initialReceiver.2.2 move
      (pairedRightInformedForRow row result.1.physical,
        some ⟨key, row, result.2⟩)

/-- Strict-left exceptional owner from the staged initial-right key. -/
noncomputable def startProfiledRawJointInitialRightExceptionalOwner
    (bank : ProfiledRawJointInitialControllerBank A strategy)
    (receiver : ProfiledRawJointRootRightReceiverControl A strategy)
    (input : In₂) :
    Out₂ × Option (ProfiledRawJointInitialRightOwnerControl A strategy bank) :=
  match profiledRawJointInitialRightStagedKey A strategy receiver with
  | none => (default, none)
  | some key =>
      let next := stepProfiledRawJointInitialRightOwner A strategy bank
        (initialProfiledRawJointInitialRightOwner A strategy bank key) input
      (next.1, some next.2)

/-- Matching exceptional-left receiver. -/
noncomputable def startProfiledRawJointInitialRightExceptionalReceiver
    (bank : ProfiledRawJointInitialControllerBank A strategy)
    (partner : ProfiledRawJointRootRightReceiverControl A strategy)
    (row : PairedEntryRow) (move : In₁ × In₂) :
    Out₁ × Option
      (ProfiledRawJointInitialRightReceiverControl A strategy bank) :=
  match profiledRawJointInitialRightStagedKey A strategy partner with
  | none => (default, none)
  | some key =>
      let initialOwner := initialProfiledRawJointInitialRightOwner A strategy
        bank key
      let initialReceiver := initialProfiledRawJointInitialRightReceiver A
        strategy bank key row
      let result := stepProfiledRawJointInitialRightReceiverFor A strategy bank
        key initialOwner.2 initialReceiver.2.2 move
      (pairedLeftInformedForRow row result.1.physical,
        some ⟨key, row, result.2⟩)

/-- If both strict-right activation sides are present, their dependent keys
are the same literal delayed key. -/
theorem startProfiledRawJointInitialLeftExceptional_common_key
    (bank : ProfiledRawJointInitialControllerBank A strategy)
    (receiver : ProfiledRawJointRootLeftReceiverControl A strategy)
    (input : In₁) (row : PairedEntryRow) (move : In₂ × In₁)
    (owner : ProfiledRawJointInitialLeftOwnerControl A strategy bank)
    (nextReceiver : ProfiledRawJointInitialLeftReceiverControl A strategy bank)
    (howner : (startProfiledRawJointInitialLeftExceptionalOwner A strategy bank
      receiver input).2 = some owner)
    (hreceiver :
      (startProfiledRawJointInitialLeftExceptionalReceiver A strategy bank
        receiver row move).2 = some nextReceiver) :
    owner.1 = nextReceiver.1 := by
  cases hkey : profiledRawJointInitialLeftStagedKey A strategy receiver with
  | none =>
      simp [startProfiledRawJointInitialLeftExceptionalOwner, hkey] at howner
  | some key =>
      simp only [startProfiledRawJointInitialLeftExceptionalOwner, hkey,
        Option.some.injEq] at howner
      simp only [startProfiledRawJointInitialLeftExceptionalReceiver, hkey,
        Option.some.injEq] at hreceiver
      subst owner
      subst nextReceiver
      rfl

/-- Strict-left mirror common key. -/
theorem startProfiledRawJointInitialRightExceptional_common_key
    (bank : ProfiledRawJointInitialControllerBank A strategy)
    (receiver : ProfiledRawJointRootRightReceiverControl A strategy)
    (input : In₂) (row : PairedEntryRow) (move : In₁ × In₂)
    (owner : ProfiledRawJointInitialRightOwnerControl A strategy bank)
    (nextReceiver : ProfiledRawJointInitialRightReceiverControl A strategy bank)
    (howner : (startProfiledRawJointInitialRightExceptionalOwner A strategy
      bank receiver input).2 = some owner)
    (hreceiver :
      (startProfiledRawJointInitialRightExceptionalReceiver A strategy bank
        receiver row move).2 = some nextReceiver) :
    owner.1 = nextReceiver.1 := by
  cases hkey : profiledRawJointInitialRightStagedKey A strategy receiver with
  | none =>
      simp [startProfiledRawJointInitialRightExceptionalOwner, hkey] at howner
  | some key =>
      simp only [startProfiledRawJointInitialRightExceptionalOwner, hkey,
        Option.some.injEq] at howner
      simp only [startProfiledRawJointInitialRightExceptionalReceiver, hkey,
        Option.some.injEq] at hreceiver
      subst owner
      subst nextReceiver
      rfl

/-! ## The next strict event from an immediate root cross -/

/-- After an immediate root receive, a process-one non-receive and a
process-two receive start a matched exceptional-right pair. -/
theorem exists_profiledRawJointInitialRootCross_startRight
    (bank : ProfiledRawJointInitialControllerBank A strategy)
    (rootMove nextMove : In₁ × In₂) (row : PairedEntryRow) :
    let cross :=
      (profiledRawJointInitialRootCrossStep A strategy controllers rootMove).2
    ∃ owner receiver,
      (startProfiledRawJointInitialLeftExceptionalOwner A strategy bank
        cross.leftReceiver nextMove.1).2 = some owner ∧
      (startProfiledRawJointInitialLeftExceptionalReceiver A strategy bank
        cross.leftReceiver row (nextMove.2, nextMove.1)).2 = some receiver ∧
      owner.1 = receiver.1 := by
  dsimp only
  let key := ((controllers.leftController.labelOf
    controllers.leftController.initial).2
      (ProfiledRawJointInitialLeftRootMonitor A strategy).initial rootMove).2
  let ownerResult := stepProfiledRawJointInitialLeftOwner A strategy bank
    (initialProfiledRawJointInitialLeftOwner A strategy bank key) nextMove.1
  let receiverResult := stepProfiledRawJointInitialLeftReceiverFor A strategy
    bank key (initialProfiledRawJointInitialLeftOwner A strategy bank key).2
      (initialProfiledRawJointInitialLeftReceiver A strategy bank key row).2.2
      (nextMove.2, nextMove.1)
  refine ⟨ownerResult.2, ⟨key, row, receiverResult.2⟩, ?_, ?_, rfl⟩
  · simp [startProfiledRawJointInitialLeftExceptionalOwner,
      profiledRawJointInitialRootCrossStep_left_stagedKey, key, ownerResult]
  · simp [startProfiledRawJointInitialLeftExceptionalReceiver,
      profiledRawJointInitialRootCrossStep_left_stagedKey, key,
      receiverResult]

/-- Process-two non-receive / process-one receive mirror. -/
theorem exists_profiledRawJointInitialRootCross_startLeft
    (bank : ProfiledRawJointInitialControllerBank A strategy)
    (rootMove nextMove : In₁ × In₂) (row : PairedEntryRow) :
    let cross :=
      (profiledRawJointInitialRootCrossStep A strategy controllers rootMove).2
    ∃ owner receiver,
      (startProfiledRawJointInitialRightExceptionalOwner A strategy bank
        cross.rightReceiver nextMove.2).2 = some owner ∧
      (startProfiledRawJointInitialRightExceptionalReceiver A strategy bank
        cross.rightReceiver row nextMove).2 = some receiver ∧
      owner.1 = receiver.1 := by
  dsimp only
  let key := ((controllers.rightController.labelOf
    controllers.rightController.initial).2
      (ProfiledRawJointInitialRightRootMonitor A strategy).initial
        (rootMove.2, rootMove.1)).2
  let ownerResult := stepProfiledRawJointInitialRightOwner A strategy bank
    (initialProfiledRawJointInitialRightOwner A strategy bank key) nextMove.2
  let receiverResult := stepProfiledRawJointInitialRightReceiverFor A strategy
    bank key (initialProfiledRawJointInitialRightOwner A strategy bank key).2
      (initialProfiledRawJointInitialRightReceiver A strategy bank key row).2.2
      nextMove
  refine ⟨ownerResult.2, ⟨key, row, receiverResult.2⟩, ?_, ?_, rfl⟩
  · simp [startProfiledRawJointInitialRightExceptionalOwner,
      profiledRawJointInitialRootCrossStep_right_stagedKey, key, ownerResult]
  · simp [startProfiledRawJointInitialRightExceptionalReceiver,
      profiledRawJointInitialRootCrossStep_right_stagedKey, key,
      receiverResult]

end

end DetParityAutomaton

end DistributedSynthesis
