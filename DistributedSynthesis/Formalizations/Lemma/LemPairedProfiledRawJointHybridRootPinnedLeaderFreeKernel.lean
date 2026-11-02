/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridRootPinnedStrictRecurrentHandoff
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointLeaderFreeControllerCarrier

/-!
# Root-pinned strict recurrence in the leader-free kernel

This module fills every ordinary recurrent field of
`ProfiledRawJointLeaderFreeKernel` from the exact guarded-child handoff.  The
only remaining parameter is the finite front adapter: initial rounds,
repeated-common exceptional rounds, and total off-invariant receives.

The front types are intentionally polymorphic here.  In the concrete model an
honest adapter must retain the initial local shadow between the first and
second physical rounds and then the root-pinned `(first,current)` ambiguity;
it may not reconstruct the first input from a default.  Keeping that boundary
typed prevents the solved strict recurrence from concealing the outstanding
common-front case.
-/

namespace DistributedSynthesis

universe u v x y s i₁ i₂ e₁ e₂

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

/-! ## Complete local control sums -/

abbrev ProfiledRawJointHybridRootPinnedStrictOneControl
    (InitialOne : Type i₁) (ExceptionalOne : Type e₁) :=
  ProfiledRawJointLeaderFreeOneControl InitialOne ExceptionalOne
    (ProfiledRawJointHybridRootPinnedChildCode A strategy hwin)
    (ProfiledRawJointHybridRootPinnedStrictRightOwner A strategy hwin)
    (ProfiledRawJointHybridRootPinnedStrictLeftReceiver A strategy hwin)

abbrev ProfiledRawJointHybridRootPinnedStrictTwoControl
    (InitialTwo : Type i₂) (ExceptionalTwo : Type e₂) :=
  ProfiledRawJointLeaderFreeTwoControl InitialTwo ExceptionalTwo
    (ProfiledRawJointHybridRootPinnedChildCode A strategy hwin)
    (ProfiledRawJointHybridRootPinnedStrictRightReceiver A strategy hwin)
    (ProfiledRawJointHybridRootPinnedStrictLeftOwner A strategy hwin)

/-! ## The explicitly isolated finite-front seam -/

/-- Executable front maps above the concrete strict recurrent table.

For the concrete root-pinned construction, `ExceptionalOne/Two` must include
the honest first-round local-shadow phase as well as the later common-key
phase.  This bundle assumes no semantic proposition; it is exactly the named
construction seam that remains after strict recurrence. -/
structure ProfiledRawJointHybridRootPinnedExceptionalAdapter
    (InitialOne : Type i₁) (InitialTwo : Type i₂)
    (ExceptionalOne : Type e₁) (ExceptionalTwo : Type e₂) where
  initialOne : InitialOne
  initialTwo : InitialTwo
  initialOutputOne : Out₁
  initialOutputTwo : Out₂
  initialNoRecvOne : InitialOne → In₁ → Out₁ ×
    ProfiledRawJointHybridRootPinnedStrictOneControl A strategy hwin InitialOne
      ExceptionalOne
  exceptionalNoRecvOne : ExceptionalOne → In₁ → Out₁ ×
    ProfiledRawJointHybridRootPinnedStrictOneControl A strategy hwin InitialOne
      ExceptionalOne
  initialNoRecvTwo : InitialTwo → In₂ → Out₂ ×
    ProfiledRawJointHybridRootPinnedStrictTwoControl A strategy hwin InitialTwo
      ExceptionalTwo
  exceptionalNoRecvTwo : ExceptionalTwo → In₂ → Out₂ ×
    ProfiledRawJointHybridRootPinnedStrictTwoControl A strategy hwin InitialTwo
      ExceptionalTwo
  otherRecvOne :
    ProfiledRawJointHybridRootPinnedStrictOneControl A strategy hwin InitialOne
        ExceptionalOne → In₁ →
      ProfiledRawJointHybridRootPinnedStrictTwoControl A strategy hwin
        InitialTwo ExceptionalTwo → In₂ →
      Out₁ × ProfiledRawJointHybridRootPinnedStrictOneControl A strategy
        hwin InitialOne ExceptionalOne
  otherRecvTwo :
    ProfiledRawJointHybridRootPinnedStrictTwoControl A strategy hwin InitialTwo
        ExceptionalTwo → In₂ →
      ProfiledRawJointHybridRootPinnedStrictOneControl A strategy hwin
        InitialOne ExceptionalOne → In₁ →
      Out₂ × ProfiledRawJointHybridRootPinnedStrictTwoControl A strategy
        hwin InitialTwo ExceptionalTwo

/-! ## Complete kernel with concrete ordinary fields -/

noncomputable def profiledRawJointHybridRootPinnedLeaderFreeKernel
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    (adapter : ProfiledRawJointHybridRootPinnedExceptionalAdapter A strategy
      hwin InitialOne InitialTwo ExceptionalOne ExceptionalTwo) :
    ProfiledRawJointLeaderFreeKernel In₁ In₂ Out₁ Out₂ InitialOne
      InitialTwo ExceptionalOne ExceptionalTwo
      (ProfiledRawJointHybridRootPinnedChildCode A strategy hwin)
      (ProfiledRawJointHybridRootPinnedStrictRightOwner A strategy hwin)
      (ProfiledRawJointHybridRootPinnedStrictLeftReceiver A strategy hwin)
      (ProfiledRawJointHybridRootPinnedStrictRightReceiver A strategy hwin)
      (ProfiledRawJointHybridRootPinnedStrictLeftOwner A strategy hwin) where
  initialOne := adapter.initialOne
  initialTwo := adapter.initialTwo
  initialOutputOne := adapter.initialOutputOne
  initialOutputTwo := adapter.initialOutputTwo
  initialNoRecvOne := adapter.initialNoRecvOne
  exceptionalNoRecvOne := adapter.exceptionalNoRecvOne
  rightOwnerNoRecvOne := fun child owner input ↦
    profiledRawJointHybridRootPinnedStrictStepRightOwner A strategy hwin child
      owner input
  leftReceiverNoRecvOne := fun child receiver input ↦
    profiledRawJointHybridRootPinnedStrictStartRightOwner A strategy hwin child
      receiver input
  initialNoRecvTwo := adapter.initialNoRecvTwo
  exceptionalNoRecvTwo := adapter.exceptionalNoRecvTwo
  rightReceiverNoRecvTwo := fun child receiver input ↦
    profiledRawJointHybridRootPinnedStrictStartLeftOwner A strategy hwin child
      receiver input
  leftOwnerNoRecvTwo := fun child owner input ↦
    profiledRawJointHybridRootPinnedStrictStepLeftOwner A strategy hwin child
      owner input
  matchedRightRecvOne := fun _ receiverChild _ inputOne receiver inputTwo ↦
    profiledRawJointHybridRootPinnedStrictStartLeftReceiver A strategy hwin
      receiverChild receiver (inputOne, inputTwo)
  matchedRightRecvTwo := fun receiverChild rightChild receiver inputTwo owner
      inputOne ↦
    profiledRawJointHybridRootPinnedStrictContinueRightReceiver A strategy hwin
      receiverChild rightChild receiver owner (inputTwo, inputOne)
  matchedLeftRecvOne := fun receiverChild leftChild receiver inputOne owner
      inputTwo ↦
    profiledRawJointHybridRootPinnedStrictContinueLeftReceiver A strategy hwin
      receiverChild leftChild receiver owner (inputOne, inputTwo)
  matchedLeftRecvTwo := fun _ receiverChild _ inputTwo receiver inputOne ↦
    profiledRawJointHybridRootPinnedStrictStartRightReceiver A strategy hwin
      receiverChild receiver (inputTwo, inputOne)
  crossRecvOne := fun _ rightChild _ inputOne right inputTwo ↦
    profiledRawJointHybridRootPinnedStrictStartLeftReceiver A strategy hwin
      rightChild right (inputOne, inputTwo)
  crossRecvTwo := fun _ leftChild _ inputTwo left inputOne ↦
    profiledRawJointHybridRootPinnedStrictStartRightReceiver A strategy hwin
      leftChild left (inputTwo, inputOne)
  otherRecvOne := adapter.otherRecvOne
  otherRecvTwo := adapter.otherRecvTwo

/-! ## Definitional audit of all ordinary fields -/

@[simp] theorem profiledRawJointHybridRootPinnedKernel_rightOwnerNoRecvOne
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    (adapter : ProfiledRawJointHybridRootPinnedExceptionalAdapter A strategy
      hwin InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (child : ProfiledRawJointHybridRootPinnedChildCode A strategy hwin)
    (owner : ProfiledRawJointHybridRootPinnedStrictRightOwner A strategy hwin
      child) (input : In₁) :
    (profiledRawJointHybridRootPinnedLeaderFreeKernel A strategy hwin adapter
      ).rightOwnerNoRecvOne child owner input =
      profiledRawJointHybridRootPinnedStrictStepRightOwner A strategy hwin
        child owner input :=
  rfl

@[simp] theorem profiledRawJointHybridRootPinnedKernel_leftReceiverNoRecvOne
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    (adapter : ProfiledRawJointHybridRootPinnedExceptionalAdapter A strategy
      hwin InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (child : ProfiledRawJointHybridRootPinnedChildCode A strategy hwin)
    (receiver :
      ProfiledRawJointHybridRootPinnedStrictLeftReceiver A strategy hwin child)
    (input : In₁) :
    (profiledRawJointHybridRootPinnedLeaderFreeKernel A strategy hwin adapter
      ).leftReceiverNoRecvOne child receiver input =
      profiledRawJointHybridRootPinnedStrictStartRightOwner A strategy hwin
        child receiver input :=
  rfl

@[simp] theorem profiledRawJointHybridRootPinnedKernel_rightReceiverNoRecvTwo
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    (adapter : ProfiledRawJointHybridRootPinnedExceptionalAdapter A strategy
      hwin InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (child : ProfiledRawJointHybridRootPinnedChildCode A strategy hwin)
    (receiver :
      ProfiledRawJointHybridRootPinnedStrictRightReceiver A strategy hwin child)
    (input : In₂) :
    (profiledRawJointHybridRootPinnedLeaderFreeKernel A strategy hwin adapter
      ).rightReceiverNoRecvTwo child receiver input =
      profiledRawJointHybridRootPinnedStrictStartLeftOwner A strategy hwin child
        receiver input :=
  rfl

@[simp] theorem profiledRawJointHybridRootPinnedKernel_leftOwnerNoRecvTwo
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    (adapter : ProfiledRawJointHybridRootPinnedExceptionalAdapter A strategy
      hwin InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (child : ProfiledRawJointHybridRootPinnedChildCode A strategy hwin)
    (owner : ProfiledRawJointHybridRootPinnedStrictLeftOwner A strategy hwin
      child) (input : In₂) :
    (profiledRawJointHybridRootPinnedLeaderFreeKernel A strategy hwin adapter
      ).leftOwnerNoRecvTwo child owner input =
      profiledRawJointHybridRootPinnedStrictStepLeftOwner A strategy hwin child
        owner input :=
  rfl

@[simp] theorem profiledRawJointHybridRootPinnedKernel_matchedRightRecvOne
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    (adapter : ProfiledRawJointHybridRootPinnedExceptionalAdapter A strategy
      hwin InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (rightChild receiverChild :
      ProfiledRawJointHybridRootPinnedChildCode A strategy hwin)
    (owner : ProfiledRawJointHybridRootPinnedStrictRightOwner A strategy hwin
      rightChild)
    (receiver : ProfiledRawJointHybridRootPinnedStrictRightReceiver A strategy
      hwin receiverChild) (inputOne : In₁) (inputTwo : In₂) :
    (profiledRawJointHybridRootPinnedLeaderFreeKernel A strategy hwin adapter
      ).matchedRightRecvOne rightChild receiverChild owner inputOne receiver
        inputTwo =
      profiledRawJointHybridRootPinnedStrictStartLeftReceiver A strategy hwin
        receiverChild receiver (inputOne, inputTwo) :=
  rfl

@[simp] theorem profiledRawJointHybridRootPinnedKernel_matchedRightRecvTwo
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    (adapter : ProfiledRawJointHybridRootPinnedExceptionalAdapter A strategy
      hwin InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (receiverChild rightChild :
      ProfiledRawJointHybridRootPinnedChildCode A strategy hwin)
    (receiver : ProfiledRawJointHybridRootPinnedStrictRightReceiver A strategy
      hwin receiverChild)
    (owner : ProfiledRawJointHybridRootPinnedStrictRightOwner A strategy hwin
      rightChild) (inputTwo : In₂) (inputOne : In₁) :
    (profiledRawJointHybridRootPinnedLeaderFreeKernel A strategy hwin adapter
      ).matchedRightRecvTwo receiverChild rightChild receiver inputTwo owner
        inputOne =
      profiledRawJointHybridRootPinnedStrictContinueRightReceiver A strategy
        hwin receiverChild rightChild receiver owner (inputTwo, inputOne) :=
  rfl

@[simp] theorem profiledRawJointHybridRootPinnedKernel_matchedLeftRecvOne
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    (adapter : ProfiledRawJointHybridRootPinnedExceptionalAdapter A strategy
      hwin InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (receiverChild leftChild :
      ProfiledRawJointHybridRootPinnedChildCode A strategy hwin)
    (receiver : ProfiledRawJointHybridRootPinnedStrictLeftReceiver A strategy
      hwin receiverChild)
    (owner : ProfiledRawJointHybridRootPinnedStrictLeftOwner A strategy hwin
      leftChild) (inputOne : In₁) (inputTwo : In₂) :
    (profiledRawJointHybridRootPinnedLeaderFreeKernel A strategy hwin adapter
      ).matchedLeftRecvOne receiverChild leftChild receiver inputOne owner
        inputTwo =
      profiledRawJointHybridRootPinnedStrictContinueLeftReceiver A strategy
        hwin receiverChild leftChild receiver owner (inputOne, inputTwo) :=
  rfl

@[simp] theorem profiledRawJointHybridRootPinnedKernel_matchedLeftRecvTwo
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    (adapter : ProfiledRawJointHybridRootPinnedExceptionalAdapter A strategy
      hwin InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (leftChild receiverChild :
      ProfiledRawJointHybridRootPinnedChildCode A strategy hwin)
    (owner : ProfiledRawJointHybridRootPinnedStrictLeftOwner A strategy hwin
      leftChild)
    (receiver : ProfiledRawJointHybridRootPinnedStrictLeftReceiver A strategy
      hwin receiverChild) (inputTwo : In₂) (inputOne : In₁) :
    (profiledRawJointHybridRootPinnedLeaderFreeKernel A strategy hwin adapter
      ).matchedLeftRecvTwo leftChild receiverChild owner inputTwo receiver
        inputOne =
      profiledRawJointHybridRootPinnedStrictStartRightReceiver A strategy hwin
        receiverChild receiver (inputTwo, inputOne) :=
  rfl

@[simp] theorem profiledRawJointHybridRootPinnedKernel_crossRecvOne
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    (adapter : ProfiledRawJointHybridRootPinnedExceptionalAdapter A strategy
      hwin InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (leftChild rightChild :
      ProfiledRawJointHybridRootPinnedChildCode A strategy hwin)
    (left : ProfiledRawJointHybridRootPinnedStrictLeftReceiver A strategy hwin
      leftChild)
    (right : ProfiledRawJointHybridRootPinnedStrictRightReceiver A strategy
      hwin rightChild) (inputOne : In₁) (inputTwo : In₂) :
    (profiledRawJointHybridRootPinnedLeaderFreeKernel A strategy hwin adapter
      ).crossRecvOne leftChild rightChild left inputOne right inputTwo =
      profiledRawJointHybridRootPinnedStrictStartLeftReceiver A strategy hwin
        rightChild right (inputOne, inputTwo) :=
  rfl

@[simp] theorem profiledRawJointHybridRootPinnedKernel_crossRecvTwo
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    (adapter : ProfiledRawJointHybridRootPinnedExceptionalAdapter A strategy
      hwin InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (rightChild leftChild :
      ProfiledRawJointHybridRootPinnedChildCode A strategy hwin)
    (right : ProfiledRawJointHybridRootPinnedStrictRightReceiver A strategy
      hwin rightChild)
    (left : ProfiledRawJointHybridRootPinnedStrictLeftReceiver A strategy hwin
      leftChild) (inputTwo : In₂) (inputOne : In₁) :
    (profiledRawJointHybridRootPinnedLeaderFreeKernel A strategy hwin adapter
      ).crossRecvTwo rightChild leftChild right inputTwo left inputOne =
      profiledRawJointHybridRootPinnedStrictStartRightReceiver A strategy hwin
        leftChild left (inputTwo, inputOne) :=
  rfl

/-! ## Exact child synchronization at every strict selection -/

/-- A matched-right pair switching left installs one literal complete child at
both processes. -/
theorem profiledRawJointHybridRootPinnedKernel_switchLeft_commonChild
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    (adapter : ProfiledRawJointHybridRootPinnedExceptionalAdapter A strategy
      hwin InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (rightChild receiverChild :
      ProfiledRawJointHybridRootPinnedChildCode A strategy hwin)
    (owner : ProfiledRawJointHybridRootPinnedStrictRightOwner A strategy hwin
      rightChild)
    (receiver : ProfiledRawJointHybridRootPinnedStrictRightReceiver A strategy
      hwin receiverChild) (move : In₁ × In₂) :
    ((profiledRawJointHybridRootPinnedLeaderFreeKernel A strategy hwin adapter
      ).matchedRightRecvOne rightChild receiverChild owner move.1 receiver
        move.2).2.1 =
      ((profiledRawJointHybridRootPinnedLeaderFreeKernel A strategy hwin
        adapter).rightReceiverNoRecvTwo receiverChild receiver move.2).2.1 :=
  profiledRawJointHybridRootPinnedStrictStartLeft_commonChild A strategy hwin
    receiverChild receiver move

/-- The same child synchronization holds when strict left is selected from a
receiver/receiver cross. -/
theorem profiledRawJointHybridRootPinnedKernel_crossLeft_commonChild
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    (adapter : ProfiledRawJointHybridRootPinnedExceptionalAdapter A strategy
      hwin InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (leftChild rightChild :
      ProfiledRawJointHybridRootPinnedChildCode A strategy hwin)
    (left : ProfiledRawJointHybridRootPinnedStrictLeftReceiver A strategy hwin
      leftChild)
    (right : ProfiledRawJointHybridRootPinnedStrictRightReceiver A strategy
      hwin rightChild) (move : In₁ × In₂) :
    ((profiledRawJointHybridRootPinnedLeaderFreeKernel A strategy hwin adapter
      ).crossRecvOne leftChild rightChild left move.1 right move.2).2.1 =
      ((profiledRawJointHybridRootPinnedLeaderFreeKernel A strategy hwin
        adapter).rightReceiverNoRecvTwo rightChild right move.2).2.1 :=
  profiledRawJointHybridRootPinnedStrictStartLeft_commonChild A strategy hwin
    rightChild right move

/-- A matched-left pair switching right installs one literal complete child. -/
theorem profiledRawJointHybridRootPinnedKernel_switchRight_commonChild
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    (adapter : ProfiledRawJointHybridRootPinnedExceptionalAdapter A strategy
      hwin InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (leftChild receiverChild :
      ProfiledRawJointHybridRootPinnedChildCode A strategy hwin)
    (owner : ProfiledRawJointHybridRootPinnedStrictLeftOwner A strategy hwin
      leftChild)
    (receiver : ProfiledRawJointHybridRootPinnedStrictLeftReceiver A strategy
      hwin receiverChild) (move : In₁ × In₂) :
    ((profiledRawJointHybridRootPinnedLeaderFreeKernel A strategy hwin adapter
      ).leftReceiverNoRecvOne receiverChild receiver move.1).2.1 =
      ((profiledRawJointHybridRootPinnedLeaderFreeKernel A strategy hwin
        adapter).matchedLeftRecvTwo leftChild receiverChild owner move.2
          receiver move.1).2.1 :=
  profiledRawJointHybridRootPinnedStrictStartRight_commonChild A strategy hwin
    receiverChild receiver (move.2, move.1)

/-- Strict right from a receiver/receiver cross has the same property. -/
theorem profiledRawJointHybridRootPinnedKernel_crossRight_commonChild
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    (adapter : ProfiledRawJointHybridRootPinnedExceptionalAdapter A strategy
      hwin InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (leftChild rightChild :
      ProfiledRawJointHybridRootPinnedChildCode A strategy hwin)
    (left : ProfiledRawJointHybridRootPinnedStrictLeftReceiver A strategy hwin
      leftChild)
    (right : ProfiledRawJointHybridRootPinnedStrictRightReceiver A strategy
      hwin rightChild) (move : In₁ × In₂) :
    ((profiledRawJointHybridRootPinnedLeaderFreeKernel A strategy hwin adapter
      ).leftReceiverNoRecvOne leftChild left move.1).2.1 =
      ((profiledRawJointHybridRootPinnedLeaderFreeKernel A strategy hwin
        adapter).crossRecvTwo rightChild leftChild right move.2 left
          move.1).2.1 :=
  profiledRawJointHybridRootPinnedStrictStartRight_commonChild A strategy hwin
    leftChild left (move.2, move.1)

end

end DetParityAutomaton

end DistributedSynthesis
