/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointLeaderFreeControllerCarrier

/-!
# Enlarging the exceptional carrier of a leader-free controller

The switching construction extends the already verified finite front with
charged right/left shadows.  Its ordinary recurrent controls, initial
controls, and outputs do not change.  This file gives the two canonical maps
which embed an old local control into a controller with a larger exceptional
state type.

The maps inspect only the stored local control constructor.  They take no
graph, orientation, leader bit, environment round, or semantic history.
-/

namespace DistributedSynthesis

universe i e e' k ro lr rr lo

namespace ProfiledRawJointLeaderFreeOneControl

/-- Enlarge only process one's exceptional-state carrier. -/
def mapExceptional
    {InitialOne : Type i} {ExceptionalOne : Type e}
    {ExceptionalOne' : Type e'} {ChildCode : Type k}
    {RightOwner : ChildCode → Type ro}
    {LeftReceiver : ChildCode → Type lr}
    (embed : ExceptionalOne → ExceptionalOne') :
    ProfiledRawJointLeaderFreeOneControl InitialOne ExceptionalOne ChildCode
        RightOwner LeftReceiver →
      ProfiledRawJointLeaderFreeOneControl InitialOne ExceptionalOne'
        ChildCode RightOwner LeftReceiver
  | .initial state => .initial state
  | .exceptional state => .exceptional (embed state)
  | .rightOwner key state => .rightOwner key state
  | .leftReceiver key state => .leftReceiver key state

@[simp] theorem mapExceptional_initial
    {InitialOne : Type i} {ExceptionalOne : Type e}
    {ExceptionalOne' : Type e'} {ChildCode : Type k}
    {RightOwner : ChildCode → Type ro}
    {LeftReceiver : ChildCode → Type lr}
    (embed : ExceptionalOne → ExceptionalOne') (state : InitialOne) :
    mapExceptional (ChildCode := ChildCode) (RightOwner := RightOwner)
        (LeftReceiver := LeftReceiver) embed (.initial state) =
      .initial state :=
  rfl

@[simp] theorem mapExceptional_exceptional
    {InitialOne : Type i} {ExceptionalOne : Type e}
    {ExceptionalOne' : Type e'} {ChildCode : Type k}
    {RightOwner : ChildCode → Type ro}
    {LeftReceiver : ChildCode → Type lr}
    (embed : ExceptionalOne → ExceptionalOne') (state : ExceptionalOne) :
    mapExceptional (InitialOne := InitialOne) (ChildCode := ChildCode)
        (RightOwner := RightOwner) (LeftReceiver := LeftReceiver) embed
        (.exceptional state) =
      .exceptional (embed state) :=
  rfl

@[simp] theorem mapExceptional_rightOwner
    {InitialOne : Type i} {ExceptionalOne : Type e}
    {ExceptionalOne' : Type e'} {ChildCode : Type k}
    {RightOwner : ChildCode → Type ro}
    {LeftReceiver : ChildCode → Type lr}
    (embed : ExceptionalOne → ExceptionalOne') (key : ChildCode)
    (state : RightOwner key) :
    mapExceptional (InitialOne := InitialOne) (ExceptionalOne := ExceptionalOne)
        (LeftReceiver := LeftReceiver) embed (.rightOwner key state) =
      .rightOwner key state :=
  rfl

@[simp] theorem mapExceptional_leftReceiver
    {InitialOne : Type i} {ExceptionalOne : Type e}
    {ExceptionalOne' : Type e'} {ChildCode : Type k}
    {RightOwner : ChildCode → Type ro}
    {LeftReceiver : ChildCode → Type lr}
    (embed : ExceptionalOne → ExceptionalOne') (key : ChildCode)
    (state : LeftReceiver key) :
    mapExceptional (InitialOne := InitialOne) (ExceptionalOne := ExceptionalOne)
        (RightOwner := RightOwner) embed (.leftReceiver key state) =
      .leftReceiver key state :=
  rfl

theorem mapExceptional_id
    {InitialOne : Type i} {ExceptionalOne : Type e}
    {ChildCode : Type k} {RightOwner : ChildCode → Type ro}
    {LeftReceiver : ChildCode → Type lr}
    (control : ProfiledRawJointLeaderFreeOneControl InitialOne ExceptionalOne
      ChildCode RightOwner LeftReceiver) :
    mapExceptional id control = control := by
  cases control <;> rfl

theorem mapExceptional_comp
    {InitialOne : Type i} {ExceptionalOne : Type e}
    {ExceptionalOne' : Type e'} {ExceptionalOne'' : Type*}
    {ChildCode : Type k} {RightOwner : ChildCode → Type ro}
    {LeftReceiver : ChildCode → Type lr}
    (outer : ExceptionalOne' → ExceptionalOne'')
    (inner : ExceptionalOne → ExceptionalOne')
    (control : ProfiledRawJointLeaderFreeOneControl InitialOne ExceptionalOne
      ChildCode RightOwner LeftReceiver) :
    mapExceptional outer (mapExceptional inner control) =
      mapExceptional (outer ∘ inner) control := by
  cases control <;> rfl

end ProfiledRawJointLeaderFreeOneControl

namespace ProfiledRawJointLeaderFreeTwoControl

/-- Process-two mirror of `mapExceptional`. -/
def mapExceptional
    {InitialTwo : Type i} {ExceptionalTwo : Type e}
    {ExceptionalTwo' : Type e'} {ChildCode : Type k}
    {RightReceiver : ChildCode → Type rr}
    {LeftOwner : ChildCode → Type lo}
    (embed : ExceptionalTwo → ExceptionalTwo') :
    ProfiledRawJointLeaderFreeTwoControl InitialTwo ExceptionalTwo ChildCode
        RightReceiver LeftOwner →
      ProfiledRawJointLeaderFreeTwoControl InitialTwo ExceptionalTwo'
        ChildCode RightReceiver LeftOwner
  | .initial state => .initial state
  | .exceptional state => .exceptional (embed state)
  | .rightReceiver key state => .rightReceiver key state
  | .leftOwner key state => .leftOwner key state

@[simp] theorem mapExceptional_initial
    {InitialTwo : Type i} {ExceptionalTwo : Type e}
    {ExceptionalTwo' : Type e'} {ChildCode : Type k}
    {RightReceiver : ChildCode → Type rr}
    {LeftOwner : ChildCode → Type lo}
    (embed : ExceptionalTwo → ExceptionalTwo') (state : InitialTwo) :
    mapExceptional (ChildCode := ChildCode) (RightReceiver := RightReceiver)
        (LeftOwner := LeftOwner) embed (.initial state) =
      .initial state :=
  rfl

@[simp] theorem mapExceptional_exceptional
    {InitialTwo : Type i} {ExceptionalTwo : Type e}
    {ExceptionalTwo' : Type e'} {ChildCode : Type k}
    {RightReceiver : ChildCode → Type rr}
    {LeftOwner : ChildCode → Type lo}
    (embed : ExceptionalTwo → ExceptionalTwo') (state : ExceptionalTwo) :
    mapExceptional (InitialTwo := InitialTwo) (ChildCode := ChildCode)
        (RightReceiver := RightReceiver) (LeftOwner := LeftOwner) embed
        (.exceptional state) =
      .exceptional (embed state) :=
  rfl

@[simp] theorem mapExceptional_rightReceiver
    {InitialTwo : Type i} {ExceptionalTwo : Type e}
    {ExceptionalTwo' : Type e'} {ChildCode : Type k}
    {RightReceiver : ChildCode → Type rr}
    {LeftOwner : ChildCode → Type lo}
    (embed : ExceptionalTwo → ExceptionalTwo') (key : ChildCode)
    (state : RightReceiver key) :
    mapExceptional (InitialTwo := InitialTwo) (ExceptionalTwo := ExceptionalTwo)
        (LeftOwner := LeftOwner) embed (.rightReceiver key state) =
      .rightReceiver key state :=
  rfl

@[simp] theorem mapExceptional_leftOwner
    {InitialTwo : Type i} {ExceptionalTwo : Type e}
    {ExceptionalTwo' : Type e'} {ChildCode : Type k}
    {RightReceiver : ChildCode → Type rr}
    {LeftOwner : ChildCode → Type lo}
    (embed : ExceptionalTwo → ExceptionalTwo') (key : ChildCode)
    (state : LeftOwner key) :
    mapExceptional (InitialTwo := InitialTwo) (ExceptionalTwo := ExceptionalTwo)
        (RightReceiver := RightReceiver) embed (.leftOwner key state) =
      .leftOwner key state :=
  rfl

theorem mapExceptional_id
    {InitialTwo : Type i} {ExceptionalTwo : Type e}
    {ChildCode : Type k} {RightReceiver : ChildCode → Type rr}
    {LeftOwner : ChildCode → Type lo}
    (control : ProfiledRawJointLeaderFreeTwoControl InitialTwo ExceptionalTwo
      ChildCode RightReceiver LeftOwner) :
    mapExceptional id control = control := by
  cases control <;> rfl

theorem mapExceptional_comp
    {InitialTwo : Type i} {ExceptionalTwo : Type e}
    {ExceptionalTwo' : Type e'} {ExceptionalTwo'' : Type*}
    {ChildCode : Type k} {RightReceiver : ChildCode → Type rr}
    {LeftOwner : ChildCode → Type lo}
    (outer : ExceptionalTwo' → ExceptionalTwo'')
    (inner : ExceptionalTwo → ExceptionalTwo')
    (control : ProfiledRawJointLeaderFreeTwoControl InitialTwo ExceptionalTwo
      ChildCode RightReceiver LeftOwner) :
    mapExceptional outer (mapExceptional inner control) =
      mapExceptional (outer ∘ inner) control := by
  cases control <;> rfl

end ProfiledRawJointLeaderFreeTwoControl

end DistributedSynthesis
