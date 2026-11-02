/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenWitnessedPhysicalRoundAdapter
import DistributedSynthesis.Formalizations.Theorem.ThmLocalSummaryAutomaton

/-!
# A leader-free physical carrier for the raw-joint construction

This file isolates the operational shell needed by the raw-joint proof.  Its
local controls contain no graph, strict-leader, orientation, or hidden-side
bit.  A process selects a transition only from its own finite control and the
event it actually observes:

* `noRecv` supplies the own input only;
* `recv` supplies the delivered partner control and both inputs.

The ordinary controls have the four roles forced by the construction:
process one is either a right owner or a left receiver, and process two is
either a right receiver or a left owner.  Importantly, the receiver/receiver
cross is **not** a fifth local phase.  It is the proof-side joint pair

```
  (process one: left receiver, process two: right receiver).
```

Thus neither process is told whether its receive came from a strict graph or
from `both`.  Starting from a matched right pair, `left` and `both` give
process one the same local receive transition; only process two's honest
`noRecv` versus `recv` event separates matched-left from cross.  The mirror
holds from a matched left pair.  From cross, the next `noRecv` installs the
staged owner on that process, while another pair of receives refreshes the
two receiver controls.

`ChildCode` is an opaque finite key.  The controller families indexed by it
are precisely the adapter seam for the literal-child policy bank.  The
initial/exceptional transition maps and the six ordinary receive maps are
data fields, not assumed mathematical propositions.  Concrete modules must
construct them from their already-proved handoff theorems.  Everything in
this file after that seam -- local dispatch, Moore timing, the physical
controller, the local-summary automaton, and the exact cross transition
table -- is unconditional.
-/

namespace DistributedSynthesis

universe u v x y i₁ i₂ e₁ e₂ k ro lr rr lo

set_option synthInstance.maxHeartbeats 200000

/-! ## Local controls and proof-side joint shapes -/

/-- Process one's locally stored phase.  There is deliberately no `cross`
constructor: the cross is locally just a `leftReceiver`. -/
inductive ProfiledRawJointLeaderFreeOneControl
    (InitialOne : Type i₁) (ExceptionalOne : Type e₁)
    (ChildCode : Type k)
    (RightOwner : ChildCode → Type ro)
    (LeftReceiver : ChildCode → Type lr) where
  | initial (state : InitialOne)
  | exceptional (state : ExceptionalOne)
  | rightOwner (key : ChildCode) (state : RightOwner key)
  | leftReceiver (key : ChildCode) (state : LeftReceiver key)

/-- Process two's mirror local phase.  Again, a cross stores an ordinary
`rightReceiver`, not a locally visible cross tag. -/
inductive ProfiledRawJointLeaderFreeTwoControl
    (InitialTwo : Type i₂) (ExceptionalTwo : Type e₂)
    (ChildCode : Type k)
    (RightReceiver : ChildCode → Type rr)
    (LeftOwner : ChildCode → Type lo) where
  | initial (state : InitialTwo)
  | exceptional (state : ExceptionalTwo)
  | rightReceiver (key : ChildCode) (state : RightReceiver key)
  | leftOwner (key : ChildCode) (state : LeftOwner key)

namespace ProfiledRawJointLeaderFreeOneControl

/-- Explicit finite representation, avoiding the expensive dependent
deriving search on the two policy-indexed constructors. -/
noncomputable instance controlFintype
    {InitialOne : Type i₁} {ExceptionalOne : Type e₁}
    {ChildCode : Type k}
    {RightOwner : ChildCode → Type ro}
    {LeftReceiver : ChildCode → Type lr}
    [Fintype InitialOne] [Fintype ExceptionalOne] [Fintype ChildCode]
    [∀ key, Fintype (RightOwner key)]
    [∀ key, Fintype (LeftReceiver key)] :
    Fintype (ProfiledRawJointLeaderFreeOneControl InitialOne ExceptionalOne
      ChildCode RightOwner LeftReceiver) := by
  classical
  let Rep := InitialOne ⊕ ExceptionalOne ⊕
    (Σ key : ChildCode, RightOwner key) ⊕
    (Σ key : ChildCode, LeftReceiver key)
  let equiv :
      ProfiledRawJointLeaderFreeOneControl InitialOne ExceptionalOne ChildCode
          RightOwner LeftReceiver ≃ Rep := {
    toFun := fun control =>
      match control with
      | .initial state => .inl state
      | .exceptional state => .inr (.inl state)
      | .rightOwner key state => .inr (.inr (.inl ⟨key, state⟩))
      | .leftReceiver key state => .inr (.inr (.inr ⟨key, state⟩))
    invFun := fun rep =>
      match rep with
      | .inl state => .initial state
      | .inr (.inl state) => .exceptional state
      | .inr (.inr (.inl state)) => .rightOwner state.1 state.2
      | .inr (.inr (.inr state)) => .leftReceiver state.1 state.2
    left_inv := by intro control; cases control <;> rfl
    right_inv := by
      intro rep
      rcases rep with state | state
      · rfl
      · rcases state with state | state
        · rfl
        · rcases state with state | state <;> rfl }
  exact Fintype.ofEquiv Rep equiv.symm

end ProfiledRawJointLeaderFreeOneControl

namespace ProfiledRawJointLeaderFreeTwoControl

/-- Process-two mirror explicit finite representation. -/
noncomputable instance controlFintype
    {InitialTwo : Type i₂} {ExceptionalTwo : Type e₂}
    {ChildCode : Type k}
    {RightReceiver : ChildCode → Type rr}
    {LeftOwner : ChildCode → Type lo}
    [Fintype InitialTwo] [Fintype ExceptionalTwo] [Fintype ChildCode]
    [∀ key, Fintype (RightReceiver key)]
    [∀ key, Fintype (LeftOwner key)] :
    Fintype (ProfiledRawJointLeaderFreeTwoControl InitialTwo ExceptionalTwo
      ChildCode RightReceiver LeftOwner) := by
  classical
  let Rep := InitialTwo ⊕ ExceptionalTwo ⊕
    (Σ key : ChildCode, RightReceiver key) ⊕
    (Σ key : ChildCode, LeftOwner key)
  let equiv :
      ProfiledRawJointLeaderFreeTwoControl InitialTwo ExceptionalTwo ChildCode
          RightReceiver LeftOwner ≃ Rep := {
    toFun := fun control =>
      match control with
      | .initial state => .inl state
      | .exceptional state => .inr (.inl state)
      | .rightReceiver key state => .inr (.inr (.inl ⟨key, state⟩))
      | .leftOwner key state => .inr (.inr (.inr ⟨key, state⟩))
    invFun := fun rep =>
      match rep with
      | .inl state => .initial state
      | .inr (.inl state) => .exceptional state
      | .inr (.inr (.inl state)) => .rightReceiver state.1 state.2
      | .inr (.inr (.inr state)) => .leftOwner state.1 state.2
    left_inv := by intro control; cases control <;> rfl
    right_inv := by
      intro rep
      rcases rep with state | state
      · rfl
      · rcases state with state | state
        · rfl
        · rcases state with state | state <;> rfl }
  exact Fintype.ofEquiv Rep equiv.symm

end ProfiledRawJointLeaderFreeTwoControl

/-! The summary interface uses one universe for both process sorts. -/

abbrev ProfiledRawJointLeaderFreeLiftedOneSummary
    (InitialOne : Type i₁) (_InitialTwo : Type i₂)
    (ExceptionalOne : Type e₁) (_ExceptionalTwo : Type e₂)
    (ChildCode : Type k)
    (RightOwner : ChildCode → Type ro)
    (LeftReceiver : ChildCode → Type lr)
    (_RightReceiver : ChildCode → Type rr)
    (_LeftOwner : ChildCode → Type lo)
    (Out₁ : Type x) (_Out₂ : Type y) :=
  ULift.{max i₁ i₂ e₁ e₂ k ro lr rr lo x y}
    (ProfiledRawJointLeaderFreeOneControl InitialOne ExceptionalOne ChildCode
      RightOwner LeftReceiver × Out₁)

abbrev ProfiledRawJointLeaderFreeLiftedTwoSummary
    (_InitialOne : Type i₁) (InitialTwo : Type i₂)
    (_ExceptionalOne : Type e₁) (ExceptionalTwo : Type e₂)
    (ChildCode : Type k)
    (_RightOwner : ChildCode → Type ro)
    (_LeftReceiver : ChildCode → Type lr)
    (RightReceiver : ChildCode → Type rr)
    (LeftOwner : ChildCode → Type lo)
    (_Out₁ : Type x) (Out₂ : Type y) :=
  ULift.{max i₁ i₂ e₁ e₂ k ro lr rr lo x y}
    (ProfiledRawJointLeaderFreeTwoControl InitialTwo ExceptionalTwo ChildCode
      RightReceiver LeftOwner × Out₂)

/-- A matched right-oriented pair.  This is a proof-side joint shape, never a
local orientation signal. -/
abbrev ProfiledRawJointLeaderFreeMatchedRight
    (ChildCode : Type k)
    (RightOwner : ChildCode → Type ro)
    (RightReceiver : ChildCode → Type rr) :=
  Σ key : ChildCode, RightOwner key × RightReceiver key

/-- A matched left-oriented pair, used only in joint invariants. -/
abbrev ProfiledRawJointLeaderFreeMatchedLeft
    (ChildCode : Type k)
    (LeftReceiver : ChildCode → Type lr)
    (LeftOwner : ChildCode → Type lo) :=
  Σ key : ChildCode, LeftReceiver key × LeftOwner key

/-- The receiver/receiver cross.  Its projections are ordinary local
receiver controls; this type exists only to state a joint invariant. -/
abbrev ProfiledRawJointLeaderFreeCross
    (ChildCode : Type k)
    (LeftReceiver : ChildCode → Type lr)
    (RightReceiver : ChildCode → Type rr) :=
  Σ key : ChildCode, LeftReceiver key × RightReceiver key

/-! ## The typed local transition seam -/

/--
All executable maps required by the raw-joint carrier.

The four ordinary `noRecv` types already enforce the intended switch table:
a right owner and a left owner stay owners, whereas a left receiver at
process one installs a staged right owner and a right receiver at process two
installs a staged left owner.  This uses only the honest local non-receipt
event.

The six typed ordinary receive maps cover matched right, matched left, and
receiver/receiver cross.  `otherRecvOne` and `otherRecvTwo` are the narrow
adapter boundary for root/initial/exceptional receives and totalize
off-invariant phase pairs.  They are the only fields that still depend on the
exceptional monitor now being assembled.
-/
structure ProfiledRawJointLeaderFreeKernel
    (In₁ : Type u) (In₂ : Type v) (Out₁ : Type x) (Out₂ : Type y)
    (InitialOne : Type i₁) (InitialTwo : Type i₂)
    (ExceptionalOne : Type e₁) (ExceptionalTwo : Type e₂)
    (ChildCode : Type k)
    (RightOwner : ChildCode → Type ro)
    (LeftReceiver : ChildCode → Type lr)
    (RightReceiver : ChildCode → Type rr)
    (LeftOwner : ChildCode → Type lo) where
  initialOne : InitialOne
  initialTwo : InitialTwo
  initialOutputOne : Out₁
  initialOutputTwo : Out₂

  initialNoRecvOne : InitialOne → In₁ →
    Out₁ × ProfiledRawJointLeaderFreeOneControl InitialOne ExceptionalOne
      ChildCode RightOwner LeftReceiver
  exceptionalNoRecvOne : ExceptionalOne → In₁ →
    Out₁ × ProfiledRawJointLeaderFreeOneControl InitialOne ExceptionalOne
      ChildCode RightOwner LeftReceiver
  rightOwnerNoRecvOne : ∀ key : ChildCode,
    RightOwner key → In₁ → Out₁ × RightOwner key
  leftReceiverNoRecvOne : ∀ key : ChildCode,
    LeftReceiver key → In₁ → Out₁ × (Σ next : ChildCode, RightOwner next)

  initialNoRecvTwo : InitialTwo → In₂ →
    Out₂ × ProfiledRawJointLeaderFreeTwoControl InitialTwo ExceptionalTwo
      ChildCode RightReceiver LeftOwner
  exceptionalNoRecvTwo : ExceptionalTwo → In₂ →
    Out₂ × ProfiledRawJointLeaderFreeTwoControl InitialTwo ExceptionalTwo
      ChildCode RightReceiver LeftOwner
  rightReceiverNoRecvTwo : ∀ key : ChildCode,
    RightReceiver key → In₂ → Out₂ × (Σ next : ChildCode, LeftOwner next)
  leftOwnerNoRecvTwo : ∀ key : ChildCode,
    LeftOwner key → In₂ → Out₂ × LeftOwner key

  /-- Process one receives while the pre-round pair is matched right. -/
  matchedRightRecvOne : ∀ rightKey receiverKey : ChildCode,
    RightOwner rightKey → In₁ → RightReceiver receiverKey → In₂ →
      Out₁ × (Σ next : ChildCode, LeftReceiver next)
  /-- Process two's continuing receive in a matched right pair. -/
  matchedRightRecvTwo : ∀ receiverKey rightKey : ChildCode,
    RightReceiver receiverKey → In₂ → RightOwner rightKey → In₁ →
      Out₂ × (Σ next : ChildCode, RightReceiver next)
  /-- Process one's continuing receive in a matched left pair. -/
  matchedLeftRecvOne : ∀ receiverKey leftKey : ChildCode,
    LeftReceiver receiverKey → In₁ → LeftOwner leftKey → In₂ →
      Out₁ × (Σ next : ChildCode, LeftReceiver next)
  /-- Process two receives while the pre-round pair is matched left. -/
  matchedLeftRecvTwo : ∀ leftKey receiverKey : ChildCode,
    LeftOwner leftKey → In₂ → LeftReceiver receiverKey → In₁ →
      Out₂ × (Σ next : ChildCode, RightReceiver next)
  /-- Process one's receive in the receiver/receiver cross. -/
  crossRecvOne : ∀ leftKey rightKey : ChildCode,
    LeftReceiver leftKey → In₁ → RightReceiver rightKey → In₂ →
      Out₁ × (Σ next : ChildCode, LeftReceiver next)
  /-- Process two's mirror receive in the cross. -/
  crossRecvTwo : ∀ rightKey leftKey : ChildCode,
    RightReceiver rightKey → In₂ → LeftReceiver leftKey → In₁ →
      Out₂ × (Σ next : ChildCode, RightReceiver next)

  /-- Root/initial/exceptional and unreachable mismatched receives. -/
  otherRecvOne :
    ProfiledRawJointLeaderFreeOneControl InitialOne ExceptionalOne ChildCode
        RightOwner LeftReceiver → In₁ →
      ProfiledRawJointLeaderFreeTwoControl InitialTwo ExceptionalTwo ChildCode
        RightReceiver LeftOwner → In₂ →
      Out₁ × ProfiledRawJointLeaderFreeOneControl InitialOne ExceptionalOne
        ChildCode RightOwner LeftReceiver
  /-- Process-two mirror of `otherRecvOne`. -/
  otherRecvTwo :
    ProfiledRawJointLeaderFreeTwoControl InitialTwo ExceptionalTwo ChildCode
        RightReceiver LeftOwner → In₂ →
      ProfiledRawJointLeaderFreeOneControl InitialOne ExceptionalOne ChildCode
        RightOwner LeftReceiver → In₁ →
      Out₂ × ProfiledRawJointLeaderFreeTwoControl InitialTwo ExceptionalTwo
        ChildCode RightReceiver LeftOwner

namespace ProfiledRawJointLeaderFreeKernel

variable
  {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
  {InitialOne : Type i₁} {InitialTwo : Type i₂}
  {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
  {ChildCode : Type k}
  {RightOwner : ChildCode → Type ro}
  {LeftReceiver : ChildCode → Type lr}
  {RightReceiver : ChildCode → Type rr}
  {LeftOwner : ChildCode → Type lo}

local notation "OneControlT" =>
  ProfiledRawJointLeaderFreeOneControl InitialOne ExceptionalOne ChildCode
    RightOwner LeftReceiver

local notation "TwoControlT" =>
  ProfiledRawJointLeaderFreeTwoControl InitialTwo ExceptionalTwo ChildCode
    RightReceiver LeftOwner

variable (kernel : ProfiledRawJointLeaderFreeKernel In₁ In₂ Out₁ Out₂
  InitialOne InitialTwo ExceptionalOne ExceptionalTwo ChildCode RightOwner
  LeftReceiver RightReceiver LeftOwner)

/-- Dispatch a non-receive at process one using only its local constructor. -/
def noRecvOne (control : OneControlT) (input : In₁) : Out₁ × OneControlT :=
  match control with
  | .initial state => kernel.initialNoRecvOne state input
  | .exceptional state => kernel.exceptionalNoRecvOne state input
  | .rightOwner key state =>
      let next := kernel.rightOwnerNoRecvOne key state input
      (next.1, .rightOwner key next.2)
  | .leftReceiver key state =>
      let next := kernel.leftReceiverNoRecvOne key state input
      (next.1, .rightOwner next.2.1 next.2.2)

/-- Process-two mirror of `noRecvOne`. -/
def noRecvTwo (control : TwoControlT) (input : In₂) : Out₂ × TwoControlT :=
  match control with
  | .initial state => kernel.initialNoRecvTwo state input
  | .exceptional state => kernel.exceptionalNoRecvTwo state input
  | .rightReceiver key state =>
      let next := kernel.rightReceiverNoRecvTwo key state input
      (next.1, .leftOwner next.2.1 next.2.2)
  | .leftOwner key state =>
      let next := kernel.leftOwnerNoRecvTwo key state input
      (next.1, .leftOwner key next.2)

/-- Dispatch process one's receive by the two delivered local constructors.
No graph value is available here. -/
def recvOne (one : OneControlT) (inputOne : In₁)
    (two : TwoControlT) (inputTwo : In₂) : Out₁ × OneControlT :=
  match one, two with
  | .rightOwner rightKey owner, .rightReceiver receiverKey receiver =>
      let next := kernel.matchedRightRecvOne rightKey receiverKey owner
        inputOne receiver inputTwo
      (next.1, .leftReceiver next.2.1 next.2.2)
  | .leftReceiver receiverKey receiver, .leftOwner leftKey owner =>
      let next := kernel.matchedLeftRecvOne receiverKey leftKey receiver
        inputOne owner inputTwo
      (next.1, .leftReceiver next.2.1 next.2.2)
  | .leftReceiver leftKey left, .rightReceiver rightKey right =>
      let next := kernel.crossRecvOne leftKey rightKey left inputOne right
        inputTwo
      (next.1, .leftReceiver next.2.1 next.2.2)
  | _, _ => kernel.otherRecvOne one inputOne two inputTwo

/-- Process-two receive dispatch, again with no graph or leader argument. -/
def recvTwo (two : TwoControlT) (inputTwo : In₂)
    (one : OneControlT) (inputOne : In₁) : Out₂ × TwoControlT :=
  match two, one with
  | .rightReceiver receiverKey receiver, .rightOwner rightKey owner =>
      let next := kernel.matchedRightRecvTwo receiverKey rightKey receiver
        inputTwo owner inputOne
      (next.1, .rightReceiver next.2.1 next.2.2)
  | .leftOwner leftKey owner, .leftReceiver receiverKey receiver =>
      let next := kernel.matchedLeftRecvTwo leftKey receiverKey owner inputTwo
        receiver inputOne
      (next.1, .rightReceiver next.2.1 next.2.2)
  | .rightReceiver rightKey right, .leftReceiver leftKey left =>
      let next := kernel.crossRecvTwo rightKey leftKey right inputTwo left
        inputOne
      (next.1, .rightReceiver next.2.1 next.2.2)
  | _, _ => kernel.otherRecvTwo two inputTwo one inputOne

/-! ## Exact local dispatch equations -/

@[simp] theorem noRecvOne_rightOwner (key : ChildCode)
    (state : RightOwner key) (input : In₁) :
    kernel.noRecvOne (.rightOwner key state) input =
      let next := kernel.rightOwnerNoRecvOne key state input
      (next.1, .rightOwner key next.2) :=
  rfl

@[simp] theorem noRecvOne_leftReceiver (key : ChildCode)
    (state : LeftReceiver key) (input : In₁) :
    kernel.noRecvOne (.leftReceiver key state) input =
      let next := kernel.leftReceiverNoRecvOne key state input
      (next.1, .rightOwner next.2.1 next.2.2) :=
  rfl

@[simp] theorem noRecvTwo_rightReceiver (key : ChildCode)
    (state : RightReceiver key) (input : In₂) :
    kernel.noRecvTwo (.rightReceiver key state) input =
      let next := kernel.rightReceiverNoRecvTwo key state input
      (next.1, .leftOwner next.2.1 next.2.2) :=
  rfl

@[simp] theorem noRecvTwo_leftOwner (key : ChildCode)
    (state : LeftOwner key) (input : In₂) :
    kernel.noRecvTwo (.leftOwner key state) input =
      let next := kernel.leftOwnerNoRecvTwo key state input
      (next.1, .leftOwner key next.2) :=
  rfl

@[simp] theorem recvOne_matchedRight
    (rightKey receiverKey : ChildCode) (owner : RightOwner rightKey)
    (receiver : RightReceiver receiverKey) (inputOne : In₁) (inputTwo : In₂) :
    kernel.recvOne (.rightOwner rightKey owner) inputOne
        (.rightReceiver receiverKey receiver) inputTwo =
      let next := kernel.matchedRightRecvOne rightKey receiverKey owner
        inputOne receiver inputTwo
      (next.1, .leftReceiver next.2.1 next.2.2) :=
  rfl

@[simp] theorem recvTwo_matchedRight
    (receiverKey rightKey : ChildCode) (receiver : RightReceiver receiverKey)
    (owner : RightOwner rightKey) (inputTwo : In₂) (inputOne : In₁) :
    kernel.recvTwo (.rightReceiver receiverKey receiver) inputTwo
        (.rightOwner rightKey owner) inputOne =
      let next := kernel.matchedRightRecvTwo receiverKey rightKey receiver
        inputTwo owner inputOne
      (next.1, .rightReceiver next.2.1 next.2.2) :=
  rfl

@[simp] theorem recvOne_matchedLeft
    (receiverKey leftKey : ChildCode) (receiver : LeftReceiver receiverKey)
    (owner : LeftOwner leftKey) (inputOne : In₁) (inputTwo : In₂) :
    kernel.recvOne (.leftReceiver receiverKey receiver) inputOne
        (.leftOwner leftKey owner) inputTwo =
      let next := kernel.matchedLeftRecvOne receiverKey leftKey receiver
        inputOne owner inputTwo
      (next.1, .leftReceiver next.2.1 next.2.2) :=
  rfl

@[simp] theorem recvTwo_matchedLeft
    (leftKey receiverKey : ChildCode) (owner : LeftOwner leftKey)
    (receiver : LeftReceiver receiverKey) (inputTwo : In₂) (inputOne : In₁) :
    kernel.recvTwo (.leftOwner leftKey owner) inputTwo
        (.leftReceiver receiverKey receiver) inputOne =
      let next := kernel.matchedLeftRecvTwo leftKey receiverKey owner inputTwo
        receiver inputOne
      (next.1, .rightReceiver next.2.1 next.2.2) :=
  rfl

@[simp] theorem recvOne_cross
    (leftKey rightKey : ChildCode) (left : LeftReceiver leftKey)
    (right : RightReceiver rightKey) (inputOne : In₁) (inputTwo : In₂) :
    kernel.recvOne (.leftReceiver leftKey left) inputOne
        (.rightReceiver rightKey right) inputTwo =
      let next := kernel.crossRecvOne leftKey rightKey left inputOne right
        inputTwo
      (next.1, .leftReceiver next.2.1 next.2.2) :=
  rfl

@[simp] theorem recvTwo_cross
    (rightKey leftKey : ChildCode) (right : RightReceiver rightKey)
    (left : LeftReceiver leftKey) (inputTwo : In₂) (inputOne : In₁) :
    kernel.recvTwo (.rightReceiver rightKey right) inputTwo
        (.leftReceiver leftKey left) inputOne =
      let next := kernel.crossRecvTwo rightKey leftKey right inputTwo left
        inputOne
      (next.1, .rightReceiver next.2.1 next.2.2) :=
  rfl

/-! ## Moore carrier and physical controller -/

local notation "OneSummaryT" => (OneControlT × Out₁)

local notation "TwoSummaryT" => (TwoControlT × Out₂)

variable [Fintype Out₁] [Fintype Out₂]

/-- Store the output produced by the last local event beside its phase. -/
noncomputable def physicalController
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    [Fintype ChildCode]
    [∀ key, Fintype (RightOwner key)]
    [∀ key, Fintype (LeftReceiver key)]
    [∀ key, Fintype (RightReceiver key)]
    [∀ key, Fintype (LeftOwner key)] :
    FinitePairedPhysicalController In₁ In₂ Out₁ Out₂ where
  OneControl := OneSummaryT
  TwoControl := TwoSummaryT
  oneFinite := by
    exact @instFintypeProd OneControlT Out₁
      ProfiledRawJointLeaderFreeOneControl.controlFintype inferInstance
  twoFinite := by
    exact @instFintypeProd TwoControlT Out₂
      ProfiledRawJointLeaderFreeTwoControl.controlFintype inferInstance
  initialOne := (.initial kernel.initialOne, kernel.initialOutputOne)
  initialTwo := (.initial kernel.initialTwo, kernel.initialOutputTwo)
  noRecvOne control input :=
    let next := kernel.noRecvOne control.1 input
    (next.2, next.1)
  noRecvTwo control input :=
    let next := kernel.noRecvTwo control.1 input
    (next.2, next.1)
  recvOne one inputOne two inputTwo :=
    let next := kernel.recvOne one.1 inputOne two.1 inputTwo
    (next.2, next.1)
  recvTwo two inputTwo one inputOne :=
    let next := kernel.recvTwo two.1 inputTwo one.1 inputOne
    (next.2, next.1)
  outputOne control := control.2
  outputTwo control := control.2

@[simp] theorem physicalController_noRecvOne
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    [Fintype ChildCode]
    [∀ key, Fintype (RightOwner key)]
    [∀ key, Fintype (LeftReceiver key)]
    [∀ key, Fintype (RightReceiver key)]
    [∀ key, Fintype (LeftOwner key)]
    (control : OneSummaryT) (input : In₁) :
    ((physicalController kernel).noRecvOne control input) =
      let next := kernel.noRecvOne control.1 input
      (next.2, next.1) :=
  rfl

@[simp] theorem physicalController_noRecvTwo
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    [Fintype ChildCode]
    [∀ key, Fintype (RightOwner key)]
    [∀ key, Fintype (LeftReceiver key)]
    [∀ key, Fintype (RightReceiver key)]
    [∀ key, Fintype (LeftOwner key)]
    (control : TwoSummaryT) (input : In₂) :
    ((physicalController kernel).noRecvTwo control input) =
      let next := kernel.noRecvTwo control.1 input
      (next.2, next.1) :=
  rfl

@[simp] theorem physicalController_recvOne
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    [Fintype ChildCode]
    [∀ key, Fintype (RightOwner key)]
    [∀ key, Fintype (LeftReceiver key)]
    [∀ key, Fintype (RightReceiver key)]
    [∀ key, Fintype (LeftOwner key)]
    (one : OneSummaryT) (inputOne : In₁)
    (two : TwoSummaryT) (inputTwo : In₂) :
    (physicalController kernel).recvOne one inputOne two inputTwo =
      let next := kernel.recvOne one.1 inputOne two.1 inputTwo
      (next.2, next.1) :=
  rfl

@[simp] theorem physicalController_recvTwo
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    [Fintype ChildCode]
    [∀ key, Fintype (RightOwner key)]
    [∀ key, Fintype (LeftReceiver key)]
    [∀ key, Fintype (RightReceiver key)]
    [∀ key, Fintype (LeftOwner key)]
    (two : TwoSummaryT) (inputTwo : In₂)
    (one : OneSummaryT) (inputOne : In₁) :
    (physicalController kernel).recvTwo two inputTwo one inputOne =
      let next := kernel.recvTwo two.1 inputTwo one.1 inputOne
      (next.2, next.1) :=
  rfl

/-! ## The receiver/receiver pair test -/

/-- Constructor-level matched-right shape.  The two keys are allowed to be
temporarily different: equality of the literal child keys is the named
common-source theorem supplied by the concrete handoff adapter. -/
def HasMatchedRightShape (controls : OneSummaryT × TwoSummaryT) : Prop :=
  ∃ (oneKey : ChildCode) (owner : RightOwner oneKey) (outputOne : Out₁)
      (twoKey : ChildCode) (receiver : RightReceiver twoKey)
      (outputTwo : Out₂),
    controls = ((.rightOwner oneKey owner, outputOne),
      (.rightReceiver twoKey receiver, outputTwo))

/-- Constructor-level matched-left shape. -/
def HasMatchedLeftShape (controls : OneSummaryT × TwoSummaryT) : Prop :=
  ∃ (oneKey : ChildCode) (receiver : LeftReceiver oneKey) (outputOne : Out₁)
      (twoKey : ChildCode) (owner : LeftOwner twoKey) (outputTwo : Out₂),
    controls = ((.leftReceiver oneKey receiver, outputOne),
      (.leftOwner twoKey owner, outputTwo))

/-- Constructor-level receiver/receiver cross.  This is a predicate on the
joint proof state, not an extra constructor of either local control. -/
def HasCrossShape (controls : OneSummaryT × TwoSummaryT) : Prop :=
  ∃ (oneKey : ChildCode) (left : LeftReceiver oneKey) (outputOne : Out₁)
      (twoKey : ChildCode) (right : RightReceiver twoKey) (outputTwo : Out₂),
    controls = ((.leftReceiver oneKey left, outputOne),
      (.rightReceiver twoKey right, outputTwo))

/-- A simultaneous receive from a matched-right pair has the cross shape. -/
theorem matchedRight_both_hasCrossShape
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    [Fintype ChildCode]
    [∀ key, Fintype (RightOwner key)]
    [∀ key, Fintype (LeftReceiver key)]
    [∀ key, Fintype (RightReceiver key)]
    [∀ key, Fintype (LeftOwner key)]
    (key : ChildCode) (owner : RightOwner key)
    (receiver : RightReceiver key) (oldOutputOne : Out₁)
    (oldOutputTwo : Out₂) (inputOne : In₁) (inputTwo : In₂) :
    HasCrossShape
      (kernel.physicalController.advanceControls
        ((.rightOwner key owner, oldOutputOne),
          (.rightReceiver key receiver, oldOutputTwo))
        { inputOne := inputOne, inputTwo := inputTwo, graph := .both }) := by
  let leftNext := kernel.matchedRightRecvOne key key owner inputOne receiver
    inputTwo
  let rightNext := kernel.matchedRightRecvTwo key key receiver inputTwo owner
    inputOne
  refine ⟨leftNext.2.1, leftNext.2.2, leftNext.1,
    rightNext.2.1, rightNext.2.2, rightNext.1, ?_⟩
  rfl

/-- The matched-left mirror also enters the same receiver/receiver cross on
`both`. -/
theorem matchedLeft_both_hasCrossShape
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    [Fintype ChildCode]
    [∀ key, Fintype (RightOwner key)]
    [∀ key, Fintype (LeftReceiver key)]
    [∀ key, Fintype (RightReceiver key)]
    [∀ key, Fintype (LeftOwner key)]
    (key : ChildCode) (receiver : LeftReceiver key)
    (owner : LeftOwner key) (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (inputOne : In₁) (inputTwo : In₂) :
    HasCrossShape
      (kernel.physicalController.advanceControls
        ((.leftReceiver key receiver, oldOutputOne),
          (.leftOwner key owner, oldOutputTwo))
        { inputOne := inputOne, inputTwo := inputTwo, graph := .both }) := by
  let leftNext := kernel.matchedLeftRecvOne key key receiver inputOne owner
    inputTwo
  let rightNext := kernel.matchedLeftRecvTwo key key owner inputTwo receiver
    inputOne
  refine ⟨leftNext.2.1, leftNext.2.2, leftNext.1,
    rightNext.2.1, rightNext.2.2, rightNext.1, ?_⟩
  rfl

/-- From cross, a strict `left` is selected only because process two observes
`noRecv`; the result has the matched-left constructor shape. -/
theorem cross_left_hasMatchedLeftShape
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    [Fintype ChildCode]
    [∀ key, Fintype (RightOwner key)]
    [∀ key, Fintype (LeftReceiver key)]
    [∀ key, Fintype (RightReceiver key)]
    [∀ key, Fintype (LeftOwner key)]
    (key : ChildCode) (left : LeftReceiver key)
    (right : RightReceiver key) (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (inputOne : In₁) (inputTwo : In₂) :
    HasMatchedLeftShape
      (kernel.physicalController.advanceControls
        ((.leftReceiver key left, oldOutputOne),
          (.rightReceiver key right, oldOutputTwo))
        { inputOne := inputOne, inputTwo := inputTwo, graph := .left }) := by
  let leftNext := kernel.crossRecvOne key key left inputOne right inputTwo
  let ownerNext := kernel.rightReceiverNoRecvTwo key right inputTwo
  refine ⟨leftNext.2.1, leftNext.2.2, leftNext.1,
    ownerNext.2.1, ownerNext.2.2, ownerNext.1, ?_⟩
  rfl

/-- From cross, the mirror strict event is selected by process one's honest
`noRecv` and has the matched-right constructor shape. -/
theorem cross_right_hasMatchedRightShape
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    [Fintype ChildCode]
    [∀ key, Fintype (RightOwner key)]
    [∀ key, Fintype (LeftReceiver key)]
    [∀ key, Fintype (RightReceiver key)]
    [∀ key, Fintype (LeftOwner key)]
    (key : ChildCode) (left : LeftReceiver key)
    (right : RightReceiver key) (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (inputOne : In₁) (inputTwo : In₂) :
    HasMatchedRightShape
      (kernel.physicalController.advanceControls
        ((.leftReceiver key left, oldOutputOne),
          (.rightReceiver key right, oldOutputTwo))
        { inputOne := inputOne, inputTwo := inputTwo, graph := .right }) := by
  let ownerNext := kernel.leftReceiverNoRecvOne key left inputOne
  let rightNext := kernel.crossRecvTwo key key right inputTwo left inputOne
  refine ⟨ownerNext.2.1, ownerNext.2.2, ownerNext.1,
    rightNext.2.1, rightNext.2.2, rightNext.1, ?_⟩
  rfl

/-- A further simultaneous receive refreshes both receiver controls and stays
in the cross constructor shape. -/
theorem cross_both_hasCrossShape
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    [Fintype ChildCode]
    [∀ key, Fintype (RightOwner key)]
    [∀ key, Fintype (LeftReceiver key)]
    [∀ key, Fintype (RightReceiver key)]
    [∀ key, Fintype (LeftOwner key)]
    (key : ChildCode) (left : LeftReceiver key)
    (right : RightReceiver key) (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (inputOne : In₁) (inputTwo : In₂) :
    HasCrossShape
      (kernel.physicalController.advanceControls
        ((.leftReceiver key left, oldOutputOne),
          (.rightReceiver key right, oldOutputTwo))
        { inputOne := inputOne, inputTwo := inputTwo, graph := .both }) := by
  let leftNext := kernel.crossRecvOne key key left inputOne right inputTwo
  let rightNext := kernel.crossRecvTwo key key right inputTwo left inputOne
  refine ⟨leftNext.2.1, leftNext.2.2, leftNext.1,
    rightNext.2.1, rightNext.2.2, rightNext.1, ?_⟩
  rfl

/-- Process one cannot distinguish `left` from `both`: both apply the literal
same receive map to the same pre-round controls and inputs. -/
theorem physical_one_left_eq_both
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    [Fintype ChildCode]
    [∀ key, Fintype (RightOwner key)]
    [∀ key, Fintype (LeftReceiver key)]
    [∀ key, Fintype (RightReceiver key)]
    [∀ key, Fintype (LeftOwner key)]
    (controls : OneSummaryT × TwoSummaryT) (inputOne : In₁) (inputTwo : In₂) :
    ((physicalController kernel).advanceControls controls
      { inputOne := inputOne, inputTwo := inputTwo, graph := .left }).1 =
    ((physicalController kernel).advanceControls controls
      { inputOne := inputOne, inputTwo := inputTwo, graph := .both }).1 :=
  rfl

/-- Process two's mirror indistinguishability of `right` and `both`. -/
theorem physical_two_right_eq_both
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    [Fintype ChildCode]
    [∀ key, Fintype (RightOwner key)]
    [∀ key, Fintype (LeftReceiver key)]
    [∀ key, Fintype (RightReceiver key)]
    [∀ key, Fintype (LeftOwner key)]
    (controls : OneSummaryT × TwoSummaryT) (inputOne : In₁) (inputTwo : In₂) :
    ((physicalController kernel).advanceControls controls
      { inputOne := inputOne, inputTwo := inputTwo, graph := .right }).2 =
    ((physicalController kernel).advanceControls controls
      { inputOne := inputOne, inputTwo := inputTwo, graph := .both }).2 :=
  rfl

/-! ## Local-summary automaton -/

/-- Both process summaries are lifted to one common universe, as required by
the dependent `Summary : Proc → Type _` interface. -/
local notation "OneLocalSummaryT" =>
  ProfiledRawJointLeaderFreeLiftedOneSummary InitialOne InitialTwo
    ExceptionalOne ExceptionalTwo ChildCode RightOwner LeftReceiver
    RightReceiver LeftOwner Out₁ Out₂

local notation "TwoLocalSummaryT" =>
  ProfiledRawJointLeaderFreeLiftedTwoSummary InitialOne InitialTwo
    ExceptionalOne ExceptionalTwo ChildCode RightOwner LeftReceiver
    RightReceiver LeftOwner Out₁ Out₂

/-- The exact local-summary automaton induced by the Moore carrier. -/
noncomputable def summaryAutomaton
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    [Fintype ChildCode]
    [∀ key, Fintype (RightOwner key)]
    [∀ key, Fintype (LeftReceiver key)]
    [∀ key, Fintype (RightReceiver key)]
    [∀ key, Fintype (LeftOwner key)] :
    LocalSummaryAutomaton In₁ In₂ where
  Summary
    | .one => OneLocalSummaryT
    | .two => TwoLocalSummaryT
  finite
    | .one =>
        @ULift.fintype OneSummaryT
          (@instFintypeProd OneControlT Out₁
            ProfiledRawJointLeaderFreeOneControl.controlFintype inferInstance)
    | .two =>
        @ULift.fintype TwoSummaryT
          (@instFintypeProd TwoControlT Out₂
            ProfiledRawJointLeaderFreeTwoControl.controlFintype inferInstance)
  initial
    | .one => .up (.initial kernel.initialOne, kernel.initialOutputOne)
    | .two => .up (.initial kernel.initialTwo, kernel.initialOutputTwo)
  stepNoRecv
    | .one, summary, .inl input =>
        let next := kernel.noRecvOne summary.down.1 input
        .up (next.2, next.1)
    | .two, summary, .inr input =>
        let next := kernel.noRecvTwo summary.down.1 input
        .up (next.2, next.1)
    | _, summary, _ => summary
  stepRecv
    | .one, self, .inl inputOne, other, .inr inputTwo =>
        let next := kernel.recvOne self.down.1 inputOne other.down.1 inputTwo
        .up (next.2, next.1)
    | .two, self, .inr inputTwo, other, .inl inputOne =>
        let next := kernel.recvTwo self.down.1 inputTwo other.down.1 inputOne
        .up (next.2, next.1)
    | _, self, _, _, _ => self

@[simp] theorem summaryAutomaton_stepNoRecv_one
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    [Fintype ChildCode]
    [∀ key, Fintype (RightOwner key)]
    [∀ key, Fintype (LeftReceiver key)]
    [∀ key, Fintype (RightReceiver key)]
    [∀ key, Fintype (LeftOwner key)]
    (summary : OneSummaryT) (input : In₁) :
    (summaryAutomaton kernel).stepNoRecv Proc.one (.up summary) (.inl input) =
      let next := kernel.noRecvOne summary.1 input
      ULift.up (next.2, next.1) :=
  rfl

@[simp] theorem summaryAutomaton_stepNoRecv_two
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    [Fintype ChildCode]
    [∀ key, Fintype (RightOwner key)]
    [∀ key, Fintype (LeftReceiver key)]
    [∀ key, Fintype (RightReceiver key)]
    [∀ key, Fintype (LeftOwner key)]
    (summary : TwoSummaryT) (input : In₂) :
    (summaryAutomaton kernel).stepNoRecv Proc.two (.up summary) (.inr input) =
      let next := kernel.noRecvTwo summary.1 input
      ULift.up (next.2, next.1) :=
  rfl

@[simp] theorem summaryAutomaton_stepRecv_one
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    [Fintype ChildCode]
    [∀ key, Fintype (RightOwner key)]
    [∀ key, Fintype (LeftReceiver key)]
    [∀ key, Fintype (RightReceiver key)]
    [∀ key, Fintype (LeftOwner key)]
    (one : OneSummaryT) (inputOne : In₁)
    (two : TwoSummaryT) (inputTwo : In₂) :
    (summaryAutomaton kernel).stepRecv Proc.one (.up one) (.inl inputOne)
        (.up two) (.inr inputTwo) =
      let next := kernel.recvOne one.1 inputOne two.1 inputTwo
      ULift.up (next.2, next.1) :=
  rfl

@[simp] theorem summaryAutomaton_stepRecv_two
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    [Fintype ChildCode]
    [∀ key, Fintype (RightOwner key)]
    [∀ key, Fintype (LeftReceiver key)]
    [∀ key, Fintype (RightReceiver key)]
    [∀ key, Fintype (LeftOwner key)]
    (two : TwoSummaryT) (inputTwo : In₂)
    (one : OneSummaryT) (inputOne : In₁) :
    (summaryAutomaton kernel).stepRecv Proc.two (.up two) (.inr inputTwo)
        (.up one) (.inl inputOne) =
      let next := kernel.recvTwo two.1 inputTwo one.1 inputOne
      ULift.up (next.2, next.1) :=
  rfl

end ProfiledRawJointLeaderFreeKernel

end DistributedSynthesis
