/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointLeaderFreeControllerCarrier
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointUnitPolicyMatchedPhase

/-!
# The recurrent raw-joint policy in the leader-free carrier

This module fills the ordinary transition fields of
`ProfiledRawJointLeaderFreeKernel` from the unconditional singleton-policy
handoff.  The initial and exceptional phases remain one small typed adapter;
no semantic proposition is assumed here.

The important transition is the receiver/receiver cross.  It is represented
only by a process-one left receiver paired with a process-two right receiver.
On `left`, both local computations read the target already staged in the
right receiver and restart the same left macro.  On `right`, they read the
target staged in the left receiver and restart the same right macro.  On
`both`, each receiving process independently refreshes its receiver from the
opposite receiver's staged target.  No function receives a graph, leader, or
orientation bit.
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
  (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
  (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
    (initial.code A))
  (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)

/-! ## The four ordinary local families -/

abbrev ProfiledRawJointUnitPolicyRightOwner (_ : Unit) :=
  ProfiledRawJointUnitRightPolicyOwnerControl A strategy initial policy bank

abbrev ProfiledRawJointUnitPolicyLeftReceiver (_ : Unit) :=
  ProfiledRawJointUnitLeftPolicyReceiverControl A strategy initial policy

abbrev ProfiledRawJointUnitPolicyRightReceiver (_ : Unit) :=
  ProfiledRawJointUnitRightPolicyReceiverControl A strategy initial policy

abbrev ProfiledRawJointUnitPolicyLeftOwner (_ : Unit) :=
  ProfiledRawJointUnitLeftPolicyOwnerControl A strategy initial policy bank

/-! ## Total staged-target lookup -/

/-- An off-invariant right receiver still has a total left target.  The
fallback is obtained from the controller's unconditional close theorem at a
fixed dummy physical direction; reachable runs always use the stored target
instead. -/
noncomputable def profiledRawJointUnitPolicyFallbackLeft
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy
      (initial.code A) policy) :
    ProfiledRawJointUnitLeftPolicyMacro A strategy (initial.code A) policy :=
  Classical.choose
    (profiledRawJointUnitRightPolicy_real_close_stages_exact A strategy
      initial policy bank source .first [] default)

/-- Mirror fallback for a left receiver. -/
noncomputable def profiledRawJointUnitPolicyFallbackRight
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy
      (initial.code A) policy) :
    ProfiledRawJointUnitRightPolicyMacro A strategy (initial.code A) policy :=
  Classical.choose
    (profiledRawJointUnitLeftPolicy_real_close_stages_exact A strategy initial
      policy bank source .first [] default)

/-- The literal left macro already staged in a right receiver. -/
noncomputable def profiledRawJointUnitPolicyRightReceiverTarget
    (receiver : ProfiledRawJointUnitRightPolicyReceiverControl A strategy
      initial policy) :
    ProfiledRawJointUnitLeftPolicyMacro A strategy (initial.code A) policy :=
  receiver.2.2.2.getD
    (profiledRawJointUnitPolicyFallbackLeft A strategy initial policy bank
      receiver.1)

/-- The literal right macro already staged in a left receiver. -/
noncomputable def profiledRawJointUnitPolicyLeftReceiverTarget
    (receiver : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy
      initial policy) :
    ProfiledRawJointUnitRightPolicyMacro A strategy (initial.code A) policy :=
  receiver.2.2.2.getD
    (profiledRawJointUnitPolicyFallbackRight A strategy initial policy bank
      receiver.1)

/-! ## Locally executable switch and refresh maps -/

/-- Process one reads a delivered right receiver, restarts its staged left
macro, and executes the current receive as a left receiver. -/
noncomputable def profiledRawJointUnitPolicyStartLeftReceiver
    (receiver : ProfiledRawJointUnitRightPolicyReceiverControl A strategy
      initial policy) (move : In₁ × In₂) :
    Out₁ × ProfiledRawJointUnitLeftPolicyReceiverControl A strategy initial
      policy :=
  let target := profiledRawJointUnitPolicyRightReceiverTarget A strategy
    initial policy bank receiver
  let restart := profiledRawJointUnitRestartLeft A strategy initial policy bank
    target receiver.2.1
  continueProfiledRawJointUnitLeftPolicyReceiver A strategy initial policy
    bank restart.2 restart.1 move

/-- Process two observes `noRecv`, reads the same target from its own right
receiver, installs the staged left owner, and executes its own input. -/
noncomputable def profiledRawJointUnitPolicyStartLeftOwner
    (receiver : ProfiledRawJointUnitRightPolicyReceiverControl A strategy
      initial policy) (input : In₂) :
    Out₂ × ProfiledRawJointUnitLeftPolicyOwnerControl A strategy initial policy
      bank :=
  let target := profiledRawJointUnitPolicyRightReceiverTarget A strategy
    initial policy bank receiver
  let restart := profiledRawJointUnitRestartLeft A strategy initial policy bank
    target receiver.2.1
  stepProfiledRawJointUnitLeftPolicyOwner A strategy initial policy bank
    restart.1 input

/-- Process two's mirror receive-side restart from a delivered left
receiver. -/
noncomputable def profiledRawJointUnitPolicyStartRightReceiver
    (receiver : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy
      initial policy) (move : In₂ × In₁) :
    Out₂ × ProfiledRawJointUnitRightPolicyReceiverControl A strategy initial
      policy :=
  let target := profiledRawJointUnitPolicyLeftReceiverTarget A strategy
    initial policy bank receiver
  let restart := profiledRawJointUnitRestartRight A strategy initial policy
    bank target receiver.2.1
  continueProfiledRawJointUnitRightPolicyReceiver A strategy initial policy
    bank restart.2 restart.1 move

/-- Process one's mirror `noRecv` restart into a right owner. -/
noncomputable def profiledRawJointUnitPolicyStartRightOwner
    (receiver : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy
      initial policy) (input : In₁) :
    Out₁ × ProfiledRawJointUnitRightPolicyOwnerControl A strategy initial
      policy bank :=
  let target := profiledRawJointUnitPolicyLeftReceiverTarget A strategy
    initial policy bank receiver
  let restart := profiledRawJointUnitRestartRight A strategy initial policy
    bank target receiver.2.1
  stepProfiledRawJointUnitRightPolicyOwner A strategy initial policy bank
    restart.1 input

/-! ## Definitional common-source laws -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The two independently executable left restarts carry the same staged
macro. -/
theorem profiledRawJointUnitPolicyStartLeft_common_source
    (receiver : ProfiledRawJointUnitRightPolicyReceiverControl A strategy
      initial policy) (move : In₁ × In₂) :
    (profiledRawJointUnitPolicyStartLeftReceiver A strategy initial policy bank
      receiver move).2.1 =
    (profiledRawJointUnitPolicyStartLeftOwner A strategy initial policy bank
      receiver move.2).2.1 := by
  simp [profiledRawJointUnitPolicyStartLeftReceiver,
    profiledRawJointUnitPolicyStartLeftOwner,
    continueProfiledRawJointUnitLeftPolicyReceiver_source,
    stepProfiledRawJointUnitLeftPolicyOwner_source]

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Right-to-left mirror common-source restart. -/
theorem profiledRawJointUnitPolicyStartRight_common_source
    (receiver : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy
      initial policy) (move : In₂ × In₁) :
    (profiledRawJointUnitPolicyStartRightOwner A strategy initial policy bank
      receiver move.2).2.1 =
    (profiledRawJointUnitPolicyStartRightReceiver A strategy initial policy
      bank receiver move).2.1 := by
  simp [profiledRawJointUnitPolicyStartRightReceiver,
    profiledRawJointUnitPolicyStartRightOwner,
    continueProfiledRawJointUnitRightPolicyReceiver_source,
    stepProfiledRawJointUnitRightPolicyOwner_source]

/-! ## Fixed-policy specialization of the generic carrier -/

abbrev ProfiledRawJointUnitPolicyOneControl
    (InitialOne : Type i₁) (ExceptionalOne : Type e₁) :=
  ProfiledRawJointLeaderFreeOneControl InitialOne ExceptionalOne Unit
    (ProfiledRawJointUnitPolicyRightOwner A strategy initial policy bank)
    (ProfiledRawJointUnitPolicyLeftReceiver A strategy initial policy)

abbrev ProfiledRawJointUnitPolicyTwoControl
    (InitialTwo : Type i₂) (ExceptionalTwo : Type e₂) :=
  ProfiledRawJointLeaderFreeTwoControl InitialTwo ExceptionalTwo Unit
    (ProfiledRawJointUnitPolicyRightReceiver A strategy initial policy)
    (ProfiledRawJointUnitPolicyLeftOwner A strategy initial policy bank)

/--
The only part of the fixed-policy kernel not supplied by the recurrent
handoff.  A later module plugs in the root/initial/exceptional controller and
its total off-invariant receive cases.  These are executable transition maps,
not assumed correctness propositions.

This adapter begins only after the exceptional seam has collapsed to one
fixed child policy.  Repeated `both` at that seam can still carry two distinct
child policies and belongs to the heterogeneous initial carrier, not here.
-/
structure ProfiledRawJointUnitPolicyExceptionalAdapter
    (InitialOne : Type i₁) (InitialTwo : Type i₂)
    (ExceptionalOne : Type e₁) (ExceptionalTwo : Type e₂) where
  initialOne : InitialOne
  initialTwo : InitialTwo
  initialOutputOne : Out₁
  initialOutputTwo : Out₂
  initialNoRecvOne : InitialOne → In₁ → Out₁ ×
    ProfiledRawJointUnitPolicyOneControl A strategy initial policy bank
      InitialOne ExceptionalOne
  exceptionalNoRecvOne : ExceptionalOne → In₁ → Out₁ ×
    ProfiledRawJointUnitPolicyOneControl A strategy initial policy bank
      InitialOne ExceptionalOne
  initialNoRecvTwo : InitialTwo → In₂ → Out₂ ×
    ProfiledRawJointUnitPolicyTwoControl A strategy initial policy bank
      InitialTwo ExceptionalTwo
  exceptionalNoRecvTwo : ExceptionalTwo → In₂ → Out₂ ×
    ProfiledRawJointUnitPolicyTwoControl A strategy initial policy bank
      InitialTwo ExceptionalTwo
  otherRecvOne :
    ProfiledRawJointUnitPolicyOneControl A strategy initial policy bank
        InitialOne ExceptionalOne → In₁ →
      ProfiledRawJointUnitPolicyTwoControl A strategy initial policy bank
        InitialTwo ExceptionalTwo → In₂ →
      Out₁ × ProfiledRawJointUnitPolicyOneControl A strategy initial policy
        bank InitialOne ExceptionalOne
  otherRecvTwo :
    ProfiledRawJointUnitPolicyTwoControl A strategy initial policy bank
        InitialTwo ExceptionalTwo → In₂ →
      ProfiledRawJointUnitPolicyOneControl A strategy initial policy bank
        InitialOne ExceptionalOne → In₁ →
      Out₂ × ProfiledRawJointUnitPolicyTwoControl A strategy initial policy
        bank InitialTwo ExceptionalTwo

/-- The complete leader-free kernel below one fixed child policy. -/
noncomputable def profiledRawJointUnitPolicyLeaderFreeKernel
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo) :
    ProfiledRawJointLeaderFreeKernel In₁ In₂ Out₁ Out₂ InitialOne InitialTwo
      ExceptionalOne ExceptionalTwo Unit
      (ProfiledRawJointUnitPolicyRightOwner A strategy initial policy bank)
      (ProfiledRawJointUnitPolicyLeftReceiver A strategy initial policy)
      (ProfiledRawJointUnitPolicyRightReceiver A strategy initial policy)
      (ProfiledRawJointUnitPolicyLeftOwner A strategy initial policy bank) where
  initialOne := adapter.initialOne
  initialTwo := adapter.initialTwo
  initialOutputOne := adapter.initialOutputOne
  initialOutputTwo := adapter.initialOutputTwo
  initialNoRecvOne := adapter.initialNoRecvOne
  exceptionalNoRecvOne := adapter.exceptionalNoRecvOne
  rightOwnerNoRecvOne := fun _ owner input =>
    stepProfiledRawJointUnitRightPolicyOwner A strategy initial policy bank
      owner input
  leftReceiverNoRecvOne := fun _ receiver input =>
    let next := profiledRawJointUnitPolicyStartRightOwner A strategy initial
      policy bank receiver input
    (next.1, ⟨(), next.2⟩)
  initialNoRecvTwo := adapter.initialNoRecvTwo
  exceptionalNoRecvTwo := adapter.exceptionalNoRecvTwo
  rightReceiverNoRecvTwo := fun _ receiver input =>
    let next := profiledRawJointUnitPolicyStartLeftOwner A strategy initial
      policy bank receiver input
    (next.1, ⟨(), next.2⟩)
  leftOwnerNoRecvTwo := fun _ owner input =>
    stepProfiledRawJointUnitLeftPolicyOwner A strategy initial policy bank
      owner input
  matchedRightRecvOne := fun _ _ _ inputOne receiver inputTwo =>
    let next := profiledRawJointUnitPolicyStartLeftReceiver A strategy initial
      policy bank receiver (inputOne, inputTwo)
    (next.1, ⟨(), next.2⟩)
  matchedRightRecvTwo := fun _ _ receiver inputTwo owner inputOne =>
    let next := continueProfiledRawJointUnitRightPolicyReceiver A strategy
      initial policy bank receiver owner (inputTwo, inputOne)
    (next.1, ⟨(), next.2⟩)
  matchedLeftRecvOne := fun _ _ receiver inputOne owner inputTwo =>
    let next := continueProfiledRawJointUnitLeftPolicyReceiver A strategy
      initial policy bank receiver owner (inputOne, inputTwo)
    (next.1, ⟨(), next.2⟩)
  matchedLeftRecvTwo := fun _ _ _ inputTwo receiver inputOne =>
    let next := profiledRawJointUnitPolicyStartRightReceiver A strategy initial
      policy bank receiver (inputTwo, inputOne)
    (next.1, ⟨(), next.2⟩)
  crossRecvOne := fun _ _ _ inputOne right inputTwo =>
    let next := profiledRawJointUnitPolicyStartLeftReceiver A strategy initial
      policy bank right (inputOne, inputTwo)
    (next.1, ⟨(), next.2⟩)
  crossRecvTwo := fun _ _ _ inputTwo left inputOne =>
    let next := profiledRawJointUnitPolicyStartRightReceiver A strategy initial
      policy bank left (inputTwo, inputOne)
    (next.1, ⟨(), next.2⟩)
  otherRecvOne := adapter.otherRecvOne
  otherRecvTwo := adapter.otherRecvTwo

/-! ## Exact recurrent transition equations -/

section
omit [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem profiledRawJointUnitPolicyKernel_rightOwnerNoRecvOne
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (owner : ProfiledRawJointUnitRightPolicyOwnerControl A strategy initial
      policy bank) (input : In₁) :
    (profiledRawJointUnitPolicyLeaderFreeKernel A strategy initial policy bank
      adapter).rightOwnerNoRecvOne () owner input =
      stepProfiledRawJointUnitRightPolicyOwner A strategy initial policy bank
        owner input :=
  rfl

@[simp] theorem profiledRawJointUnitPolicyKernel_leftReceiverNoRecvOne
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (receiver : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy
      initial policy) (input : In₁) :
    (profiledRawJointUnitPolicyLeaderFreeKernel A strategy initial policy bank
      adapter).leftReceiverNoRecvOne () receiver input =
      let next := profiledRawJointUnitPolicyStartRightOwner A strategy initial
        policy bank receiver input
      (next.1, ⟨(), next.2⟩) :=
  rfl

@[simp] theorem profiledRawJointUnitPolicyKernel_rightReceiverNoRecvTwo
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (receiver : ProfiledRawJointUnitRightPolicyReceiverControl A strategy
      initial policy) (input : In₂) :
    (profiledRawJointUnitPolicyLeaderFreeKernel A strategy initial policy bank
      adapter).rightReceiverNoRecvTwo () receiver input =
      let next := profiledRawJointUnitPolicyStartLeftOwner A strategy initial
        policy bank receiver input
      (next.1, ⟨(), next.2⟩) :=
  rfl

@[simp] theorem profiledRawJointUnitPolicyKernel_leftOwnerNoRecvTwo
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (owner : ProfiledRawJointUnitLeftPolicyOwnerControl A strategy initial
      policy bank) (input : In₂) :
    (profiledRawJointUnitPolicyLeaderFreeKernel A strategy initial policy bank
      adapter).leftOwnerNoRecvTwo () owner input =
      stepProfiledRawJointUnitLeftPolicyOwner A strategy initial policy bank
        owner input :=
  rfl

@[simp] theorem profiledRawJointUnitPolicyKernel_matchedRightRecvOne
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (owner : ProfiledRawJointUnitRightPolicyOwnerControl A strategy initial
      policy bank)
    (receiver : ProfiledRawJointUnitRightPolicyReceiverControl A strategy
      initial policy) (inputOne : In₁) (inputTwo : In₂) :
    (profiledRawJointUnitPolicyLeaderFreeKernel A strategy initial policy bank
      adapter).matchedRightRecvOne () () owner inputOne receiver inputTwo =
      let next := profiledRawJointUnitPolicyStartLeftReceiver A strategy
        initial policy bank receiver (inputOne, inputTwo)
      (next.1, ⟨(), next.2⟩) :=
  rfl

@[simp] theorem profiledRawJointUnitPolicyKernel_matchedRightRecvTwo
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (receiver : ProfiledRawJointUnitRightPolicyReceiverControl A strategy
      initial policy)
    (owner : ProfiledRawJointUnitRightPolicyOwnerControl A strategy initial
      policy bank) (inputTwo : In₂) (inputOne : In₁) :
    (profiledRawJointUnitPolicyLeaderFreeKernel A strategy initial policy bank
      adapter).matchedRightRecvTwo () () receiver inputTwo owner inputOne =
      let next := continueProfiledRawJointUnitRightPolicyReceiver A strategy
        initial policy bank receiver owner (inputTwo, inputOne)
      (next.1, ⟨(), next.2⟩) :=
  rfl

@[simp] theorem profiledRawJointUnitPolicyKernel_matchedLeftRecvOne
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (receiver : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy
      initial policy)
    (owner : ProfiledRawJointUnitLeftPolicyOwnerControl A strategy initial
      policy bank) (inputOne : In₁) (inputTwo : In₂) :
    (profiledRawJointUnitPolicyLeaderFreeKernel A strategy initial policy bank
      adapter).matchedLeftRecvOne () () receiver inputOne owner inputTwo =
      let next := continueProfiledRawJointUnitLeftPolicyReceiver A strategy
        initial policy bank receiver owner (inputOne, inputTwo)
      (next.1, ⟨(), next.2⟩) :=
  rfl

@[simp] theorem profiledRawJointUnitPolicyKernel_matchedLeftRecvTwo
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (owner : ProfiledRawJointUnitLeftPolicyOwnerControl A strategy initial
      policy bank)
    (receiver : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy
      initial policy) (inputTwo : In₂) (inputOne : In₁) :
    (profiledRawJointUnitPolicyLeaderFreeKernel A strategy initial policy bank
      adapter).matchedLeftRecvTwo () () owner inputTwo receiver inputOne =
      let next := profiledRawJointUnitPolicyStartRightReceiver A strategy
        initial policy bank receiver (inputTwo, inputOne)
      (next.1, ⟨(), next.2⟩) :=
  rfl

@[simp] theorem profiledRawJointUnitPolicyKernel_crossRecvOne
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (left : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy initial
      policy)
    (right : ProfiledRawJointUnitRightPolicyReceiverControl A strategy initial
      policy) (inputOne : In₁) (inputTwo : In₂) :
    (profiledRawJointUnitPolicyLeaderFreeKernel A strategy initial policy bank
      adapter).crossRecvOne () () left inputOne right inputTwo =
      let next := profiledRawJointUnitPolicyStartLeftReceiver A strategy
        initial policy bank right (inputOne, inputTwo)
      (next.1, ⟨(), next.2⟩) :=
  rfl

@[simp] theorem profiledRawJointUnitPolicyKernel_crossRecvTwo
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (right : ProfiledRawJointUnitRightPolicyReceiverControl A strategy initial
      policy)
    (left : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy initial
      policy) (inputTwo : In₂) (inputOne : In₁) :
    (profiledRawJointUnitPolicyLeaderFreeKernel A strategy initial policy bank
      adapter).crossRecvTwo () () right inputTwo left inputOne =
      let next := profiledRawJointUnitPolicyStartRightReceiver A strategy
        initial policy bank left (inputTwo, inputOne)
      (next.1, ⟨(), next.2⟩) :=
  rfl

end

/-! ## Common-source preservation at strict selections -/

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- A right-to-left switch installs literally the same left macro at both
processes. -/
theorem profiledRawJointUnitPolicyKernel_switchLeft_common_source
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (owner : ProfiledRawJointUnitRightPolicyOwnerControl A strategy initial
      policy bank)
    (receiver : ProfiledRawJointUnitRightPolicyReceiverControl A strategy
      initial policy) (move : In₁ × In₂) :
    ((profiledRawJointUnitPolicyLeaderFreeKernel A strategy initial policy bank
      adapter).matchedRightRecvOne () () owner move.1 receiver move.2).2.2.1 =
    ((profiledRawJointUnitPolicyLeaderFreeKernel A strategy initial policy bank
      adapter).rightReceiverNoRecvTwo () receiver move.2).2.2.1 :=
  profiledRawJointUnitPolicyStartLeft_common_source A strategy initial policy
    bank receiver move

/-- The same common-source equation holds when strict `left` selects the left
side of a receiver/receiver cross. -/
theorem profiledRawJointUnitPolicyKernel_crossLeft_common_source
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (left : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy initial
      policy)
    (right : ProfiledRawJointUnitRightPolicyReceiverControl A strategy initial
      policy) (move : In₁ × In₂) :
    ((profiledRawJointUnitPolicyLeaderFreeKernel A strategy initial policy bank
      adapter).crossRecvOne () () left move.1 right move.2).2.2.1 =
    ((profiledRawJointUnitPolicyLeaderFreeKernel A strategy initial policy bank
      adapter).rightReceiverNoRecvTwo () right move.2).2.2.1 :=
  profiledRawJointUnitPolicyStartLeft_common_source A strategy initial policy
    bank right move

/-- A left-to-right switch installs literally the same right macro. -/
theorem profiledRawJointUnitPolicyKernel_switchRight_common_source
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (receiver : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy
      initial policy)
    (owner : ProfiledRawJointUnitLeftPolicyOwnerControl A strategy initial
      policy bank) (move : In₁ × In₂) :
    ((profiledRawJointUnitPolicyLeaderFreeKernel A strategy initial policy bank
      adapter).leftReceiverNoRecvOne () receiver move.1).2.2.1 =
    ((profiledRawJointUnitPolicyLeaderFreeKernel A strategy initial policy bank
      adapter).matchedLeftRecvTwo () () owner move.2 receiver move.1).2.2.1 :=
  profiledRawJointUnitPolicyStartRight_common_source A strategy initial policy
    bank receiver (move.2, move.1)

/-- Strict `right` selects the right side of a cross with the same literal
source at both processes. -/
theorem profiledRawJointUnitPolicyKernel_crossRight_common_source
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (left : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy initial
      policy)
    (right : ProfiledRawJointUnitRightPolicyReceiverControl A strategy initial
      policy) (move : In₁ × In₂) :
    ((profiledRawJointUnitPolicyLeaderFreeKernel A strategy initial policy bank
      adapter).leftReceiverNoRecvOne () left move.1).2.2.1 =
    ((profiledRawJointUnitPolicyLeaderFreeKernel A strategy initial policy bank
      adapter).crossRecvTwo () () right move.2 left move.1).2.2.1 :=
  profiledRawJointUnitPolicyStartRight_common_source A strategy initial policy
    bank left (move.2, move.1)

/-- Interior matched-right continuation preserves a common source. -/
theorem profiledRawJointUnitPolicyKernel_matchedRight_common_source
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (owner : ProfiledRawJointUnitRightPolicyOwnerControl A strategy initial
      policy bank)
    (receiver : ProfiledRawJointUnitRightPolicyReceiverControl A strategy
      initial policy) (hsame : owner.1 = receiver.1) (move : In₁ × In₂) :
    ((profiledRawJointUnitPolicyLeaderFreeKernel A strategy initial policy bank
      adapter).rightOwnerNoRecvOne () owner move.1).2.1 =
    ((profiledRawJointUnitPolicyLeaderFreeKernel A strategy initial policy bank
      adapter).matchedRightRecvTwo () () receiver move.2 owner move.1).2.2.1 := by
  rw [profiledRawJointUnitPolicyKernel_rightOwnerNoRecvOne,
    profiledRawJointUnitPolicyKernel_matchedRightRecvTwo,
    stepProfiledRawJointUnitRightPolicyOwner_source,
    continueProfiledRawJointUnitRightPolicyReceiver_source]
  exact hsame

/-- Interior matched-left mirror. -/
theorem profiledRawJointUnitPolicyKernel_matchedLeft_common_source
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (receiver : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy
      initial policy)
    (owner : ProfiledRawJointUnitLeftPolicyOwnerControl A strategy initial
      policy bank) (hsame : receiver.1 = owner.1) (move : In₁ × In₂) :
    ((profiledRawJointUnitPolicyLeaderFreeKernel A strategy initial policy bank
      adapter).matchedLeftRecvOne () () receiver move.1 owner move.2).2.2.1 =
    ((profiledRawJointUnitPolicyLeaderFreeKernel A strategy initial policy bank
      adapter).leftOwnerNoRecvTwo () owner move.2).2.1 := by
  rw [profiledRawJointUnitPolicyKernel_matchedLeftRecvOne,
    profiledRawJointUnitPolicyKernel_leftOwnerNoRecvTwo,
    continueProfiledRawJointUnitLeftPolicyReceiver_source,
    stepProfiledRawJointUnitLeftPolicyOwner_source]
  exact hsame

end

/-! ## The specialized five-case recurrent pair table -/

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- In the fixed-policy recurrent carrier, a simultaneous receive from a
matched-right pair produces the proof-side receiver/receiver cross. -/
theorem profiledRawJointUnitPolicyKernel_matchedRight_both_hasCrossShape
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (owner : ProfiledRawJointUnitRightPolicyOwnerControl A strategy initial
      policy bank)
    (receiver : ProfiledRawJointUnitRightPolicyReceiverControl A strategy
      initial policy) (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (inputOne : In₁) (inputTwo : In₂) :
    ProfiledRawJointLeaderFreeKernel.HasCrossShape
      ((profiledRawJointUnitPolicyLeaderFreeKernel A strategy initial policy
        bank adapter).physicalController.advanceControls
        ((.rightOwner () owner, oldOutputOne),
          (.rightReceiver () receiver, oldOutputTwo))
        { inputOne := inputOne, inputTwo := inputTwo, graph := .both }) :=
  ProfiledRawJointLeaderFreeKernel.matchedRight_both_hasCrossShape
    (profiledRawJointUnitPolicyLeaderFreeKernel A strategy initial policy bank
      adapter) () owner receiver oldOutputOne oldOutputTwo inputOne inputTwo

/-- The matched-left mirror enters the same proof-side cross. -/
theorem profiledRawJointUnitPolicyKernel_matchedLeft_both_hasCrossShape
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (receiver : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy
      initial policy)
    (owner : ProfiledRawJointUnitLeftPolicyOwnerControl A strategy initial
      policy bank) (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (inputOne : In₁) (inputTwo : In₂) :
    ProfiledRawJointLeaderFreeKernel.HasCrossShape
      ((profiledRawJointUnitPolicyLeaderFreeKernel A strategy initial policy
        bank adapter).physicalController.advanceControls
        ((.leftReceiver () receiver, oldOutputOne),
          (.leftOwner () owner, oldOutputTwo))
        { inputOne := inputOne, inputTwo := inputTwo, graph := .both }) :=
  ProfiledRawJointLeaderFreeKernel.matchedLeft_both_hasCrossShape
    (profiledRawJointUnitPolicyLeaderFreeKernel A strategy initial policy bank
      adapter) () receiver owner oldOutputOne oldOutputTwo inputOne inputTwo

/-- From cross, strict `left` is selected only by process two's honest
non-receipt and produces a matched-left pair. -/
theorem profiledRawJointUnitPolicyKernel_cross_left_hasMatchedLeftShape
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (left : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy initial
      policy)
    (right : ProfiledRawJointUnitRightPolicyReceiverControl A strategy initial
      policy) (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (inputOne : In₁) (inputTwo : In₂) :
    ProfiledRawJointLeaderFreeKernel.HasMatchedLeftShape
      ((profiledRawJointUnitPolicyLeaderFreeKernel A strategy initial policy
        bank adapter).physicalController.advanceControls
        ((.leftReceiver () left, oldOutputOne),
          (.rightReceiver () right, oldOutputTwo))
        { inputOne := inputOne, inputTwo := inputTwo, graph := .left }) :=
  ProfiledRawJointLeaderFreeKernel.cross_left_hasMatchedLeftShape
    (profiledRawJointUnitPolicyLeaderFreeKernel A strategy initial policy bank
      adapter) () left right oldOutputOne oldOutputTwo inputOne inputTwo

/-- From cross, strict `right` is the mirror honest-non-receipt case. -/
theorem profiledRawJointUnitPolicyKernel_cross_right_hasMatchedRightShape
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (left : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy initial
      policy)
    (right : ProfiledRawJointUnitRightPolicyReceiverControl A strategy initial
      policy) (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (inputOne : In₁) (inputTwo : In₂) :
    ProfiledRawJointLeaderFreeKernel.HasMatchedRightShape
      ((profiledRawJointUnitPolicyLeaderFreeKernel A strategy initial policy
        bank adapter).physicalController.advanceControls
        ((.leftReceiver () left, oldOutputOne),
          (.rightReceiver () right, oldOutputTwo))
        { inputOne := inputOne, inputTwo := inputTwo, graph := .right }) :=
  ProfiledRawJointLeaderFreeKernel.cross_right_hasMatchedRightShape
    (profiledRawJointUnitPolicyLeaderFreeKernel A strategy initial policy bank
      adapter) () left right oldOutputOne oldOutputTwo inputOne inputTwo

/-- A further simultaneous receive refreshes both local receivers and remains
in the cross shape. -/
theorem profiledRawJointUnitPolicyKernel_cross_both_hasCrossShape
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (left : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy initial
      policy)
    (right : ProfiledRawJointUnitRightPolicyReceiverControl A strategy initial
      policy) (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (inputOne : In₁) (inputTwo : In₂) :
    ProfiledRawJointLeaderFreeKernel.HasCrossShape
      ((profiledRawJointUnitPolicyLeaderFreeKernel A strategy initial policy
        bank adapter).physicalController.advanceControls
        ((.leftReceiver () left, oldOutputOne),
          (.rightReceiver () right, oldOutputTwo))
        { inputOne := inputOne, inputTwo := inputTwo, graph := .both }) :=
  ProfiledRawJointLeaderFreeKernel.cross_both_hasCrossShape
    (profiledRawJointUnitPolicyLeaderFreeKernel A strategy initial policy bank
      adapter) () left right oldOutputOne oldOutputTwo inputOne inputTwo

end

end

end DetParityAutomaton

end DistributedSynthesis
