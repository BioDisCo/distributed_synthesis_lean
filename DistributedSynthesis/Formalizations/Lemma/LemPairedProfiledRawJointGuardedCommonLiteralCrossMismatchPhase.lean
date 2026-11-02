/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossPolicyInstallation

/-!
# Finite local phase shell for literal cross-table mismatches

The retained annotation contains both one-sided tables.  Hence a local
receipt event can select the table matching that endpoint's current role:

* process one uses the right sender on `noRecv` and the left receiver on
  `recv`;
* process two uses the left sender on `noRecv` and the right receiver on
  `recv`.

This removes the structural part of a strict reversal.  A right-to-left
switch (`procOne.recv`, `procTwo.noRecv`) installs and advances the same left
table at both endpoints; the mirror installs and advances the same right
table.  On `both`, the locally indistinguishable events retain exactly one
finite split: process one is in the left table and process two in the right
table.  Repeating `both` does not multiply that split.

The executable maps below accept only a stored finite phase and the endpoint's
local input/delivered input.  They receive no graph, orientation, leader bit,
strict-leader bit, hidden member, or semantic history.  The final global-step
function is explicitly proof-side: it only records which pair of these local
maps a physical graph invokes.
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

private abbrev Extra :=
  ProfiledRawJointGuardedCommonLiteralCrossExtra A

private abbrev RightSender :=
  ProfiledRawJointGuardedCommonRightLiteralCrossSenderState A

private abbrev RightReceiver :=
  ProfiledRawJointGuardedCommonRightLiteralCrossReceiverState A

private abbrev LeftSender :=
  ProfiledRawJointGuardedCommonLeftLiteralCrossSenderState A

private abbrev LeftReceiver :=
  ProfiledRawJointGuardedCommonLeftLiteralCrossReceiverState A

/-! ## Fixed finite local phases -/

/-- Process one is either the right-table sender or the left-table receiver.
The complete two-table annotation is retained in either case. -/
abbrev ProfiledRawJointGuardedCommonLiteralCrossMismatchOneState :=
  (Extra A × RightSender A) ⊕ (Extra A × LeftReceiver A)

/-- Process-two mirror. -/
abbrev ProfiledRawJointGuardedCommonLiteralCrossMismatchTwoState :=
  (Extra A × RightReceiver A) ⊕ (Extra A × LeftSender A)

noncomputable instance
    profiledRawJointGuardedCommonLiteralCrossMismatchOneStateFintype :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralCrossMismatchOneState A) := by
  infer_instance

noncomputable instance
    profiledRawJointGuardedCommonLiteralCrossMismatchTwoStateFintype :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralCrossMismatchTwoState A) := by
  infer_instance

/-- Both endpoints begin in the retained right table. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossMismatchRightInitial
    (extra : Extra A) (anchor : Bool) :
    ProfiledRawJointGuardedCommonLiteralCrossMismatchOneState A ×
      ProfiledRawJointGuardedCommonLiteralCrossMismatchTwoState A :=
  (.inl
      (extra,
        profiledRawJointGuardedCommonRightLiteralCrossSenderInitial A extra.1),
    .inl
      (extra,
        profiledRawJointGuardedCommonRightLiteralCrossReceiverInitial A
          extra.1 anchor))

/-- Both endpoints begin in the left table. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossMismatchLeftInitial
    (extra : Extra A) (anchor : Bool) :
    ProfiledRawJointGuardedCommonLiteralCrossMismatchOneState A ×
      ProfiledRawJointGuardedCommonLiteralCrossMismatchTwoState A :=
  (.inr
      (extra,
        profiledRawJointGuardedCommonLeftLiteralCrossReceiverInitial A extra.2
          anchor),
    .inr
      (extra,
        profiledRawJointGuardedCommonLeftLiteralCrossSenderInitial A extra.2))

/-! ## Installation from the table stored at the current policy occurrence -/

/-- Forget the retained copy of the two-table annotation at process one. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossMismatchForgetOne
    (state : ProfiledRawJointGuardedCommonLiteralCrossMismatchOneState A) :
    ProfiledRawJointGuardedCommonLiteralCrossOneState A :=
  match state with
  | .inl (_extra, sender) => .inl sender
  | .inr (_extra, receiver) => .inr receiver

/-- Process-two mirror of `MismatchForgetOne`. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossMismatchForgetTwo
    (state : ProfiledRawJointGuardedCommonLiteralCrossMismatchTwoState A) :
    ProfiledRawJointGuardedCommonLiteralCrossTwoState A :=
  match state with
  | .inl (_extra, receiver) => .inl receiver
  | .inr (_extra, sender) => .inr sender

namespace ProfiledRawJointGuardedCommonDecoratedPolicyPackage

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

private abbrev CommonPoint :=
  ProfiledRawJointGuardedCommonSemanticPoint A strategy

private abbrev CrossValid :=
  ProfiledRawJointGuardedCommonLiteralCrossExtraValid A strategy hwin

variable {initial : CommonPoint A strategy}

/-- Install the right phase from `extraAt state`, the table already stored at
the current policy occurrence.  In particular the definition has no current
input pair and cannot inspect a blind endpoint's missing partner input. -/
noncomputable def currentRightLiteralCrossMismatchInitial
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin))
    (anchor : Bool) :
    ProfiledRawJointGuardedCommonLiteralCrossMismatchOneState A ×
      ProfiledRawJointGuardedCommonLiteralCrossMismatchTwoState A :=
  profiledRawJointGuardedCommonLiteralCrossMismatchRightInitial A
    (package.extraAt A strategy hwin state) anchor

/-- Current left phase, using the other component of the same stored
two-table annotation. -/
noncomputable def currentLeftLiteralCrossMismatchInitial
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin))
    (anchor : Bool) :
    ProfiledRawJointGuardedCommonLiteralCrossMismatchOneState A ×
      ProfiledRawJointGuardedCommonLiteralCrossMismatchTwoState A :=
  profiledRawJointGuardedCommonLiteralCrossMismatchLeftInitial A
    (package.extraAt A strategy hwin state) anchor

/-- Successor-table refresh used only at a common automatic cut, where the
cut interface supplies the complete input pair.  Blind recurrent transitions
do not call this function. -/
noncomputable def nextRightLiteralCrossMismatchInitial
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin))
    (input : In₁ × In₂) (anchor : Bool) :
    ProfiledRawJointGuardedCommonLiteralCrossMismatchOneState A ×
      ProfiledRawJointGuardedCommonLiteralCrossMismatchTwoState A :=
  profiledRawJointGuardedCommonLiteralCrossMismatchRightInitial A
    (package.nextExtraAt A strategy hwin state input) anchor

/-- Left mirror of the common-cut refresh. -/
noncomputable def nextLeftLiteralCrossMismatchInitial
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin))
    (input : In₁ × In₂) (anchor : Bool) :
    ProfiledRawJointGuardedCommonLiteralCrossMismatchOneState A ×
      ProfiledRawJointGuardedCommonLiteralCrossMismatchTwoState A :=
  profiledRawJointGuardedCommonLiteralCrossMismatchLeftInitial A
    (package.nextExtraAt A strategy hwin state input) anchor

/-- Exact refresh law: installing at the actual successor is definitionally
the same as replacing the retained annotation by `nextExtraAt`.  What remains
for epoch chaining is to show that the automatic-cut trace reaches this
common refresh interface, not to identify the refreshed table. -/
theorem currentRightLiteralCrossMismatchInitial_successor
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin))
    (input : In₁ × In₂) (anchor : Bool) :
    package.currentRightLiteralCrossMismatchInitial A strategy hwin
        (package.policy.successor state input) anchor =
      package.nextRightLiteralCrossMismatchInitial A strategy hwin state input
        anchor := by
  rfl

/-- Left exact refresh law. -/
theorem currentLeftLiteralCrossMismatchInitial_successor
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin))
    (input : In₁ × In₂) (anchor : Bool) :
    package.currentLeftLiteralCrossMismatchInitial A strategy hwin
        (package.policy.successor state input) anchor =
      package.nextLeftLiteralCrossMismatchInitial A strategy hwin state input
        anchor := by
  rfl

/-- Erasing the retained annotation gives exactly the pre-existing current
right installation. -/
@[simp] theorem currentRightLiteralCrossMismatchInitial_forget
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin))
    (anchor : Bool) :
    (profiledRawJointGuardedCommonLiteralCrossMismatchForgetOne A
        (package.currentRightLiteralCrossMismatchInitial A strategy hwin state
          anchor).1,
      profiledRawJointGuardedCommonLiteralCrossMismatchForgetTwo A
        (package.currentRightLiteralCrossMismatchInitial A strategy hwin state
          anchor).2) =
      package.currentRightLiteralCrossInitial A strategy hwin state anchor := by
  rfl

/-- Left mirror of `currentRightLiteralCrossMismatchInitial_forget`. -/
@[simp] theorem currentLeftLiteralCrossMismatchInitial_forget
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin))
    (anchor : Bool) :
    (profiledRawJointGuardedCommonLiteralCrossMismatchForgetOne A
        (package.currentLeftLiteralCrossMismatchInitial A strategy hwin state
          anchor).1,
      profiledRawJointGuardedCommonLiteralCrossMismatchForgetTwo A
        (package.currentLeftLiteralCrossMismatchInitial A strategy hwin state
          anchor).2) =
      package.currentLeftLiteralCrossInitial A strategy hwin state anchor := by
  rfl

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

/-! ## Total graph-blind local transitions -/

/-- A process-one nonreceive always leaves process one in the right sender.
If it was previously the left receiver, this is the strict-reversal event and
the retained right table is restarted before consuming the current input. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossMismatchNoRecvOne
    (state : ProfiledRawJointGuardedCommonLiteralCrossMismatchOneState A)
    (input : In₁) : Out₁ ×
      ProfiledRawJointGuardedCommonLiteralCrossMismatchOneState A :=
  match state with
  | .inl (extra, sender) =>
      let next :=
        profiledRawJointGuardedCommonRightLiteralCrossSenderNoRecv A sender
          input
      (next.1, .inl (extra, next.2))
  | .inr (extra, _receiver) =>
      let sender :=
        profiledRawJointGuardedCommonRightLiteralCrossSenderInitial A extra.1
      let next :=
        profiledRawJointGuardedCommonRightLiteralCrossSenderNoRecv A sender
          input
      (next.1, .inl (extra, next.2))

/-- A process-one receive always leaves process one in the left receiver.
Switching uses the fixed `false` member.  This is not an observed bit: both
members of the preselected move are winning and retain the same literal
two-record guard. -/
noncomputable def profiledRawJointGuardedCommonLiteralCrossMismatchRecvOne
    (state : ProfiledRawJointGuardedCommonLiteralCrossMismatchOneState A)
    (own : In₁) (delivered : In₂) : Out₁ ×
      ProfiledRawJointGuardedCommonLiteralCrossMismatchOneState A :=
  match state with
  | .inr (extra, receiver) =>
      let next :=
        profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecvPhysical A
          receiver own delivered
      (next.1, .inr (extra, next.2))
  | .inl (extra, _sender) =>
      let receiver :=
        profiledRawJointGuardedCommonLeftLiteralCrossReceiverInitial A extra.2
          false
      let next :=
        profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecvPhysical A
          receiver own delivered
      (next.1, .inr (extra, next.2))

/-- Process-two nonreceive always selects the left sender. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossMismatchNoRecvTwo
    (state : ProfiledRawJointGuardedCommonLiteralCrossMismatchTwoState A)
    (input : In₂) : Out₂ ×
      ProfiledRawJointGuardedCommonLiteralCrossMismatchTwoState A :=
  match state with
  | .inr (extra, sender) =>
      let next :=
        profiledRawJointGuardedCommonLeftLiteralCrossSenderNoRecv A sender input
      (next.1, .inr (extra, next.2))
  | .inl (extra, _receiver) =>
      let sender :=
        profiledRawJointGuardedCommonLeftLiteralCrossSenderInitial A extra.2
      let next :=
        profiledRawJointGuardedCommonLeftLiteralCrossSenderNoRecv A sender input
      (next.1, .inr (extra, next.2))

/-- Process-two receive always selects the right receiver. -/
noncomputable def profiledRawJointGuardedCommonLiteralCrossMismatchRecvTwo
    (state : ProfiledRawJointGuardedCommonLiteralCrossMismatchTwoState A)
    (own : In₂) (delivered : In₁) : Out₂ ×
      ProfiledRawJointGuardedCommonLiteralCrossMismatchTwoState A :=
  match state with
  | .inl (extra, receiver) =>
      let next :=
        profiledRawJointGuardedCommonRightLiteralCrossReceiverRecvPhysical A
          receiver own delivered
      (next.1, .inl (extra, next.2))
  | .inr (extra, _sender) =>
      let receiver :=
        profiledRawJointGuardedCommonRightLiteralCrossReceiverInitial A extra.1
          false
      let next :=
        profiledRawJointGuardedCommonRightLiteralCrossReceiverRecvPhysical A
          receiver own delivered
      (next.1, .inl (extra, next.2))

/-! ## Retention and phase laws -/

def profiledRawJointGuardedCommonLiteralCrossMismatchExtraOne
    (state : ProfiledRawJointGuardedCommonLiteralCrossMismatchOneState A) :
    Extra A :=
  match state with
  | .inl state => state.1
  | .inr state => state.1

def profiledRawJointGuardedCommonLiteralCrossMismatchExtraTwo
    (state : ProfiledRawJointGuardedCommonLiteralCrossMismatchTwoState A) :
    Extra A :=
  match state with
  | .inl state => state.1
  | .inr state => state.1

/-- `false` names the right phase and `true` the left phase.  This is a stored
constructor projection, never a physical orientation input. -/
def profiledRawJointGuardedCommonLiteralCrossMismatchSideOne
    (state : ProfiledRawJointGuardedCommonLiteralCrossMismatchOneState A) :
    Bool :=
  match state with
  | .inl _ => false
  | .inr _ => true

def profiledRawJointGuardedCommonLiteralCrossMismatchSideTwo
    (state : ProfiledRawJointGuardedCommonLiteralCrossMismatchTwoState A) :
    Bool :=
  match state with
  | .inl _ => false
  | .inr _ => true

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem
    profiledRawJointGuardedCommonLiteralCrossMismatchNoRecvOne_extra
    (state : ProfiledRawJointGuardedCommonLiteralCrossMismatchOneState A)
    (input : In₁) :
    profiledRawJointGuardedCommonLiteralCrossMismatchExtraOne A
        (profiledRawJointGuardedCommonLiteralCrossMismatchNoRecvOne A state
          input).2 =
      profiledRawJointGuardedCommonLiteralCrossMismatchExtraOne A state := by
  cases state <;> rfl

@[simp] theorem profiledRawJointGuardedCommonLiteralCrossMismatchRecvOne_extra
    (state : ProfiledRawJointGuardedCommonLiteralCrossMismatchOneState A)
    (own : In₁) (delivered : In₂) :
    profiledRawJointGuardedCommonLiteralCrossMismatchExtraOne A
        (profiledRawJointGuardedCommonLiteralCrossMismatchRecvOne A state own
          delivered).2 =
      profiledRawJointGuardedCommonLiteralCrossMismatchExtraOne A state := by
  cases state <;> rfl

@[simp] theorem
    profiledRawJointGuardedCommonLiteralCrossMismatchNoRecvTwo_extra
    (state : ProfiledRawJointGuardedCommonLiteralCrossMismatchTwoState A)
    (input : In₂) :
    profiledRawJointGuardedCommonLiteralCrossMismatchExtraTwo A
        (profiledRawJointGuardedCommonLiteralCrossMismatchNoRecvTwo A state
          input).2 =
      profiledRawJointGuardedCommonLiteralCrossMismatchExtraTwo A state := by
  cases state <;> rfl

@[simp] theorem profiledRawJointGuardedCommonLiteralCrossMismatchRecvTwo_extra
    (state : ProfiledRawJointGuardedCommonLiteralCrossMismatchTwoState A)
    (own : In₂) (delivered : In₁) :
    profiledRawJointGuardedCommonLiteralCrossMismatchExtraTwo A
        (profiledRawJointGuardedCommonLiteralCrossMismatchRecvTwo A state own
          delivered).2 =
      profiledRawJointGuardedCommonLiteralCrossMismatchExtraTwo A state := by
  cases state <;> rfl

@[simp] theorem
    profiledRawJointGuardedCommonLiteralCrossMismatchNoRecvOne_side
    (state : ProfiledRawJointGuardedCommonLiteralCrossMismatchOneState A)
    (input : In₁) :
    profiledRawJointGuardedCommonLiteralCrossMismatchSideOne A
        (profiledRawJointGuardedCommonLiteralCrossMismatchNoRecvOne A state
          input).2 = false := by
  cases state <;> rfl

@[simp] theorem profiledRawJointGuardedCommonLiteralCrossMismatchRecvOne_side
    (state : ProfiledRawJointGuardedCommonLiteralCrossMismatchOneState A)
    (own : In₁) (delivered : In₂) :
    profiledRawJointGuardedCommonLiteralCrossMismatchSideOne A
        (profiledRawJointGuardedCommonLiteralCrossMismatchRecvOne A state own
          delivered).2 = true := by
  cases state <;> rfl

@[simp] theorem
    profiledRawJointGuardedCommonLiteralCrossMismatchNoRecvTwo_side
    (state : ProfiledRawJointGuardedCommonLiteralCrossMismatchTwoState A)
    (input : In₂) :
    profiledRawJointGuardedCommonLiteralCrossMismatchSideTwo A
        (profiledRawJointGuardedCommonLiteralCrossMismatchNoRecvTwo A state
          input).2 = true := by
  cases state <;> rfl

@[simp] theorem profiledRawJointGuardedCommonLiteralCrossMismatchRecvTwo_side
    (state : ProfiledRawJointGuardedCommonLiteralCrossMismatchTwoState A)
    (own : In₂) (delivered : In₁) :
    profiledRawJointGuardedCommonLiteralCrossMismatchSideTwo A
        (profiledRawJointGuardedCommonLiteralCrossMismatchRecvTwo A state own
          delivered).2 = false := by
  cases state <;> rfl

end

/-! ## Proof-side three-graph phase audit -/

/-- Pair the honest local maps for one proof-side physical round.  This is an
audit evaluator, not an executable endpoint transition. -/
noncomputable def profiledRawJointGuardedCommonLiteralCrossMismatchLocalStep
    (one : ProfiledRawJointGuardedCommonLiteralCrossMismatchOneState A)
    (two : ProfiledRawJointGuardedCommonLiteralCrossMismatchTwoState A)
    (input : In₁ × In₂) (graph : Graph) :=
  match graph with
  | .right =>
      (profiledRawJointGuardedCommonLiteralCrossMismatchNoRecvOne A one
          input.1,
        profiledRawJointGuardedCommonLiteralCrossMismatchRecvTwo A two
          input.2 input.1)
  | .left =>
      (profiledRawJointGuardedCommonLiteralCrossMismatchRecvOne A one input.1
          input.2,
        profiledRawJointGuardedCommonLiteralCrossMismatchNoRecvTwo A two
          input.2)
  | .both =>
      (profiledRawJointGuardedCommonLiteralCrossMismatchRecvOne A one input.1
          input.2,
        profiledRawJointGuardedCommonLiteralCrossMismatchRecvTwo A two
          input.2 input.1)

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- The retained two-table ID is invariant under every physical event,
provided the two endpoints carried the same ID beforehand. -/
theorem profiledRawJointGuardedCommonLiteralCrossMismatchLocalStep_extra_eq
    (one : ProfiledRawJointGuardedCommonLiteralCrossMismatchOneState A)
    (two : ProfiledRawJointGuardedCommonLiteralCrossMismatchTwoState A)
    (hsame :
      profiledRawJointGuardedCommonLiteralCrossMismatchExtraOne A one =
        profiledRawJointGuardedCommonLiteralCrossMismatchExtraTwo A two)
    (input : In₁ × In₂) (graph : Graph) :
    let next :=
      profiledRawJointGuardedCommonLiteralCrossMismatchLocalStep A one two
        input graph
    profiledRawJointGuardedCommonLiteralCrossMismatchExtraOne A next.1.2 =
      profiledRawJointGuardedCommonLiteralCrossMismatchExtraTwo A next.2.2 := by
  cases graph <;> simp [hsame,
    profiledRawJointGuardedCommonLiteralCrossMismatchLocalStep]

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- After the round the two finite phase tags have exactly the receipt shape:
aligned right on `right`, aligned left on `left`, and the unique left/right
split on `both`, independently of the preceding phase tags. -/
theorem profiledRawJointGuardedCommonLiteralCrossMismatchLocalStep_sides
    (one : ProfiledRawJointGuardedCommonLiteralCrossMismatchOneState A)
    (two : ProfiledRawJointGuardedCommonLiteralCrossMismatchTwoState A)
    (input : In₁ × In₂) (graph : Graph) :
    let next :=
      profiledRawJointGuardedCommonLiteralCrossMismatchLocalStep A one two
        input graph
    (profiledRawJointGuardedCommonLiteralCrossMismatchSideOne A next.1.2,
      profiledRawJointGuardedCommonLiteralCrossMismatchSideTwo A next.2.2) =
      match graph with
      | .right => (false, false)
      | .left => (true, true)
      | .both => (true, false) := by
  cases graph <;> simp
    [profiledRawJointGuardedCommonLiteralCrossMismatchLocalStep]

end

end DetParityAutomaton

end DistributedSynthesis
