/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryBootstrap
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossLocalRound

/-!
# Strict receives inside the root-pinned entry bootstrap

The entry bootstrap stores one blind sender and two receiver candidates for
the opposite orientation at each endpoint.  This file supplies the first
operational layer below that storage.  A strict receive advances exactly the
receiver selected by the endpoint's stored member bit and retains the
dormant sender.  The opposite endpoint advances the matching sender through
its existing no-receive map.

`ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryAligned` is the
proof-side synchronization invariant.  It says that the two stored member
bits agree and that each selected receiver carries the same table move and
shared controller control as the opposite sender.  The initial bootstrap
pair satisfies this invariant after the actual entry input has been consumed,
and both strict directions preserve it.

No executable definition in this file receives a graph, orientation,
leader bit, semantic history, or proof of alignment.
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

private abbrev CommonPoint :=
  ProfiledRawJointGuardedCommonSemanticPoint A strategy

private abbrev OneControl :=
  ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneControl A

private abbrev TwoControl :=
  ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoControl A

private abbrev RightReceiver :=
  ProfiledRawJointGuardedCommonRightLiteralCrossReceiverState A

private abbrev LeftReceiver :=
  ProfiledRawJointGuardedCommonLeftLiteralCrossReceiverState A

/-! ## Updating one locally selected receiver -/

/-- Replace the member selected by `member`, leaving the other receiver
candidate unchanged. -/
def profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryReplaceCandidate
    {Control : Type*} (fork : FiniteDelayedFork Control) (member : Bool)
    (next : Control) : FiniteDelayedFork Control :=
  if member then ⟨fork.openControl, next⟩
  else ⟨next, fork.closedControl⟩

@[simp] theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryReplaceCandidate_selected
    {Control : Type*} (fork : FiniteDelayedFork Control) (member : Bool)
    (next : Control) :
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryReplaceCandidate
      fork member next).candidate member = next := by
  cases member <;>
    simp [profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryReplaceCandidate]

/-- Process one receives along the left-oriented table selected by its stored
member.  Its right-oriented sender is dormant in this strict-left round. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOpenRecvOne
    (one : OneControl A) (own : In₁) (_two : TwoControl A)
    (delivered : In₂) : OneControl A × Out₁ :=
  let receiver := one.2.2.candidate one.1
  let next :=
    profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecvPhysical A
      receiver own delivered
  ((one.1, one.2.1,
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryReplaceCandidate
        one.2.2 one.1 next.2),
    next.1)

/-- Process-two strict-right mirror. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOpenRecvTwo
    (two : TwoControl A) (own : In₂) (_one : OneControl A)
    (delivered : In₁) : TwoControl A × Out₂ :=
  let receiver := two.2.2.candidate two.1
  let next :=
    profiledRawJointGuardedCommonRightLiteralCrossReceiverRecvPhysical A
      receiver own delivered
  ((two.1, two.2.1,
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryReplaceCandidate
        two.2.2 two.1 next.2),
    next.1)

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOpenRecvOne_member
    (one : OneControl A) (own : In₁) (two : TwoControl A)
    (delivered : In₂) :
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOpenRecvOne A one
      own two delivered).1.1 = one.1 :=
  rfl

@[simp] theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryNoRecvOne_member
    (one : OneControl A) (input : In₁) :
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryNoRecvOne A one
      input).1.1 = one.1 :=
  rfl

@[simp] theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryNoRecvTwo_member
    (two : TwoControl A) (input : In₂) :
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryNoRecvTwo A two
      input).1.1 = two.1 :=
  rfl

@[simp] theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOpenRecvTwo_member
    (two : TwoControl A) (own : In₂) (one : OneControl A)
    (delivered : In₁) :
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOpenRecvTwo A two
      own one delivered).1.1 = two.1 :=
  rfl

@[simp] theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOpenRecvOne_sender
    (one : OneControl A) (own : In₁) (two : TwoControl A)
    (delivered : In₂) :
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOpenRecvOne A one
      own two delivered).1.2.1 = one.2.1 :=
  rfl

@[simp] theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOpenRecvTwo_sender
    (two : TwoControl A) (own : In₂) (one : OneControl A)
    (delivered : In₁) :
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOpenRecvTwo A two
      own one delivered).1.2.1 = two.2.1 :=
  rfl

@[simp] theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryNoRecvOne_receivers
    (one : OneControl A) (input : In₁) :
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryNoRecvOne A one
      input).1.2.2 = one.2.2 :=
  rfl

@[simp] theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryNoRecvTwo_receivers
    (two : TwoControl A) (input : In₂) :
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryNoRecvTwo A two
      input).1.2.2 = two.2.2 :=
  rfl

@[simp] theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOpenRecvOne_selected
    (one : OneControl A) (own : In₁) (two : TwoControl A)
    (delivered : In₂) :
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOpenRecvOne A one
      own two delivered).1.2.2.candidate one.1 =
      (profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecvPhysical A
        (one.2.2.candidate one.1) own delivered).2 := by
  simp [profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOpenRecvOne]

@[simp] theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOpenRecvTwo_selected
    (two : TwoControl A) (own : In₂) (one : OneControl A)
    (delivered : In₁) :
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOpenRecvTwo A two
      own one delivered).1.2.2.candidate two.1 =
      (profiledRawJointGuardedCommonRightLiteralCrossReceiverRecvPhysical A
        (two.2.2.candidate two.1) own delivered).2 := by
  simp [profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOpenRecvTwo]

end

/-! ## Selected-table synchronization -/

/-- The two endpoint controls name the same member, and the sender/selected
receiver pair for each orientation has the same guarded move and shared table
control. -/
structure
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryAligned
    (one : OneControl A) (two : TwoControl A) : Prop where
  member_eq : one.1 = two.1
  right_move : one.2.1.1 = (two.2.2.candidate two.1).1
  right_control : HEq one.2.1.2 (two.2.2.candidate two.1).2.2.1
  left_move : two.2.1.1 = (one.2.2.candidate one.1).1
  left_control : HEq two.2.1.2 (one.2.2.candidate one.1).2.2.1

/-! ## Alignment at the actual entry -/

/-- After the actual entry input is consumed, the selected right table is
synchronized at its first successor state. -/
private theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryInitial_right
    (initial : CommonPoint A strategy) (entry : In₁ × In₂)
    (member : Bool) :
    let one :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneInitial A
        strategy hwin initial entry member
    let two :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoInitial A
        strategy hwin initial entry member
    one.2.1.1 = (two.2.2.candidate two.1).1 ∧
      HEq one.2.1.2 (two.2.2.candidate two.1).2.2.1 := by
  dsimp only
  cases member <;>
    exact profiledRawJointGuardedCommonRightLiteralCross_localRound_preserves A
      (profiledRawJointGuardedCommonRightLiteralCrossSenderInitial A
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryExtra A
          strategy hwin initial).1)
      (profiledRawJointGuardedCommonRightLiteralCrossReceiverInitial A
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryExtra A
          strategy hwin initial).1 _)
      rfl
      (heq_of_eq
        (profiledRawJointGuardedCommonRightLiteralCross_initial_controls_eq A
          (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryExtra A
            strategy hwin initial).1 _))
      entry.2 entry.1

/-- Left-oriented mirror at the first successor state. -/
private theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryInitial_left
    (initial : CommonPoint A strategy) (entry : In₁ × In₂)
    (member : Bool) :
    let one :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneInitial A
        strategy hwin initial entry member
    let two :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoInitial A
        strategy hwin initial entry member
    two.2.1.1 = (one.2.2.candidate one.1).1 ∧
      HEq two.2.1.2 (one.2.2.candidate one.1).2.2.1 := by
  dsimp only
  cases member <;>
    exact profiledRawJointGuardedCommonLeftLiteralCross_localRound_preserves A
      (profiledRawJointGuardedCommonLeftLiteralCrossSenderInitial A
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryExtra A
          strategy hwin initial).2)
      (profiledRawJointGuardedCommonLeftLiteralCrossReceiverInitial A
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryExtra A
          strategy hwin initial).2 _)
      rfl
      (heq_of_eq
        (profiledRawJointGuardedCommonLeftLiteralCross_initial_controls_eq A
          (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryExtra A
            strategy hwin initial).2 _))
      entry.1 entry.2

/-- The false or true pair selected from one entry-aligned bootstrap is a
synchronized pair of local tables. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryInitial_aligned
    (initial : CommonPoint A strategy) (entry : In₁ × In₂)
    (member : Bool) :
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryAligned A
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneInitial A
        strategy hwin initial entry member)
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoInitial A
        strategy hwin initial entry member) := by
  have hright :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryInitial_right A
      strategy hwin initial entry member
  have hleft :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryInitial_left A
      strategy hwin initial entry member
  exact ⟨rfl, hright.1, hright.2, hleft.1, hleft.2⟩

/-! ## Preservation by strict rounds -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- A strict-right round advances the right sender and selected right
receiver together and leaves the left-oriented pair dormant. -/
theorem
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryAligned.strictRight
    {one : OneControl A} {two : TwoControl A}
    (haligned :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryAligned A one two)
    (input : In₁ × In₂) :
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryAligned A
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryNoRecvOne A one
        input.1).1
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOpenRecvTwo A two
        input.2 one input.1).1 := by
  have hright :=
    profiledRawJointGuardedCommonRightLiteralCross_localRound_preserves A
      one.2.1 (two.2.2.candidate two.1) haligned.right_move
      haligned.right_control input.2 input.1
  constructor
  · simpa only [
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryNoRecvOne_member,
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOpenRecvTwo_member]
      using haligned.member_eq
  · change
      (profiledRawJointGuardedCommonRightLiteralCrossSenderNoRecv A one.2.1
        input.1).2.1 = _
    rw [profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOpenRecvTwo_member,
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOpenRecvTwo_selected]
    exact hright.1
  · change HEq
      (profiledRawJointGuardedCommonRightLiteralCrossSenderNoRecv A one.2.1
        input.1).2.2 _
    rw [profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOpenRecvTwo_member,
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOpenRecvTwo_selected]
    exact hright.2
  · rw [profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOpenRecvTwo_sender,
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryNoRecvOne_member,
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryNoRecvOne_receivers]
    exact haligned.left_move
  · rw [profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOpenRecvTwo_sender,
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryNoRecvOne_member,
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryNoRecvOne_receivers]
    exact haligned.left_control

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Strict-left mirror. -/
theorem
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryAligned.strictLeft
    {one : OneControl A} {two : TwoControl A}
    (haligned :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryAligned A one two)
    (input : In₁ × In₂) :
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryAligned A
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOpenRecvOne A one
        input.1 two input.2).1
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryNoRecvTwo A two
        input.2).1 := by
  have hleft :=
    profiledRawJointGuardedCommonLeftLiteralCross_localRound_preserves A
      two.2.1 (one.2.2.candidate one.1) haligned.left_move
      haligned.left_control input.1 input.2
  constructor
  · simpa only [
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOpenRecvOne_member,
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryNoRecvTwo_member]
      using haligned.member_eq
  · rw [profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOpenRecvOne_sender,
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryNoRecvTwo_member,
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryNoRecvTwo_receivers]
    exact haligned.right_move
  · rw [profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOpenRecvOne_sender,
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryNoRecvTwo_member,
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryNoRecvTwo_receivers]
    exact haligned.right_control
  · change
      (profiledRawJointGuardedCommonLeftLiteralCrossSenderNoRecv A two.2.1
        input.2).2.1 = _
    rw [profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOpenRecvOne_member,
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOpenRecvOne_selected]
    exact hleft.1
  · change HEq
      (profiledRawJointGuardedCommonLeftLiteralCrossSenderNoRecv A two.2.1
        input.2).2.2 _
    rw [profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOpenRecvOne_member,
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOpenRecvOne_selected]
    exact hleft.2

end

end DetParityAutomaton

end DistributedSynthesis
