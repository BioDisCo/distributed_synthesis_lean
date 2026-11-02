/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindNoRecv
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLocalStrictInstallation

/-!
# Source alignment at a receive after the entry-selection seam

The endpoint-local blind law retains a dormant parent-linked common state
beside every live guarded owner.  This file supplies the first receive-side
use of that retained information.

Starting from two agreeing parent-linked common states, a strict-right round
creates a right owner at process one and advances the common/strict receiver
at process two.  The two controls have exactly the same guarded source.
The next strict-right receive can therefore advance the owner and receiver
through one controller record without a source cast or a restart.  The
strict-left construction is symmetric.

The local maps below are total: on an off-invariant source mismatch the
existing guarded owner lookup uses its fixed initial-control fallback.  The
proof-side pending relation rules that branch out on reachable pairs.  The
retained parent-linked key is carried through resolution, because it is the
closed/common alternative that a later acknowledged dispatcher still needs.

This is the source-alignment half of the receive dispatcher.  It does not
identify the dormant dependent strict seed with `shadow.strictTarget`: the
former is certified by the parent-linked literal-cross table, while the
latter comes from the independently narrowed common-pair root.  The next
obligation is a branch-selection law that reads strict provenance from the
retained literal table.
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

private abbrev CommonOne (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonOneState
    A strategy hwin initial

private abbrev CommonTwo (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonTwoState
    A strategy hwin initial

private abbrev CommonAgree {initial : CommonPoint A strategy} :=
  ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonStatesAgree
    A strategy hwin (initial := initial)

private abbrev Key (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedFalseKey A
    strategy hwin initial

private abbrev RightOwner :=
  ProfiledRawJointGuardedCommonRightOwner A strategy hwin

private abbrev LeftOwner :=
  ProfiledRawJointGuardedCommonLeftOwner A strategy hwin

/-! ## Parent-linked pending pairs -/

/-- Proof-side state after a strict-right round from an agreeing recurrent
common pair.  The receiver retains its parent-linked key in addition to the
guarded shadow used by the local strict transition. -/
structure
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionRightPending
    (initial : CommonPoint A strategy) where
  owner : RightOwner A strategy hwin
  receiver : CommonTwo A strategy hwin initial
  source_eq : owner.1 = receiver.shadow.source

/-- Strict-left mirror. -/
structure
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionLeftPending
    (initial : CommonPoint A strategy) where
  receiver : CommonOne A strategy hwin initial
  owner : LeftOwner A strategy hwin
  source_eq : owner.1 = receiver.shadow.source

noncomputable instance
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionRightPendingFintype
    (initial : CommonPoint A strategy) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionRightPending
        A strategy hwin initial) := by
  classical
  let Rep := Σ owner : RightOwner A strategy hwin,
    { receiver : CommonTwo A strategy hwin initial //
      owner.1 = receiver.shadow.source }
  let equiv :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionRightPending
          A strategy hwin initial ≃ Rep :=
    { toFun := fun state ↦ ⟨state.owner, state.receiver, state.source_eq⟩
      invFun := fun state ↦ ⟨state.1, state.2.1, state.2.2⟩
      left_inv := by intro state; cases state; rfl
      right_inv := by
        intro state
        rcases state with ⟨owner, receiver, h⟩
        rfl }
  exact Fintype.ofEquiv Rep equiv.symm

noncomputable instance
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionLeftPendingFintype
    (initial : CommonPoint A strategy) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionLeftPending
        A strategy hwin initial) := by
  classical
  let Rep := Σ receiver : CommonOne A strategy hwin initial,
    { owner : LeftOwner A strategy hwin //
      owner.1 = receiver.shadow.source }
  let equiv :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionLeftPending
          A strategy hwin initial ≃ Rep :=
    { toFun := fun state ↦ ⟨state.receiver, state.owner, state.source_eq⟩
      invFun := fun state ↦ ⟨state.1, state.2.1, state.2.2⟩
      left_inv := by intro state; cases state; rfl
      right_inv := by
        intro state
        rcases state with ⟨receiver, owner, h⟩
        rfl }
  exact Fintype.ofEquiv Rep equiv.symm

private abbrev RightPending (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionRightPending
    A strategy hwin initial

private abbrev LeftPending (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionLeftPending
    A strategy hwin initial

/-! ## Creation by the first strict round -/

/-- One strict-right round from an agreeing recurrent common pair creates an
exactly source-aligned owner/receiver pair. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionFirstStrictRight
    {initial : CommonPoint A strategy}
    (one : CommonOne A strategy hwin initial)
    (two : CommonTwo A strategy hwin initial)
    (hagrees : CommonAgree A strategy hwin one two)
    (input : In₁ × In₂) :
    (Out₁ × Out₂) × RightPending A strategy hwin initial :=
  let owner :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonOneNoRecv
      A strategy hwin one input.1
  let receiver :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonTwoRecv
      A strategy hwin two one input.2 input.1
  ((owner.1, receiver.1),
    ⟨owner.2, receiver.2,
      profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommon_strictRight_sources
        A strategy hwin one two hagrees input⟩)

/-- Strict-left mirror. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionFirstStrictLeft
    {initial : CommonPoint A strategy}
    (one : CommonOne A strategy hwin initial)
    (two : CommonTwo A strategy hwin initial)
    (hagrees : CommonAgree A strategy hwin one two)
    (input : In₁ × In₂) :
    (Out₁ × Out₂) × LeftPending A strategy hwin initial :=
  let receiver :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonOneRecv
      A strategy hwin one two input.1 input.2
  let owner :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonTwoNoRecv
      A strategy hwin two input.2
  ((receiver.1, owner.1),
    ⟨receiver.2, owner.2,
      profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommon_strictLeft_sources
        A strategy hwin one two hagrees input⟩)

theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionFirstStrictRight_outputs
    {initial : CommonPoint A strategy}
    (one : CommonOne A strategy hwin initial)
    (two : CommonTwo A strategy hwin initial)
    (hagrees : CommonAgree A strategy hwin one two)
    (input : In₁ × In₂) :
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionFirstStrictRight
      A strategy hwin one two hagrees input).1 =
      (((one.key.pair A strategy hwin).rightRootRecord A strategy hwin input
          ).2.2,
        pairedRightInformedForRow .both
          ((one.key.pair A strategy hwin).rightRootRecord A strategy hwin
            input).2.1.physical) :=
  profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommon_strictRight_outputs
    A strategy hwin one two hagrees input

theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionFirstStrictLeft_outputs
    {initial : CommonPoint A strategy}
    (one : CommonOne A strategy hwin initial)
    (two : CommonTwo A strategy hwin initial)
    (hagrees : CommonAgree A strategy hwin one two)
    (input : In₁ × In₂) :
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionFirstStrictLeft
      A strategy hwin one two hagrees input).1 =
      (pairedLeftInformedForRow .both
          ((one.key.pair A strategy hwin).leftRootRecord A strategy hwin input
            ).2.1.physical,
        ((one.key.pair A strategy hwin).leftRootRecord A strategy hwin input
          ).2.2) :=
  profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommon_strictLeft_outputs
    A strategy hwin one two hagrees input

/-! ## Total local receive maps -/

/-- Process one's blind step in an already opened strict-right block. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionRightOwnerStep
    (owner : RightOwner A strategy hwin) (input : In₁) :
    Out₁ × RightOwner A strategy hwin :=
  profiledRawJointGuardedCommonRightOwnerNoRecv A strategy hwin owner input

/-- Process two consumes the delivered owner using the strict receiver stored
in its parent-linked common shadow. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionRightReceive
    {initial : CommonPoint A strategy}
    (receiver : CommonTwo A strategy hwin initial)
    (owner : RightOwner A strategy hwin)
    (own : In₂) (delivered : In₁) :
    Out₂ × ProfiledRawJointGuardedCommonRightStrictReceiver A strategy
      hwin :=
  profiledRawJointGuardedCommonTwoShadowRecvRightOwner A strategy hwin
    receiver.shadow owner own delivered

/-- Strict-left local maps. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionLeftReceive
    {initial : CommonPoint A strategy}
    (receiver : CommonOne A strategy hwin initial)
    (owner : LeftOwner A strategy hwin)
    (own : In₁) (delivered : In₂) :
    Out₁ × ProfiledRawJointGuardedCommonLeftStrictReceiver A strategy
      hwin :=
  profiledRawJointGuardedCommonOneShadowRecvLeftOwner A strategy hwin
    receiver.shadow owner own delivered

noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionLeftOwnerStep
    (owner : LeftOwner A strategy hwin) (input : In₂) :
    Out₂ × LeftOwner A strategy hwin :=
  profiledRawJointGuardedCommonLeftOwnerNoRecv A strategy hwin owner input

/-! ## Resolved states and the receive/source-alignment law -/

/-- A resolved strict-right pair, retaining the key of the closed/common
alternative from the receiver's local state. -/
structure
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionRightResolved
    (initial : CommonPoint A strategy) where
  closedKey : Key A strategy hwin initial
  strict : ProfiledRawJointGuardedCommonRightStrictState A strategy hwin

/-- Strict-left mirror. -/
structure
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionLeftResolved
    (initial : CommonPoint A strategy) where
  closedKey : Key A strategy hwin initial
  strict : ProfiledRawJointGuardedCommonLeftStrictState A strategy hwin

noncomputable instance
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionRightResolvedFintype
    (initial : CommonPoint A strategy) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionRightResolved
        A strategy hwin initial) := by
  classical
  let equiv :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionRightResolved
          A strategy hwin initial ≃
        Key A strategy hwin initial ×
          ProfiledRawJointGuardedCommonRightStrictState A strategy hwin :=
    { toFun := fun state ↦ (state.closedKey, state.strict)
      invFun := fun state ↦ ⟨state.1, state.2⟩
      left_inv := by intro state; cases state; rfl
      right_inv := by intro state; cases state; rfl }
  exact Fintype.ofEquiv _ equiv.symm

noncomputable instance
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionLeftResolvedFintype
    (initial : CommonPoint A strategy) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionLeftResolved
        A strategy hwin initial) := by
  classical
  let equiv :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionLeftResolved
          A strategy hwin initial ≃
        Key A strategy hwin initial ×
          ProfiledRawJointGuardedCommonLeftStrictState A strategy hwin :=
    { toFun := fun state ↦ (state.closedKey, state.strict)
      invFun := fun state ↦ ⟨state.1, state.2⟩
      left_inv := by intro state; cases state; rfl
      right_inv := by intro state; cases state; rfl }
  exact Fintype.ofEquiv _ equiv.symm

private abbrev RightResolved (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionRightResolved
    A strategy hwin initial

private abbrev LeftResolved (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionLeftResolved
    A strategy hwin initial

/-- The two endpoint-local maps consume one source-aligned strict-right
record and produce another source-aligned pair. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionResolveRight
    {initial : CommonPoint A strategy}
    (state : RightPending A strategy hwin initial)
    (input : In₁ × In₂) :
    (Out₁ × Out₂) × RightResolved A strategy hwin initial :=
  let owner :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionRightOwnerStep
      A strategy hwin state.owner input.1
  let receiver :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionRightReceive
      A strategy hwin state.receiver state.owner input.2 input.1
  ((owner.1, receiver.1),
    ⟨state.receiver.key,
      ⟨owner.2, receiver.2, by
        change
          (profiledRawJointGuardedCommonRightOwnerNoRecv A strategy hwin
            state.owner input.1).2.1 =
          (profiledRawJointGuardedCommonTwoShadowRecvRightOwner A strategy
            hwin state.receiver.shadow state.owner input.2 input.1).2.1
        rw [profiledRawJointGuardedCommonRightOwnerNoRecv_source,
          profiledRawJointGuardedCommonTwoShadowRecvRightOwner_source]
        exact state.source_eq⟩⟩)

/-- Strict-left mirror. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionResolveLeft
    {initial : CommonPoint A strategy}
    (state : LeftPending A strategy hwin initial)
    (input : In₁ × In₂) :
    (Out₁ × Out₂) × LeftResolved A strategy hwin initial :=
  let receiver :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionLeftReceive
      A strategy hwin state.receiver state.owner input.1 input.2
  let owner :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionLeftOwnerStep
      A strategy hwin state.owner input.2
  ((receiver.1, owner.1),
    ⟨state.receiver.key,
      ⟨receiver.2, owner.2, by
        change
          (profiledRawJointGuardedCommonLeftOwnerNoRecv A strategy hwin
            state.owner input.2).2.1 =
          (profiledRawJointGuardedCommonOneShadowRecvLeftOwner A strategy hwin
            state.receiver.shadow state.owner input.1 input.2).2.1
        rw [profiledRawJointGuardedCommonLeftOwnerNoRecv_source,
          profiledRawJointGuardedCommonOneShadowRecvLeftOwner_source]
        exact state.source_eq⟩⟩)

/-- Receive/source alignment, stated directly on the two independently
computed strict-right postcontrols. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionResolveRight_sources
    {initial : CommonPoint A strategy}
    (state : RightPending A strategy hwin initial)
    (input : In₁ × In₂) :
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionResolveRight
      A strategy hwin state input).2.strict.owner.1 =
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionResolveRight
        A strategy hwin state input).2.strict.receiver.1 :=
  (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionResolveRight
    A strategy hwin state input).2.strict.source_eq

/-- Strict-left receive/source alignment. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionResolveLeft_sources
    {initial : CommonPoint A strategy}
    (state : LeftPending A strategy hwin initial)
    (input : In₁ × In₂) :
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionResolveLeft
      A strategy hwin state input).2.strict.owner.1 =
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionResolveLeft
        A strategy hwin state input).2.strict.receiver.1 :=
  (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionResolveLeft
    A strategy hwin state input).2.strict.source_eq

@[simp] theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionResolveRight_closedKey
    {initial : CommonPoint A strategy}
    (state : RightPending A strategy hwin initial)
    (input : In₁ × In₂) :
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionResolveRight
      A strategy hwin state input).2.closedKey = state.receiver.key :=
  rfl

@[simp] theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionResolveLeft_closedKey
    {initial : CommonPoint A strategy}
    (state : LeftPending A strategy hwin initial)
    (input : In₁ × In₂) :
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionResolveLeft
      A strategy hwin state input).2.closedKey = state.receiver.key :=
  rfl

end

end DetParityAutomaton

end DistributedSynthesis
