/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionReceiveSourceAlignment

/-!
# Branch selection from a delivered entry-selection control

The receive-created fork has two logically different continuations.  Its
open member must retain the dependent strict seed certified by the literal-
cross table.  Its closed member must retain the recurrent common state and
its represented guarded pair.  These data cannot be reconstructed from a
public output and must not be identified with each other.

This file gives a finite, total decoder for the control delivered at the end
of a blind epoch.  On the open control it returns the retained strict seed;
on the closed control it returns the common branch.  In either case it also
returns the same live owner-backed occurrence that produced all blind
outputs.  The decoder commutes with a blind non-receive step.  Consequently
the branch selected after an arbitrary blind prefix is still paired with the
correct live owner, rather than with a table having the same public code.

The resulting law is deliberately a branch-selection law, not a target-
identification lemma.  In particular, it does not equate the strict seed's
target with the independently narrowed `shadow.strictTarget`.
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

private abbrev StrictRightSeed (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightSeed A
    strategy hwin initial

private abbrev StrictLeftSeed (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftSeed A
    strategy hwin initial

private abbrev OneOwnerBacked (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneOwnerBacked
    A strategy hwin initial

private abbrev TwoOwnerBacked (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoOwnerBacked
    A strategy hwin initial

private abbrev BlindOneControl (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindOneControl
    A strategy hwin initial

private abbrev BlindTwoControl (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindTwoControl
    A strategy hwin initial

/-! ## Finite selected branches -/

/-- What process two learns from a delivered process-one control.  The
`strictLeft` constructor retains the literal-cross-certified strict seed;
the `common` constructor records that the closed branch was selected.  Both
constructors carry the live right owner and its exact dormant occurrence. -/
inductive
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneBranch
    (initial : CommonPoint A strategy) where
  | strictLeft
      (seed : StrictLeftSeed A strategy hwin initial)
      (backed : OneOwnerBacked A strategy hwin initial)
  | common (backed : OneOwnerBacked A strategy hwin initial)

/-- Process-one mirror. -/
inductive
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoBranch
    (initial : CommonPoint A strategy) where
  | strictRight
      (seed : StrictRightSeed A strategy hwin initial)
      (backed : TwoOwnerBacked A strategy hwin initial)
  | common (backed : TwoOwnerBacked A strategy hwin initial)

private abbrev OneBranch (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneBranch
    A strategy hwin initial

private abbrev TwoBranch (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoBranch
    A strategy hwin initial

noncomputable instance
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneBranchFintype
    (initial : CommonPoint A strategy) :
    Fintype (OneBranch A strategy hwin initial) := by
  classical
  let Rep :=
    (StrictLeftSeed A strategy hwin initial ×
      OneOwnerBacked A strategy hwin initial) ⊕
      OneOwnerBacked A strategy hwin initial
  let equiv : OneBranch A strategy hwin initial ≃ Rep :=
    { toFun := fun branch ↦ match branch with
        | .strictLeft seed backed => .inl (seed, backed)
        | .common backed => .inr backed
      invFun := fun state ↦ match state with
        | .inl pending => .strictLeft pending.1 pending.2
        | .inr backed => .common backed
      left_inv := by intro branch; cases branch <;> rfl
      right_inv := by intro state; cases state <;> rfl }
  exact Fintype.ofEquiv Rep equiv.symm

noncomputable instance
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoBranchFintype
    (initial : CommonPoint A strategy) :
    Fintype (TwoBranch A strategy hwin initial) := by
  classical
  let Rep :=
    (StrictRightSeed A strategy hwin initial ×
      TwoOwnerBacked A strategy hwin initial) ⊕
      TwoOwnerBacked A strategy hwin initial
  let equiv : TwoBranch A strategy hwin initial ≃ Rep :=
    { toFun := fun branch ↦ match branch with
        | .strictRight seed backed => .inl (seed, backed)
        | .common backed => .inr backed
      invFun := fun state ↦ match state with
        | .inl pending => .strictRight pending.1 pending.2
        | .inr backed => .common backed
      left_inv := by intro branch; cases branch <;> rfl
      right_inv := by intro state; cases state <;> rfl }
  exact Fintype.ofEquiv Rep equiv.symm

/-! ## Total delivered-control decoders -/

/-- Equip a recurrent common control with the root owner of its represented
guarded pair. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneBackedAtCommon
    {initial : CommonPoint A strategy}
    (common : CommonOne A strategy hwin initial) :
    OneOwnerBacked A strategy hwin initial :=
  ⟨common,
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionRightOwnerRoot
      A strategy hwin common.shadow.common,
    rfl⟩

/-- Process-two mirror. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoBackedAtCommon
    {initial : CommonPoint A strategy}
    (common : CommonTwo A strategy hwin initial) :
    TwoOwnerBacked A strategy hwin initial :=
  ⟨common,
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionLeftOwnerRoot
      A strategy hwin common.shadow.common,
    rfl⟩

/-- Decode a delivered process-one control.  The three raw control forms are:
an open strict seed with a live owner, an unstepped common root, and a common
branch with an already advanced owner. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionDecodeOne
    {initial : CommonPoint A strategy}
    (control : BlindOneControl A strategy hwin initial) :
    OneBranch A strategy hwin initial :=
  match control with
  | .inl pending => .strictLeft pending.1 pending.2
  | .inr (.inl common) =>
      .common
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneBackedAtCommon
          A strategy hwin common)
  | .inr (.inr backed) => .common backed

/-- Decode a delivered process-two control. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionDecodeTwo
    {initial : CommonPoint A strategy}
    (control : BlindTwoControl A strategy hwin initial) :
    TwoBranch A strategy hwin initial :=
  match control with
  | .inl pending => .strictRight pending.1 pending.2
  | .inr (.inl common) =>
      .common
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoBackedAtCommon
          A strategy hwin common)
  | .inr (.inr backed) => .common backed

/-! ## Branch-level blind steps -/

/-- Advance the live right owner while retaining its exact dormant common
occurrence. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneBackedNoRecv
    {initial : CommonPoint A strategy}
    (backed : OneOwnerBacked A strategy hwin initial) (input : In₁) :
    OneOwnerBacked A strategy hwin initial × Out₁ :=
  let next := profiledRawJointGuardedCommonRightOwnerNoRecv A strategy hwin
    backed.owner input
  (⟨backed.common, next.2, by simpa using backed.source_eq⟩, next.1)

/-- Process-two mirror. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoBackedNoRecv
    {initial : CommonPoint A strategy}
    (backed : TwoOwnerBacked A strategy hwin initial) (input : In₂) :
    TwoOwnerBacked A strategy hwin initial × Out₂ :=
  let next := profiledRawJointGuardedCommonLeftOwnerNoRecv A strategy hwin
    backed.owner input
  (⟨backed.common, next.2, by simpa using backed.source_eq⟩, next.1)

/-- The selected branch advances only its common live owner.  In particular,
the dependent strict seed remains dormant. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneBranchNoRecv
    {initial : CommonPoint A strategy}
    (branch : OneBranch A strategy hwin initial) (input : In₁) :
    OneBranch A strategy hwin initial × Out₁ :=
  match branch with
  | .strictLeft seed backed =>
      let next :=
        profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneBackedNoRecv
          A strategy hwin backed input
      (.strictLeft seed next.1, next.2)
  | .common backed =>
      let next :=
        profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneBackedNoRecv
          A strategy hwin backed input
      (.common next.1, next.2)

/-- Process-two mirror. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoBranchNoRecv
    {initial : CommonPoint A strategy}
    (branch : TwoBranch A strategy hwin initial) (input : In₂) :
    TwoBranch A strategy hwin initial × Out₂ :=
  match branch with
  | .strictRight seed backed =>
      let next :=
        profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoBackedNoRecv
          A strategy hwin backed input
      (.strictRight seed next.1, next.2)
  | .common backed =>
      let next :=
        profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoBackedNoRecv
          A strategy hwin backed input
      (.common next.1, next.2)

/-! ## Exact decoding equations -/

/-- Decoding commutes with every process-one blind step, including the first
step out of the unstepped common-root constructor. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionDecodeOne_noRecv
    {initial : CommonPoint A strategy}
    (control : BlindOneControl A strategy hwin initial) (input : In₁) :
    let raw :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindNoRecvOne
        A strategy hwin control input
    let selected :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneBranchNoRecv
        A strategy hwin
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionDecodeOne
          A strategy hwin control) input
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionDecodeOne
        A strategy hwin raw.1 = selected.1 ∧ raw.2 = selected.2 := by
  cases control with
  | inl pending =>
      simp [
        profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindNoRecvOne,
        profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionDecodeOne,
        profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneBranchNoRecv,
        profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneBackedNoRecv]
  | inr rest =>
      cases rest with
      | inl common =>
          simp [
            profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindNoRecvOne,
            profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionDecodeOne,
            profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneBranchNoRecv,
            profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneBackedNoRecv,
            profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneBackedAtCommon,
            profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionCommonOneNoRecv_eq_ownerRoot]
      | inr backed =>
          simp [
            profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindNoRecvOne,
            profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionDecodeOne,
            profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneBranchNoRecv,
            profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneBackedNoRecv]

/-- Process-two mirror. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionDecodeTwo_noRecv
    {initial : CommonPoint A strategy}
    (control : BlindTwoControl A strategy hwin initial) (input : In₂) :
    let raw :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindNoRecvTwo
        A strategy hwin control input
    let selected :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoBranchNoRecv
        A strategy hwin
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionDecodeTwo
          A strategy hwin control) input
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionDecodeTwo
        A strategy hwin raw.1 = selected.1 ∧ raw.2 = selected.2 := by
  cases control with
  | inl pending =>
      simp [
        profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindNoRecvTwo,
        profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionDecodeTwo,
        profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoBranchNoRecv,
        profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoBackedNoRecv]
  | inr rest =>
      cases rest with
      | inl common =>
          simp [
            profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindNoRecvTwo,
            profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionDecodeTwo,
            profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoBranchNoRecv,
            profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoBackedNoRecv,
            profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoBackedAtCommon,
            profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionCommonTwoNoRecv_eq_ownerRoot]
      | inr backed =>
          simp [
            profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindNoRecvTwo,
            profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionDecodeTwo,
            profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoBranchNoRecv,
            profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoBackedNoRecv]

/-- At a fresh process-one fork, the delivered open control selects precisely
the stored strict-left seed, whereas the delivered closed control selects
the common branch with the same owner-backed occurrence. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionDecodeOne_fresh
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) :
    let pending :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOnePendingAt
        A strategy hwin initial entry input member
    let fork :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindOneFork
        A strategy hwin initial entry input member
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionDecodeOne
        A strategy hwin fork.openControl = .strictLeft pending.1 pending.2 ∧
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionDecodeOne
        A strategy hwin fork.closedControl = .common pending.2 := by
  exact ⟨rfl, rfl⟩

/-- Process-two mirror. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionDecodeTwo_fresh
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) :
    let pending :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoPendingAt
        A strategy hwin initial entry input member
    let fork :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindTwoFork
        A strategy hwin initial entry input member
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionDecodeTwo
        A strategy hwin fork.openControl = .strictRight pending.1 pending.2 ∧
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionDecodeTwo
        A strategy hwin fork.closedControl = .common pending.2 := by
  exact ⟨rfl, rfl⟩

/-! ## Reachable branch-selection laws -/

/-- The exact relation induced by decoding the two members of a process-one
blind fork.  An unresolved fork differs only by its strict seed versus common
tag; its live owner-backed occurrence is literally shared. -/
inductive
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneBranches
    {initial : CommonPoint A strategy} :
    OneBranch A strategy hwin initial →
      OneBranch A strategy hwin initial → Prop
  | fork (seed : StrictLeftSeed A strategy hwin initial)
      (backed : OneOwnerBacked A strategy hwin initial) :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneBranches
        (.strictLeft seed backed) (.common backed)
  | common (backed : OneOwnerBacked A strategy hwin initial) :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneBranches
        (.common backed) (.common backed)

/-- Process-two mirror. -/
inductive
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoBranches
    {initial : CommonPoint A strategy} :
    TwoBranch A strategy hwin initial →
      TwoBranch A strategy hwin initial → Prop
  | fork (seed : StrictRightSeed A strategy hwin initial)
      (backed : TwoOwnerBacked A strategy hwin initial) :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoBranches
        (.strictRight seed backed) (.common backed)
  | common (backed : TwoOwnerBacked A strategy hwin initial) :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoBranches
        (.common backed) (.common backed)

/-! ## Cross-endpoint selected shapes -/

/-- The owner-backed payload carried by a selected process-one branch. -/
def
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneBranch.backed
    {initial : CommonPoint A strategy}
    (branch : OneBranch A strategy hwin initial) :
    OneOwnerBacked A strategy hwin initial :=
  match branch with
  | .strictLeft _ backed => backed
  | .common backed => backed

/-- Process-two mirror. -/
def
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoBranch.backed
    {initial : CommonPoint A strategy}
    (branch : TwoBranch A strategy hwin initial) :
    TwoOwnerBacked A strategy hwin initial :=
  match branch with
  | .strictRight _ backed => backed
  | .common backed => backed

/-- The three coarse cross-endpoint branch shapes.  Strict-right means that
process two selected its open branch and process one selected common;
strict-left is symmetric; a simultaneous round selects both common arms.
In all cases the dormant recurrent states carry one parent-linked key.

This relation records branch and occurrence agreement only.  A recurrent
selected-pair invariant must additionally relate the two internal owner
controller positions; equality of their represented source pair does not
imply equality or synchronization of those controls. -/
inductive
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionSelected
    {initial : CommonPoint A strategy} :
    OneBranch A strategy hwin initial →
      TwoBranch A strategy hwin initial → Prop
  | strictRight
      (seed : StrictRightSeed A strategy hwin initial)
      (one : OneOwnerBacked A strategy hwin initial)
      (two : TwoOwnerBacked A strategy hwin initial)
      (keys_eq : one.common.key = two.common.key) :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionSelected
        (.common one) (.strictRight seed two)
  | strictLeft
      (seed : StrictLeftSeed A strategy hwin initial)
      (one : OneOwnerBacked A strategy hwin initial)
      (two : TwoOwnerBacked A strategy hwin initial)
      (keys_eq : one.common.key = two.common.key) :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionSelected
        (.strictLeft seed one) (.common two)
  | common
      (one : OneOwnerBacked A strategy hwin initial)
      (two : TwoOwnerBacked A strategy hwin initial)
      (keys_eq : one.common.key = two.common.key) :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionSelected
        (.common one) (.common two)

/-- A cross-endpoint selected pair exposes agreement of its two dormant
parent-linked common states. -/
theorem
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionSelected.common_agrees
    {initial : CommonPoint A strategy}
    {one : OneBranch A strategy hwin initial}
    {two : TwoBranch A strategy hwin initial}
    (hselected :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionSelected
        A strategy hwin one two) :
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonStatesAgree
      A strategy hwin one.backed.common two.backed.common := by
  cases hselected <;> assumption

/-- Parent-linked key agreement forces the two live owner controllers to
belong to the same represented guarded pair.  This is the occurrence-level
source equation needed before a strict receive continuation can be built. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOwnerBacked_sources_eq
    {initial : CommonPoint A strategy}
    (one : OneOwnerBacked A strategy hwin initial)
    (two : TwoOwnerBacked A strategy hwin initial)
    (hkeys : one.common.key = two.common.key) :
    one.owner.1 = two.owner.1 := by
  calc
    one.owner.1 = one.common.shadow.common := one.source_eq
    _ = one.common.key.pair A strategy hwin := one.common.common_eq
    _ = two.common.key.pair A strategy hwin := by rw [hkeys]
    _ = two.common.shadow.common := two.common.common_eq.symm
    _ = two.owner.1 := two.source_eq.symm

/-- Hence every coarsely selected branch pair carries live owners with one
and the same guarded source, independently of which branch tag was selected.
This is a source equation, not a controller-position equation. -/
theorem
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionSelected.owner_sources_eq
    {initial : CommonPoint A strategy}
    {one : OneBranch A strategy hwin initial}
    {two : TwoBranch A strategy hwin initial}
    (hselected :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionSelected
        A strategy hwin one two) :
    one.backed.owner.1 = two.backed.owner.1 :=
  profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOwnerBacked_sources_eq
    A strategy hwin one.backed two.backed
      (hselected.common_agrees A strategy hwin)

/-- Every reachable raw process-one blind pair decodes to the exact selected-
branch relation.  Thus the receiver never combines a strict seed from one
occurrence with the live owner of another. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionDecodeOne_of_blind
    {initial : CommonPoint A strategy}
    {left right : BlindOneControl A strategy hwin initial}
    (hblind :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindOne
        A strategy hwin initial left right) :
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneBranches
      A strategy hwin
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionDecodeOne
        A strategy hwin left)
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionDecodeOne
        A strategy hwin right) := by
  cases hblind with
  | fresh entry input member =>
      exact
        ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneBranches.fork
          _ _
  | pending seed backed =>
      exact
        ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneBranches.fork
          seed backed
  | owner backed =>
      exact
        ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneBranches.common
          backed

/-- Process-two mirror. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionDecodeTwo_of_blind
    {initial : CommonPoint A strategy}
    {left right : BlindTwoControl A strategy hwin initial}
    (hblind :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindTwo
        A strategy hwin initial left right) :
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoBranches
      A strategy hwin
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionDecodeTwo
        A strategy hwin left)
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionDecodeTwo
        A strategy hwin right) := by
  cases hblind with
  | fresh entry input member =>
      exact
        ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoBranches.fork
          _ _
  | pending seed backed =>
      exact
        ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoBranches.fork
          seed backed
  | owner backed =>
      exact
        ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoBranches.common
          backed

/-- One selected process-one step preserves the branch relation and has
equal output on both sides. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneBranches_noRecv
    {initial : CommonPoint A strategy}
    {left right : OneBranch A strategy hwin initial} (input : In₁)
    (hbranches :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneBranches
        A strategy hwin left right) :
    let nextLeft :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneBranchNoRecv
        A strategy hwin left input
    let nextRight :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneBranchNoRecv
        A strategy hwin right input
    nextLeft.2 = nextRight.2 ∧
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneBranches
        A strategy hwin nextLeft.1 nextRight.1 := by
  cases hbranches with
  | fork seed backed =>
      exact ⟨rfl,
        ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneBranches.fork
          _ _⟩
  | common backed =>
      exact ⟨rfl,
        ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneBranches.common
          _⟩

/-- Process-two mirror. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoBranches_noRecv
    {initial : CommonPoint A strategy}
    {left right : TwoBranch A strategy hwin initial} (input : In₂)
    (hbranches :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoBranches
        A strategy hwin left right) :
    let nextLeft :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoBranchNoRecv
        A strategy hwin left input
    let nextRight :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoBranchNoRecv
        A strategy hwin right input
    nextLeft.2 = nextRight.2 ∧
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoBranches
        A strategy hwin nextLeft.1 nextRight.1 := by
  cases hbranches with
  | fork seed backed =>
      exact ⟨rfl,
        ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoBranches.fork
          _ _⟩
  | common backed =>
      exact ⟨rfl,
        ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoBranches.common
          _⟩

end

end DetParityAutomaton

end DistributedSynthesis
