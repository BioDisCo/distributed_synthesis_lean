/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionControl

/-!
# Blind coherence of the receive-created entry-selection fork

The fresh ambiguity is created by a receive.  At process one its ordinary
branch is strict-left and its exact branch is `both`; at process two the two
branches are strict-right and `both`.  The pre-receive table bundle is not a
member of this fresh fork.

The strict branch retains its exact dependent policy seed, but does not start
that ordinary policy while the endpoint is blind.  Its live coordinate is
the owner controller of the very same guarded successor pair carried by the
common branch.  That controller is the finite realization of the shared
sender lambda on the relevant `left`/`both` or `right`/`both` pending overlap.
Consequently the first non-receive has definitionally equal output.  The
ordinary branch retains its strict seed beside the advanced shared owner,
whereas the exact branch retains the same advanced owner alone.  Every later
non-receive preserves this relation.

This file proves the complete endpoint-local `BlindNoRecvLaws` and the
arbitrary-depth `NoRecvOutputCoherent` theorem for both receive-created
forks.  The strict seed and the dormant recurrent common state remain
available for the later receive dispatcher; no ordinary policy is restarted
before the old ambiguity is acknowledged.  Retaining the common state is
essential: its shadow contains the strict receiver state, while its key
identifies the occurrence-sensitive common continuation.
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

private abbrev RightOwner :=
  ProfiledRawJointGuardedCommonRightOwner A strategy hwin

private abbrev LeftOwner :=
  ProfiledRawJointGuardedCommonLeftOwner A strategy hwin

/-! ## The shared owner roots -/

/-- Initial process-one owner control of a represented guarded pair. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionRightOwnerRoot
    (pair : ProfiledRawJointGuardedCommonPair A strategy hwin) :
    RightOwner A strategy hwin :=
  ⟨pair, ((pair.1.1).memberController A false).initial⟩

/-- Process-two mirror. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionLeftOwnerRoot
    (pair : ProfiledRawJointGuardedCommonPair A strategy hwin) :
    LeftOwner A strategy hwin :=
  ⟨pair, ((pair.1.2).memberController A false).initial⟩

/-- Starting a strict-right exit from a common state is exactly one step of
the root owner of the pair carried by that state. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionCommonOneNoRecv_eq_ownerRoot
    {initial : CommonPoint A strategy}
    (common : CommonOne A strategy hwin initial) (input : In₁) :
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonOneNoRecv
        A strategy hwin common input =
      profiledRawJointGuardedCommonRightOwnerNoRecv A strategy hwin
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionRightOwnerRoot
          A strategy hwin common.shadow.common) input := by
  rfl

/-- Process-two mirror. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionCommonTwoNoRecv_eq_ownerRoot
    {initial : CommonPoint A strategy}
    (common : CommonTwo A strategy hwin initial) (input : In₂) :
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonTwoNoRecv
        A strategy hwin common input =
      profiledRawJointGuardedCommonLeftOwnerNoRecv A strategy hwin
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionLeftOwnerRoot
          A strategy hwin common.shadow.common) input := by
  rfl

/-! ## Finite blind controls -/

/-- A right-owner continuation together with the dormant recurrent common
state from which that owner was started.  The equation is executable-data
free, but prevents the later receive dispatcher from combining different
guarded occurrences merely because their public codes agree. -/
structure
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneOwnerBacked
    (initial : CommonPoint A strategy) where
  common : CommonOne A strategy hwin initial
  owner : RightOwner A strategy hwin
  source_eq : owner.1 = common.shadow.common

/-- Process-two mirror. -/
structure
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoOwnerBacked
    (initial : CommonPoint A strategy) where
  common : CommonTwo A strategy hwin initial
  owner : LeftOwner A strategy hwin
  source_eq : owner.1 = common.shadow.common

noncomputable instance
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneOwnerBackedFintype
    (initial : CommonPoint A strategy) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneOwnerBacked
        A strategy hwin initial) := by
  classical
  let Rep := Σ common : CommonOne A strategy hwin initial,
    { owner : RightOwner A strategy hwin //
      owner.1 = common.shadow.common }
  let equiv :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneOwnerBacked
          A strategy hwin initial ≃ Rep :=
    { toFun := fun state ↦ ⟨state.common, state.owner, state.source_eq⟩
      invFun := fun state ↦ ⟨state.1, state.2.1, state.2.2⟩
      left_inv := by intro state; cases state; rfl
      right_inv := by
        intro state
        rcases state with ⟨common, owner, h⟩
        rfl }
  exact Fintype.ofEquiv Rep equiv.symm

noncomputable instance
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoOwnerBackedFintype
    (initial : CommonPoint A strategy) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoOwnerBacked
        A strategy hwin initial) := by
  classical
  let Rep := Σ common : CommonTwo A strategy hwin initial,
    { owner : LeftOwner A strategy hwin //
      owner.1 = common.shadow.common }
  let equiv :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoOwnerBacked
          A strategy hwin initial ≃ Rep :=
    { toFun := fun state ↦ ⟨state.common, state.owner, state.source_eq⟩
      invFun := fun state ↦ ⟨state.1, state.2.1, state.2.2⟩
      left_inv := by intro state; cases state; rfl
      right_inv := by
        intro state
        rcases state with ⟨common, owner, h⟩
        rfl }
  exact Fintype.ofEquiv Rep equiv.symm

private abbrev OneOwnerBacked (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneOwnerBacked
    A strategy hwin initial

private abbrev TwoOwnerBacked (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoOwnerBacked
    A strategy hwin initial

/-- Process one's ordinary branch retains both the strict-left policy seed
and the common state whose right-owner controller supplies the blind output. -/
abbrev
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOnePending
    (initial : CommonPoint A strategy) :=
  StrictLeftSeed A strategy hwin initial ×
    OneOwnerBacked A strategy hwin initial

/-- Process-two mirror. -/
abbrev
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoPending
    (initial : CommonPoint A strategy) :=
  StrictRightSeed A strategy hwin initial ×
    TwoOwnerBacked A strategy hwin initial

/-- During the fresh blind epoch, process one is either at the strict/common
fork or already in their common right-owner continuation. -/
abbrev
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindOneControl
    (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOnePending
      A strategy hwin initial ⊕
    (CommonOne A strategy hwin initial ⊕
      OneOwnerBacked A strategy hwin initial)

/-- Process-two mirror. -/
abbrev
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindTwoControl
    (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoPending
      A strategy hwin initial ⊕
    (CommonTwo A strategy hwin initial ⊕
      TwoOwnerBacked A strategy hwin initial)

noncomputable instance
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindOneControlFintype
    (initial : CommonPoint A strategy) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindOneControl
        A strategy hwin initial) := by
  classical
  infer_instance

noncomputable instance
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindTwoControlFintype
    (initial : CommonPoint A strategy) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindTwoControl
        A strategy hwin initial) := by
  classical
  infer_instance

private abbrev BlindOneControl (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindOneControl
    A strategy hwin initial

private abbrev BlindTwoControl (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindTwoControl
    A strategy hwin initial

/-! ## The correctly timed receive forks -/

/-- The common state used by both members of process one's fresh fork. -/
private noncomputable def entrySelectionBlindCommonOne
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    CommonOne A strategy hwin initial :=
  (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryCommonControlStartOne
    A strategy hwin initial entry input).2

/-- Process-two mirror. -/
private noncomputable def entrySelectionBlindCommonTwo
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    CommonTwo A strategy hwin initial :=
  (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryCommonControlStartTwo
    A strategy hwin initial entry input).2

/-- Process one's strict-left pending branch.  Its ordinary policy seed stays
dormant; its live blind coordinate is the root owner of the common branch's
same successor pair. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOnePendingAt
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) :
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOnePending
      A strategy hwin initial :=
  let common := entrySelectionBlindCommonOne A strategy hwin initial entry
    input
  (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftSeedAt A
      strategy hwin initial entry input member,
    ⟨common,
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionRightOwnerRoot
        A strategy hwin common.shadow.common,
      rfl⟩)

/-- Process-two strict-right mirror. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoPendingAt
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) :
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoPending
      A strategy hwin initial :=
  let common := entrySelectionBlindCommonTwo A strategy hwin initial entry
    input
  (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightSeedAt A
      strategy hwin initial entry input member,
    ⟨common,
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionLeftOwnerRoot
        A strategy hwin common.shadow.common,
      rfl⟩)

/-- Process one's fresh post-receive strict/common fork. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindOneFork
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) :
    FiniteDelayedFork (BlindOneControl A strategy hwin initial) :=
  ⟨.inl
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOnePendingAt
        A strategy hwin initial entry input member),
    .inr (.inl
      (entrySelectionBlindCommonOne A strategy hwin initial entry input))⟩

/-- Process-two mirror. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindTwoFork
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) :
    FiniteDelayedFork (BlindTwoControl A strategy hwin initial) :=
  ⟨.inl
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoPendingAt
        A strategy hwin initial entry input member),
    .inr (.inl
      (entrySelectionBlindCommonTwo A strategy hwin initial entry input))⟩

/-! ## Local non-receive maps -/

noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindNoRecvOne
    {initial : CommonPoint A strategy}
    (control : BlindOneControl A strategy hwin initial) (input : In₁) :
    BlindOneControl A strategy hwin initial × Out₁ :=
  match control with
  | .inl pending =>
      let next := profiledRawJointGuardedCommonRightOwnerNoRecv A strategy hwin
        pending.2.owner input
      (.inl (pending.1,
        ⟨pending.2.common, next.2, by simpa using pending.2.source_eq⟩),
        next.1)
  | .inr (.inl common) =>
      let next :=
        profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonOneNoRecv
          A strategy hwin common input
      (.inr (.inr ⟨common, next.2, rfl⟩), next.1)
  | .inr (.inr backed) =>
      let next := profiledRawJointGuardedCommonRightOwnerNoRecv A strategy hwin
        backed.owner input
      (.inr (.inr
        ⟨backed.common, next.2, by simpa using backed.source_eq⟩), next.1)

noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindNoRecvTwo
    {initial : CommonPoint A strategy}
    (control : BlindTwoControl A strategy hwin initial) (input : In₂) :
    BlindTwoControl A strategy hwin initial × Out₂ :=
  match control with
  | .inl pending =>
      let next := profiledRawJointGuardedCommonLeftOwnerNoRecv A strategy hwin
        pending.2.owner input
      (.inl (pending.1,
        ⟨pending.2.common, next.2, by simpa using pending.2.source_eq⟩),
        next.1)
  | .inr (.inl common) =>
      let next :=
        profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonTwoNoRecv
          A strategy hwin common input
      (.inr (.inr ⟨common, next.2, rfl⟩), next.1)
  | .inr (.inr backed) =>
      let next := profiledRawJointGuardedCommonLeftOwnerNoRecv A strategy hwin
        backed.owner input
      (.inr (.inr
        ⟨backed.common, next.2, by simpa using backed.source_eq⟩), next.1)

/-! ## Blind relations and one-step laws -/

inductive
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindOne
    (initial : CommonPoint A strategy) :
    BlindOneControl A strategy hwin initial →
      BlindOneControl A strategy hwin initial → Prop
  | fresh (entry input : In₁ × In₂) (member : Bool) :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindOne
        initial
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindOneFork
          A strategy hwin initial entry input member).openControl
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindOneFork
          A strategy hwin initial entry input member).closedControl
  | pending (seed : StrictLeftSeed A strategy hwin initial)
      (backed : OneOwnerBacked A strategy hwin initial) :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindOne
        initial (.inl (seed, backed)) (.inr (.inr backed))
  | owner (backed : OneOwnerBacked A strategy hwin initial) :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindOne
        initial (.inr (.inr backed)) (.inr (.inr backed))

inductive
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindTwo
    (initial : CommonPoint A strategy) :
    BlindTwoControl A strategy hwin initial →
      BlindTwoControl A strategy hwin initial → Prop
  | fresh (entry input : In₁ × In₂) (member : Bool) :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindTwo
        initial
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindTwoFork
          A strategy hwin initial entry input member).openControl
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindTwoFork
          A strategy hwin initial entry input member).closedControl
  | pending (seed : StrictRightSeed A strategy hwin initial)
      (backed : TwoOwnerBacked A strategy hwin initial) :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindTwo
        initial (.inl (seed, backed)) (.inr (.inr backed))
  | owner (backed : TwoOwnerBacked A strategy hwin initial) :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindTwo
        initial (.inr (.inr backed)) (.inr (.inr backed))

theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindOne_noRecv
    {initial : CommonPoint A strategy}
    (left right : BlindOneControl A strategy hwin initial) (input : In₁)
    (hblind :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindOne
        A strategy hwin initial left right) :
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindNoRecvOne
        A strategy hwin left input).2 =
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindNoRecvOne
          A strategy hwin right input).2 ∧
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindOne
        A strategy hwin initial
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindNoRecvOne
          A strategy hwin left input).1
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindNoRecvOne
          A strategy hwin right input).1 := by
  cases hblind with
  | fresh entry current member =>
      change
        (profiledRawJointGuardedCommonRightOwnerNoRecv A strategy hwin _
          input).1 =
            (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonOneNoRecv
              A strategy hwin _ input).1 ∧ _
      rw [
        profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionCommonOneNoRecv_eq_ownerRoot]
      exact ⟨rfl,
        ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindOne.pending
          _ _⟩
  | pending seed control =>
      exact ⟨rfl,
        ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindOne.pending
          _ _⟩
  | owner control =>
      exact ⟨rfl,
        ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindOne.owner
          _⟩

theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindTwo_noRecv
    {initial : CommonPoint A strategy}
    (left right : BlindTwoControl A strategy hwin initial) (input : In₂)
    (hblind :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindTwo
        A strategy hwin initial left right) :
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindNoRecvTwo
        A strategy hwin left input).2 =
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindNoRecvTwo
          A strategy hwin right input).2 ∧
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindTwo
        A strategy hwin initial
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindNoRecvTwo
          A strategy hwin left input).1
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindNoRecvTwo
          A strategy hwin right input).1 := by
  cases hblind with
  | fresh entry current member =>
      change
        (profiledRawJointGuardedCommonLeftOwnerNoRecv A strategy hwin _
          input).1 =
            (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonTwoNoRecv
              A strategy hwin _ input).1 ∧ _
      rw [
        profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionCommonTwoNoRecv_eq_ownerRoot]
      exact ⟨rfl,
        ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindTwo.pending
          _ _⟩
  | pending seed control =>
      exact ⟨rfl,
        ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindTwo.pending
          _ _⟩
  | owner control =>
      exact ⟨rfl,
        ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindTwo.owner
          _⟩

/-- Complete local no-receive law bundle for the corrected receive-created
fork. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindNoRecvLaws
    (initial : CommonPoint A strategy) :
    FiniteAcknowledgedDelayedCarrier.BlindNoRecvLaws
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindNoRecvOne
        A strategy hwin)
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindNoRecvTwo
        A strategy hwin)
      (ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindOne
        A strategy hwin initial)
      (ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindTwo
        A strategy hwin initial) :=
  {
    one :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindOne_noRecv
        A strategy hwin
    two :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindTwo_noRecv
        A strategy hwin
  }

/-! ## Arbitrary-depth coherence -/

private abbrev BlindOneRelay (initial : CommonPoint A strategy) :=
  FiniteAcknowledgedDelayedCarrier (Fin 5)
    (BlindOneControl A strategy hwin initial)

private abbrev BlindTwoRelay (initial : CommonPoint A strategy) :=
  FiniteAcknowledgedDelayedCarrier (Fin 5)
    (BlindTwoControl A strategy hwin initial)

noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindOneInitialRelay
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) : BlindOneRelay A strategy hwin initial :=
  ⟨.fork 0
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindOneFork
        A strategy hwin initial entry input member), none⟩

noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindTwoInitialRelay
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) : BlindTwoRelay A strategy hwin initial :=
  ⟨.fork 0
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindTwoFork
        A strategy hwin initial entry input member), none⟩

noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindOneRun
    {initial : CommonPoint A strategy} :
    BlindOneRelay A strategy hwin initial → List In₁ →
      BlindOneRelay A strategy hwin initial
  | state, [] => state
  | state, input :: rest =>
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindOneRun
        (FiniteAcknowledgedDelayedCarrier.noRecvMealy
          (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindNoRecvOne
            A strategy hwin) state input).1 rest

noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindTwoRun
    {initial : CommonPoint A strategy} :
    BlindTwoRelay A strategy hwin initial → List In₂ →
      BlindTwoRelay A strategy hwin initial
  | state, [] => state
  | state, input :: rest =>
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindTwoRun
        (FiniteAcknowledgedDelayedCarrier.noRecvMealy
          (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindNoRecvTwo
            A strategy hwin) state input).1 rest

theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindOneRun_satisfies
    {initial : CommonPoint A strategy}
    (state : BlindOneRelay A strategy hwin initial)
    (hblind : FiniteAcknowledgedDelayedCarrier.SatisfiesBlindFork
      (ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindOne
        A strategy hwin initial) state) :
    ∀ past : List In₁,
      FiniteAcknowledgedDelayedCarrier.SatisfiesBlindFork
        (ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindOne
          A strategy hwin initial)
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindOneRun
          A strategy hwin state past) := by
  intro past
  induction past generalizing state with
  | nil => exact hblind
  | cons input rest ih =>
      apply ih
      exact hblind.noRecv
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindNoRecvOne
          A strategy hwin)
        (ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindOne
          A strategy hwin initial)
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindOne_noRecv
          A strategy hwin) state input

theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindTwoRun_satisfies
    {initial : CommonPoint A strategy}
    (state : BlindTwoRelay A strategy hwin initial)
    (hblind : FiniteAcknowledgedDelayedCarrier.SatisfiesBlindFork
      (ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindTwo
        A strategy hwin initial) state) :
    ∀ past : List In₂,
      FiniteAcknowledgedDelayedCarrier.SatisfiesBlindFork
        (ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindTwo
          A strategy hwin initial)
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindTwoRun
          A strategy hwin state past) := by
  intro past
  induction past generalizing state with
  | nil => exact hblind
  | cons input rest ih =>
      apply ih
      exact hblind.noRecv
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindNoRecvTwo
          A strategy hwin)
        (ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindTwo
          A strategy hwin initial)
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindTwo_noRecv
          A strategy hwin) state input

/-- Process one's receive-created strict/common fork has coherent output
after every finite blind suffix. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindOne_reachable_coherent
    (initial : CommonPoint A strategy) (entry current : In₁ × In₂)
    (member : Bool) (past : List In₁) (input : In₁) :
    FiniteAcknowledgedDelayedCarrier.NoRecvOutputCoherent
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindNoRecvOne
        A strategy hwin)
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindOneRun
        A strategy hwin
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindOneInitialRelay
          A strategy hwin initial entry current member) past)
      input := by
  apply FiniteAcknowledgedDelayedCarrier.SatisfiesBlindFork.noRecvOutputCoherent
    (Blind :=
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindOne
        A strategy hwin initial)
    (hstep :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindOne_noRecv
        A strategy hwin)
  apply
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindOneRun_satisfies
      A strategy hwin _ _ past
  exact
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindOne.fresh
      entry current member

/-- Process-two mirror. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindTwo_reachable_coherent
    (initial : CommonPoint A strategy) (entry current : In₁ × In₂)
    (member : Bool) (past : List In₂) (input : In₂) :
    FiniteAcknowledgedDelayedCarrier.NoRecvOutputCoherent
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindNoRecvTwo
        A strategy hwin)
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindTwoRun
        A strategy hwin
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindTwoInitialRelay
          A strategy hwin initial entry current member) past)
      input := by
  apply FiniteAcknowledgedDelayedCarrier.SatisfiesBlindFork.noRecvOutputCoherent
    (Blind :=
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindTwo
        A strategy hwin initial)
    (hstep :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindTwo_noRecv
        A strategy hwin)
  apply
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindTwoRun_satisfies
      A strategy hwin _ _ past
  exact
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBlindTwo.fresh
      entry current member

end

end DetParityAutomaton

end DistributedSynthesis
