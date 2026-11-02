/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTailPoweredReceivers

/-!
# Fixed-anchor mixed phases below the guarded-common tail

On the first simultaneous receive out of a resolved guarded strict block, the
guarded parent may compute a new staged close.  The recurrent child already
selected for the other local process must not be refreshed to that new close.
This file records the pre-receive close as an immutable anchor and constructs
the powered recurrent receiver from that exact anchor.

The two mixed states are proof-side synchronization packages.  Their next
physical round resolves in each of the three graph shapes to ordinary
recurrent controls at one literal combined key.  The key is definitionally the
powered receiver's key and is propositionally identified with the immutable
anchor's key.  The evolving guarded parent's current close is never consulted
by a resolver.

No operation takes a graph, orientation, hierarchy side, leader bit, semantic
world, or history as runtime data.
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
  (initialBank : ProfiledRawJointInitialControllerBank A strategy)

private abbrev CombinedKey :=
  ProfiledRawJointGuardedHybridCombinedChildCode A strategy hwin initialBank

private abbrev CombinedSource (key : CombinedKey A strategy hwin initialBank) :=
  profiledRawJointGuardedHybridCombinedChildSource A strategy hwin initialBank
    key

private abbrev CombinedPolicy (key : CombinedKey A strategy hwin initialBank) :=
  profiledRawJointGuardedHybridCombinedChildPolicy A strategy hwin initialBank
    key

private abbrev CombinedBank (key : CombinedKey A strategy hwin initialBank) :=
  profiledRawJointGuardedHybridCombinedControllerBank A strategy hwin
    initialBank key

private abbrev LeftReceiver (key : CombinedKey A strategy hwin initialBank) :=
  ProfiledRawJointGuardedHybridCombinedLeftReceiver A strategy hwin initialBank
    key

private abbrev RightReceiver (key : CombinedKey A strategy hwin initialBank) :=
  ProfiledRawJointGuardedHybridCombinedRightReceiver A strategy hwin
    initialBank key

private abbrev LeftOwner (key : CombinedKey A strategy hwin initialBank) :=
  ProfiledRawJointGuardedHybridCombinedLeftOwner A strategy hwin initialBank
    key

private abbrev RightOwner (key : CombinedKey A strategy hwin initialBank) :=
  ProfiledRawJointGuardedHybridCombinedRightOwner A strategy hwin initialBank
    key

/-! ## Self-powered guarded-parent advances -/

/-- Advance the guarded strict-right parent from its internally retained
matching owner, returning the new receiver directly instead of hiding it in
the exceptional-control sum.  Its new staged close is deliberately allowed to
change. -/
noncomputable def
    advanceProfiledRawJointGuardedCommonTailAnchoredRightParent
    (parent : ProfiledRawJointGuardedCommonTailRightReceiver A strategy hwin)
    (own : In₂) (delivered : In₁) :
    Out₂ × ProfiledRawJointGuardedCommonTailRightReceiver A strategy hwin :=
  let owner := parent.strict.owner
  let ownerControl := profiledRawJointGuardedCommonRightStrictOwnerFor A
    strategy hwin parent.strict.receiver owner
  let close := profiledRawJointGuardedCommonRightStageClose A strategy hwin
    parent.strict.receiver.1 (ownerControl, parent.strict.receiver.2.1)
      (own, delivered) .both
  let controller :=
    (parent.strict.receiver.1.1.1).memberController A false
  let next := profiledRawJointGuardedCommonRightStrictReceiverRecvOwner A
    strategy hwin parent.strict.receiver owner own delivered
  (next.1, ⟨⟨⟨next.2.1, controller.step ownerControl delivered⟩,
    next.2, rfl⟩, close⟩)

/-- Strict-left mirror. -/
noncomputable def
    advanceProfiledRawJointGuardedCommonTailAnchoredLeftParent
    (parent : ProfiledRawJointGuardedCommonTailLeftReceiver A strategy hwin)
    (own : In₁) (delivered : In₂) :
    Out₁ × ProfiledRawJointGuardedCommonTailLeftReceiver A strategy hwin :=
  let owner := parent.strict.owner
  let ownerControl := profiledRawJointGuardedCommonLeftStrictOwnerFor A
    strategy hwin parent.strict.receiver owner
  let close := profiledRawJointGuardedCommonLeftStageClose A strategy hwin
    parent.strict.receiver.1 (ownerControl, parent.strict.receiver.2.1)
      (own, delivered) .both
  let controller :=
    (parent.strict.receiver.1.1.2).memberController A false
  let next := profiledRawJointGuardedCommonLeftStrictReceiverRecvOwner A
    strategy hwin parent.strict.receiver owner own delivered
  (next.1, ⟨⟨next.2, ⟨next.2.1,
    controller.step ownerControl delivered⟩, rfl⟩, close⟩)

/-- The direct parent advance is exactly the existing exceptional-tail
self-powered transition, with only its sum injection removed. -/
@[simp] theorem
    advanceProfiledRawJointGuardedCommonTailAnchoredRightParent_spec
    (parent : ProfiledRawJointGuardedCommonTailRightReceiver A strategy hwin)
    (own : In₂) (delivered : In₁) :
    profiledRawJointGuardedCommonTailSelfContinueRightTwo A strategy hwin
        initialBank parent own delivered =
      let next :=
        advanceProfiledRawJointGuardedCommonTailAnchoredRightParent A strategy
          hwin parent own delivered
      (next.1, .exceptional
        (profiledRawJointGuardedCommonTailTwoOfRightReceiver A strategy hwin
          next.2)) :=
  rfl

/-- Left-parent mirror specification. -/
@[simp] theorem
    advanceProfiledRawJointGuardedCommonTailAnchoredLeftParent_spec
    (parent : ProfiledRawJointGuardedCommonTailLeftReceiver A strategy hwin)
    (own : In₁) (delivered : In₂) :
    profiledRawJointGuardedCommonTailSelfContinueLeftOne A strategy hwin
        initialBank parent own delivered =
      let next :=
        advanceProfiledRawJointGuardedCommonTailAnchoredLeftParent A strategy
          hwin parent own delivered
      (next.1, .exceptional
        (profiledRawJointGuardedCommonTailOneOfLeftReceiver A strategy hwin
          next.2)) :=
  rfl

/-! ## Immutable-anchor mixed states -/

/-- Mixed state after a first `both` out of guarded strict-right.  `parent`
contains the refreshed current close, whereas `anchor` is the old close used
to construct `recurrent`. -/
structure ProfiledRawJointGuardedCommonTailAnchoredRightMixed where
  parent : ProfiledRawJointGuardedCommonTailRightReceiver A strategy hwin
  anchor : ProfiledRawJointGuardedCommonRightStagedClose A strategy hwin
  recurrent : ProfiledRawJointGuardedCommonTailPoweredLeftReceiver A strategy
    hwin initialBank
  frozen : recurrent.key =
    profiledRawJointGuardedCommonRightStagedCombinedKey A strategy hwin
      initialBank anchor

/-- Strict-left mirror. -/
structure ProfiledRawJointGuardedCommonTailAnchoredLeftMixed where
  parent : ProfiledRawJointGuardedCommonTailLeftReceiver A strategy hwin
  anchor : ProfiledRawJointGuardedCommonLeftStagedClose A strategy hwin
  recurrent : ProfiledRawJointGuardedCommonTailPoweredRightReceiver A strategy
    hwin initialBank
  frozen : recurrent.key =
    profiledRawJointGuardedCommonLeftStagedCombinedKey A strategy hwin
      initialBank anchor

noncomputable instance
    profiledRawJointGuardedCommonTailAnchoredRightMixedFintype :
    Fintype (ProfiledRawJointGuardedCommonTailAnchoredRightMixed A strategy
      hwin initialBank) := by
  classical
  apply Fintype.ofInjective
    (fun state : ProfiledRawJointGuardedCommonTailAnchoredRightMixed A strategy
      hwin initialBank ↦ (state.parent, state.anchor, state.recurrent))
  intro left right heq
  cases left
  cases right
  cases heq
  rfl

noncomputable instance
    profiledRawJointGuardedCommonTailAnchoredLeftMixedFintype :
    Fintype (ProfiledRawJointGuardedCommonTailAnchoredLeftMixed A strategy
      hwin initialBank) := by
  classical
  apply Fintype.ofInjective
    (fun state : ProfiledRawJointGuardedCommonTailAnchoredLeftMixed A strategy
      hwin initialBank ↦ (state.parent, state.anchor, state.recurrent))
  intro left right heq
  cases left
  cases right
  cases heq
  rfl

/-! ## The first simultaneous round -/

/-- Enter the strict-right mixed phase.  The recurrent receiver is built from
`parent.close` before the guarded parent is advanced. -/
noncomputable def
    startProfiledRawJointGuardedCommonTailAnchoredRightMixed
    (parent : ProfiledRawJointGuardedCommonTailRightReceiver A strategy hwin)
    (current : In₁ × In₂) :
    (Out₁ × Out₂) ×
      ProfiledRawJointGuardedCommonTailAnchoredRightMixed A strategy hwin
        initialBank :=
  let anchor := parent.close
  let recurrent :=
    profiledRawJointGuardedCommonRightStagedStartPoweredLeftReceiver A
      strategy hwin initialBank anchor current.1 current.2
  let parentNext :=
    advanceProfiledRawJointGuardedCommonTailAnchoredRightParent A strategy hwin
      parent current.2 current.1
  ((recurrent.1, parentNext.1),
    ⟨parentNext.2, anchor, recurrent.2, rfl⟩)

/-- Strict-left mixed entry mirror. -/
noncomputable def
    startProfiledRawJointGuardedCommonTailAnchoredLeftMixed
    (parent : ProfiledRawJointGuardedCommonTailLeftReceiver A strategy hwin)
    (current : In₁ × In₂) :
    (Out₁ × Out₂) ×
      ProfiledRawJointGuardedCommonTailAnchoredLeftMixed A strategy hwin
        initialBank :=
  let anchor := parent.close
  let parentNext :=
    advanceProfiledRawJointGuardedCommonTailAnchoredLeftParent A strategy hwin
      parent current.1 current.2
  let recurrent :=
    profiledRawJointGuardedCommonLeftStagedStartPoweredRightReceiver A
      strategy hwin initialBank anchor current.2 current.1
  ((parentNext.1, recurrent.1),
    ⟨parentNext.2, anchor, recurrent.2, rfl⟩)

@[simp] theorem
    startProfiledRawJointGuardedCommonTailAnchoredRightMixed_anchor
    (parent : ProfiledRawJointGuardedCommonTailRightReceiver A strategy hwin)
    (current : In₁ × In₂) :
    (startProfiledRawJointGuardedCommonTailAnchoredRightMixed A strategy hwin
      initialBank parent current).2.anchor = parent.close :=
  rfl

@[simp] theorem
    startProfiledRawJointGuardedCommonTailAnchoredLeftMixed_anchor
    (parent : ProfiledRawJointGuardedCommonTailLeftReceiver A strategy hwin)
    (current : In₁ × In₂) :
    (startProfiledRawJointGuardedCommonTailAnchoredLeftMixed A strategy hwin
      initialBank parent current).2.anchor = parent.close :=
  rfl

/-- The right mixed phase stays keyed by the pre-receive close, independently
of the refreshed close stored in its current parent. -/
@[simp] theorem
    ProfiledRawJointGuardedCommonTailAnchoredRightMixed.recurrent_key
    (state : ProfiledRawJointGuardedCommonTailAnchoredRightMixed A strategy
      hwin initialBank) :
    state.recurrent.key =
      profiledRawJointGuardedCommonRightStagedCombinedKey A strategy hwin
        initialBank state.anchor :=
  state.frozen

/-- Left mirror. -/
@[simp] theorem
    ProfiledRawJointGuardedCommonTailAnchoredLeftMixed.recurrent_key
    (state : ProfiledRawJointGuardedCommonTailAnchoredLeftMixed A strategy
      hwin initialBank) :
    state.recurrent.key =
      profiledRawJointGuardedCommonLeftStagedCombinedKey A strategy hwin
        initialBank state.anchor :=
  state.frozen

/-! ## Strict-right-parent mixed resolutions -/

/-- A following strict-left round continues the frozen left receiver and its
retained matching owner. -/
noncomputable def
    resolveProfiledRawJointGuardedCommonTailAnchoredRightMixedLeft
    (state : ProfiledRawJointGuardedCommonTailAnchoredRightMixed A strategy
      hwin initialBank)
    (current : In₁ × In₂) :
    (Out₁ × Out₂) ×
      (LeftReceiver A strategy hwin initialBank state.recurrent.key ×
        LeftOwner A strategy hwin initialBank state.recurrent.key) :=
  let key := state.recurrent.key
  let source := CombinedSource A strategy hwin initialBank key
  let policy := CombinedPolicy A strategy hwin initialBank key
  let bank := CombinedBank A strategy hwin initialBank key
  let owner : LeftOwner A strategy hwin initialBank key :=
    ⟨state.recurrent.receiver.1, state.recurrent.owner⟩
  let receiverNext := continueProfiledRawJointUnitLeftPolicyReceiver A strategy
    source policy bank state.recurrent.receiver owner current
  let ownerNext := stepProfiledRawJointUnitLeftPolicyOwner A strategy source
    policy bank owner current.2
  ((receiverNext.1, ownerNext.1), (receiverNext.2, ownerNext.2))

/-- A following strict-right round switches both controls from the frozen left
receiver into the ordinary right orientation. -/
noncomputable def
    resolveProfiledRawJointGuardedCommonTailAnchoredRightMixedRight
    (state : ProfiledRawJointGuardedCommonTailAnchoredRightMixed A strategy
      hwin initialBank)
    (current : In₁ × In₂) :
    (Out₁ × Out₂) ×
      (RightOwner A strategy hwin initialBank state.recurrent.key ×
        RightReceiver A strategy hwin initialBank state.recurrent.key) :=
  let key := state.recurrent.key
  let source := CombinedSource A strategy hwin initialBank key
  let policy := CombinedPolicy A strategy hwin initialBank key
  let bank := CombinedBank A strategy hwin initialBank key
  let owner := profiledRawJointUnitPolicyStartRightOwner A strategy source
    policy bank state.recurrent.receiver current.1
  let receiver := profiledRawJointUnitPolicyStartRightReceiver A strategy
    source policy bank state.recurrent.receiver (current.2, current.1)
  ((owner.1, receiver.1), (owner.2, receiver.2))

/-- A following simultaneous round produces the ordinary receiver/receiver
cross at the frozen key. -/
noncomputable def
    resolveProfiledRawJointGuardedCommonTailAnchoredRightMixedBoth
    (state : ProfiledRawJointGuardedCommonTailAnchoredRightMixed A strategy
      hwin initialBank)
    (current : In₁ × In₂) :
    (Out₁ × Out₂) ×
      (LeftReceiver A strategy hwin initialBank state.recurrent.key ×
        RightReceiver A strategy hwin initialBank state.recurrent.key) :=
  let key := state.recurrent.key
  let source := CombinedSource A strategy hwin initialBank key
  let policy := CombinedPolicy A strategy hwin initialBank key
  let bank := CombinedBank A strategy hwin initialBank key
  let owner : LeftOwner A strategy hwin initialBank key :=
    ⟨state.recurrent.receiver.1, state.recurrent.owner⟩
  let left := continueProfiledRawJointUnitLeftPolicyReceiver A strategy source
    policy bank state.recurrent.receiver owner current
  let right := profiledRawJointUnitPolicyStartRightReceiver A strategy source
    policy bank state.recurrent.receiver (current.2, current.1)
  ((left.1, right.1), (left.2, right.2))

/-! ## Strict-left-parent mixed resolutions -/

/-- A following strict-right round continues the frozen right receiver and
its retained matching owner. -/
noncomputable def
    resolveProfiledRawJointGuardedCommonTailAnchoredLeftMixedRight
    (state : ProfiledRawJointGuardedCommonTailAnchoredLeftMixed A strategy
      hwin initialBank)
    (current : In₁ × In₂) :
    (Out₁ × Out₂) ×
      (RightOwner A strategy hwin initialBank state.recurrent.key ×
        RightReceiver A strategy hwin initialBank state.recurrent.key) :=
  let key := state.recurrent.key
  let source := CombinedSource A strategy hwin initialBank key
  let policy := CombinedPolicy A strategy hwin initialBank key
  let bank := CombinedBank A strategy hwin initialBank key
  let owner : RightOwner A strategy hwin initialBank key :=
    ⟨state.recurrent.receiver.1, state.recurrent.owner⟩
  let receiverNext := continueProfiledRawJointUnitRightPolicyReceiver A
    strategy source policy bank state.recurrent.receiver owner
      (current.2, current.1)
  let ownerNext := stepProfiledRawJointUnitRightPolicyOwner A strategy source
    policy bank owner current.1
  ((ownerNext.1, receiverNext.1), (ownerNext.2, receiverNext.2))

/-- A following strict-left round switches both controls from the frozen right
receiver into the ordinary left orientation. -/
noncomputable def
    resolveProfiledRawJointGuardedCommonTailAnchoredLeftMixedLeft
    (state : ProfiledRawJointGuardedCommonTailAnchoredLeftMixed A strategy
      hwin initialBank)
    (current : In₁ × In₂) :
    (Out₁ × Out₂) ×
      (LeftReceiver A strategy hwin initialBank state.recurrent.key ×
        LeftOwner A strategy hwin initialBank state.recurrent.key) :=
  let key := state.recurrent.key
  let source := CombinedSource A strategy hwin initialBank key
  let policy := CombinedPolicy A strategy hwin initialBank key
  let bank := CombinedBank A strategy hwin initialBank key
  let receiver := profiledRawJointUnitPolicyStartLeftReceiver A strategy source
    policy bank state.recurrent.receiver current
  let owner := profiledRawJointUnitPolicyStartLeftOwner A strategy source
    policy bank state.recurrent.receiver current.2
  ((receiver.1, owner.1), (receiver.2, owner.2))

/-- A following simultaneous round produces the mirror ordinary
receiver/receiver cross at the frozen key. -/
noncomputable def
    resolveProfiledRawJointGuardedCommonTailAnchoredLeftMixedBoth
    (state : ProfiledRawJointGuardedCommonTailAnchoredLeftMixed A strategy
      hwin initialBank)
    (current : In₁ × In₂) :
    (Out₁ × Out₂) ×
      (LeftReceiver A strategy hwin initialBank state.recurrent.key ×
        RightReceiver A strategy hwin initialBank state.recurrent.key) :=
  let key := state.recurrent.key
  let source := CombinedSource A strategy hwin initialBank key
  let policy := CombinedPolicy A strategy hwin initialBank key
  let bank := CombinedBank A strategy hwin initialBank key
  let left := profiledRawJointUnitPolicyStartLeftReceiver A strategy source
    policy bank state.recurrent.receiver current
  let owner : RightOwner A strategy hwin initialBank key :=
    ⟨state.recurrent.receiver.1, state.recurrent.owner⟩
  let right := continueProfiledRawJointUnitRightPolicyReceiver A strategy
    source policy bank state.recurrent.receiver owner (current.2, current.1)
  ((left.1, right.1), (left.2, right.2))

/-! ## Frozen-key endpoint facts -/

/-- All three right-parent resolvers have endpoint controls at this one key,
which is the immutable pre-receive anchor key. -/
theorem profiledRawJointGuardedCommonTailAnchoredRightMixed_frozenKey
    (state : ProfiledRawJointGuardedCommonTailAnchoredRightMixed A strategy
      hwin initialBank) :
    state.recurrent.key =
      profiledRawJointGuardedCommonRightStagedCombinedKey A strategy hwin
        initialBank state.anchor :=
  state.frozen

/-- All three left-parent resolvers have endpoint controls at this one key. -/
theorem profiledRawJointGuardedCommonTailAnchoredLeftMixed_frozenKey
    (state : ProfiledRawJointGuardedCommonTailAnchoredLeftMixed A strategy
      hwin initialBank) :
    state.recurrent.key =
      profiledRawJointGuardedCommonLeftStagedCombinedKey A strategy hwin
        initialBank state.anchor :=
  state.frozen

end

end DetParityAutomaton

end DistributedSynthesis
