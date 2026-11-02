/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionPostResolveReceiveTimingAudit

/-!
# A phase-live fork at the actual post-resolve boundary

The timing audit shows that a reversal does not create a same-target receiver
fork.  Its open receiver has advanced in the table staged on the preceding
block round, whereas its closed receiver is fresh at the target emitted by
the closing record.  Those two receivers need not have the same key and must
not themselves be used as the next blind sender.

This file records the finite carrier which avoids that false comparison.  A
pending endpoint stores the actual old/new receiver fork dormantly.  Its two
unresolved members instead share one live sender state rooted at the new
target.  A no-receive advances only that shared sender and retains the whole
receiver fork.  Hence output equality and blind closure are definitional for
arbitrary old and new roots.

This construction proves the relay-level blind law only.  A correctness
relation must additionally show that the shared live sender is a legal sender
for both the old open history and the new closed history.  The present
code-indexed fresh-policy bank proves legality only for its selected fresh
source; it does not prove the old-history half.  That transition-linked
sender theorem comes before receive-side closure and is deliberately not
assumed here.  Once it is available, the next receive must use the retained
member to select and advance the corresponding dormant receiver.
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

variable (strategy : StrategyPair In₁ In₂ Out₁ Out₂)

/-! ## Finite phase-live pending controls -/

/-- Process one's shared post-boundary state.  The first component is the
only state executed by a blind no-receive.  The receiver fork is dormant
until a later receive resolves its member. -/
abbrev ProfiledRawJointPostResolvePhaseLiveOneShared :=
  ProfiledRawJointPostResolveFreshOneBlindControl A strategy ×
    FiniteDelayedFork
      (ProfiledRawJointPostResolveFreshTargetLeftReceiverControl A strategy)

/-- Process-two mirror. -/
abbrev ProfiledRawJointPostResolvePhaseLiveTwoShared :=
  ProfiledRawJointPostResolveFreshTwoBlindControl A strategy ×
    FiniteDelayedFork
      (ProfiledRawJointPostResolveFreshTargetRightReceiverControl A strategy)

/-- The member bit selects a dormant receiver; the payload is currently
empty because both receiver candidates are stored in the shared state. -/
abbrev ProfiledRawJointPostResolvePhaseLiveOnePending :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (ProfiledRawJointPostResolvePhaseLiveOneShared A strategy) Unit

/-- Process-two mirror pending state. -/
abbrev ProfiledRawJointPostResolvePhaseLiveTwoPending :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (ProfiledRawJointPostResolvePhaseLiveTwoShared A strategy) Unit

noncomputable instance :
    Fintype (ProfiledRawJointPostResolvePhaseLiveOneShared A strategy) := by
  classical
  infer_instance

noncomputable instance :
    Fintype (ProfiledRawJointPostResolvePhaseLiveTwoShared A strategy) := by
  classical
  infer_instance

noncomputable instance :
    Fintype (ProfiledRawJointPostResolvePhaseLiveOnePending A strategy) := by
  classical
  infer_instance

noncomputable instance :
    Fintype (ProfiledRawJointPostResolvePhaseLiveTwoPending A strategy) := by
  classical
  infer_instance

/-! ## The actual old/new boundary fork -/

/-- At a right-to-left boundary, process one's next blind sender is rooted at
the newly emitted target.  Its dormant open receiver is the advanced old
receiver and its dormant closed receiver is the new simultaneous root. -/
noncomputable def profiledRawJointPostResolveRightPhaseLiveShared
    (oldRoot newRoot :
      ProfiledRawJointPostResolveRightFreshInstalledRoot A strategy)
    (input : In₁ × In₂) :
    ProfiledRawJointPostResolvePhaseLiveOneShared A strategy :=
  let freshClosed :=
    (profiledRawJointPostResolveRightFreshLeftReceiverFork A strategy
      newRoot.1).closedControl
  (.inl freshClosed,
    profiledRawJointPostResolveRightFreshReceiverBoundaryFork A strategy
      oldRoot newRoot input)

/-- Mirrored left-to-right boundary. -/
noncomputable def profiledRawJointPostResolveLeftPhaseLiveShared
    (oldRoot newRoot :
      ProfiledRawJointPostResolveLeftFreshInstalledRoot A strategy)
    (input : In₂ × In₁) :
    ProfiledRawJointPostResolvePhaseLiveTwoShared A strategy :=
  let freshClosed :=
    (profiledRawJointPostResolveLeftFreshRightReceiverFork A strategy
      newRoot.1).closedControl
  (.inl freshClosed,
    profiledRawJointPostResolveLeftFreshReceiverBoundaryFork A strategy
      oldRoot newRoot input)

/-- The unresolved process-one member fork.  Both candidates carry exactly
the same executable shared state. -/
noncomputable def profiledRawJointPostResolveRightPhaseLivePendingFork
    (oldRoot newRoot :
      ProfiledRawJointPostResolveRightFreshInstalledRoot A strategy)
    (input : In₁ × In₂) :
    FiniteDelayedFork
      (ProfiledRawJointPostResolvePhaseLiveOnePending A strategy) :=
  FiniteAcknowledgedDelayedCarrier.deferredMemberFork
    (profiledRawJointPostResolveRightPhaseLiveShared A strategy oldRoot
      newRoot input) ()

/-- Mirrored unresolved process-two fork. -/
noncomputable def profiledRawJointPostResolveLeftPhaseLivePendingFork
    (oldRoot newRoot :
      ProfiledRawJointPostResolveLeftFreshInstalledRoot A strategy)
    (input : In₂ × In₁) :
    FiniteDelayedFork
      (ProfiledRawJointPostResolvePhaseLiveTwoPending A strategy) :=
  FiniteAcknowledgedDelayedCarrier.deferredMemberFork
    (profiledRawJointPostResolveLeftPhaseLiveShared A strategy oldRoot
      newRoot input) ()

@[simp] theorem profiledRawJointPostResolveRightPhaseLive_open_receiver
    (oldRoot newRoot :
      ProfiledRawJointPostResolveRightFreshInstalledRoot A strategy)
    (input : In₁ × In₂) :
    (profiledRawJointPostResolveRightPhaseLivePendingFork A strategy oldRoot
      newRoot input).openControl.2.1.2.openControl =
        (profiledRawJointPostResolveRightFreshReceiverBoundaryFork A strategy
          oldRoot newRoot input).openControl :=
  rfl

@[simp] theorem profiledRawJointPostResolveRightPhaseLive_closed_receiver
    (oldRoot newRoot :
      ProfiledRawJointPostResolveRightFreshInstalledRoot A strategy)
    (input : In₁ × In₂) :
    (profiledRawJointPostResolveRightPhaseLivePendingFork A strategy oldRoot
      newRoot input).closedControl.2.1.2.closedControl =
        (profiledRawJointPostResolveRightFreshReceiverBoundaryFork A strategy
          oldRoot newRoot input).closedControl :=
  rfl

@[simp] theorem profiledRawJointPostResolveLeftPhaseLive_open_receiver
    (oldRoot newRoot :
      ProfiledRawJointPostResolveLeftFreshInstalledRoot A strategy)
    (input : In₂ × In₁) :
    (profiledRawJointPostResolveLeftPhaseLivePendingFork A strategy oldRoot
      newRoot input).openControl.2.1.2.openControl =
        (profiledRawJointPostResolveLeftFreshReceiverBoundaryFork A strategy
          oldRoot newRoot input).openControl :=
  rfl

@[simp] theorem profiledRawJointPostResolveLeftPhaseLive_closed_receiver
    (oldRoot newRoot :
      ProfiledRawJointPostResolveLeftFreshInstalledRoot A strategy)
    (input : In₂ × In₁) :
    (profiledRawJointPostResolveLeftPhaseLivePendingFork A strategy oldRoot
      newRoot input).closedControl.2.1.2.closedControl =
        (profiledRawJointPostResolveLeftFreshReceiverBoundaryFork A strategy
          oldRoot newRoot input).closedControl :=
  rfl

/-! ## Member-independent blind evolution -/

/-- A process-one blind step advances only the common live sender and leaves
both dormant receivers untouched. -/
noncomputable def profiledRawJointPostResolvePhaseLiveOneStep
    (_member : Bool)
    (shared : ProfiledRawJointPostResolvePhaseLiveOneShared A strategy)
    (input : In₁) :
    ProfiledRawJointPostResolvePhaseLiveOneShared A strategy × Out₁ :=
  let next := profiledRawJointPostResolveFreshOneBlindNoRecv A strategy
    shared.1 input
  ((next.1, shared.2), next.2)

/-- Process-two mirror. -/
noncomputable def profiledRawJointPostResolvePhaseLiveTwoStep
    (_member : Bool)
    (shared : ProfiledRawJointPostResolvePhaseLiveTwoShared A strategy)
    (input : In₂) :
    ProfiledRawJointPostResolvePhaseLiveTwoShared A strategy × Out₂ :=
  let next := profiledRawJointPostResolveFreshTwoBlindNoRecv A strategy
    shared.1 input
  ((next.1, shared.2), next.2)

/-- The process-one phase-live step is independent of the unresolved member. -/
theorem profiledRawJointPostResolvePhaseLiveOneStepLaws :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberStepLaws
      (profiledRawJointPostResolvePhaseLiveOneStep A strategy) where
  outputEq := by
    intro shared input
    rfl
  stateEq := by
    intro shared input
    rfl

/-- Mirrored member-independence. -/
theorem profiledRawJointPostResolvePhaseLiveTwoStepLaws :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberStepLaws
      (profiledRawJointPostResolvePhaseLiveTwoStep A strategy) where
  outputEq := by
    intro shared input
    rfl
  stateEq := by
    intro shared input
    rfl

/-- The actual two-target process-one fork is blind-related for arbitrary old
and new roots; no key equality is required. -/
theorem profiledRawJointPostResolveRightPhaseLivePendingFork_blind
    (oldRoot newRoot :
      ProfiledRawJointPostResolveRightFreshInstalledRoot A strategy)
    (input : In₁ × In₂) :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberBlind
      (profiledRawJointPostResolveRightPhaseLivePendingFork A strategy oldRoot
        newRoot input).openControl
      (profiledRawJointPostResolveRightPhaseLivePendingFork A strategy oldRoot
        newRoot input).closedControl := by
  exact FiniteAcknowledgedDelayedCarrier.deferredMemberFork_blind _ _

/-- Mirrored blind relation without an old/new-key premise. -/
theorem profiledRawJointPostResolveLeftPhaseLivePendingFork_blind
    (oldRoot newRoot :
      ProfiledRawJointPostResolveLeftFreshInstalledRoot A strategy)
    (input : In₂ × In₁) :
    FiniteAcknowledgedDelayedCarrier.DeferredMemberBlind
      (profiledRawJointPostResolveLeftPhaseLivePendingFork A strategy oldRoot
        newRoot input).openControl
      (profiledRawJointPostResolveLeftPhaseLivePendingFork A strategy oldRoot
        newRoot input).closedControl := by
  exact FiniteAcknowledgedDelayedCarrier.deferredMemberFork_blind _ _

/-- Every first blind input produces the same process-one output from the
actual boundary fork. -/
theorem profiledRawJointPostResolveRightPhaseLivePendingFork_coherent
    (oldRoot newRoot :
      ProfiledRawJointPostResolveRightFreshInstalledRoot A strategy)
    (boundaryInput : In₁ × In₂) (input : In₁) :
    (profiledRawJointPostResolveRightPhaseLivePendingFork A strategy oldRoot
      newRoot boundaryInput).NoRecvMealyOutputCoherent
        (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
          (profiledRawJointPostResolvePhaseLiveOneStep A strategy)) input := by
  exact
    FiniteAcknowledgedDelayedCarrier.deferredMemberFork_noRecvOutputCoherent
      (profiledRawJointPostResolvePhaseLiveOneStep A strategy)
      (profiledRawJointPostResolvePhaseLiveOneStepLaws A strategy) _ _ input

/-- Process-two mirror. -/
theorem profiledRawJointPostResolveLeftPhaseLivePendingFork_coherent
    (oldRoot newRoot :
      ProfiledRawJointPostResolveLeftFreshInstalledRoot A strategy)
    (boundaryInput : In₂ × In₁) (input : In₂) :
    (profiledRawJointPostResolveLeftPhaseLivePendingFork A strategy oldRoot
      newRoot boundaryInput).NoRecvMealyOutputCoherent
        (FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
          (profiledRawJointPostResolvePhaseLiveTwoStep A strategy)) input := by
  exact
    FiniteAcknowledgedDelayedCarrier.deferredMemberFork_noRecvOutputCoherent
      (profiledRawJointPostResolvePhaseLiveTwoStep A strategy)
      (profiledRawJointPostResolvePhaseLiveTwoStepLaws A strategy) _ _ input

/-- A blind process-one step preserves both the blind relation and output
equality.  The dormant old/new receiver fork is retained as part of the
common shared state. -/
theorem profiledRawJointPostResolvePhaseLiveOne_blind_noRecv
    (left right : ProfiledRawJointPostResolvePhaseLiveOnePending A strategy)
    (input : In₁)
    (hblind : FiniteAcknowledgedDelayedCarrier.DeferredMemberBlind left
      right) :
    let step := FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
      (profiledRawJointPostResolvePhaseLiveOneStep A strategy)
    (step left input).2 = (step right input).2 ∧
      FiniteAcknowledgedDelayedCarrier.DeferredMemberBlind
        (step left input).1 (step right input).1 := by
  dsimp only
  exact FiniteAcknowledgedDelayedCarrier.deferredMemberBlind_noRecv
    (profiledRawJointPostResolvePhaseLiveOneStep A strategy)
    (profiledRawJointPostResolvePhaseLiveOneStepLaws A strategy) left right
      input hblind

/-- Mirrored one-step blind closure. -/
theorem profiledRawJointPostResolvePhaseLiveTwo_blind_noRecv
    (left right : ProfiledRawJointPostResolvePhaseLiveTwoPending A strategy)
    (input : In₂)
    (hblind : FiniteAcknowledgedDelayedCarrier.DeferredMemberBlind left
      right) :
    let step := FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv
      (profiledRawJointPostResolvePhaseLiveTwoStep A strategy)
    (step left input).2 = (step right input).2 ∧
      FiniteAcknowledgedDelayedCarrier.DeferredMemberBlind
        (step left input).1 (step right input).1 := by
  dsimp only
  exact FiniteAcknowledgedDelayedCarrier.deferredMemberBlind_noRecv
    (profiledRawJointPostResolvePhaseLiveTwoStep A strategy)
    (profiledRawJointPostResolvePhaseLiveTwoStepLaws A strategy) left right
      input hblind

end

end DetParityAutomaton

end DistributedSynthesis
